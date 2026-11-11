// File: src/elf64.rs (64GB Virtual Arena per App: 0x10_0000_0000 & 0x20_0000_0000 + SMP AP Trampoline)
use crate::ir::*;
use std::collections::HashMap;

const RT_PARALLEL: &[u8] = include_bytes!("rt/rt_parallel.bin");
const RT_EXC: &[u8] = include_bytes!("rt/rt_exc.bin");

fn pack_elf64(code: &[u8], entry_offset: u64, panic_offset: Option<u64>) -> Result<Vec<u8>, String> {
    let base: u32 = 0x100000;
    let mut elf = Vec::new();

    // 1. ELF Header (52B) + Program Header (32B) = 84B (0x54)
    elf.extend_from_slice(&[
        0x7F, b'E', b'L', b'F', 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 1, 0, 0, 0,
    ]);
    let entry_vaddr = base + 0xA8;
    elf.extend_from_slice(&entry_vaddr.to_le_bytes());
    elf.extend_from_slice(&52u32.to_le_bytes());
    elf.extend_from_slice(&0u32.to_le_bytes());
    elf.extend_from_slice(&0u32.to_le_bytes());
    elf.extend_from_slice(&52u16.to_le_bytes());
    elf.extend_from_slice(&32u16.to_le_bytes());
    elf.extend_from_slice(&1u16.to_le_bytes());
    elf.extend_from_slice(&[0u8; 6]);

    // Program Header PT_LOAD (32B)
    elf.extend_from_slice(&1u32.to_le_bytes());
    elf.extend_from_slice(&0u32.to_le_bytes());
    elf.extend_from_slice(&base.to_le_bytes());
    elf.extend_from_slice(&base.to_le_bytes());
    elf.extend_from_slice(&0u32.to_le_bytes());
    elf.extend_from_slice(&0u32.to_le_bytes());
    elf.extend_from_slice(&7u32.to_le_bytes());
    elf.extend_from_slice(&0x1000u32.to_le_bytes());

    // 2. Multiboot1 Header tại offset 0x54 (48B) + GDT 64-bit tại 0x88 (24B) + GDTR tại 0xA0 (8B), entry tại 0xA8
    // flags = bit 1 (Memory Map) | bit 2 (xin chế độ đồ họa: linear 1920x1080x32; GRUB EFI trả framebuffer GOP thật,
    // có thể khác kích thước — kernel đọc lại từ Multiboot Info). Cờ 0x40 cũ là bit không định nghĩa: QEMU bỏ qua
    // nhưng GRUB từ chối ("unsupported flag"). checksum = -(magic + flags)
    let mb_flags: u32 = 0x0000_0006;
    elf.extend_from_slice(&0x1BADB002u32.to_le_bytes());
    elf.extend_from_slice(&mb_flags.to_le_bytes());
    elf.extend_from_slice(&0u32.wrapping_sub(0x1BADB002u32.wrapping_add(mb_flags)).to_le_bytes());
    elf.extend_from_slice(&[0u8; 20]); // header_addr..entry_addr (bit 16 tắt: dùng ELF header)
    for v in [0u32, 1920, 1080, 32] {
        elf.extend_from_slice(&v.to_le_bytes()); // mode_type = 0 (linear), width, height, depth
    }
    elf.extend_from_slice(&[0u8; 4]);
    assert_eq!(elf.len(), 0x88);
    elf.extend_from_slice(&0x0000000000000000u64.to_le_bytes());
    elf.extend_from_slice(&0x00AF9A000000FFFFu64.to_le_bytes());
    elf.extend_from_slice(&0x00CF92000000FFFFu64.to_le_bytes());
    elf.extend_from_slice(&23u16.to_le_bytes());
    elf.extend_from_slice(&(base + 0x88).to_le_bytes());
    elf.extend_from_slice(&0u16.to_le_bytes());
    assert_eq!(elf.len(), 0xA8);

    // 3. Trampoline 32-bit -> 64-bit Long Mode (Đặt Page Table tại 0x10000 để Kernel .lit tự cấp phát Lô động!):
    //    - 0x10000: PML4 (CR3 = 0x10000)
    //    - 0x11000: PDPT (Kernel .lit sẽ tự gắn các Lô 64GB vào đây lúc chạy!)
    //    - 0x12000: PD_0 (0..24MB cho Kernel, VRAM, PD_Pool, Backbuffer, DMA USB, LightFS)
    //    - 0x20000: PD_Pool (Bể chứa bảng trang động cho N Apps)
    elf.extend_from_slice(&[
        0xFA, // cli
        0xB0, 0xFF, 0xE6, 0x21, 0xE6, 0xA1, // mov al, 0xff; out 0x21, al; out 0xa1, al (Mask 8259 PIC)
        0xBC, 0x00, 0x00, 0x07, 0x00, // mov esp, 0x70000
        // Sao chép Multiboot Info (128B, gồm cả trường framebuffer 88..115) -> 0x7d000 và Memory Map (tối đa 0xF00B)
        // -> 0x7d100 (EBX còn nguyên từ Bootloader) để Kernel .lit đọc được bằng con trỏ hằng
        0x89, 0xDE, 0xBF, 0x00, 0xD0, 0x07, 0x00, 0xB9, 0x20, 0x00, 0x00, 0x00, 0xFC, 0xF3,
        0xA5, // mov esi, ebx; mov edi, 0x7d000; mov ecx, 32; cld; rep movsd
        0xF6, 0x05, 0x00, 0xD0, 0x07, 0x00, 0x40, // test byte [0x7d000], 0x40 (cờ mmap hợp lệ?)
        0x74, 0x23, // jz skip_mmap
        0x8B, 0x35, 0x30, 0xD0, 0x07, 0x00, // mov esi, [0x7d030] (mmap_addr)
        0x8B, 0x0D, 0x2C, 0xD0, 0x07, 0x00, // mov ecx, [0x7d02c] (mmap_length)
        0x81, 0xF9, 0x00, 0x0F, 0x00, 0x00, // cmp ecx, 0xF00
        0x76, 0x05, // jbe +5
        0xB9, 0x00, 0x0F, 0x00, 0x00, // mov ecx, 0xF00
        0xC1, 0xE9, 0x02, // shr ecx, 2
        0xBF, 0x00, 0xD1, 0x07, 0x00, // mov edi, 0x7d100
        0xF3, 0xA5, // rep movsd
        // skip_mmap: Firmware UEFI có thể để Local APIC ở chế độ x2APIC (MMIO 0xFEE00000 khi đó vô hiệu) ->
        // x2APIC -> tắt hẳn -> xAPIC (chuyển thẳng x2APIC -> xAPIC là #GP theo Intel SDM)
        0xB9, 0x1B, 0x00, 0x00, 0x00, // mov ecx, 0x1B (IA32_APIC_BASE)
        0x0F, 0x32,                   // rdmsr
        0xA9, 0x00, 0x04, 0x00, 0x00, // test eax, 0x400 (EXTD)
        0x74, 0x0E,                   // jz +14
        0x25, 0xFF, 0xF3, 0xFF, 0xFF, // and eax, ~0xC00 (EN = EXTD = 0)
        0x0F, 0x30,                   // wrmsr
        0x0D, 0x00, 0x08, 0x00, 0x00, // or eax, 0x800 (EN = 1, xAPIC)
        0x0F, 0x30,                   // wrmsr
        // PAT: PA1 (PWT=1, PCD=0) = Write-Combining thay cho Write-Through -> ánh xạ framebuffer dùng WC;
        // PA0 = WB (mọi ánh xạ RAM hiện có), PA3 = UC (MMIO: PCD|PWT) giữ như mặc định
        0xB9, 0x77, 0x02, 0x00, 0x00, // mov ecx, 0x277 (IA32_PAT)
        0xB8, 0x06, 0x01, 0x07, 0x00, // mov eax, 0x00070106
        0xBA, 0x06, 0x04, 0x07, 0x00, // mov edx, 0x00070406
        0x0F, 0x30,                   // wrmsr
        0xBF, 0x00, 0x00, 0x01, 0x00, 0xB9, 0x00, 0x80, 0x00, 0x00, 0x31, 0xC0, 0xFC, 0xF3,
        0xAB, // Clear 0x10000..0x30000
        0xC7, 0x05, 0x00, 0x00, 0x01, 0x00, 0x03, 0x10, 0x01, 0x00, // PML4[0] (0x10000) = 0x11003
        0xC7, 0x05, 0x00, 0x10, 0x01, 0x00, 0x03, 0x20, 0x01, 0x00, // PDPT[0] (0x11000) = 0x12003
        0xB9, 0x01, 0x00, 0x00, 0x00, // mov ecx, 1
        0x89, 0xC8, 0xC1, 0xE0, 0x1E, // mov eax, ecx; shl eax, 30
        0x0D, 0x83, 0x00, 0x00, 0x00, // or eax, 0x83
        0x89, 0x04, 0xCD, 0x00, 0x10, 0x01, 0x00, // mov [ecx*8 + 0x11000], eax
        0x89, 0xC8, 0xC1, 0xE8, 0x02, // mov eax, ecx; shr eax, 2
        0x89, 0x04, 0xCD, 0x04, 0x10, 0x01, 0x00, // mov [ecx*8 + 0x11004], eax
        0x41, 0x83, 0xF9, 0x40, 0x7C, 0xDD, // inc ecx; cmp ecx, 64; jl -35
        0xC7, 0x05, 0x00, 0x20, 0x01, 0x00, 0x83, 0x00, 0x00, 0x00, // PD_0[0] (0x12000) = 0..2MB RAM
        // VRAM logic 0x200000..0x600000 = RAM (identity). Framebuffer thật do kernel .lit ánh xạ (fb_init) và
        // chép ra bằng fb_present_rect. Trước đây chỗ này đọc mò BAR0 của PCI 00:02.0 — trên Intel iGPU đó là
        // thanh ghi GPU, không phải framebuffer.
        0xC7, 0x05, 0x08, 0x20, 0x01, 0x00, 0x83, 0x00, 0x20, 0x00, // PD_0[1] = 0x200000 | 0x83
        0xC7, 0x05, 0x10, 0x20, 0x01, 0x00, 0x83, 0x00, 0x40, 0x00, // PD_0[2] = 0x400000 | 0x83
        // VRAM logic 1920x1080 (8MB) = 0x200000..0xA00000 (PD_0[1..4]) + 2MB PD_Pool tại 0xA00000..0xC00000
        // + 8MB Backbuffer tại 0xC00000..0x1400000 (PD_0[6..9])
        0xC7, 0x05, 0x18, 0x20, 0x01, 0x00, 0x83, 0x00, 0x60, 0x00, 0xC7, 0x05, 0x20, 0x20, 0x01,
        0x00, 0x83, 0x00, 0x80, 0x00, 0xC7, 0x05, 0x28, 0x20, 0x01, 0x00, 0x83, 0x00, 0xA0, 0x00,
        0xC7, 0x05, 0x30, 0x20, 0x01, 0x00, 0x83, 0x00, 0xC0, 0x00, // PD_0[6] = 0xC00000 | 0x83
        0xC7, 0x05, 0x38, 0x20, 0x01, 0x00, 0x83, 0x00, 0xE0, 0x00, // PD_0[7] = 0xE00000 | 0x83
        0xC7, 0x05, 0x40, 0x20, 0x01, 0x00, 0x83, 0x00, 0x00, 0x01, // PD_0[8] = 0x1000000 | 0x83
        0xC7, 0x05, 0x48, 0x20, 0x01, 0x00, 0x83, 0x00, 0x20, 0x01, // PD_0[9] = 0x1200000 | 0x83
        0xC7, 0x05, 0x50, 0x20, 0x01, 0x00, 0x83, 0x00, 0x40, 0x01, // PD_0[10] = 0x1400000 | 0x83 (DMA USB xHCI)
        0xC7, 0x05, 0x58, 0x20, 0x01, 0x00, 0x83, 0x00, 0x60, 0x01, // PD_0[11] = 0x1600000 | 0x83 (LightFS: bảng, bitmap)
        0xC7, 0x05, 0x60, 0x20, 0x01, 0x00, 0x83, 0x00, 0x80, 0x01, // PD_0[12] = 0x1800000 | 0x83 (DMA xHCI thứ 2)
        0xBF, 0x00, 0x00, 0xA0, 0x00, 0xB9, 0x00, 0x00, 0x08, 0x00, 0x31, 0xC0, 0xFC, 0xF3, 0xAB,
        // Bật PAE + SSE/FXSR (CR4 = 0x620) + Long Mode + Paging (CR3 = 0x10000)
        0xB8, 0x00, 0x00, 0x01, 0x00, 0x0F, 0x22, 0xD8, 0x0F, 0x20, 0xE0, 0x0D, 0x20, 0x06, 0x00,
        0x00, 0x0F, 0x22, 0xE0, 0xB9, 0x80, 0x00, 0x00, 0xC0, 0x0F, 0x32, 0x0D, 0x00, 0x01, 0x00,
        0x00, 0x0F, 0x30, 0x0F, 0x20, 0xC0, 0x0D, 0x00, 0x00, 0x00, 0x80, 0x0F, 0x22, 0xC0, 0x0F,
        0x01, 0x15, 0xA0, 0x00, 0x10, 0x00, // lgdt [0x1000A0]
    ]);
    let start64 = base + (elf.len() as u32) + 7;
    elf.push(0xEA);
    elf.extend_from_slice(&start64.to_le_bytes());
    elf.extend_from_slice(&0x0008u16.to_le_bytes());

    // 4. Đoạn khởi tạo 64-bit của BSP (Core 0):
    elf.extend_from_slice(&[0x66, 0xB8, 0x10, 0x00, 0x8E, 0xD8, 0x8E, 0xC0, 0x8E, 0xD0]);

    // Xây dựng AP Trampoline tại 0x8000 (Chạy khi được đánh thức -> Tính xong -> Tự động HLT ngủ 0% CPU!)
    let mut ap_code: Vec<u8> = Vec::new();
    ap_code.extend_from_slice(&[
        0xFA, // cli
        0x31, 0xC0, 0x8E, 0xD8, 0x8E, 0xC0, 0x8E, 0xD0, 0x0F, 0x01, 0x16, 0x00,
        0x82, // lgdt [0x8200]
        0x0F, 0x20, 0xC0, 0x66, 0x83, 0xC8, 0x01, 0x0F, 0x22, 0xC0, // CR0.PE = 1
    ]);
    let ap_32_addr = 0x8000u16 + (ap_code.len() as u16) + 5;
    ap_code.push(0xEA);
    ap_code.extend_from_slice(&ap_32_addr.to_le_bytes());
    ap_code.extend_from_slice(&0x0018u16.to_le_bytes());

    ap_code.extend_from_slice(&[
        0x66, 0xB8, 0x10, 0x00, 0x8E, 0xD8, 0x8E, 0xC0, 0x8E, 0xD0, 0xB8, 0x00, 0x00, 0x01, 0x00,
        0x0F, 0x22, 0xD8, // CR3 = 0x10000
        0x0F, 0x20, 0xE0, 0x0D, 0x20, 0x06, 0x00, 0x00, 0x0F, 0x22, 0xE0, // CR4.PAE | OSFXSR | OSXMMEXCPT
        0xB9, 0x80, 0x00, 0x00, 0xC0, 0x0F, 0x32, 0x0D, 0x00, 0x01, 0x00, 0x00, 0x0F,
        0x30, // EFER.LME = 1
        0x0F, 0x20, 0xC0, 0x0D, 0x00, 0x00, 0x00, 0x80, 0x0F, 0x22, 0xC0, // CR0.PG = 1
    ]);
    let ap_64_addr = 0x8000u32 + (ap_code.len() as u32) + 7;
    ap_code.push(0xEA);
    ap_code.extend_from_slice(&ap_64_addr.to_le_bytes());
    ap_code.extend_from_slice(&0x0008u16.to_le_bytes());

    ap_code.extend_from_slice(&[
        0x66, 0xB8, 0x10, 0x00, 0x8E, 0xD8, 0x8E, 0xC0, 0x8E, 0xD0,
        // Mở khóa FPU/SSE + AVX2 256-bit (YMM0..YMM15) trên các nhân phụ AP:
        0x0F, 0x20, 0xC0, 0x66, 0x83, 0xE0, 0xFB, 0x66, 0x83, 0xC8, 0x02, 0x0F, 0x22, 0xC0,
        0x80, 0x3C, 0x25, 0x08, 0xE0, 0x07, 0x00, 0x00, 0x74, 0x17, 0x0F, 0x20, 0xE0, 0x48,
        0x0F, 0xBA, 0xE8, 0x12, 0x0F, 0x22, 0xE0, 0x31, 0xC9, 0xB8, 0x07, 0x00, 0x00, 0x00,
        0x31, 0xD2, 0x0F, 0x01, 0xD1,
        0xB8, 0x01, 0x00, 0x00, 0x00,
        0x0F, 0xA2, // cpuid (eax=1)
        0x89, 0xD8, 0xC1, 0xE8, 0x18,       // eax = apic_id
        // Chỉ APIC ID 1..15 làm worker (slot 1..15 của bảng SMP); ID khác dừng hẳn. Trước đây `and eax, 7`
        // làm ID 8..15 trùng slot 0..7 -> hai AP chạy cùng một việc.
        0x8D, 0x50, 0xFF,                   // lea edx, [rax-1]
        0x83, 0xFA, 0x0E,                   // cmp edx, 14
        0x76, 0x04,                         // jbe +4
        0xFA, 0xF4, 0xEB, 0xFC,             // cli; hlt; jmp hlt
        // Nạp IDT & Cấp Stack 32KB riêng biệt cho từng AP: RSP = 0x150000 + (apic_id << 15) (<= 0x1C8000, dưới VRAM 0x200000)
        0x0F, 0x01, 0x1C, 0x25, 0x00, 0x98, 0x00, 0x00, // lidt [0x9800]
        0x89, 0xC1,                         // mov ecx, eax
        0xC1, 0xE1, 0x0F,                   // shl ecx, 15
        0xBC, 0x00, 0x00, 0x15, 0x00,       // mov esp, 0x150000
        0x48, 0x01, 0xCC,                   // add rsp, rcx
        // rbp = 0x7e000 + (apic_id << 5)
        0x89, 0xC5,                         // mov ebp, eax
        0xC1, 0xE5, 0x05,                   // shl ebp, 5
        0x48, 0x81, 0xC5, 0x00, 0xE0, 0x07, 0x00, // add rbp, 0x7e000
        // Bật Local APIC trên AP (SVR = 0x1FF):
        0xBA, 0xF0, 0x00, 0xE0, 0xFE,       // mov edx, 0xFEE000F0
        0xC7, 0x02, 0xFF, 0x01, 0x00, 0x00, // mov dword [rdx], 0x000001FF
        // Báo đã online: bật bit apic_id trong bitmask tại 0x7e010 (slot 0 [2]); `parallel` chỉ giao việc cho AP online
        0xF0, 0x48, 0x0F, 0xAB, 0x04, 0x25, 0x10, 0xE0, 0x07, 0x00, // lock bts [0x7e010], rax
    // worker_idle (Atomic STI + HLT, ngủ 0% CPU cho tới khi nhận Fixed IPI từ spawn):
        0xFA,                               // cli
        0x48, 0x8B, 0x45, 0x00,             // mov rax, [rbp + 0]
        0x48, 0x85, 0xC0,                   // test rax, rax
        0x75, 0x04,                         // jnz do_work (+4 bytes)
        0xFB,                               // sti
        0xF4,                               // hlt (vCPU ngủ thực sự, 0% CPU trên host!)
        0xEB, 0xF2,                         // jmp worker_idle (-14 bytes)
    // do_work:
        0x55,                               // push rbp
        0x48, 0x8B, 0x7D, 0x08,             // mov rdi, [rbp + 8]  (slice_ptr)
        0x48, 0x8B, 0x75, 0x10,             // mov rsi, [rbp + 16] (arg1)
        0x48, 0x8B, 0x55, 0x18,             // mov rdx, [rbp + 24] (chỉ số phần i)
        // Nạp lại CR3 = xả TLB của AP: kernel có thể đã gỡ/đổi ánh xạ chunk (mem_req thu hồi rồi cấp lại khung khác)
        // từ lần chạy trước; TLB cũ của AP sẽ trỏ vào khung đã thuộc App khác.
        0x0F, 0x20, 0xD9,                   // mov rcx, cr3
        0x0F, 0x22, 0xD9,                   // mov cr3, rcx
        0xFF, 0xD0,                         // call rax
        0x5D,                               // pop rbp
        0x48, 0x89, 0x45, 0x18,             // mov [rbp + 24], rax
        0x48, 0xC7, 0x45, 0x00, 0x00, 0x00, 0x00, 0x00, // mov qword [rbp + 0], 0 (báo BSP đã xong)
        0xEB, 0xCE,                         // jmp worker_idle (-50 bytes, lập tức quay lại HLT ngủ!)
    ]);
    assert!(ap_code.len() <= 0x200, "AP trampoline đè lên GDT tại 0x8200");

    for (idx, &b) in ap_code.iter().enumerate() {
        let addr = (0x8000 + idx) as u32;
        elf.extend_from_slice(&[0xC6, 0x04, 0x25]);
        elf.extend_from_slice(&addr.to_le_bytes());
        elf.push(b);
    }

    let ap_gdt: [u64; 4] = [
        0x0000000000000000,
        0x00AF9A000000FFFF,
        0x00CF92000000FFFF,
        0x00CF9A000000FFFF,
    ];
    let mut gdt_bytes = Vec::new();
    for entry in ap_gdt {
        gdt_bytes.extend_from_slice(&entry.to_le_bytes());
    }
    for (idx, &b) in gdt_bytes.iter().enumerate() {
        let addr = (0x8210 + idx) as u32;
        elf.extend_from_slice(&[0xC6, 0x04, 0x25]);
        elf.extend_from_slice(&addr.to_le_bytes());
        elf.push(b);
    }

    elf.extend_from_slice(&[
        0x48, 0xC7, 0xC7, 0x00, 0xE0, 0x07, 0x00, 0xB9, 0x40, 0x00, 0x00, 0x00, 0x31, 0xC0, 0xF3,
        0x48, 0xAB, 0x66, 0xC7, 0x04, 0x25, 0x00, 0x82, 0x00, 0x00, 0x1F, 0x00, 0xC7, 0x04, 0x25,
        0x02, 0x82, 0x00, 0x00, 0x10, 0x82, 0x00, 0x00, 0xB8, 0xF0, 0x00, 0xE0, 0xFE, 0xC7, 0x00,
        0xFF, 0x01, 0x00, 0x00,
        // Nhận diện số lượng CPU Core thực tế từ phần cứng qua CPUID (leaf 1: ebx[23:16])
        // Ghi (Tổng số core - 1) vào 0x7e000[0] để làm số lượng Worker APs (Core 1..N-1)
        0xB8, 0x01, 0x00, 0x00, 0x00, // mov eax, 1
        0x0F, 0xA2,                   // cpuid
        0xC1, 0xEB, 0x10,             // shr ebx, 16
        0x81, 0xE3, 0xFF, 0x00, 0x00, 0x00, // and ebx, 0xFF
        0xFF, 0xCB,                   // dec ebx
        0x85, 0xDB,                   // test ebx, ebx
        0x79, 0x02,                   // jns +2
        0x31, 0xDB,                   // xor ebx, ebx
        0x48, 0x89, 0x1C, 0x25, 0x00, 0xE0, 0x07, 0x00, // mov [0x7e000], rbx
        // Mở khóa FPU/SSE (CR0.EM=0, CR0.MP=1) & Kiểm tra CPUID mở khóa AVX2 256-bit (CR4.OSXSAVE + XCR0=7)
        // Ghi cờ phần cứng AVX2 vào [0x7e008] (1 = AVX2 YMM 256-bit, 0 = SSE2 XMM Fallback)
        0x0F, 0x20, 0xC0, 0x66, 0x83, 0xE0, 0xFB, 0x66, 0x83, 0xC8, 0x02, 0x0F, 0x22, 0xC0,
        0xB8, 0x01, 0x00, 0x00, 0x00, 0x0F, 0xA2,
        0x81, 0xE1, 0x00, 0x00, 0x00, 0x14, 0x81, 0xF9, 0x00, 0x00, 0x00, 0x14, 0x75, 0x2D,
        0xB8, 0x07, 0x00, 0x00, 0x00, 0x31, 0xC9, 0x0F, 0xA2, 0xF6, 0xC3, 0x20, 0x74, 0x1F,
        0x0F, 0x20, 0xE0, 0x48, 0x0F, 0xBA, 0xE8, 0x12, 0x0F, 0x22, 0xE0,
        0x31, 0xC9, 0xB8, 0x07, 0x00, 0x00, 0x00, 0x31, 0xD2, 0x0F, 0x01, 0xD1,
        0xC6, 0x04, 0x25, 0x08, 0xE0, 0x07, 0x00, 0x01,
        // Khởi tạo bảng IDT toàn cục (0x9000..0x9800) và nạp IPI Handler (0x8300):
        // 1. Ghi ipi_handler vào 0x8300 (push rax; mov eax, 0xFEE000B0; mov [rax], 0; pop rax; iretq):
        0x48, 0xB8, 0x50, 0xB8, 0xB0, 0x00, 0xE0, 0xFE, 0xC7, 0x00,
        0x48, 0x89, 0x04, 0x25, 0x00, 0x83, 0x00, 0x00,
        0x48, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x58, 0x48, 0xCF, 0x90,
        0x48, 0x89, 0x04, 0x25, 0x08, 0x83, 0x00, 0x00,
        // 2. Điền 128 Gate Descriptor (16B mỗi gate, trỏ về 0x8300, CS=0x08, Type=0x8E) vào 0x9000:
        0x48, 0xC7, 0xC7, 0x00, 0x90, 0x00, 0x00,
        0xB9, 0x80, 0x00, 0x00, 0x00,
        0x48, 0xB8, 0x00, 0x83, 0x08, 0x00, 0x00, 0x8E, 0x00, 0x00,
        0x48, 0x89, 0x07,
        0x48, 0xC7, 0x47, 0x08, 0x00, 0x00, 0x00, 0x00,
        0x48, 0x83, 0xC7, 0x10,
        0xFF, 0xC9,
        0x75, 0xED,
    ]);
    // 2b. Vector 0..31 (exception CPU) trỏ về stub trong rt_exc.bin (đặt cuối ảnh ELF, địa chỉ vá sau),
    //     các vector còn lại vẫn là IPI handler 0x8300. [0x8FF0] = cờ đang panic, [0x8FF8] = địa chỉ kernel_panic.
    let mut gate_patches = Vec::new();
    for i in 0..32u32 {
        elf.extend_from_slice(&[0x48, 0xB8]);
        gate_patches.push(elf.len());
        elf.extend_from_slice(&0u64.to_le_bytes());
        elf.extend_from_slice(&[0x48, 0x89, 0x04, 0x25]);
        elf.extend_from_slice(&(0x9000 + 16 * i).to_le_bytes());
    }
    elf.extend_from_slice(&[0x48, 0xC7, 0x04, 0x25, 0xF0, 0x8F, 0x00, 0x00, 0, 0, 0, 0]);
    elf.extend_from_slice(&[0x48, 0xB8]);
    let panic_patch = elf.len();
    elf.extend_from_slice(&0u64.to_le_bytes());
    elf.extend_from_slice(&[0x48, 0x89, 0x04, 0x25, 0xF8, 0x8F, 0x00, 0x00]);
    elf.extend_from_slice(&[
        // 3. Ghi IDT Pointer tại 0x9800 (limit=0x07FF, base=0x9000) và nạp IDT trên BSP:
        0x66, 0xC7, 0x04, 0x25, 0x00, 0x98, 0x00, 0x00, 0xFF, 0x07,
        0x48, 0xC7, 0x04, 0x25, 0x02, 0x98, 0x00, 0x00, 0x00, 0x90, 0x00, 0x00,
        0x0F, 0x01, 0x1C, 0x25, 0x00, 0x98, 0x00, 0x00, // lidt [0x9800]
        0xFA,                                           // cli
        // Đánh thức tất cả các nhân AP 1..N vào Long Mode & Worker Loop lúc boot:
        // Nếu số worker ([0x7e000]) > 0:
        0x48, 0x83, 0x3C, 0x25, 0x00, 0xE0, 0x07, 0x00, 0x00, // cmp qword [0x7e000], 0
        0x74, 0x2C,                                           // jz skip_ap_boot (+44 bytes)
        // rax = 0xFEE00300 (Local APIC ICR low)
        0xB8, 0x00, 0x03, 0xE0, 0xFE,                         // mov eax, 0xFEE00300
        // Gửi INIT IPI broadcast tới All Excluding Self (0x000C4500)
        0xC7, 0x00, 0x00, 0x45, 0x0C, 0x00,                   // mov dword [rax], 0x000C4500
        0xB9, 0x40, 0x4B, 0x4C, 0x00,                         // mov ecx, 5000000 (~10ms chờ INIT trên máy thật)
        0xE2, 0xFE,                                           // loop $
        // Gửi SIPI broadcast tới All Excluding Self với vector 0x08 (0x000C4608), 2 lần như Intel MP spec
        // (máy thật có thể bỏ lỡ SIPI đầu; AP đã chạy thì bỏ qua SIPI thứ hai)
        0xC7, 0x00, 0x08, 0x46, 0x0C, 0x00,                   // mov dword [rax], 0x000C4608
        0xB9, 0xA0, 0x86, 0x01, 0x00,                         // mov ecx, 100000
        0xE2, 0xFE,                                           // loop $
        0xC7, 0x00, 0x08, 0x46, 0x0C, 0x00,                   // mov dword [rax], 0x000C4608
        0xB9, 0xA0, 0x86, 0x01, 0x00,                         // mov ecx, 100000
        0xE2, 0xFE,                                           // loop $
        // skip_ap_boot:
    ]);

    let call_rel = (entry_offset as u32) + 2;
    elf.push(0xE8);
    elf.extend_from_slice(&call_rel.to_le_bytes());
    elf.extend_from_slice(&[0xFA, 0xF4]);

    let code_start = elf.len() as u64;
    elf.extend_from_slice(code);
    while elf.len() % 16 != 0 {
        elf.push(0xCC);
    }
    let exc_addr = base as u64 + elf.len() as u64;
    elf.extend_from_slice(RT_EXC);
    for (i, &pos) in gate_patches.iter().enumerate() {
        let a = exc_addr + 16 * i as u64; // mỗi stub 16 byte
        let gate = (a & 0xFFFF) | (0x08 << 16) | (0x8E << 40) | (((a >> 16) & 0xFFFF) << 48);
        elf[pos..pos + 8].copy_from_slice(&gate.to_le_bytes());
    }
    let panic_addr = panic_offset.map_or(0, |o| base as u64 + code_start + o);
    elf[panic_patch..panic_patch + 8].copy_from_slice(&panic_addr.to_le_bytes());
    // Ảnh kernel nạp tại 0x100000 và phải kết thúc trước vùng stack AP (0x150000)
    if elf.len() > 0x50000 {
        return Err(format!("Ảnh kernel {} byte vượt 0x50000 (đè lên stack nhân AP tại 0x150000)", elf.len()));
    }
    // Bảng section header tối thiểu (1 section SHN_UNDEF rỗng, 40B): GRUB 2.14 từ chối ELF có e_shoff = 0
    // ("invalid section header table offset in e_shoff"); QEMU -kernel thì không kiểm tra.
    while elf.len() % 4 != 0 {
        elf.push(0);
    }
    let shoff = elf.len() as u32;
    elf.extend_from_slice(&[0u8; 40]);
    elf[32..36].copy_from_slice(&shoff.to_le_bytes()); // e_shoff
    elf[46..48].copy_from_slice(&40u16.to_le_bytes()); // e_shentsize
    elf[48..50].copy_from_slice(&1u16.to_le_bytes()); // e_shnum
    elf[50..52].copy_from_slice(&0u16.to_le_bytes()); // e_shstrndx
    let fsz = (elf.len() as u32).to_le_bytes();
    elf[68..72].copy_from_slice(&fsz);
    elf[72..76].copy_from_slice(&fsz);
    Ok(elf)
}

/// Blob ATA viết tay chỉ được thay thế khi biên dịch Kernel VÀ chữ ký hàm khớp đúng hợp đồng mà blob tôn trọng
/// (ghi tối đa count*512 <= 128KB vào buffer 16384 Qword, dùng cổng 0x1F0..0x1F7). Trước đây App chỉ cần đặt
/// trùng tên hàm là nhận được blob: in/out cổng ATA không cần thẻ io và ghi tràn buffer tùy ý.
fn ata_blob_allowed(module: &Module, func: &Func, is_kernel: bool) -> bool {
    let dq = module.layouts.iter().position(|l| l.name == "DiskQword" && l.size == 8);
    is_kernel
        && func.name == "drv_ata_read_sectors_batch"
        && dq.is_some()
        && func.params.iter().map(|p| p.1).collect::<Vec<_>>()
            == [
                Type::Io { min: 0x1f0, max: 0x1f7 },
                Type::Ptr { layout_id: dq.unwrap() as u16, max_elems: 16384 },
                Type::Bv64,
                Type::Bv64,
            ]
        && func.requires.len() >= 4
}

/// Kiểm tra chữ ký hàm App khớp đúng những gì Kernel truyền vào qua `call %ptr` (CallPtr không kiểm tra kiểu).
/// `provided`: (tên Layout, max_elems) cho con trỏ, hoặc None cho số nguyên bv64. App được nhận ÍT tham số hơn hoặc
/// thu hẹp max_elems, nhưng không được nới rộng, đổi Layout hay tự khai báo thẻ io (nếu không App sẽ tự cấp quyền gốc).
const ROOT_IO_TY: Type = Type::Io { min: 0, max: 0xFFFF };

/// Giá trị Kernel truyền cho App qua `call %ptr`
#[derive(Debug)]
enum Prov {
    Int,
    Ptr(&'static str, u64),
    Smp,
    /// ptr<L,%n> với %n = tham số thứ `.1` của App (Kernel bảo đảm vùng đã map đúng độ dài đó)
    DPtr(&'static str, usize),
}

fn check_app_abi(module: &Module, fname: &str, provided: &[Prov]) -> Result<(), String> {
    let Some(f) = module.funcs.iter().find(|f| f.name == fname) else {
        return Ok(());
    };
    if f.params.len() > provided.len() {
        return Err(format!("ABI App: '{}' nhận {} tham số, Kernel chỉ truyền {}", fname, f.params.len(), provided.len()));
    }
    for (i, (&(r, ty), want)) in f.params.iter().zip(provided).enumerate() {
        let ok = match (ty, want) {
            (Type::Bv64, Prov::Int) | (Type::Smp, Prov::Smp) => true,
            (Type::Ptr { layout_id, max_elems }, Prov::Ptr(lname, kmax)) => {
                let l = &module.layouts[layout_id as usize];
                l.name == *lname && max_elems <= *kmax
            }
            // Độ dài phải đúng là tham số mà Kernel dùng làm độ dài (không phải tham số số nguyên khác)
            (Type::DPtr { layout_id, len }, Prov::DPtr(lname, li)) => {
                let l = &module.layouts[layout_id as usize];
                l.name == *lname && f.params.get(*li).map(|p| p.0) == Some(len)
            }
            _ => false,
        };
        if !ok {
            return Err(format!(
                "ABI App: tham số #{} (%{}: {:?}) của '{}' không khớp với giá trị Kernel truyền ({:?})",
                i, r, ty, fname, want
            ));
        }
    }
    Ok(())
}

/// Trả về (mã máy, offset hàm cuối = entry, offset app_draw_icon, offset app_smp_worker, offset kernel_panic)
fn compile_raw(module: &Module, is_kernel: bool) -> Result<(Vec<u8>, u64, u64, u64, Option<u64>), String> {
    let (code, offs) = compile_code(module, is_kernel)?;
    let off_of = |name: &str| module.funcs.iter().position(|f| f.name == name).map(|i| offs[i] as u64);
    let entry_offset = offs.last().copied().unwrap_or(0) as u64;
    let icon_offset = off_of("app_draw_icon").unwrap_or(0);
    let worker_offset = off_of("app_smp_worker").unwrap_or(0);
    Ok((code, entry_offset, icon_offset, worker_offset, off_of("kernel_panic")))
}

/// Mã máy của cả module + offset bắt đầu của từng hàm (theo thứ tự module.funcs)
pub fn compile_code(module: &Module, is_kernel: bool) -> Result<(Vec<u8>, Vec<usize>), String> {
    let mut code: Vec<u8> = Vec::new();
    let mut func_addrs: HashMap<u32, usize> = HashMap::new();
    let mut call_patches: Vec<(usize, u32)> = Vec::new();
    let mut rt_patches: Vec<usize> = Vec::new();

    for (f_idx, func) in module.funcs.iter().enumerate() {
        func_addrs.insert(f_idx as u32, code.len());

        // Tối ưu hóa phần cứng tầng Driver ATA: Dùng lệnh x86-64 REP INSW đọc khối trực tiếp
        // Giảm số lần ngắt trap máy ảo từ 12 triệu lần xuống còn 47.000 lần (nhanh gấp 256 lần!)
        if ata_blob_allowed(module, func, is_kernel) {
            code.extend_from_slice(&[
                0x53, 0x41, 0x54, 0x41, 0x55, 0x41, 0x56, 0x41, 0x57, 0x49, 0x89, 0xF4, 0x49, 0x89, 0xD5, 0x49,
                0x89, 0xCE, 0x4C, 0x89, 0xE8, 0x48, 0xC1, 0xE8, 0x18, 0x24, 0x0F, 0x0C, 0xE0, 0x66, 0xBA, 0xF6,
                0x01, 0xEE, 0x4C, 0x89, 0xF0, 0x66, 0xBA, 0xF2, 0x01, 0xEE, 0x4C, 0x89, 0xE8, 0x66, 0xBA, 0xF3,
                0x01, 0xEE, 0x4C, 0x89, 0xE8, 0x48, 0xC1, 0xE8, 0x08, 0x66, 0xBA, 0xF4, 0x01, 0xEE, 0x4C, 0x89,
                0xE8, 0x48, 0xC1, 0xE8, 0x10, 0x66, 0xBA, 0xF5, 0x01, 0xEE, 0xB0, 0x20, 0x66, 0xBA, 0xF7, 0x01,
                0xEE, 0x4D, 0x89, 0xF7, 0x4D, 0x85, 0xFF, 0x74, 0x2C, 0xB9, 0x40, 0x42, 0x0F, 0x00, 0x66, 0xBA,
                0xF7, 0x01, 0xEC, 0x24, 0x88, 0x3C, 0x08, 0x74, 0x04, 0xFF, 0xC9, 0x75, 0xF1, 0xFC, 0x4C, 0x89,
                0xE7, 0x66, 0xBA, 0xF0, 0x01, 0xB9, 0x00, 0x01, 0x00, 0x00, 0x66, 0xF3, 0x6D, 0x49, 0x89, 0xFC,
                0x49, 0xFF, 0xCF, 0xEB, 0xCF, 0x41, 0x5F, 0x41, 0x5E, 0x41, 0x5D, 0x41, 0x5C, 0x5B, 0xC3,
            ]);
            continue;
        }

        crate::x86::emit_func(module, func, &mut code, &mut call_patches, &mut rt_patches)?;
    }

    if !rt_patches.is_empty() {
        while code.len() % 16 != 0 {
            code.push(0xCC);
        }
        let rt = code.len();
        code.extend_from_slice(RT_PARALLEL);
        for p in rt_patches {
            let rel = (rt as i32) - ((p + 4) as i32);
            code[p..p + 4].copy_from_slice(&rel.to_le_bytes());
        }
    }
    for (patch_pos, f_id) in call_patches {
        let target_addr = *func_addrs.get(&f_id).ok_or("Không tìm thấy func_id")?;
        let rel = (target_addr as i32) - ((patch_pos + 4) as i32);
        code[patch_pos..patch_pos + 4].copy_from_slice(&rel.to_le_bytes());
    }

    let offs = (0..module.funcs.len()).map(|i| func_addrs[&(i as u32)]).collect();
    Ok((code, offs))
}

pub fn compile_elf64(module: &Module) -> Result<Vec<u8>, String> {
    // kernel_panic được gọi từ stub exception (rt_exc.s) với rdi=0 (thẻ io ghost), rsi=vector, rdx=mã lỗi,
    // rcx=RIP, r8=CR2, r9=APIC ID — không ai chứng minh được @req tại đó nên cấm @req.
    if let Some(f) = module.funcs.iter().find(|f| f.name == "kernel_panic") {
        let want = [ROOT_IO_TY, Type::Bv64, Type::Bv64, Type::Bv64, Type::Bv64, Type::Bv64];
        if f.params.iter().map(|p| p.1).collect::<Vec<_>>() != want || !f.requires.is_empty() {
            return Err("kernel_panic phải có chữ ký (io<0,0xffff>, bv64 vec, bv64 err, bv64 rip, bv64 cr2, bv64 apic) và không có @req".into());
        }
    }
    let (code, entry_offset, _, _, panic_offset) = compile_raw(module, true)?;
    pack_elf64(&code, entry_offset, panic_offset)
}

pub fn compile_app_bin(module: &Module) -> Result<Vec<u8>, String> {
    if !module.funcs.iter().any(|f| f.name == "app_draw_icon") {
        return Err("Mỗi App bắt buộc phải implement hàm 'func app_draw_icon'!".into());
    }
    // Khớp với app_dispatch_entry: call %code VgaCell* Ipc* State Q64 Q64 smp heap_len heap; app_dispatch_draw_icon.
    // State = 15 chunk tĩnh luôn được map (30MB); heap = mọi chunk ĐÃ map (độ dài động, đổi theo mem_req).
    let main_name = module.funcs.last().map(|f| f.name.clone()).unwrap_or_default();
    check_app_abi(
        module,
        &main_name,
        &[
            Prov::Ptr("VgaCell", 1382400),
            Prov::Ptr("IpcChannel", 1),
            Prov::Ptr("DiskQword", 3932160),
            Prov::Ptr("DiskQword", 64),
            Prov::Ptr("DiskQword", 64),
            Prov::Smp,
            Prov::Int,
            Prov::DPtr("DiskQword", 6),
        ],
    )?;
    check_app_abi(module, "app_draw_icon", &[Prov::Ptr("VgaCell", 1382400), Prov::Int, Prov::Int])?;
    let (code, entry_offset, icon_offset, worker_offset, _) = compile_raw(module, false)?;
    let mut bin = Vec::with_capacity(24 + code.len());

    let rel_main = (entry_offset as i32) + 19;
    bin.push(0xE9);
    bin.extend_from_slice(&rel_main.to_le_bytes());
    bin.extend_from_slice(&[0x90, 0x90, 0x90]);

    let rel_icon = (icon_offset as i32) + 11;
    bin.push(0xE9);
    bin.extend_from_slice(&rel_icon.to_le_bytes());
    bin.extend_from_slice(&[0x90, 0x90, 0x90]);

    let rel_worker = (worker_offset as i32) + 3;
    bin.push(0xE9);
    bin.extend_from_slice(&rel_worker.to_le_bytes());
    bin.extend_from_slice(&[0x90, 0x90, 0x90]);

    bin.extend_from_slice(&code);
    if bin.len() > 1048576 {
        return Err(format!(
            "App binary quá lớn ({} > 1048576 bytes)!",
            bin.len()
        ));
    }
    Ok(bin)
}
