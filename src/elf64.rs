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
    let entry_vaddr = base + 0x80;
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

    // 2. Multiboot1 Header tại offset 0x54 (12B) + GDT 64-bit tại 0x60 (24B) + GDTR tại 0x78 (8B)
    // flags = 0x40 (bit 6): yêu cầu Bootloader/QEMU cung cấp Memory Map (mmap_length/mmap_addr). checksum = -(magic + flags)
    elf.extend_from_slice(&0x1BADB002u32.to_le_bytes());
    elf.extend_from_slice(&0x00000040u32.to_le_bytes());
    elf.extend_from_slice(&0xE4524FBEu32.to_le_bytes());
    elf.extend_from_slice(&0x0000000000000000u64.to_le_bytes());
    elf.extend_from_slice(&0x00AF9A000000FFFFu64.to_le_bytes());
    elf.extend_from_slice(&0x00CF92000000FFFFu64.to_le_bytes());
    elf.extend_from_slice(&23u16.to_le_bytes());
    elf.extend_from_slice(&(base + 0x60).to_le_bytes());
    elf.extend_from_slice(&0u16.to_le_bytes());

    // 3. Trampoline 32-bit -> 64-bit Long Mode (Đặt Page Table tại 0x10000 để Kernel .lit tự cấp phát Lô động!):
    //    - 0x10000: PML4 (CR3 = 0x10000)
    //    - 0x11000: PDPT (Kernel .lit sẽ tự gắn các Lô 64GB vào đây lúc chạy!)
    //    - 0x12000: PD_0 (0..10MB cho Kernel, VRAM, Backbuffer)
    //    - 0x20000: PD_Pool (Bể chứa bảng trang động cho N Apps)
    elf.extend_from_slice(&[
        0xFA, // cli
        0xB0, 0xFF, 0xE6, 0x21, 0xE6, 0xA1, // mov al, 0xff; out 0x21, al; out 0xa1, al (Mask 8259 PIC)
        0xBC, 0x00, 0x00, 0x07, 0x00, // mov esp, 0x70000
        // Sao chép Multiboot Info (96B) -> 0x7d000 và Memory Map (tối đa 0xF00B) -> 0x7d100 (EBX còn nguyên từ Bootloader)
        // để Kernel .lit đọc được bằng con trỏ hằng (vùng này nằm ngoài 0x10000..0x30000 bị xóa bên dưới)
        0x89, 0xDE, 0xBF, 0x00, 0xD0, 0x07, 0x00, 0xB9, 0x18, 0x00, 0x00, 0x00, 0xFC, 0xF3,
        0xA5, // mov esi, ebx; mov edi, 0x7d000; mov ecx, 24; cld; rep movsd
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
        // Đọc địa chỉ vật lý Linear Framebuffer từ PCI VGA BAR0
        0xB8, 0x10, 0x10, 0x00, 0x80, 0x66, 0xBA, 0xF8, 0x0C, 0xEF, 0x66, 0xBA, 0xFC, 0x0C, 0xED,
        0x25, 0x00, 0x00, 0xE0, 0xFF, 0x0D, 0x83, 0x00, 0x00, 0x00, 0xA3, 0x08, 0x20, 0x01, 0x00,
        0x05, 0x00, 0x00, 0x20, 0x00, 0xA3, 0x10, 0x20, 0x01, 0x00,
        // Ánh xạ 4MB Backbuffer RAM tại Virtual 0x600000..0xA00000 + 2MB PD_Pool tại 0xA00000..0xC00000
        0xC7, 0x05, 0x18, 0x20, 0x01, 0x00, 0x83, 0x00, 0x60, 0x00, 0xC7, 0x05, 0x20, 0x20, 0x01,
        0x00, 0x83, 0x00, 0x80, 0x00, 0xC7, 0x05, 0x28, 0x20, 0x01, 0x00, 0x83, 0x00, 0xA0, 0x00,
        0xBF, 0x00, 0x00, 0xA0, 0x00, 0xB9, 0x00, 0x00, 0x08, 0x00, 0x31, 0xC0, 0xFC, 0xF3, 0xAB,
        // Bật PAE + SSE/FXSR (CR4 = 0x620) + Long Mode + Paging (CR3 = 0x10000)
        0xB8, 0x00, 0x00, 0x01, 0x00, 0x0F, 0x22, 0xD8, 0x0F, 0x20, 0xE0, 0x0D, 0x20, 0x06, 0x00,
        0x00, 0x0F, 0x22, 0xE0, 0xB9, 0x80, 0x00, 0x00, 0xC0, 0x0F, 0x32, 0x0D, 0x00, 0x01, 0x00,
        0x00, 0x0F, 0x30, 0x0F, 0x20, 0xC0, 0x0D, 0x00, 0x00, 0x00, 0x80, 0x0F, 0x22, 0xC0, 0x0F,
        0x01, 0x15, 0x78, 0x00, 0x10, 0x00,
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
        0x74, 0x1F,                                           // jz skip_ap_boot (+31 bytes)
        // rax = 0xFEE00300 (Local APIC ICR low)
        0xB8, 0x00, 0x03, 0xE0, 0xFE,                         // mov eax, 0xFEE00300
        // Gửi INIT IPI broadcast tới All Excluding Self (0x000C4500)
        0xC7, 0x00, 0x00, 0x45, 0x0C, 0x00,                   // mov dword [rax], 0x000C4500
        0xB9, 0xA0, 0x86, 0x01, 0x00,                         // mov ecx, 100000
        0xE2, 0xFE,                                           // loop $
        // Gửi SIPI broadcast tới All Excluding Self với vector 0x08 (0x000C4608)
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
    let fsz = (elf.len() as u32).to_le_bytes();
    elf[68..72].copy_from_slice(&fsz);
    elf[72..76].copy_from_slice(&fsz);
    Ok(elf)
}

fn slot(r: Reg) -> i32 {
    -(((r as i32) + 1) * 8)
}

fn pick_hot_regs(func: &Func) -> [Reg; 5] {
    let mut score: HashMap<Reg, u32> = HashMap::new();
    for &(r, _) in &func.params {
        *score.entry(r).or_insert(0) += 2;
    }
    for (bi, b) in func.blocks.iter().enumerate() {
        let weight = if bi > 0 { 16 } else { 1 };
        for &(r, _) in &b.params {
            *score.entry(r).or_insert(0) += 100 * weight;
        }
        for inst in &b.insts {
            match inst {
                Inst::Bin { dst, lhs, rhs, .. } | Inst::Cmp { dst, lhs, rhs, .. } => {
                    *score.entry(*dst).or_insert(0) += weight;
                    *score.entry(*lhs).or_insert(0) += weight;
                    *score.entry(*rhs).or_insert(0) += weight;
                }
                Inst::Slice { dst, base, idx, .. } => {
                    *score.entry(*dst).or_insert(0) += weight;
                    *score.entry(*base).or_insert(0) += weight;
                    *score.entry(*idx).or_insert(0) += weight;
                }
                Inst::Load { dst, base, .. } => {
                    *score.entry(*dst).or_insert(0) += weight;
                    *score.entry(*base).or_insert(0) += weight;
                }
                Inst::Store { base, val, .. } => {
                    *score.entry(*base).or_insert(0) += weight;
                    *score.entry(*val).or_insert(0) += weight;
                }
                Inst::Simd256 { dst, lhs, rhs, .. } => {
                    *score.entry(*dst).or_insert(0) += weight;
                    *score.entry(*lhs).or_insert(0) += weight;
                    *score.entry(*rhs).or_insert(0) += weight;
                }
                Inst::Parallel { smp, n, base, arg, .. } => {
                    for r in [smp, n, base, arg] {
                        *score.entry(*r).or_insert(0) += weight;
                    }
                }
                Inst::AtaRead { ptr, idx, nsec, .. } => {
                    for r in [ptr, idx, nsec] {
                        *score.entry(*r).or_insert(0) += weight;
                    }
                }
                Inst::Br { cond, .. } => {
                    *score.entry(*cond).or_insert(0) += weight;
                }
                Inst::Jmp { args, .. } | Inst::Call { args, .. } => {
                    for &a in args {
                        *score.entry(a).or_insert(0) += weight * 2;
                    }
                }
                _ => {}
            }
        }
    }
    let mut ranked: Vec<(Reg, u32)> = score.into_iter().collect();
    ranked.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    let mut out = [u32::MAX; 5];
    for (i, &(r, _)) in ranked.iter().take(5).enumerate() {
        out[i] = r;
    }
    out
}

fn emit_load_rax(c: &mut Vec<u8>, r: Reg, hot: &[Reg; 5]) {
    if r == hot[0] {
        c.extend_from_slice(&[0x48, 0x89, 0xD8]);
    } else if r == hot[1] {
        c.extend_from_slice(&[0x4C, 0x89, 0xE0]);
    } else if r == hot[2] {
        c.extend_from_slice(&[0x4C, 0x89, 0xE8]);
    } else if r == hot[3] {
        c.extend_from_slice(&[0x4C, 0x89, 0xF0]);
    } else if r == hot[4] {
        c.extend_from_slice(&[0x4C, 0x89, 0xF8]);
    } else {
        c.extend_from_slice(&[0x48, 0x8B, 0x85]);
        c.extend_from_slice(&slot(r).to_le_bytes());
    }
}

fn emit_load_rcx(c: &mut Vec<u8>, r: Reg, hot: &[Reg; 5]) {
    if r == hot[0] {
        c.extend_from_slice(&[0x48, 0x89, 0xD9]);
    } else if r == hot[1] {
        c.extend_from_slice(&[0x4C, 0x89, 0xE1]);
    } else if r == hot[2] {
        c.extend_from_slice(&[0x4C, 0x89, 0xE9]);
    } else if r == hot[3] {
        c.extend_from_slice(&[0x4C, 0x89, 0xF1]);
    } else if r == hot[4] {
        c.extend_from_slice(&[0x4C, 0x89, 0xF9]);
    } else {
        c.extend_from_slice(&[0x48, 0x8B, 0x8D]);
        c.extend_from_slice(&slot(r).to_le_bytes());
    }
}

fn emit_store_rax(c: &mut Vec<u8>, r: Reg, hot: &[Reg; 5]) {
    if r == hot[0] {
        c.extend_from_slice(&[0x48, 0x89, 0xC3]);
    } else if r == hot[1] {
        c.extend_from_slice(&[0x49, 0x89, 0xC4]);
    } else if r == hot[2] {
        c.extend_from_slice(&[0x49, 0x89, 0xC5]);
    } else if r == hot[3] {
        c.extend_from_slice(&[0x49, 0x89, 0xC6]);
    } else if r == hot[4] {
        c.extend_from_slice(&[0x49, 0x89, 0xC7]);
    } else {
        c.extend_from_slice(&[0x48, 0x89, 0x85]);
        c.extend_from_slice(&slot(r).to_le_bytes());
    }
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

        let hot = pick_hot_regs(func);

        let mut reg_tys: HashMap<Reg, Type> = func.params.iter().cloned().collect();
        for b in &func.blocks {
            for &(r, ty) in &b.params {
                reg_tys.insert(r, ty);
            }
            for i in &b.insts {
                match i {
                    Inst::Const { dst, ty, .. }
                    | Inst::Load { dst, ty, .. }
                    | Inst::Slice { dst, ty, .. } => {
                        reg_tys.insert(*dst, *ty);
                    }
                    Inst::Cmp { dst, .. } => {
                        reg_tys.insert(*dst, Type::Bv8);
                    }
                    Inst::Bin { dst, .. }
                    | Inst::HwIo { dst: Some(dst), .. }
                    | Inst::CallPtr { dst: Some(dst), .. }
                    | Inst::SmpWorkers { dst, .. }
                    | Inst::Simd256 {
                        op: SimdOp::Dot,
                        dst,
                        ..
                    } => {
                        reg_tys.insert(*dst, Type::Bv64);
                    }
                    Inst::Call {
                        dst: Some(dst),
                        func_id,
                        ..
                    } => {
                        if let Some(t) = module.funcs[*func_id as usize].ret_ty {
                            reg_tys.insert(*dst, t);
                        }
                    }
                    _ => {}
                }
            }
        }

        let max_reg = reg_tys.keys().max().copied().unwrap_or(32);
        let frame_size = (((max_reg as u32 + 8) * 8 + 15) & !15).max(0x800);
        code.extend_from_slice(&[0x55, 0x48, 0x89, 0xE5, 0x48, 0x81, 0xEC]);
        code.extend_from_slice(&frame_size.to_le_bytes());
        code.extend_from_slice(&[
            0x53, 0x41, 0x54, 0x41, 0x55, 0x41, 0x56, 0x41, 0x57, 0x48, 0x83, 0xEC, 0x08,
        ]);

        let abi_to_rax: [&[u8]; 6] = [
            &[0x48, 0x89, 0xF8],
            &[0x48, 0x89, 0xF0],
            &[0x48, 0x89, 0xD0],
            &[0x48, 0x89, 0xC8],
            &[0x4C, 0x89, 0xC0],
            &[0x4C, 0x89, 0xC8],
        ];
        for (i, &(reg, _)) in func.params.iter().take(6).enumerate() {
            code.extend_from_slice(abi_to_rax[i]);
            emit_store_rax(&mut code, reg, &hot);
        }
        for (i, &(reg, _)) in func.params.iter().skip(6).enumerate() {
            let caller_off = (16 + i * 8) as i32;
            code.extend_from_slice(&[0x48, 0x8B, 0x85]);
            code.extend_from_slice(&caller_off.to_le_bytes());
            emit_store_rax(&mut code, reg, &hot);
        }

        let mut blk_addrs: HashMap<BlockId, usize> = HashMap::new();
        let mut jmp_patches: Vec<(usize, BlockId)> = Vec::new();

        for block in &func.blocks {
            blk_addrs.insert(block.id, code.len());
            for inst in &block.insts {
                match inst {
                    Inst::Const { dst, val, .. } => {
                        code.extend_from_slice(&[0x48, 0xB8]);
                        code.extend_from_slice(&val.to_le_bytes());
                        emit_store_rax(&mut code, *dst, &hot);
                    }
                    Inst::Bin { dst, op, lhs, rhs } => {
                        emit_load_rax(&mut code, *lhs, &hot);
                        emit_load_rcx(&mut code, *rhs, &hot);
                        match op {
                            BinOp::Add => code.extend_from_slice(&[0x48, 0x01, 0xC8]),
                            BinOp::Sub => code.extend_from_slice(&[0x48, 0x29, 0xC8]),
                            BinOp::Mul => code.extend_from_slice(&[0x48, 0x0F, 0xAF, 0xC1]),
                            BinOp::And => code.extend_from_slice(&[0x48, 0x21, 0xC8]),
                            BinOp::Or => code.extend_from_slice(&[0x48, 0x09, 0xC8]),
                            BinOp::Xor => code.extend_from_slice(&[0x48, 0x31, 0xC8]),
                            BinOp::Shl => code.extend_from_slice(&[0x48, 0xD3, 0xE0]),
                            BinOp::LShr => code.extend_from_slice(&[0x48, 0xD3, 0xE8]),
                            BinOp::AShr => code.extend_from_slice(&[0x48, 0xD3, 0xF8]),
                            BinOp::UDiv => code.extend_from_slice(&[0x31, 0xD2, 0x48, 0xF7, 0xF1]),
                            BinOp::SDiv => code.extend_from_slice(&[0x48, 0x99, 0x48, 0xF7, 0xF9]),
                            BinOp::URem => code.extend_from_slice(&[
                                0x31, 0xD2, 0x48, 0xF7, 0xF1, 0x48, 0x89, 0xD0,
                            ]),
                            BinOp::SRem => code.extend_from_slice(&[
                                0x48, 0x99, 0x48, 0xF7, 0xF9, 0x48, 0x89, 0xD0,
                            ]),
                            BinOp::FxMul => code.extend_from_slice(&[
                                0x48, 0x0F, 0xAF, 0xC1, 0x48, 0xC1, 0xE8, 0x10,
                            ]),
                            BinOp::FxDiv => code.extend_from_slice(&[
                                0x48, 0xC1, 0xE0, 0x10, 0x31, 0xD2, 0x48, 0xF7, 0xF1,
                            ]),
                        }
                        emit_store_rax(&mut code, *dst, &hot);
                    }
                    Inst::Cmp { dst, op, lhs, rhs } => {
                        emit_load_rax(&mut code, *lhs, &hot);
                        emit_load_rcx(&mut code, *rhs, &hot);
                        let setcc = match op {
                            CmpOp::Eq => 0x94,
                            CmpOp::Ne => 0x95,
                            CmpOp::Ult => 0x92,
                            CmpOp::Ule => 0x96,
                            CmpOp::Ugt => 0x97,
                            CmpOp::Uge => 0x93,
                            CmpOp::Slt => 0x9C,
                            CmpOp::Sle => 0x9E,
                            CmpOp::Sgt => 0x9F,
                            CmpOp::Sge => 0x9D,
                        };
                        code.extend_from_slice(&[
                            0x48, 0x39, 0xC8, 0x0F, setcc, 0xC0, 0x48, 0x0F, 0xB6, 0xC0,
                        ]);
                        emit_store_rax(&mut code, *dst, &hot);
                    }
                    Inst::Slice { dst, base, idx, ty } => {
                        let layout_id = ty.ptr_layout().ok_or("Lỗi kiểu Slice")? as usize;
                        let elem_size = module.layouts[layout_id].size;
                        emit_load_rax(&mut code, *idx, &hot);
                        code.extend_from_slice(&[0x48, 0x69, 0xC0]);
                        code.extend_from_slice(&elem_size.to_le_bytes());
                        emit_load_rcx(&mut code, *base, &hot);
                        code.extend_from_slice(&[0x48, 0x01, 0xC8]);
                        emit_store_rax(&mut code, *dst, &hot);
                    }
                    Inst::Load {
                        dst,
                        ty,
                        base,
                        offset,
                    } => {
                        emit_load_rcx(&mut code, *base, &hot);
                        match ty {
                            Type::Bv8 => code.extend_from_slice(&[0x48, 0x0F, 0xB6, 0x81]),
                            Type::Bv16 => code.extend_from_slice(&[0x48, 0x0F, 0xB7, 0x81]),
                            Type::Bv32 => code.extend_from_slice(&[0x8B, 0x81]),
                            _ => code.extend_from_slice(&[0x48, 0x8B, 0x81]),
                        }
                        code.extend_from_slice(&offset.to_le_bytes());
                        emit_store_rax(&mut code, *dst, &hot);
                    }
                    Inst::Store { base, offset, val } => {
                        emit_load_rcx(&mut code, *base, &hot);
                        emit_load_rax(&mut code, *val, &hot);
                        match reg_tys.get(val).unwrap_or(&Type::Bv64) {
                            Type::Bv8 => code.extend_from_slice(&[0x88, 0x81]),
                            Type::Bv16 => code.extend_from_slice(&[0x66, 0x89, 0x81]),
                            Type::Bv32 => code.extend_from_slice(&[0x89, 0x81]),
                            _ => code.extend_from_slice(&[0x48, 0x89, 0x81]),
                        }
                        code.extend_from_slice(&offset.to_le_bytes());
                    }
                    Inst::Simd256 { op, dst, lhs, rhs } => {
                        emit_load_rax(&mut code, *lhs, &hot);
                        code.extend_from_slice(&[0x48, 0x89, 0xC6]); // mov rsi, rax (lhs_ptr)
                        emit_load_rax(&mut code, *rhs, &hot);
                        code.extend_from_slice(&[0x48, 0x89, 0xC2]); // mov rdx, rax (rhs_ptr)
                        if *op == SimdOp::Dot {
                            // AVX2 256-bit Dot Product (vmovdqu + vpmuludq + vextracti128 + vpaddq) + SSE2 Fallback
                            code.extend_from_slice(&[
                                0x80, 0x3C, 0x25, 0x08, 0xE0, 0x07, 0x00, 0x00, 0x74, 0x25,
                                0xC5, 0xFE, 0x6F, 0x06, 0xC5, 0xFD, 0xF4, 0x02,
                                0xC4, 0xE3, 0x7D, 0x39, 0xC1, 0x01, 0xC5, 0xF9, 0xD4, 0xC1,
                                0xC5, 0xF9, 0x70, 0xC8, 0x4E, 0xC5, 0xF9, 0xD4, 0xC1,
                                0xC4, 0xE1, 0xF9, 0x7E, 0xC0, 0xC5, 0xF8, 0x77, 0xEB, 0x2C,
                                0xF3, 0x0F, 0x6F, 0x06, 0xF3, 0x0F, 0x6F, 0x0A,
                                0x66, 0x0F, 0xF4, 0xC1, 0xF3, 0x0F, 0x6F, 0x56, 0x10,
                                0xF3, 0x0F, 0x6F, 0x4A, 0x10, 0x66, 0x0F, 0xF4, 0xD1,
                                0x66, 0x0F, 0xD4, 0xC2, 0x66, 0x0F, 0x70, 0xC8, 0x4E,
                                0x66, 0x0F, 0xD4, 0xC1, 0x66, 0x48, 0x0F, 0x7E, 0xC0,
                            ]);
                            emit_store_rax(&mut code, *dst, &hot);
                        } else {
                            emit_load_rcx(&mut code, *dst, &hot); // rcx = dst_ptr
                            let op_b = match op {
                                SimdOp::Add => 0xD4, // vpaddq / paddq
                                SimdOp::Sub => 0xFB, // vpsubq / psubq
                                SimdOp::Mul => 0xF4, // vpmuludq / pmuludq
                                _ => 0xEF,           // vpxor / pxor
                            };
                            code.extend_from_slice(&[
                                0x80, 0x3C, 0x25, 0x08, 0xE0, 0x07, 0x00, 0x00, 0x74, 0x11,
                                0xC5, 0xFE, 0x6F, 0x06, 0xC5, 0xFD, op_b, 0x02,
                                0xC5, 0xFE, 0x7F, 0x01, 0xC5, 0xF8, 0x77, 0xEB, 0x23,
                                0xF3, 0x0F, 0x6F, 0x06, 0xF3, 0x0F, 0x6F, 0x0A,
                                0x66, 0x0F, op_b, 0xC1, 0xF3, 0x0F, 0x7F, 0x01,
                                0xF3, 0x0F, 0x6F, 0x46, 0x10, 0xF3, 0x0F, 0x6F, 0x4A, 0x10,
                                0x66, 0x0F, op_b, 0xC1, 0xF3, 0x0F, 0x7F, 0x41, 0x10,
                            ]);
                        }
                    }
                    Inst::Parallel { smp, n, func_id, base, arg } => {
                        // lt_parallel(rdi=smp, rsi=n, rdx=&worker, rcx=base, r8=stride, r9=arg)
                        let Some(layout_id) = reg_tys[base].ptr_layout() else {
                            return Err("parallel: base không phải ptr".into());
                        };
                        let Some(&(_, Type::Ptr { max_elems: k, .. })) = module.funcs[*func_id as usize].params.first() else {
                            return Err("parallel: worker sai chữ ký".into());
                        };
                        let stride = k * module.layouts[layout_id as usize].size as u64;
                        emit_load_rax(&mut code, *smp, &hot);
                        code.extend_from_slice(&[0x48, 0x89, 0xC7]); // mov rdi, rax
                        emit_load_rax(&mut code, *n, &hot);
                        code.extend_from_slice(&[0x48, 0x89, 0xC6]); // mov rsi, rax
                        emit_load_rax(&mut code, *base, &hot);
                        code.extend_from_slice(&[0x48, 0x89, 0xC1]); // mov rcx, rax
                        emit_load_rax(&mut code, *arg, &hot);
                        code.extend_from_slice(&[0x49, 0x89, 0xC1]); // mov r9, rax
                        code.extend_from_slice(&[0x49, 0xB8]); // movabs r8, stride
                        code.extend_from_slice(&stride.to_le_bytes());
                        code.extend_from_slice(&[0x48, 0x8D, 0x15, 0, 0, 0, 0]); // lea rdx, [rip + worker]
                        call_patches.push((code.len() - 4, *func_id));
                        code.extend_from_slice(&[0xE8, 0, 0, 0, 0]); // call lt_parallel
                        rt_patches.push(code.len() - 4);
                    }
                    Inst::SmpWorkers { dst, smp } => {
                        // popcount(bitmask online tại [smp+16], bỏ bit 0)
                        emit_load_rcx(&mut code, *smp, &hot);
                        code.extend_from_slice(&[
                            0x48, 0x8B, 0x51, 0x10, // mov rdx, [rcx+16]
                            0x81, 0xE2, 0xFE, 0xFF, 0x00, 0x00, // and edx, 0xfffe
                            0x31, 0xC0, // xor eax, eax
                            0x48, 0x85, 0xD2, 0x74, 0x0B, // test rdx, rdx; jz +11
                            0x48, 0x8D, 0x4A, 0xFF, 0x48, 0x21, 0xCA, // lea rcx,[rdx-1]; and rdx,rcx
                            0xFF, 0xC0, 0xEB, 0xF0, // inc eax; jmp test
                        ]);
                        emit_store_rax(&mut code, *dst, &hot);
                    }
                    Inst::AtaRead { ptr, idx, nsec, .. } => {
                        // rep insd: nsec*128 dword từ 0x1F0 vào [ptr + idx*512]
                        emit_load_rax(&mut code, *ptr, &hot);
                        emit_load_rcx(&mut code, *idx, &hot);
                        code.extend_from_slice(&[
                            0x48, 0xC1, 0xE1, 0x09, // shl rcx, 9
                            0x48, 0x01, 0xC8, // add rax, rcx
                            0x57, // push rdi
                            0x48, 0x89, 0xC7, // mov rdi, rax
                        ]);
                        emit_load_rcx(&mut code, *nsec, &hot);
                        code.extend_from_slice(&[
                            0x48, 0xC1, 0xE1, 0x07, // shl rcx, 7
                            0x66, 0xBA, 0xF0, 0x01, // mov dx, 0x1F0
                            0xFC, // cld
                            0xF3, 0x6D, // rep insd
                            0x5F, // pop rdi
                        ]);
                    }
                    Inst::HwIo {
                        dst,
                        port_or_reg,
                        val,
                        is_write,
                        ..
                    } => {
                        if *is_write {
                            let v_reg = val.unwrap();
                            emit_load_rax(&mut code, v_reg, &hot);
                            if *port_or_reg == 3 {
                                code.extend_from_slice(&[0x0F, 0x22, 0xD8]);
                            } else {
                                code.extend_from_slice(&[0x66, 0xBA]);
                                code.extend_from_slice(&port_or_reg.to_le_bytes());
                                if *port_or_reg == 0x1F0 || reg_tys.get(&v_reg) == Some(&Type::Bv16)
                                {
                                    code.extend_from_slice(&[0x66, 0xEF]);
                                } else {
                                    code.push(0xEE);
                                }
                            }
                        } else if let Some(d) = dst {
                            if *port_or_reg == 3 {
                                code.extend_from_slice(&[0x0F, 0x20, 0xD8]);
                            } else if *port_or_reg == 0x10 {
                                code.extend_from_slice(&[
                                    0x0F, 0x31, 0x48, 0xC1, 0xE2, 0x20, 0x48, 0x09, 0xD0, 0x48,
                                    0xC1, 0xE8, 0x14, 0x25, 0xFF, 0x00, 0x00, 0x00,
                                ]);
                            } else {
                                code.extend_from_slice(&[0x31, 0xC0, 0x66, 0xBA]);
                                code.extend_from_slice(&port_or_reg.to_le_bytes());
                                if *port_or_reg == 0x1F0 {
                                    code.extend_from_slice(&[0x66, 0xED]);
                                } else {
                                    code.push(0xEC);
                                }
                            }
                            emit_store_rax(&mut code, *d, &hot);
                        }
                    }
                    Inst::Br {
                        cond,
                        then_bb,
                        else_bb,
                    } => {
                        emit_load_rax(&mut code, *cond, &hot);
                        code.extend_from_slice(&[0x48, 0x85, 0xC0, 0x0F, 0x85, 0, 0, 0, 0]);
                        jmp_patches.push((code.len() - 4, *then_bb));
                        code.extend_from_slice(&[0xE9, 0, 0, 0, 0]);
                        jmp_patches.push((code.len() - 4, *else_bb));
                    }
                    Inst::Jmp { target_bb, args } => {
                        let target_blk = func
                            .blocks
                            .iter()
                            .find(|b| b.id == *target_bb)
                            .ok_or("Không tìm thấy BlockId")?;
                        for (&arg_r, &(param_r, _)) in args.iter().zip(&target_blk.params) {
                            emit_load_rax(&mut code, arg_r, &hot);
                            emit_store_rax(&mut code, param_r, &hot);
                        }
                        code.extend_from_slice(&[0xE9, 0, 0, 0, 0]);
                        jmp_patches.push((code.len() - 4, *target_bb));
                    }
                    Inst::Call { dst, func_id, args } => {
                        let rax_to_abi: [&[u8]; 6] = [
                            &[0x48, 0x89, 0xC7],
                            &[0x48, 0x89, 0xC6],
                            &[0x48, 0x89, 0xC2],
                            &[0x48, 0x89, 0xC1],
                            &[0x49, 0x89, 0xC0],
                            &[0x49, 0x89, 0xC1],
                        ];
                        let extra = args.len().saturating_sub(6);
                        let pad = if extra % 2 != 0 { 8 } else { 0 };
                        if pad > 0 {
                            code.extend_from_slice(&[0x48, 0x83, 0xEC, 0x08]);
                        }
                        for &r in args.iter().skip(6).rev() {
                            emit_load_rax(&mut code, r, &hot);
                            code.push(0x50);
                        }
                        for (i, &r) in args.iter().take(6).enumerate() {
                            emit_load_rax(&mut code, r, &hot);
                            code.extend_from_slice(rax_to_abi[i]);
                        }
                        code.extend_from_slice(&[0xE8, 0, 0, 0, 0]);
                        call_patches.push((code.len() - 4, *func_id));
                        let total_stack = (extra * 8 + pad) as i32;
                        if total_stack > 0 {
                            code.extend_from_slice(&[0x48, 0x81, 0xC4]);
                            code.extend_from_slice(&total_stack.to_le_bytes());
                        }
                        if let Some(d) = dst {
                            emit_store_rax(&mut code, *d, &hot);
                        }
                    }
                    Inst::CallPtr { dst, target, args } => {
                        let rax_to_abi: [&[u8]; 6] = [
                            &[0x48, 0x89, 0xC7],
                            &[0x48, 0x89, 0xC6],
                            &[0x48, 0x89, 0xC2],
                            &[0x48, 0x89, 0xC1],
                            &[0x49, 0x89, 0xC0],
                            &[0x49, 0x89, 0xC1],
                        ];
                        let extra = args.len().saturating_sub(6);
                        let pad = if extra % 2 != 0 { 8 } else { 0 };
                        if pad > 0 {
                            code.extend_from_slice(&[0x48, 0x83, 0xEC, 0x08]);
                        }
                        for &r in args.iter().skip(6).rev() {
                            emit_load_rax(&mut code, r, &hot);
                            code.push(0x50);
                        }
                        for (i, &r) in args.iter().take(6).enumerate() {
                            emit_load_rax(&mut code, r, &hot);
                            code.extend_from_slice(rax_to_abi[i]);
                        }
                        emit_load_rax(&mut code, *target, &hot);
                        code.extend_from_slice(&[0xFF, 0xD0]);
                        let total_stack = (extra * 8 + pad) as i32;
                        if total_stack > 0 {
                            code.extend_from_slice(&[0x48, 0x81, 0xC4]);
                            code.extend_from_slice(&total_stack.to_le_bytes());
                        }
                        if let Some(d) = dst {
                            emit_store_rax(&mut code, *d, &hot);
                        }
                    }
                    Inst::Ret { val } => {
                        if let Some(r) = val {
                            emit_load_rax(&mut code, *r, &hot);
                        }
                        code.extend_from_slice(&[
                            0x48, 0x83, 0xC4, 0x08, 0x41, 0x5F, 0x41, 0x5E, 0x41, 0x5D, 0x41, 0x5C,
                            0x5B, 0x48, 0x89, 0xEC, 0x5D, 0xC3,
                        ]);
                    }
                    Inst::Assume(_) | Inst::Assert(_) => {}
                }
            }
        }
        for (patch_pos, target_bb) in jmp_patches {
            let target_addr = *blk_addrs.get(&target_bb).ok_or("Không tìm thấy BlockId")?;
            let rel = (target_addr as i32) - ((patch_pos + 4) as i32);
            code[patch_pos..patch_pos + 4].copy_from_slice(&rel.to_le_bytes());
        }
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

    let entry_idx = (module.funcs.len().saturating_sub(1)) as u32;
    let entry_offset = *func_addrs.get(&entry_idx).unwrap_or(&0) as u64;
    let icon_offset = module
        .funcs
        .iter()
        .position(|f| f.name == "app_draw_icon")
        .and_then(|i| func_addrs.get(&(i as u32)).copied())
        .unwrap_or(0) as u64;
    let worker_offset = module
        .funcs
        .iter()
        .position(|f| f.name == "app_smp_worker")
        .and_then(|i| func_addrs.get(&(i as u32)).copied())
        .unwrap_or(0) as u64;
    let panic_offset = module
        .funcs
        .iter()
        .position(|f| f.name == "kernel_panic")
        .and_then(|i| func_addrs.get(&(i as u32)).map(|&a| a as u64));
    Ok((code, entry_offset, icon_offset, worker_offset, panic_offset))
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
            Prov::Ptr("VgaCell", 921600),
            Prov::Ptr("IpcChannel", 1),
            Prov::Ptr("DiskQword", 3932160),
            Prov::Ptr("DiskQword", 64),
            Prov::Ptr("DiskQword", 64),
            Prov::Smp,
            Prov::Int,
            Prov::DPtr("DiskQword", 6),
        ],
    )?;
    check_app_abi(module, "app_draw_icon", &[Prov::Ptr("VgaCell", 921600), Prov::Int, Prov::Int])?;
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
