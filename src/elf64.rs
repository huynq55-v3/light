// File: src/elf64.rs (Ngân sách: < 200 dòng - Thực tế: ~175 dòng)
use crate::ir::*;
use std::collections::HashMap;

/// Đóng gói mã máy 64-bit kèm Multiboot1 Header & Trampoline 32->64 bit để chạy thẳng trên QEMU -kernel
fn pack_elf64(code: &[u8], _entry_offset: u64) -> Vec<u8> {
    let base: u32 = 0x100000; // Địa chỉ nạp chuẩn 1MB của Multiboot
    let mut elf = Vec::new();

    // 1. ELF Header (52B) + Program Header (32B) = 84B (0x54)
    elf.extend_from_slice(&[
        0x7F, b'E', b'L', b'F', 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 1, 0, 0,
        0, // ET_EXEC, EM_386 (Để QEMU Multiboot chấp nhận nạp)
    ]);
    let entry_vaddr = base + 0x80; // Điểm vào 32-bit nằm ở offset 0x80 (128)
    elf.extend_from_slice(&entry_vaddr.to_le_bytes());
    elf.extend_from_slice(&52u32.to_le_bytes()); // e_phoff = 52
    elf.extend_from_slice(&0u32.to_le_bytes()); // e_shoff = 0
    elf.extend_from_slice(&0u32.to_le_bytes()); // e_flags
    elf.extend_from_slice(&52u16.to_le_bytes()); // e_ehsize = 52
    elf.extend_from_slice(&32u16.to_le_bytes()); // e_phentsize = 32
    elf.extend_from_slice(&1u16.to_le_bytes()); // e_phnum = 1
    elf.extend_from_slice(&[0u8; 6]);

    // Program Header PT_LOAD (32B) - Điền kích thước file thực tế ở cuối hàm
    elf.extend_from_slice(&1u32.to_le_bytes()); // PT_LOAD
    elf.extend_from_slice(&0u32.to_le_bytes()); // p_offset = 0
    elf.extend_from_slice(&base.to_le_bytes()); // p_vaddr = 0x100000
    elf.extend_from_slice(&base.to_le_bytes()); // p_paddr = 0x100000
    elf.extend_from_slice(&0u32.to_le_bytes()); // placeholder p_filesz (offset 68)
    elf.extend_from_slice(&0u32.to_le_bytes()); // placeholder p_memsz  (offset 72)
    elf.extend_from_slice(&7u32.to_le_bytes()); // PF_R | PF_W | PF_X
    elf.extend_from_slice(&0x1000u32.to_le_bytes());

    // 2. Multiboot1 Header tại offset 0x54 (12B) + GDT 64-bit tại 0x60 (24B) + GDTR tại 0x78 (8B)
    elf.extend_from_slice(&0x1BADB002u32.to_le_bytes()); // Magic
    elf.extend_from_slice(&0x00000000u32.to_le_bytes()); // Flags
    elf.extend_from_slice(&0xE4524FFEu32.to_le_bytes()); // Checksum
    elf.extend_from_slice(&0x0000000000000000u64.to_le_bytes()); // GDT[0]: Null
    elf.extend_from_slice(&0x00AF9A000000FFFFu64.to_le_bytes()); // GDT[1]: 64-bit Code (0x08)
    elf.extend_from_slice(&0x00CF92000000FFFFu64.to_le_bytes()); // GDT[2]: 64-bit Data (0x10)
    elf.extend_from_slice(&23u16.to_le_bytes()); // GDTR Limit
    elf.extend_from_slice(&(base + 0x60).to_le_bytes()); // GDTR Base (0x100060)
    elf.extend_from_slice(&0u16.to_le_bytes()); // Padding tròn 0x80 (128 bytes)

    // 3. Trampoline 32-bit -> 64-bit Long Mode tại offset 0x80:
    // Khởi tạo Stack (0x70000), dựng Page Table Identity-Map 2MB tại 0x1000, bật PAE, EFER.LME, Paging
    elf.extend_from_slice(&[
        0xFA, 0xBC, 0x00, 0x00, 0x07, 0x00, // cli; mov esp, 0x70000
        0xBF, 0x00, 0x10, 0x00, 0x00, 0xB9, 0x00, 0x0C, 0x00,
        0x00, // mov edi, 0x1000; mov ecx, 0xC00
        0x31, 0xC0, 0xFC, 0xF3, 0xAB, // xor eax,eax; cld; rep stosd
        0xC7, 0x05, 0x00, 0x10, 0x00, 0x00, 0x03, 0x20, 0x00, 0x00, // PML4[0] = 0x2003
        0xC7, 0x05, 0x00, 0x20, 0x00, 0x00, 0x03, 0x30, 0x00, 0x00, // PDPT[0] = 0x3003
        0xC7, 0x05, 0x00, 0x30, 0x00, 0x00, 0x83, 0x00, 0x00,
        0x00, // PD[0]   = 0x0083 (2MB HugePage)
        0xB8, 0x00, 0x10, 0x00, 0x00, 0x0F, 0x22, 0xD8, // mov eax, 0x1000; mov cr3, eax
        0x0F, 0x20, 0xE0, 0x83, 0xC8, 0x20, 0x0F, 0x22, 0xE0, // cr4 |= PAE (0x20)
        0xB9, 0x80, 0x00, 0x00, 0xC0, 0x0F, 0x32, // rdmsr (EFER 0xC0000080)
        0x0D, 0x00, 0x01, 0x00, 0x00, 0x0F, 0x30, // eax |= LME (0x100); wrmsr
        0x0F, 0x20, 0xC0, 0x0D, 0x00, 0x00, 0x00, 0x80, 0x0F, 0x22,
        0xC0, // cr0 |= PG (0x80000000)
        0x0F, 0x01, 0x15, 0x78, 0x00, 0x10, 0x00, // lgdt [0x100078]
    ]);
    // Nhảy xa (ljmp 0x08:start64) sang chế độ 64-bit
    let start64 = base + (elf.len() as u32) + 7;
    elf.push(0xEA);
    elf.extend_from_slice(&start64.to_le_bytes());
    elf.extend_from_slice(&0x0008u16.to_le_bytes());

    // 4. Đã vào 64-bit Long Mode! Nạp thanh ghi đoạn (0x10), gọi hàm đầu tiên của light v2, xong thì cli; hlt
    elf.extend_from_slice(&[
        0x66, 0xB8, 0x10, 0x00, 0x8E, 0xD8, 0x8E, 0xC0, 0x8E,
        0xD0, // mov ax, 0x10; mov ds/es/ss, ax
        0xE8, 0x02, 0x00, 0x00, 0x00, // call +2 (Gọi thẳng vào đầu mảng `code`)
        0xFA, 0xF4, // cli; hlt (Khi hàm `ret` sẽ dừng CPU tại đây)
    ]);

    // 5. Nối mã máy 64-bit do light v2 sinh ra và cập nhật kích thước file vào Program Header
    elf.extend_from_slice(code);
    let fsz = (elf.len() as u32).to_le_bytes();
    elf[68..72].copy_from_slice(&fsz);
    elf[72..76].copy_from_slice(&fsz);
    elf
}

/// Độ lệch âm trên Stack cho biến SSA `%r`: `rbp - (r + 1) * 8`
fn slot(r: Reg) -> i32 {
    -(((r as i32) + 1) * 8)
}

/// Nạp biến SSA `%r` từ Stack vào thanh ghi `rax`: `mov rax, [rbp + disp32]`
fn emit_load_rax(c: &mut Vec<u8>, r: Reg) {
    c.extend_from_slice(&[0x48, 0x8B, 0x85]);
    c.extend_from_slice(&slot(r).to_le_bytes());
}

/// Nạp biến SSA `%r` từ Stack vào thanh ghi `rcx`: `mov rcx, [rbp + disp32]`
fn emit_load_rcx(c: &mut Vec<u8>, r: Reg) {
    c.extend_from_slice(&[0x48, 0x8B, 0x8D]);
    c.extend_from_slice(&slot(r).to_le_bytes());
}

/// Lưu giá trị từ `rax` vào biến SSA `%r` trên Stack: `mov [rbp + disp32], rax`
fn emit_store_rax(c: &mut Vec<u8>, r: Reg) {
    c.extend_from_slice(&[0x48, 0x89, 0x85]);
    c.extend_from_slice(&slot(r).to_le_bytes());
}

pub fn compile_elf64(module: &Module) -> Result<Vec<u8>, String> {
    let mut code: Vec<u8> = Vec::new();
    let mut func_addrs: HashMap<u32, usize> = HashMap::new();
    let mut call_patches: Vec<(usize, u32)> = Vec::new();

    for (f_idx, func) in module.funcs.iter().enumerate() {
        func_addrs.insert(f_idx as u32, code.len());

        // Prologue: push rbp; mov rbp, rsp; sub rsp, 512 (Cấp phát cố định 64 biến SSA trên Stack)
        code.extend_from_slice(&[
            0x55, 0x48, 0x89, 0xE5, 0x48, 0x81, 0xEC, 0x00, 0x02, 0x00, 0x00,
        ]);

        // Nhận tối đa 6 tham số hàm từ thanh ghi ABI (rdi, rsi, rdx, rcx, r8, r9) đẩy vào Stack Slot
        let abi_regs: [&[u8]; 6] = [
            &[0x48, 0x89, 0xBD],
            &[0x48, 0x89, 0xB5],
            &[0x48, 0x89, 0x95],
            &[0x48, 0x89, 0x8D],
            &[0x4C, 0x89, 0x85],
            &[0x4C, 0x89, 0x8D],
        ];
        for (i, &(reg, _)) in func.params.iter().take(6).enumerate() {
            code.extend_from_slice(abi_regs[i]);
            code.extend_from_slice(&slot(reg).to_le_bytes());
        }

        let mut blk_addrs: HashMap<BlockId, usize> = HashMap::new();
        let mut jmp_patches: Vec<(usize, BlockId)> = Vec::new();

        for block in &func.blocks {
            blk_addrs.insert(block.id, code.len());
            for inst in &block.insts {
                match inst {
                    Inst::Const { dst, val, .. } => {
                        code.extend_from_slice(&[0x48, 0xB8]); // movabs rax, imm64
                        code.extend_from_slice(&val.to_le_bytes());
                        emit_store_rax(&mut code, *dst);
                    }
                    Inst::Bin { dst, op, lhs, rhs } => {
                        emit_load_rax(&mut code, *lhs);
                        emit_load_rcx(&mut code, *rhs);
                        match op {
                            BinOp::Add => code.extend_from_slice(&[0x48, 0x01, 0xC8]), // add rax, rcx
                            BinOp::Sub => code.extend_from_slice(&[0x48, 0x29, 0xC8]), // sub rax, rcx
                            BinOp::Mul => code.extend_from_slice(&[0x48, 0x0F, 0xAF, 0xC1]), // imul rax, rcx
                            BinOp::And => code.extend_from_slice(&[0x48, 0x21, 0xC8]), // and rax, rcx
                            BinOp::Or => code.extend_from_slice(&[0x48, 0x09, 0xC8]), // or rax, rcx
                            BinOp::Xor => code.extend_from_slice(&[0x48, 0x31, 0xC8]), // xor rax, rcx
                            BinOp::Shl => code.extend_from_slice(&[0x48, 0xD3, 0xE0]), // shl rax, cl
                            BinOp::LShr => code.extend_from_slice(&[0x48, 0xD3, 0xE8]), // shr rax, cl
                            BinOp::AShr => code.extend_from_slice(&[0x48, 0xD3, 0xF8]), // sar rax, cl
                            BinOp::UDiv => code.extend_from_slice(&[0x31, 0xD2, 0x48, 0xF7, 0xF1]), // xor edx,edx; div rcx
                            BinOp::SDiv => code.extend_from_slice(&[0x48, 0x99, 0x48, 0xF7, 0xF9]), // cqo; idiv rcx
                            BinOp::URem => code.extend_from_slice(&[
                                0x31, 0xD2, 0x48, 0xF7, 0xF1, 0x48, 0x89, 0xD0,
                            ]),
                            BinOp::SRem => code.extend_from_slice(&[
                                0x48, 0x99, 0x48, 0xF7, 0xF9, 0x48, 0x89, 0xD0,
                            ]),
                        }
                        emit_store_rax(&mut code, *dst);
                    }
                    Inst::Cmp { dst, op, lhs, rhs } => {
                        emit_load_rax(&mut code, *lhs);
                        emit_load_rcx(&mut code, *rhs);
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
                        // cmp rax, rcx; setcc al; movzx rax, al
                        code.extend_from_slice(&[
                            0x48, 0x39, 0xC8, 0x0F, setcc, 0xC0, 0x48, 0x0F, 0xB6, 0xC0,
                        ]);
                        emit_store_rax(&mut code, *dst);
                    }
                    Inst::Load {
                        dst,
                        ty,
                        base,
                        offset,
                    } => {
                        emit_load_rcx(&mut code, *base); // rcx = base_ptr
                        match ty {
                            Type::Bv8 => code.extend_from_slice(&[0x48, 0x0F, 0xB6, 0x81]), // movzx rax, byte [rcx+off]
                            Type::Bv16 => code.extend_from_slice(&[0x48, 0x0F, 0xB7, 0x81]), // movzx rax, word [rcx+off]
                            Type::Bv32 => code.extend_from_slice(&[0x8B, 0x81]), // mov eax, dword [rcx+off]
                            _ => code.extend_from_slice(&[0x48, 0x8B, 0x81]), // mov rax, qword [rcx+off]
                        }
                        code.extend_from_slice(&offset.to_le_bytes());
                        emit_store_rax(&mut code, *dst);
                    }
                    Inst::Store { base, offset, val } => {
                        emit_load_rcx(&mut code, *base); // rcx = base_ptr
                        emit_load_rax(&mut code, *val); // rax = val
                        code.extend_from_slice(&[0x48, 0x89, 0x81]); // mov [rcx + disp32], rax
                        code.extend_from_slice(&offset.to_le_bytes());
                    }
                    Inst::HwIo {
                        dst,
                        port_or_reg,
                        val,
                        is_write,
                    } => {
                        if *is_write {
                            emit_load_rax(&mut code, val.unwrap());
                            if *port_or_reg == 3 {
                                code.extend_from_slice(&[0x0F, 0x22, 0xD8]); // mov cr3, rax (Nạp Page Table cho OS!)
                            } else {
                                code.extend_from_slice(&[0x66, 0xBA]); // mov dx, port; out dx, al
                                code.extend_from_slice(&port_or_reg.to_le_bytes());
                                code.push(0xEE);
                            }
                        } else if let Some(d) = dst {
                            if *port_or_reg == 3 {
                                code.extend_from_slice(&[0x0F, 0x20, 0xD8]); // mov rax, cr3
                            } else {
                                code.extend_from_slice(&[0x31, 0xC0, 0x66, 0xBA]); // xor eax,eax; mov dx, port; in al, dx
                                code.extend_from_slice(&port_or_reg.to_le_bytes());
                                code.push(0xEC);
                            }
                            emit_store_rax(&mut code, *d);
                        }
                    }
                    Inst::Br {
                        cond,
                        then_bb,
                        else_bb,
                    } => {
                        emit_load_rax(&mut code, *cond);
                        code.extend_from_slice(&[0x48, 0x85, 0xC0, 0x0F, 0x85, 0, 0, 0, 0]); // test rax,rax; jnz then_bb
                        jmp_patches.push((code.len() - 4, *then_bb));
                        code.extend_from_slice(&[0xE9, 0, 0, 0, 0]); // jmp else_bb
                        jmp_patches.push((code.len() - 4, *else_bb));
                    }
                    Inst::Jmp { target_bb, args } => {
                        // Copy giá trị từ các biến `args` sang các biến `params` của Block đích trước khi nhảy
                        let target_blk = func
                            .blocks
                            .iter()
                            .find(|b| b.id == *target_bb)
                            .ok_or("Không tìm thấy BlockId")?;
                        for (&arg_r, &(param_r, _)) in args.iter().zip(&target_blk.params) {
                            emit_load_rax(&mut code, arg_r);
                            emit_store_rax(&mut code, param_r);
                        }
                        code.extend_from_slice(&[0xE9, 0, 0, 0, 0]); // jmp rel32
                        jmp_patches.push((code.len() - 4, *target_bb));
                    }
                    Inst::Call { dst, func_id, args } => {
                        let arg_loads: [&[u8]; 6] = [
                            &[0x48, 0x8B, 0xBD],
                            &[0x48, 0x8B, 0xB5],
                            &[0x48, 0x8B, 0x95],
                            &[0x48, 0x8B, 0x8D],
                            &[0x4C, 0x8B, 0x85],
                            &[0x4C, 0x8B, 0x8D],
                        ];
                        for (i, &r) in args.iter().take(6).enumerate() {
                            code.extend_from_slice(arg_loads[i]);
                            code.extend_from_slice(&slot(r).to_le_bytes());
                        }
                        code.extend_from_slice(&[0xE8, 0, 0, 0, 0]); // call rel32
                        call_patches.push((code.len() - 4, *func_id));
                        if let Some(d) = dst {
                            emit_store_rax(&mut code, *d);
                        }
                    }
                    Inst::Ret { val } => {
                        if let Some(r) = val {
                            emit_load_rax(&mut code, *r);
                        }
                        code.extend_from_slice(&[0x48, 0x89, 0xEC, 0x5D, 0xC3]);
                        // mov rsp, rbp; pop rbp; ret
                    }
                    Inst::Assume(_) | Inst::Assert(_) => {} // Bỏ qua 100% lệnh Ghost của Z3!
                }
            }
        }
        // Điền địa chỉ nhảy (Rel32 Patching) cho các lệnh Br / Jmp trong hàm
        for (patch_pos, target_bb) in jmp_patches {
            let target_addr = *blk_addrs.get(&target_bb).ok_or("Không tìm thấy BlockId")?;
            let rel = (target_addr as i32) - ((patch_pos + 4) as i32);
            code[patch_pos..patch_pos + 4].copy_from_slice(&rel.to_le_bytes());
        }
    }

    // Điền địa chỉ gọi hàm (Rel32 Patching) cho các lệnh Call
    for (patch_pos, f_id) in call_patches {
        let target_addr = *func_addrs.get(&f_id).ok_or("Không tìm thấy func_id")?;
        let rel = (target_addr as i32) - ((patch_pos + 4) as i32);
        code[patch_pos..patch_pos + 4].copy_from_slice(&rel.to_le_bytes());
    }

    Ok(pack_elf64(&code, 0))
}
