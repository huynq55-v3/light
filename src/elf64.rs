// File: src/elf64.rs (Chuẩn hóa ABI 6+ tham số cho LightUI + Đồ họa HD 1280x720x32 tại 0x200000)
use crate::ir::*;
use std::collections::HashMap;

fn pack_elf64(code: &[u8], entry_offset: u64) -> Vec<u8> {
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
    elf.extend_from_slice(&0x1BADB002u32.to_le_bytes());
    elf.extend_from_slice(&0x00000000u32.to_le_bytes());
    elf.extend_from_slice(&0xE4524FFEu32.to_le_bytes());
    elf.extend_from_slice(&0x0000000000000000u64.to_le_bytes());
    elf.extend_from_slice(&0x00AF9A000000FFFFu64.to_le_bytes());
    elf.extend_from_slice(&0x00CF92000000FFFFu64.to_le_bytes());
    elf.extend_from_slice(&23u16.to_le_bytes());
    elf.extend_from_slice(&(base + 0x60).to_le_bytes());
    elf.extend_from_slice(&0u16.to_le_bytes());

    // 3. Trampoline 32-bit -> 64-bit Long Mode + Ánh xạ 4MB VRAM (1280x720x32) vào 0x200000:
    elf.extend_from_slice(&[
        0xFA, 0xBC, 0x00, 0x00, 0x07, 0x00, // cli; mov esp, 0x70000
        0xBF, 0x00, 0x10, 0x00, 0x00, 0xB9, 0x00, 0x0C, 0x00, 0x00, 0x31, 0xC0, 0xFC, 0xF3,
        0xAB, // Clear Page Tables 0x1000..0x4000
        0xC7, 0x05, 0x00, 0x10, 0x00, 0x00, 0x03, 0x20, 0x00, 0x00, // PML4[0] = 0x2003
        0xC7, 0x05, 0x00, 0x20, 0x00, 0x00, 0x03, 0x30, 0x00, 0x00, // PDPT[0] = 0x3003
        0xC7, 0x05, 0x00, 0x30, 0x00, 0x00, 0x83, 0x00, 0x00, 0x00, // PD[0] = 0..2MB RAM
        // Đọc địa chỉ vật lý Linear Framebuffer từ PCI VGA BAR0 (Bus 0, Dev 2, Func 0 = 0x80001010)
        0xB8, 0x10, 0x10, 0x00, 0x80, // mov eax, 0x80001010
        0x66, 0xBA, 0xF8, 0x0C, 0xEF, // mov dx, 0x0CF8; out dx, eax
        0x66, 0xBA, 0xFC, 0x0C, 0xED, // mov dx, 0x0CFC; in eax, dx
        0x25, 0x00, 0x00, 0xE0, 0xFF, // and eax, 0xFFE00000
        0x0D, 0x83, 0x00, 0x00, 0x00, // or eax, 0x83 (Present + RW + 2MB HugePage)
        0xA3, 0x08, 0x30, 0x00, 0x00, // PD[1] (Virtual 0x200000..0x400000) = VRAM Part 1
        0x05, 0x00, 0x00, 0x20, 0x00, // add eax, 0x200000
        0xA3, 0x10, 0x30, 0x00, 0x00, // PD[2] (Virtual 0x400000..0x600000) = VRAM Part 2
        0xC7, 0x05, 0x18, 0x30, 0x00, 0x00, 0x83, 0x00, 0x60, 0x00, // PD[3] = 0x600083
        0xC7, 0x05, 0x20, 0x30, 0x00, 0x00, 0x83, 0x00, 0x80, 0x00, // PD[4] = 0x800083
        // Bật PAE + Long Mode + Paging
        0xB8, 0x00, 0x10, 0x00, 0x00, 0x0F, 0x22, 0xD8, 0x0F, 0x20, 0xE0, 0x83, 0xC8, 0x20, 0x0F,
        0x22, 0xE0, 0xB9, 0x80, 0x00, 0x00, 0xC0, 0x0F, 0x32, 0x0D, 0x00, 0x01, 0x00, 0x00, 0x0F,
        0x30, 0x0F, 0x20, 0xC0, 0x0D, 0x00, 0x00, 0x00, 0x80, 0x0F, 0x22, 0xC0, 0x0F, 0x01, 0x15,
        0x78, 0x00, 0x10, 0x00,
    ]);
    let start64 = base + (elf.len() as u32) + 7;
    elf.push(0xEA);
    elf.extend_from_slice(&start64.to_le_bytes());
    elf.extend_from_slice(&0x0008u16.to_le_bytes());

    let call_rel = (entry_offset as u32) + 2;
    elf.extend_from_slice(&[0x66, 0xB8, 0x10, 0x00, 0x8E, 0xD8, 0x8E, 0xC0, 0x8E, 0xD0]);
    elf.push(0xE8);
    elf.extend_from_slice(&call_rel.to_le_bytes());
    elf.extend_from_slice(&[0xFA, 0xF4]);

    elf.extend_from_slice(code);
    let fsz = (elf.len() as u32).to_le_bytes();
    elf[68..72].copy_from_slice(&fsz);
    elf[72..76].copy_from_slice(&fsz);
    elf
}

fn slot(r: Reg) -> i32 {
    -(((r as i32) + 1) * 8)
}

fn emit_load_rax(c: &mut Vec<u8>, r: Reg) {
    c.extend_from_slice(&[0x48, 0x8B, 0x85]);
    c.extend_from_slice(&slot(r).to_le_bytes());
}

fn emit_load_rcx(c: &mut Vec<u8>, r: Reg) {
    c.extend_from_slice(&[0x48, 0x8B, 0x8D]);
    c.extend_from_slice(&slot(r).to_le_bytes());
}

fn emit_store_rax(c: &mut Vec<u8>, r: Reg) {
    c.extend_from_slice(&[0x48, 0x89, 0x85]);
    c.extend_from_slice(&slot(r).to_le_bytes());
}

fn compile_raw(module: &Module) -> Result<(Vec<u8>, u64, u64), String> {
    let mut code: Vec<u8> = Vec::new();
    let mut func_addrs: HashMap<u32, usize> = HashMap::new();
    let mut call_patches: Vec<(usize, u32)> = Vec::new();

    for (f_idx, func) in module.funcs.iter().enumerate() {
        func_addrs.insert(f_idx as u32, code.len());

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
                    | Inst::CallPtr { dst: Some(dst), .. } => {
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

        // Cấp phát Stack Frame linh hoạt theo số biến SSA tối đa của hàm
        let max_reg = reg_tys.keys().max().copied().unwrap_or(32);
        let frame_size = (((max_reg as u32 + 8) * 8 + 15) & !15).max(0x800);
        code.extend_from_slice(&[0x55, 0x48, 0x89, 0xE5, 0x48, 0x81, 0xEC]);
        code.extend_from_slice(&frame_size.to_le_bytes());

        // 1. Nạp 6 tham số đầu từ thanh ghi (rdi, rsi, rdx, rcx, r8, r9)
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
        // 2. Nạp các tham số từ thứ 7 trở đi từ Stack của hàm gọi ([rbp + 16], [rbp + 24]...)
        for (i, &(reg, _)) in func.params.iter().skip(6).enumerate() {
            let caller_off = (16 + i * 8) as i32;
            code.extend_from_slice(&[0x48, 0x8B, 0x85]); // mov rax, [rbp + caller_off]
            code.extend_from_slice(&caller_off.to_le_bytes());
            emit_store_rax(&mut code, reg);
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
                        emit_store_rax(&mut code, *dst);
                    }
                    Inst::Bin { dst, op, lhs, rhs } => {
                        emit_load_rax(&mut code, *lhs);
                        emit_load_rcx(&mut code, *rhs);
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
                        code.extend_from_slice(&[
                            0x48, 0x39, 0xC8, 0x0F, setcc, 0xC0, 0x48, 0x0F, 0xB6, 0xC0,
                        ]);
                        emit_store_rax(&mut code, *dst);
                    }
                    Inst::Slice { dst, base, idx, ty } => {
                        let layout_id = match ty {
                            Type::Ptr { layout_id, .. } => *layout_id as usize,
                            _ => return Err("Lỗi kiểu Slice".into()),
                        };
                        let elem_size = module.layouts[layout_id].size;
                        emit_load_rax(&mut code, *idx);
                        code.extend_from_slice(&[0x48, 0x69, 0xC0]);
                        code.extend_from_slice(&elem_size.to_le_bytes());
                        emit_load_rcx(&mut code, *base);
                        code.extend_from_slice(&[0x48, 0x01, 0xC8]);
                        emit_store_rax(&mut code, *dst);
                    }
                    Inst::Load {
                        dst,
                        ty,
                        base,
                        offset,
                    } => {
                        emit_load_rcx(&mut code, *base);
                        match ty {
                            Type::Bv8 => code.extend_from_slice(&[0x48, 0x0F, 0xB6, 0x81]),
                            Type::Bv16 => code.extend_from_slice(&[0x48, 0x0F, 0xB7, 0x81]),
                            Type::Bv32 => code.extend_from_slice(&[0x8B, 0x81]),
                            _ => code.extend_from_slice(&[0x48, 0x8B, 0x81]),
                        }
                        code.extend_from_slice(&offset.to_le_bytes());
                        emit_store_rax(&mut code, *dst);
                    }
                    Inst::Store { base, offset, val } => {
                        emit_load_rcx(&mut code, *base);
                        emit_load_rax(&mut code, *val);
                        match reg_tys.get(val).unwrap_or(&Type::Bv64) {
                            Type::Bv8 => code.extend_from_slice(&[0x88, 0x81]),
                            Type::Bv16 => code.extend_from_slice(&[0x66, 0x89, 0x81]),
                            Type::Bv32 => code.extend_from_slice(&[0x89, 0x81]),
                            _ => code.extend_from_slice(&[0x48, 0x89, 0x81]),
                        }
                        code.extend_from_slice(&offset.to_le_bytes());
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
                            emit_load_rax(&mut code, v_reg);
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
                            } else {
                                code.extend_from_slice(&[0x31, 0xC0, 0x66, 0xBA]);
                                code.extend_from_slice(&port_or_reg.to_le_bytes());
                                if *port_or_reg == 0x1F0 {
                                    code.extend_from_slice(&[0x66, 0xED]);
                                } else {
                                    code.push(0xEC);
                                }
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
                            emit_load_rax(&mut code, arg_r);
                            emit_store_rax(&mut code, param_r);
                        }
                        code.extend_from_slice(&[0xE9, 0, 0, 0, 0]);
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
                        let extra = args.len().saturating_sub(6);
                        let pad = if extra % 2 != 0 { 8 } else { 0 };
                        if pad > 0 {
                            code.extend_from_slice(&[0x48, 0x83, 0xEC, 0x08]);
                        }
                        for &r in args.iter().skip(6).rev() {
                            emit_load_rax(&mut code, r);
                            code.push(0x50);
                        }
                        for (i, &r) in args.iter().take(6).enumerate() {
                            code.extend_from_slice(arg_loads[i]);
                            code.extend_from_slice(&slot(r).to_le_bytes());
                        }
                        code.extend_from_slice(&[0xE8, 0, 0, 0, 0]);
                        call_patches.push((code.len() - 4, *func_id));
                        let total_stack = (extra * 8 + pad) as i32;
                        if total_stack > 0 {
                            code.extend_from_slice(&[0x48, 0x81, 0xC4]);
                            code.extend_from_slice(&total_stack.to_le_bytes());
                        }
                        if let Some(d) = dst {
                            emit_store_rax(&mut code, *d);
                        }
                    }
                    Inst::CallPtr { dst, target, args } => {
                        let arg_loads: [&[u8]; 6] = [
                            &[0x48, 0x8B, 0xBD],
                            &[0x48, 0x8B, 0xB5],
                            &[0x48, 0x8B, 0x95],
                            &[0x48, 0x8B, 0x8D],
                            &[0x4C, 0x8B, 0x85],
                            &[0x4C, 0x8B, 0x8D],
                        ];
                        let extra = args.len().saturating_sub(6);
                        let pad = if extra % 2 != 0 { 8 } else { 0 };
                        if pad > 0 {
                            code.extend_from_slice(&[0x48, 0x83, 0xEC, 0x08]);
                        }
                        for &r in args.iter().skip(6).rev() {
                            emit_load_rax(&mut code, r);
                            code.push(0x50);
                        }
                        for (i, &r) in args.iter().take(6).enumerate() {
                            code.extend_from_slice(arg_loads[i]);
                            code.extend_from_slice(&slot(r).to_le_bytes());
                        }
                        emit_load_rax(&mut code, *target);
                        code.extend_from_slice(&[0xFF, 0xD0]); // call rax
                        let total_stack = (extra * 8 + pad) as i32;
                        if total_stack > 0 {
                            code.extend_from_slice(&[0x48, 0x81, 0xC4]);
                            code.extend_from_slice(&total_stack.to_le_bytes());
                        }
                        if let Some(d) = dst {
                            emit_store_rax(&mut code, *d);
                        }
                    }
                    Inst::Ret { val } => {
                        if let Some(r) = val {
                            emit_load_rax(&mut code, *r);
                        }
                        code.extend_from_slice(&[0x48, 0x89, 0xEC, 0x5D, 0xC3]);
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
    Ok((code, entry_offset, icon_offset))
}

pub fn compile_elf64(module: &Module) -> Result<Vec<u8>, String> {
    let (code, entry_offset, _) = compile_raw(module)?;
    Ok(pack_elf64(&code, entry_offset))
}

pub fn compile_app_bin(module: &Module) -> Result<Vec<u8>, String> {
    if !module.funcs.iter().any(|f| f.name == "app_draw_icon") {
        return Err("Mỗi App bắt buộc phải implement hàm 'func app_draw_icon'!".into());
    }
    let (code, entry_offset, icon_offset) = compile_raw(module)?;
    let mut bin = Vec::with_capacity(16 + code.len());

    // Qword 0 (0x90000): jmp app_main (offset 16 + entry_offset, tính từ RIP = 5 -> +11)
    let rel_main = (entry_offset as i32) + 11;
    bin.push(0xE9);
    bin.extend_from_slice(&rel_main.to_le_bytes());
    bin.extend_from_slice(&[0x90, 0x90, 0x90]);

    // Qword 1 (0x90008): jmp app_draw_icon (offset 16 + icon_offset, tính từ RIP = 13 -> +3)
    let rel_icon = (icon_offset as i32) + 3;
    bin.push(0xE9);
    bin.extend_from_slice(&rel_icon.to_le_bytes());
    bin.extend_from_slice(&[0x90, 0x90, 0x90]);

    bin.extend_from_slice(&code);
    if bin.len() > 32768 {
        return Err(format!("App binary quá lớn ({} > 32768 bytes)!", bin.len()));
    }
    Ok(bin)
}
