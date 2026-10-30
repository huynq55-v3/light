//! Native ELF64 Machine Code Emitter & Direct Binary Packager cho Light (.lit)
//! - Generates high-performance x86_64 machine code with standard stack frame allocation
//! - Directly packages standalone minimal Linux ELF64 binaries without any libc/C runtime dependency
//! - Supports all arithmetic, bitwise operations, memory loads/stores, system calls, functions, loops, and branching!

use crate::ast::*;
use std::collections::HashMap;
use std::fs::File;
use std::io::Write;
use std::os::unix::fs::PermissionsExt;

#[allow(dead_code)]
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum X86Reg {
    Rax = 0,
    Rcx = 1,
    Rdx = 2,
    Rbx = 3,
    Rsp = 4,
    Rbp = 5,
    Rsi = 6,
    Rdi = 7,
    R8 = 8,
    R9 = 9,
    R10 = 10,
    R11 = 11,
}

pub struct MachineCodeEmitter {
    pub code: Vec<u8>,
    pub data_section: Vec<u8>,
    pub func_offsets: HashMap<String, usize>,
    pub call_fixups: Vec<(usize, String)>, // (offset to patch rel32, callee function name)
    pub buffer_offsets: HashMap<String, usize>,
    pub slice_capacities: HashMap<String, usize>,
}

impl MachineCodeEmitter {
    pub fn new() -> Self {
        Self {
            code: Vec::new(),
            data_section: Vec::new(),
            func_offsets: HashMap::new(),
            call_fixups: Vec::new(),
            buffer_offsets: HashMap::new(),
            slice_capacities: HashMap::new(),
        }
    }

    // --- CÁC HÀM PHÁT SINH MÃ MÁY X86_64 CƠ BẢN ---

    /// Emit: mov reg, imm64
    pub fn emit_mov_reg_imm64(&mut self, reg: X86Reg, imm: i64) {
        let code = reg as u8;
        if code < 8 {
            self.code.push(0x48);
            self.code.push(0xb8 + code);
        } else {
            self.code.push(0x49);
            self.code.push(0xb8 + (code - 8));
        }
        self.code.extend_from_slice(&imm.to_le_bytes());
    }

    /// Emit: mov dst, src (64-bit)
    pub fn emit_mov_reg_reg(&mut self, dst: X86Reg, src: X86Reg) {
        let dst_code = dst as u8;
        let src_code = src as u8;
        let mut rex = 0x48;
        if src_code >= 8 { rex |= 0x04; }
        if dst_code >= 8 { rex |= 0x01; }
        self.code.push(rex);
        self.code.push(0x89);
        let modrm = 0xc0 | ((src_code & 7) << 3) | (dst_code & 7);
        self.code.push(modrm);
    }

    /// Emit: mov [rbp - slot], reg (64-bit store to stack slot)
    pub fn emit_store_stack(&mut self, src: X86Reg, slot: i32) {
        let src_code = src as u8;
        let mut rex = 0x48;
        if src_code >= 8 { rex |= 0x04; }
        self.code.push(rex);
        self.code.push(0x89);
        let modrm = 0x80 | ((src_code & 7) << 3) | 5; // [rbp + disp32]
        self.code.push(modrm);
        let disp = -slot;
        self.code.extend_from_slice(&disp.to_le_bytes());
    }

    /// Emit: mov reg, [rbp - slot] (64-bit load from stack slot)
    pub fn emit_load_stack(&mut self, dst: X86Reg, slot: i32) {
        let dst_code = dst as u8;
        let mut rex = 0x48;
        if dst_code >= 8 { rex |= 0x04; }
        self.code.push(rex);
        self.code.push(0x8b);
        let modrm = 0x80 | ((dst_code & 7) << 3) | 5;
        self.code.push(modrm);
        let disp = -slot;
        self.code.extend_from_slice(&disp.to_le_bytes());
    }

    /// Emit: movzx rax, byte ptr [rax + rcx]
    pub fn emit_load8_indexed(&mut self) {
        // 48 0f b6 04 08
        self.code.extend_from_slice(&[0x48, 0x0f, 0xb6, 0x04, 0x08]);
    }

    /// Emit: mov byte ptr [rax + rcx], dl
    pub fn emit_store8_indexed(&mut self) {
        // 88 14 08
        self.code.extend_from_slice(&[0x88, 0x14, 0x08]);
    }

    /// Emit: mov rax, qword ptr [rax + rcx]
    pub fn emit_load64_indexed(&mut self) {
        // 48 8b 04 08
        self.code.extend_from_slice(&[0x48, 0x8b, 0x04, 0x08]);
    }

    /// Emit: mov qword ptr [rax + rcx], rdx
    pub fn emit_store64_indexed(&mut self) {
        // 48 89 14 08
        self.code.extend_from_slice(&[0x48, 0x89, 0x14, 0x08]);
    }

    /// Emit: syscall (0F 05)
    pub fn emit_syscall(&mut self) {
        self.code.push(0x0f);
        self.code.push(0x05);
    }

    #[inline]
    fn buf_key(func_name: &str, buf: &str) -> String {
        format!("{}::{}", func_name, buf.trim_start_matches('%'))
    }

    /// Emit: ret (C3)
    pub fn emit_ret(&mut self) {
        self.code.push(0xc3);
    }

    /// Cấp phát trước tất cả các buffer tĩnh để địa chỉ data_section cố định (tránh realloc khi chạy JIT)
    pub fn preallocate_buffers(&mut self, program: &Program) {
        for func in &program.functions {
            for si in &func.instructions {
                match &si.inst {
                    Instruction::AllocSlice { dest, len, .. } => {
                        let key = Self::buf_key(&func.name, dest);
                        if !self.buffer_offsets.contains_key(&key) {
                            let offset = self.data_section.len();
                            self.data_section.resize(offset + len + 16, 0);
                            self.buffer_offsets.insert(key.clone(), offset);
                            self.slice_capacities.insert(key, *len);
                        }
                    }
                    Instruction::Alloc { dest, size } => {
                        let key = Self::buf_key(&func.name, dest);
                        if !self.buffer_offsets.contains_key(&key) {
                            let offset = self.data_section.len();
                            self.data_section.resize(offset + size + 16, 0);
                            self.buffer_offsets.insert(key, offset);
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    /// Biên dịch chương trình sẵn sàng cho đóng gói ELF64 (tự động tính toán chính xác địa chỉ ảo data theo 2 pass)
    pub fn compile_for_elf(&mut self, program: &Program) -> Result<usize, String> {
        let mut probe = MachineCodeEmitter::new();
        probe.preallocate_buffers(program);
        let _ = probe.compile_program(program, 0x400000 + 120)?;
        let code_len = probe.code.len();

        self.preallocate_buffers(program);
        let elf_data_vaddr = 0x400000u64 + 120u64 + (code_len as u64);
        self.compile_program(program, elf_data_vaddr)
    }

    /// Biên dịch toàn bộ chương trình (tất cả các hàm và link các lệnh CALL)
    pub fn compile_program(&mut self, program: &Program, base_data_vaddr: u64) -> Result<usize, String> {
        let main_func = program
            .functions
            .iter()
            .find(|f| f.name == "main")
            .ok_or_else(|| "Missing 'main' function".to_string())?;

        // 1. Compile main function first
        let main_offset = self.code.len();
        self.func_offsets.insert("main".into(), main_offset);
        self.compile_function(main_func, program, base_data_vaddr)?;

        // 2. Compile remaining functions
        for func in &program.functions {
            if func.name != "main" {
                let offset = self.code.len();
                self.func_offsets.insert(func.name.clone(), offset);
                self.compile_function(func, program, base_data_vaddr)?;
            }
        }

        // 3. Linker / Fixup rel32 for CALLs
        for (call_site, func_name) in &self.call_fixups {
            let target_offset = self
                .func_offsets
                .get(func_name)
                .ok_or_else(|| format!("Link error: Unresolved symbol '{}'", func_name))?;

            let rel32 = (*target_offset as i64) - ((*call_site + 4) as i64);
            let rel32_bytes = (rel32 as i32).to_le_bytes();
            self.code[*call_site..*call_site + 4].copy_from_slice(&rel32_bytes);
        }

        Ok(main_offset)
    }

    /// Biên dịch một hàm Light sang mã máy x86_64 dùng Stack Frame
    pub fn compile_function(
        &mut self,
        func: &Function,
        _program: &Program,
        base_data_vaddr: u64,
    ) -> Result<(), String> {
        let mut slots: HashMap<String, i32> = HashMap::new();
        let mut next_slot: i32 = 8;

        // 1. Collect all parameters
        for p in &func.params {
            let clean = p.name.trim_start_matches('%').to_string();
            slots.insert(clean.clone(), next_slot);
            next_slot += 8;
            if matches!(p.ty, Type::Slice(_)) {
                slots.insert(format!("{}_len", clean), next_slot);
                next_slot += 8;
            }
        }

        // 2. Collect all local registers & variables defined in instructions
        for si in &func.instructions {
            match &si.inst {
                Instruction::AssignConst { dest, .. }
                | Instruction::Alloc { dest, .. }
                | Instruction::SlicePtr { dest, .. }
                | Instruction::SliceLen { dest, .. }
                | Instruction::Load8 { dest, .. }
                | Instruction::Load64 { dest, .. }
                | Instruction::Mov { dest, .. }
                | Instruction::Binary { dest, .. }
                | Instruction::Not { dest, .. } => {
                    let clean = dest.trim_start_matches('%').to_string();
                    if !slots.contains_key(&clean) {
                        slots.insert(clean, next_slot);
                        next_slot += 8;
                    }
                }
                Instruction::AllocSlice { dest, len, .. } => {
                    let clean = dest.trim_start_matches('%').to_string();
                    if !slots.contains_key(&clean) {
                        slots.insert(clean.clone(), next_slot);
                        next_slot += 8;
                        slots.insert(format!("{}_len", clean), next_slot);
                        next_slot += 8;
                    }
                    let key = Self::buf_key(&func.name, dest);
                    if !self.buffer_offsets.contains_key(&key) {
                        let offset = self.data_section.len();
                        self.data_section.resize(offset + len + 16, 0);
                        self.buffer_offsets.insert(key.clone(), offset);
                        self.slice_capacities.insert(key, *len);
                    }
                }
                Instruction::Call { dest: Some(d), .. } | Instruction::Syscall { dest: Some(d), .. } => {
                    let clean = d.trim_start_matches('%').to_string();
                    if !slots.contains_key(&clean) {
                        slots.insert(clean, next_slot);
                        next_slot += 8;
                    }
                }
                _ => {}
            }
        }

        // Frame size aligned to 16 bytes
        let frame_size = ((next_slot + 15) / 16) * 16;

        // --- PROLOGUE ---
        // push rbp (0x55)
        self.code.push(0x55);
        // mov rbp, rsp (48 89 e5)
        self.code.extend_from_slice(&[0x48, 0x89, 0xe5]);
        // sub rsp, frame_size (48 81 ec disp32)
        self.code.extend_from_slice(&[0x48, 0x81, 0xec]);
        self.code.extend_from_slice(&(frame_size as i32).to_le_bytes());

        // System V AMD64 ABI registers: Rdi, Rsi, Rdx, Rcx, R8, R9
        let abi_regs = [X86Reg::Rdi, X86Reg::Rsi, X86Reg::Rdx, X86Reg::Rcx, X86Reg::R8, X86Reg::R9];

        // Save incoming parameters
        if func.name == "main" {
            // Linux raw ELF entry point stack layout:
            // [rbp + 8]: argc
            // [rbp + 24]: argv[1]
            for (idx, p) in func.params.iter().enumerate() {
                let clean = p.name.trim_start_matches('%');
                if let Some(&slot) = slots.get(clean) {
                    if idx == 0 {
                        // mov rax, [rbp + 8] (48 8b 45 08)
                        self.code.extend_from_slice(&[0x48, 0x8b, 0x45, 0x08]);
                        self.emit_store_stack(X86Reg::Rax, slot);
                    } else if idx == 1 {
                        // mov rax, [rbp + 24] (48 8b 45 18)
                        self.code.extend_from_slice(&[0x48, 0x8b, 0x45, 0x18]);
                        self.emit_store_stack(X86Reg::Rax, slot);
                    } else if idx == 2 {
                        // mov rax, [rbp + 32] (48 8b 45 20)
                        self.code.extend_from_slice(&[0x48, 0x8b, 0x45, 0x20]);
                        self.emit_store_stack(X86Reg::Rax, slot);
                    }
                }
            }
        } else {
            let mut reg_idx = 0;
            for p in &func.params {
                let clean = p.name.trim_start_matches('%');
                if let Some(&slot) = slots.get(clean) {
                    if reg_idx < abi_regs.len() {
                        self.emit_store_stack(abi_regs[reg_idx], slot);
                        reg_idx += 1;
                    }
                }
            }
        }

        // --- HELPER CLOSURES FOR OPERAND ACCESS ---
        let load_op_into_reg = |emitter: &mut MachineCodeEmitter, op: &Operand, target: X86Reg| {
            match op {
                Operand::Const(Value::I64(n)) => emitter.emit_mov_reg_imm64(target, *n),
                Operand::Const(Value::U64(n)) => emitter.emit_mov_reg_imm64(target, *n as i64),
                Operand::Const(Value::Bool(b)) => emitter.emit_mov_reg_imm64(target, if *b { 1 } else { 0 }),
                Operand::Const(Value::Ptr(p)) => emitter.emit_mov_reg_imm64(target, *p as i64),
                Operand::Reg(r) => {
                    if r.starts_with("len(") && r.ends_with(')') {
                        let inner = &r[4..r.len() - 1].trim();
                        let clean = inner.trim_start_matches('%');
                        let len_name = format!("{}_len", clean);
                        let key = Self::buf_key(&func.name, inner);
                        if let Some(&slot) = slots.get(&len_name) {
                            emitter.emit_load_stack(target, slot);
                        } else if let Some(&cap) = emitter.slice_capacities.get(&key).or_else(|| emitter.slice_capacities.get(*inner)) {
                            emitter.emit_mov_reg_imm64(target, cap as i64);
                        } else {
                            emitter.emit_mov_reg_imm64(target, 0);
                        }
                    } else {
                        let key = Self::buf_key(&func.name, r);
                        if let Some(&buf_off) = emitter.buffer_offsets.get(&key).or_else(|| emitter.buffer_offsets.get(r)) {
                            let vaddr = base_data_vaddr + (buf_off as u64);
                            emitter.emit_mov_reg_imm64(target, vaddr as i64);
                        } else {
                            let clean = r.trim_start_matches('%');
                            if let Some(&slot) = slots.get(clean) {
                                emitter.emit_load_stack(target, slot);
                            } else {
                                emitter.emit_mov_reg_imm64(target, 0);
                            }
                        }
                    }
                }
                _ => emitter.emit_mov_reg_imm64(target, 0),
            }
        };

        // --- EMIT INSTRUCTIONS ---
        let mut label_offsets: HashMap<String, usize> = HashMap::new();
        let mut jump_fixups: Vec<(usize, String, bool)> = Vec::new(); // (patch_pos, target, is_jnz)
        let mut loop_stack: Vec<(String, String)> = Vec::new(); // (start_label, end_label)

        for si in &func.instructions {
            match &si.inst {
                Instruction::Require(_) | Instruction::Ensure(_) | Instruction::Invariant(_) | Instruction::Decreases(_) | Instruction::Assert(_) => {}

                Instruction::AssignConst { dest, val, .. } => {
                    let clean = dest.trim_start_matches('%');
                    let slot = slots[clean];
                    match val {
                        Value::I64(n) => self.emit_mov_reg_imm64(X86Reg::Rax, *n),
                        Value::U64(n) => self.emit_mov_reg_imm64(X86Reg::Rax, *n as i64),
                        Value::Bool(b) => self.emit_mov_reg_imm64(X86Reg::Rax, if *b { 1 } else { 0 }),
                        Value::Ptr(p) => self.emit_mov_reg_imm64(X86Reg::Rax, *p as i64),
                        _ => self.emit_mov_reg_imm64(X86Reg::Rax, 0),
                    }
                    self.emit_store_stack(X86Reg::Rax, slot);
                }

                Instruction::Alloc { dest, size } => {
                    let key = Self::buf_key(&func.name, dest);
                    let offset = if let Some(&off) = self.buffer_offsets.get(&key).or_else(|| self.buffer_offsets.get(dest)) {
                        off
                    } else {
                        let offset = self.data_section.len();
                        self.data_section.resize(offset + size + 16, 0);
                        self.buffer_offsets.insert(key, offset);
                        offset
                    };
                    let clean = dest.trim_start_matches('%');
                    let slot = slots[clean];
                    let vaddr = base_data_vaddr + (offset as u64);
                    self.emit_mov_reg_imm64(X86Reg::Rax, vaddr as i64);
                    self.emit_store_stack(X86Reg::Rax, slot);
                }

                Instruction::AllocSlice { dest, len, .. } => {
                    let key = Self::buf_key(&func.name, dest);
                    let offset = self.buffer_offsets.get(&key).or_else(|| self.buffer_offsets.get(dest)).copied().unwrap_or(0);
                    let clean = dest.trim_start_matches('%');
                    let slot = slots[clean];
                    let vaddr = base_data_vaddr + (offset as u64);
                    self.emit_mov_reg_imm64(X86Reg::Rax, vaddr as i64);
                    self.emit_store_stack(X86Reg::Rax, slot);

                    let len_name = format!("{}_len", clean);
                    let slot_len = slots[&len_name];
                    self.emit_mov_reg_imm64(X86Reg::Rax, *len as i64);
                    self.emit_store_stack(X86Reg::Rax, slot_len);
                }

                Instruction::SlicePtr { dest, slice } => {
                    let clean = dest.trim_start_matches('%');
                    let slot = slots[clean];
                    let key = Self::buf_key(&func.name, slice);
                    if let Some(&buf_off) = self.buffer_offsets.get(&key).or_else(|| self.buffer_offsets.get(slice)) {
                        let vaddr = base_data_vaddr + (buf_off as u64);
                        self.emit_mov_reg_imm64(X86Reg::Rax, vaddr as i64);
                    } else {
                        let sl_clean = slice.trim_start_matches('%');
                        if let Some(&s_slot) = slots.get(sl_clean) {
                            self.emit_load_stack(X86Reg::Rax, s_slot);
                        }
                    }
                    self.emit_store_stack(X86Reg::Rax, slot);
                }

                Instruction::SliceLen { dest, slice } => {
                    let clean = dest.trim_start_matches('%');
                    let slot = slots[clean];
                    let sl_clean = slice.trim_start_matches('%');
                    let key = Self::buf_key(&func.name, slice);

                    if let Some(&s_slot) = slots.get(sl_clean) {
                        self.emit_load_stack(X86Reg::Rax, s_slot);
                        // Inline strlen on RAX:
                        // 31 c9: xor ecx, ecx
                        // 8a 14 08: mov dl, byte ptr [rax + rcx]
                        // 84 d2: test dl, dl
                        // 74 05: jz +5 (to mov rax, rcx)
                        // 48 ff c1: inc rcx
                        // eb f4: jmp -12 (to mov dl, [rax + rcx])
                        // 48 89 c8: mov rax, rcx
                        self.code.extend_from_slice(&[
                            0x31, 0xc9,
                            0x8a, 0x14, 0x08,
                            0x84, 0xd2,
                            0x74, 0x05,
                            0x48, 0xff, 0xc1,
                            0xeb, 0xf4,
                            0x48, 0x89, 0xc8,
                        ]);
                        // Nếu strlen == 0 và đây là biến ALLOC slice cục bộ có capacity > 0, fallback về capacity:
                        if let Some(&cap) = self.slice_capacities.get(&key).or_else(|| self.slice_capacities.get(slice)) {
                            // test rax, rax (48 85 c0)
                            // jnz +10 (75 0a) -> nhảy qua mov rax, imm64
                            self.code.extend_from_slice(&[0x48, 0x85, 0xc0, 0x75, 0x0a]);
                            self.emit_mov_reg_imm64(X86Reg::Rax, cap as i64);
                        }
                    } else if let Some(&cap) = self.slice_capacities.get(&key).or_else(|| self.slice_capacities.get(slice)) {
                        self.emit_mov_reg_imm64(X86Reg::Rax, cap as i64);
                    } else {
                        self.emit_mov_reg_imm64(X86Reg::Rax, 0);
                    }
                    self.emit_store_stack(X86Reg::Rax, slot);
                }

                Instruction::StoreStr { buf, offset, content } => {
                    let key = Self::buf_key(&func.name, buf);
                    let buf_off = self.buffer_offsets.get(&key).or_else(|| self.buffer_offsets.get(buf)).cloned().unwrap_or(0);
                    let target_off = buf_off + offset;
                    let bytes = content.as_bytes();
                    if target_off + bytes.len() + 1 > self.data_section.len() {
                        self.data_section.resize(target_off + bytes.len() + 1, 0);
                    }
                    self.data_section[target_off..target_off + bytes.len()].copy_from_slice(bytes);
                    self.data_section[target_off + bytes.len()] = 0;
                }

                Instruction::Load8 { dest, buf, offset } => {
                    load_op_into_reg(self, &Operand::Reg(buf.clone()), X86Reg::Rax);
                    load_op_into_reg(self, offset, X86Reg::Rcx);
                    self.emit_load8_indexed();
                    let clean = dest.trim_start_matches('%');
                    self.emit_store_stack(X86Reg::Rax, slots[clean]);
                }

                Instruction::Store8 { buf, offset, val } => {
                    load_op_into_reg(self, &Operand::Reg(buf.clone()), X86Reg::Rax);
                    load_op_into_reg(self, offset, X86Reg::Rcx);
                    load_op_into_reg(self, val, X86Reg::Rdx);
                    self.emit_store8_indexed();
                }

                Instruction::Load64 { dest, buf, offset } => {
                    load_op_into_reg(self, &Operand::Reg(buf.clone()), X86Reg::Rax);
                    load_op_into_reg(self, offset, X86Reg::Rcx);
                    self.emit_load64_indexed();
                    let clean = dest.trim_start_matches('%');
                    self.emit_store_stack(X86Reg::Rax, slots[clean]);
                }

                Instruction::Store64 { buf, offset, val } => {
                    load_op_into_reg(self, &Operand::Reg(buf.clone()), X86Reg::Rax);
                    load_op_into_reg(self, offset, X86Reg::Rcx);
                    load_op_into_reg(self, val, X86Reg::Rdx);
                    self.emit_store64_indexed();
                }

                Instruction::Mov { dest, src } => {
                    let d_clean = dest.trim_start_matches('%');
                    let d_slot = slots[d_clean];
                    let key = Self::buf_key(&func.name, src);
                    if let Some(&buf_off) = self.buffer_offsets.get(&key).or_else(|| self.buffer_offsets.get(src)) {
                        let vaddr = base_data_vaddr + (buf_off as u64);
                        self.emit_mov_reg_imm64(X86Reg::Rax, vaddr as i64);
                    } else {
                        let s_clean = src.trim_start_matches('%');
                        if let Some(&s_slot) = slots.get(s_clean) {
                            self.emit_load_stack(X86Reg::Rax, s_slot);
                        } else {
                            self.emit_mov_reg_imm64(X86Reg::Rax, 0);
                        }
                    }
                    self.emit_store_stack(X86Reg::Rax, d_slot);
                }

                Instruction::Binary { op, dest, src1, src2, .. } => {
                    load_op_into_reg(self, src1, X86Reg::Rax);
                    load_op_into_reg(self, src2, X86Reg::Rcx);

                    match op {
                        BinOp::Add => self.code.extend_from_slice(&[0x48, 0x01, 0xc8]),
                        BinOp::Sub => self.code.extend_from_slice(&[0x48, 0x29, 0xc8]),
                        BinOp::Mul => self.code.extend_from_slice(&[0x48, 0x0f, 0xaf, 0xc1]),
                        BinOp::Div => {
                            // cqo; idiv rcx
                            self.code.extend_from_slice(&[0x48, 0x99, 0x48, 0xf7, 0xf9]);
                        }
                        BinOp::Mod => {
                            // cqo; idiv rcx; mov rax, rdx
                            self.code.extend_from_slice(&[0x48, 0x99, 0x48, 0xf7, 0xf9, 0x48, 0x89, 0xd0]);
                        }
                        BinOp::And | BinOp::BitAnd => self.code.extend_from_slice(&[0x48, 0x21, 0xc8]),
                        BinOp::Or | BinOp::BitOr => self.code.extend_from_slice(&[0x48, 0x09, 0xc8]),
                        BinOp::Xor => self.code.extend_from_slice(&[0x48, 0x31, 0xc8]),
                        BinOp::Shl => self.code.extend_from_slice(&[0x48, 0xd3, 0xe0]),
                        BinOp::Shr => self.code.extend_from_slice(&[0x48, 0xd3, 0xe8]),
                        BinOp::Sar => self.code.extend_from_slice(&[0x48, 0xd3, 0xf8]),
                        BinOp::Eq => {
                            // cmp rax, rcx; sete al; movzx rax, al
                            self.code.extend_from_slice(&[0x48, 0x39, 0xc8, 0x0f, 0x94, 0xc0, 0x48, 0x0f, 0xb6, 0xc0]);
                        }
                        BinOp::Neq => {
                            self.code.extend_from_slice(&[0x48, 0x39, 0xc8, 0x0f, 0x95, 0xc0, 0x48, 0x0f, 0xb6, 0xc0]);
                        }
                        BinOp::Lt => {
                            self.code.extend_from_slice(&[0x48, 0x39, 0xc8, 0x0f, 0x9c, 0xc0, 0x48, 0x0f, 0xb6, 0xc0]);
                        }
                        BinOp::Lte => {
                            self.code.extend_from_slice(&[0x48, 0x39, 0xc8, 0x0f, 0x9e, 0xc0, 0x48, 0x0f, 0xb6, 0xc0]);
                        }
                        BinOp::Gt => {
                            self.code.extend_from_slice(&[0x48, 0x39, 0xc8, 0x0f, 0x9f, 0xc0, 0x48, 0x0f, 0xb6, 0xc0]);
                        }
                        BinOp::Gte => {
                            self.code.extend_from_slice(&[0x48, 0x39, 0xc8, 0x0f, 0x9d, 0xc0, 0x48, 0x0f, 0xb6, 0xc0]);
                        }
                    }

                    let clean = dest.trim_start_matches('%');
                    self.emit_store_stack(X86Reg::Rax, slots[clean]);
                }

                Instruction::Not { dest, ty, src } => {
                    load_op_into_reg(self, src, X86Reg::Rax);
                    if matches!(ty, Type::Bool) {
                        // xor rax, 1
                        self.code.extend_from_slice(&[0x48, 0x83, 0xf0, 0x01]);
                    } else {
                        // not rax
                        self.code.extend_from_slice(&[0x48, 0xf7, 0xd0]);
                    }
                    let clean = dest.trim_start_matches('%');
                    self.emit_store_stack(X86Reg::Rax, slots[clean]);
                }

                Instruction::Label(name) => {
                    label_offsets.insert(name.clone(), self.code.len());
                }

                Instruction::Jump(target) => {
                    // jmp rel32 (E9 disp32)
                    self.code.push(0xe9);
                    let fix = self.code.len();
                    self.code.extend_from_slice(&[0, 0, 0, 0]);
                    jump_fixups.push((fix, target.clone(), false));
                }

                Instruction::BrIf { cond, target } => {
                    let clean = cond.trim_start_matches('%');
                    self.emit_load_stack(X86Reg::Rax, slots[clean]);
                    // test rax, rax (48 85 c0)
                    self.code.extend_from_slice(&[0x48, 0x85, 0xc0]);
                    // jnz rel32 (0F 85 disp32)
                    self.code.extend_from_slice(&[0x0f, 0x85]);
                    let fix = self.code.len();
                    self.code.extend_from_slice(&[0, 0, 0, 0]);
                    jump_fixups.push((fix, target.clone(), true));
                }

                Instruction::Loop(name) => {
                    let start_lbl = format!("__loop_start_{}", name);
                    let end_lbl = format!("__loop_end_{}", name);
                    label_offsets.insert(start_lbl.clone(), self.code.len());
                    loop_stack.push((start_lbl, end_lbl));
                }

                Instruction::BreakIf(cond) => {
                    if let Some((_, end_lbl)) = loop_stack.last() {
                        let clean = cond.trim_start_matches('%');
                        self.emit_load_stack(X86Reg::Rax, slots[clean]);
                        self.code.extend_from_slice(&[0x48, 0x85, 0xc0]);
                        self.code.extend_from_slice(&[0x0f, 0x85]);
                        let fix = self.code.len();
                        self.code.extend_from_slice(&[0, 0, 0, 0]);
                        jump_fixups.push((fix, end_lbl.clone(), true));
                    }
                }

                Instruction::ContinueIf(cond) => {
                    if let Some((start_lbl, _)) = loop_stack.last() {
                        let clean = cond.trim_start_matches('%');
                        self.emit_load_stack(X86Reg::Rax, slots[clean]);
                        self.code.extend_from_slice(&[0x48, 0x85, 0xc0]);
                        self.code.extend_from_slice(&[0x0f, 0x85]);
                        let fix = self.code.len();
                        self.code.extend_from_slice(&[0, 0, 0, 0]);
                        jump_fixups.push((fix, start_lbl.clone(), true));
                    }
                }

                Instruction::EndLoop(_name) => {
                    if let Some((start_lbl, end_lbl)) = loop_stack.pop() {
                        self.code.push(0xe9);
                        let fix = self.code.len();
                        self.code.extend_from_slice(&[0, 0, 0, 0]);
                        jump_fixups.push((fix, start_lbl, false));
                        label_offsets.insert(end_lbl, self.code.len());
                    }
                }

                Instruction::Call { dest, func_name, args } => {
                    // System V AMD64 ABI: Rdi, Rsi, Rdx, Rcx, R8, R9
                    let mut reg_idx = 0;

                    for arg in args {
                        if reg_idx >= abi_regs.len() { break; }
                        let target_reg = abi_regs[reg_idx];
                        load_op_into_reg(self, arg, target_reg);
                        reg_idx += 1;
                    }

                    // call rel32 (E8 disp32)
                    self.code.push(0xe8);
                    let call_site = self.code.len();
                    self.code.extend_from_slice(&[0, 0, 0, 0]);
                    self.call_fixups.push((call_site, func_name.clone()));

                    if let Some(d) = dest {
                        let clean = d.trim_start_matches('%');
                        self.emit_store_stack(X86Reg::Rax, slots[clean]);
                    }
                }

                Instruction::Syscall { dest, rax, rdi, rsi, rdx, r10, r8, r9 } => {
                    if let Some(op) = r9 { load_op_into_reg(self, op, X86Reg::R9); }
                    if let Some(op) = r8 { load_op_into_reg(self, op, X86Reg::R8); }
                    if let Some(op) = r10 { load_op_into_reg(self, op, X86Reg::R10); }
                    load_op_into_reg(self, rdx, X86Reg::Rdx);
                    load_op_into_reg(self, rsi, X86Reg::Rsi);
                    load_op_into_reg(self, rdi, X86Reg::Rdi);
                    load_op_into_reg(self, rax, X86Reg::Rax);
                    self.emit_syscall();

                    if let Some(d) = dest {
                        let clean = d.trim_start_matches('%');
                        self.emit_store_stack(X86Reg::Rax, slots[clean]);
                    }
                }

                Instruction::RetIf { cond, val } => {
                    let clean = cond.trim_start_matches('%');
                    self.emit_load_stack(X86Reg::Rax, slots[clean]);
                    self.code.extend_from_slice(&[0x48, 0x85, 0xc0]); // test rax, rax
                    self.code.extend_from_slice(&[0x0f, 0x84]); // jz rel32
                    let jz_fix = self.code.len();
                    self.code.extend_from_slice(&[0, 0, 0, 0]);

                    if let Some(op) = val {
                        load_op_into_reg(self, op, X86Reg::Rax);
                    }
                    if func.name == "main" {
                        self.emit_mov_reg_reg(X86Reg::Rdi, X86Reg::Rax);
                        self.emit_mov_reg_imm64(X86Reg::Rax, 60);
                        self.emit_syscall();
                    } else {
                        // Epilogue
                        self.code.extend_from_slice(&[0x48, 0x89, 0xec]); // mov rsp, rbp
                        self.code.push(0x5d); // pop rbp
                        self.emit_ret();
                    }

                    let fallthrough = self.code.len();
                    let rel = (fallthrough as i32) - (jz_fix as i32 + 4);
                    self.code[jz_fix..jz_fix + 4].copy_from_slice(&rel.to_le_bytes());
                }

                Instruction::Ret(val) => {
                    if let Some(op) = val {
                        load_op_into_reg(self, op, X86Reg::Rax);
                    }
                    if func.name == "main" {
                        self.emit_mov_reg_reg(X86Reg::Rdi, X86Reg::Rax);
                        self.emit_mov_reg_imm64(X86Reg::Rax, 60);
                        self.emit_syscall();
                    } else {
                        // Epilogue
                        self.code.extend_from_slice(&[0x48, 0x89, 0xec]); // mov rsp, rbp
                        self.code.push(0x5d); // pop rbp
                        self.emit_ret();
                    }
                }
            }
        }

        // Epilogue default if not already returned
        if self.code.last() != Some(&0xc3) {
            self.code.extend_from_slice(&[0x48, 0x89, 0xec]);
            self.code.push(0x5d);
            self.emit_ret();
        }

        // Resolve jump_fixups within function
        for (patch_pos, target, _) in &jump_fixups {
            if let Some(&tgt_offset) = label_offsets.get(target) {
                let rel32 = (tgt_offset as i64) - ((*patch_pos + 4) as i64);
                let rel32_bytes = (rel32 as i32).to_le_bytes();
                self.code[*patch_pos..*patch_pos + 4].copy_from_slice(&rel32_bytes);
            } else {
                return Err(format!("Undefined label '{}' in function '{}'", target, func.name));
            }
        }

        Ok(())
    }

    /// Đóng gói mã máy x86_64 thành file thực thi nhị phân Linux ELF64 hoàn chỉnh
    pub fn emit_elf64(&self, output_path: &str) -> std::io::Result<()> {
        let mut file = File::create(output_path)?;

        let elf_header_size = 64usize;
        let prog_header_size = 56usize;
        let num_phdrs = 1usize;
        let headers_size = elf_header_size + prog_header_size * num_phdrs;

        let base_vaddr = 0x400000u64;
        let entry_point = base_vaddr + (headers_size as u64);

        let total_filesz = (headers_size + self.code.len() + self.data_section.len()) as u64;

        // 1. ELF Header (64 bytes)
        let mut elf_header = vec![0u8; 64];
        elf_header[0..4].copy_from_slice(b"\x7fELF"); // Magic
        elf_header[4] = 2; // 64-bit
        elf_header[5] = 1; // Little endian
        elf_header[6] = 1; // ELF version
        elf_header[7] = 0; // System V ABI
        elf_header[16..18].copy_from_slice(&2u16.to_le_bytes()); // ET_EXEC
        elf_header[18..20].copy_from_slice(&0x3eu16.to_le_bytes()); // x86_64
        elf_header[20..24].copy_from_slice(&1u32.to_le_bytes()); // Version
        elf_header[24..32].copy_from_slice(&entry_point.to_le_bytes()); // Entry point
        elf_header[32..40].copy_from_slice(&(elf_header_size as u64).to_le_bytes()); // e_phoff = 64
        elf_header[40..48].copy_from_slice(&0u64.to_le_bytes()); // e_shoff = 0
        elf_header[48..52].copy_from_slice(&0u32.to_le_bytes()); // e_flags = 0
        elf_header[52..54].copy_from_slice(&(elf_header_size as u16).to_le_bytes()); // e_ehsize = 64
        elf_header[54..56].copy_from_slice(&(prog_header_size as u16).to_le_bytes()); // e_phentsize = 56
        elf_header[56..58].copy_from_slice(&(num_phdrs as u16).to_le_bytes()); // e_phnum = 1
        elf_header[58..60].copy_from_slice(&0u16.to_le_bytes()); // e_shentsize = 0
        elf_header[60..62].copy_from_slice(&0u16.to_le_bytes()); // e_shnum = 0
        elf_header[62..64].copy_from_slice(&0u16.to_le_bytes()); // e_shstrndx = 0

        // 2. Program Header: PT_LOAD RWX (56 bytes)
        let mut phdr = vec![0u8; 56];
        phdr[0..4].copy_from_slice(&1u32.to_le_bytes()); // PT_LOAD
        phdr[4..8].copy_from_slice(&7u32.to_le_bytes()); // PF_R | PF_W | PF_X
        phdr[8..16].copy_from_slice(&0u64.to_le_bytes()); // Offset 0
        phdr[16..24].copy_from_slice(&base_vaddr.to_le_bytes()); // Vaddr 0x400000
        phdr[24..32].copy_from_slice(&base_vaddr.to_le_bytes()); // Paddr 0x400000
        phdr[32..40].copy_from_slice(&total_filesz.to_le_bytes()); // File size
        phdr[40..48].copy_from_slice(&total_filesz.to_le_bytes()); // Mem size
        phdr[48..56].copy_from_slice(&0x1000u64.to_le_bytes()); // Align 4KB

        file.write_all(&elf_header)?;
        file.write_all(&phdr)?;
        file.write_all(&self.code)?;
        file.write_all(&self.data_section)?;

        let mut perms = file.metadata()?.permissions();
        perms.set_mode(0o755);
        file.set_permissions(perms)?;

        Ok(())
    }
}
