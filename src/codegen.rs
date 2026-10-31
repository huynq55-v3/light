//! Native ELF64 Machine Code Emitter & Direct Binary Packager cho Light (.lit)
//! - Generates high-performance x86_64 machine code with standard stack frame allocation
//! - Directly packages standalone minimal Linux ELF64 binaries without any libc/C runtime dependency
//! - Supports all arithmetic, bitwise operations, memory loads/stores, system calls, functions, loops, and branching!

use crate::ast::*;
use crate::ivl::{FunctionBufferContext, IvlLowerer};
use std::collections::HashMap;
use std::fs::File;
use std::io::Write;
use std::os::unix::fs::PermissionsExt;
use std::sync::Mutex;

/// Khóa đồng bộ toàn cục giữa bước tạo/đóng file thực thi ELF (`emit_elf64`) và bước `fork()`/`spawn()` tiến trình con
/// nhằm ngăn chặn triệt để lỗi race condition `ETXTBSY (Text file busy)` của Linux Kernel khi chạy đa luồng.
pub static SPAWN_LOCK: Mutex<()> = Mutex::new(());

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
        if src_code >= 8 {
            rex |= 0x04;
        }
        if dst_code >= 8 {
            rex |= 0x01;
        }
        self.code.push(rex);
        self.code.push(0x89);
        let modrm = 0xc0 | ((src_code & 7) << 3) | (dst_code & 7);
        self.code.push(modrm);
    }

    /// Emit: mov [rbp - slot], reg (64-bit store to stack slot)
    pub fn emit_store_stack(&mut self, src: X86Reg, slot: i32) {
        let src_code = src as u8;
        let mut rex = 0x48;
        if src_code >= 8 {
            rex |= 0x04;
        }
        self.code.push(rex);
        self.code.push(0x89);
        let modrm = 0x80 | ((src_code & 7) << 3) | 5; // [rbp + disp32]
        self.code.push(modrm);
        self.code.extend_from_slice(&(-slot).to_le_bytes());
    }

    /// Emit: mov reg, [rbp - slot] (64-bit load from stack slot)
    pub fn emit_load_stack(&mut self, dst: X86Reg, slot: i32) {
        let dst_code = dst as u8;
        let mut rex = 0x48;
        if dst_code >= 8 {
            rex |= 0x04;
        }
        self.code.push(rex);
        self.code.push(0x8b);
        let modrm = 0x80 | ((dst_code & 7) << 3) | 5;
        self.code.push(modrm);
        self.code.extend_from_slice(&(-slot).to_le_bytes());
    }

    /// Emit: movzx rax, byte ptr [rax + rcx]
    pub fn emit_load8_indexed(&mut self) {
        self.code.extend_from_slice(&[0x48, 0x0f, 0xb6, 0x04, 0x08]);
    }

    /// Emit: mov byte ptr [rax + rcx], dl
    pub fn emit_store8_indexed(&mut self) {
        self.code.extend_from_slice(&[0x88, 0x14, 0x08]);
    }

    /// Emit: mov rax, qword ptr [rax + rcx]
    pub fn emit_load64_indexed(&mut self) {
        self.code.extend_from_slice(&[0x48, 0x8b, 0x04, 0x08]);
    }

    /// Emit: mov qword ptr [rax + rcx], rdx
    pub fn emit_store64_indexed(&mut self) {
        self.code.extend_from_slice(&[0x48, 0x89, 0x14, 0x08]);
    }

    /// Emit: syscall (0F 05)
    pub fn emit_syscall(&mut self) {
        self.code.extend_from_slice(&[0x0f, 0x05]);
    }

    #[inline]
    fn buf_key(func_name: &str, buf: &str) -> String {
        format!("{}::{}", func_name, IvlLowerer::clean_name(buf))
    }

    /// Emit: ret (C3)
    pub fn emit_ret(&mut self) {
        self.code.push(0xc3);
    }

    /// Emit function return or sys_exit(rax) if inside `main`
    fn emit_return_or_exit(&mut self, is_main: bool) {
        if is_main {
            self.emit_mov_reg_reg(X86Reg::Rdi, X86Reg::Rax);
            self.emit_mov_reg_imm64(X86Reg::Rax, 60);
            self.emit_syscall();
        } else {
            self.code.extend_from_slice(&[0x48, 0x89, 0xec, 0x5d]); // mov rsp, rbp; pop rbp
            self.emit_ret();
        }
    }

    /// Emit unconditional `jmp rel32` and record jump fixup
    fn emit_uncond_jump(&mut self, target: String, jump_fixups: &mut Vec<(usize, String)>) {
        self.code.push(0xe9);
        let fix = self.code.len();
        self.code.extend_from_slice(&[0, 0, 0, 0]);
        jump_fixups.push((fix, target));
    }

    /// Emit `test rax, rax; jnz rel32` from stack slot and record jump fixup
    fn emit_cond_jump(
        &mut self,
        slot: i32,
        target: String,
        jump_fixups: &mut Vec<(usize, String)>,
    ) {
        self.emit_load_stack(X86Reg::Rax, slot);
        self.code.extend_from_slice(&[0x48, 0x85, 0xc0, 0x0f, 0x85]); // test rax, rax; jnz rel32
        let fix = self.code.len();
        self.code.extend_from_slice(&[0, 0, 0, 0]);
        jump_fixups.push((fix, target));
    }

    /// Cấp phát một buffer tĩnh vào data_section nếu chưa có
    fn ensure_buffer_allocated(&mut self, func_name: &str, dest: &str, elem_ty: &Type, len: usize) {
        let key = Self::buf_key(func_name, dest);
        if !self.buffer_offsets.contains_key(&key) {
            let byte_len = len.saturating_mul(elem_ty.byte_size());
            let offset = self.data_section.len();
            self.data_section.resize(offset + byte_len + 16, 0);
            self.buffer_offsets.insert(key.clone(), offset);
            self.slice_capacities.insert(key, byte_len);
        }
    }

    /// Nạp độ dài (theo bytes) của một slice/buffer vào thanh ghi đích `target`
    fn emit_load_slice_len(
        &mut self,
        func_name: &str,
        slice_reg: &str,
        slots: &HashMap<String, i32>,
        target: X86Reg,
    ) {
        let clean = IvlLowerer::clean_name(slice_reg);
        let len_name = format!("{}_len", clean);
        let key = Self::buf_key(func_name, slice_reg);
        if let Some(&slot) = slots.get(&len_name) {
            self.emit_load_stack(target, slot);
        } else if let Some(&cap) = self
            .slice_capacities
            .get(&key)
            .or_else(|| self.slice_capacities.get(slice_reg))
        {
            self.emit_mov_reg_imm64(target, cap as i64);
        } else {
            self.emit_mov_reg_imm64(target, 0);
        }
    }

    /// Cấp phát trước tất cả các buffer tĩnh để địa chỉ data_section cố định (tránh realloc khi chạy JIT)
    pub fn preallocate_buffers(&mut self, program: &Program) {
        for func in &program.functions {
            for si in &func.instructions {
                if let Instruction::Alloc { dest, elem_ty, len } = &si.inst {
                    self.ensure_buffer_allocated(&func.name, dest, elem_ty, *len);
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
    pub fn compile_program(
        &mut self,
        program: &Program,
        base_data_vaddr: u64,
    ) -> Result<usize, String> {
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
            self.code[*call_site..*call_site + 4].copy_from_slice(&(rel32 as i32).to_le_bytes());
        }

        Ok(main_offset)
    }

    /// Biên dịch một hàm Light sang mã máy x86_64 dùng Stack Frame
    pub fn compile_function(
        &mut self,
        func: &Function,
        program: &Program,
        base_data_vaddr: u64,
    ) -> Result<(), String> {
        let mut slots: HashMap<String, i32> = HashMap::new();
        let mut next_slot: i32 = 8;

        let mut alloc_slot = |name: &str| {
            let clean = IvlLowerer::clean_name(name).to_string();
            slots.entry(clean).or_insert_with(|| {
                let s = next_slot;
                next_slot += 8;
                s
            });
        };

        // 1. Collect all parameters
        for p in &func.params {
            let clean = IvlLowerer::clean_name(&p.name);
            alloc_slot(clean);
            if matches!(p.ty, Type::Slice(_) | Type::Array(_, _)) {
                alloc_slot(&format!("{}_len", clean));
            }
        }

        // 2. Collect all local registers & variables defined in instructions using shared FunctionBufferContext
        let buf_ctx = FunctionBufferContext::analyze(func, Some(program));
        for si in &func.instructions {
            match &si.inst {
                Instruction::AssignConst { dest, .. }
                | Instruction::SliceLen { dest, .. }
                | Instruction::Load8 { dest, .. }
                | Instruction::Load64 { dest, .. }
                | Instruction::Binary { dest, .. }
                | Instruction::Not { dest, .. }
                | Instruction::Mov { dest, .. }
                | Instruction::SlicePtr { dest, .. } => {
                    let clean = IvlLowerer::clean_name(dest);
                    alloc_slot(clean);
                    if buf_ctx.is_known_buffer(dest) {
                        alloc_slot(&format!("{}_len", clean));
                    }
                }
                Instruction::Alloc { dest, elem_ty, len } => {
                    let clean = IvlLowerer::clean_name(dest);
                    alloc_slot(clean);
                    alloc_slot(&format!("{}_len", clean));
                    self.ensure_buffer_allocated(&func.name, dest, elem_ty, *len);
                }
                Instruction::Call { dest: Some(d), .. }
                | Instruction::Syscall { dest: Some(d), .. } => {
                    alloc_slot(d);
                }
                Instruction::Syscall { dest: None, .. } => {
                    alloc_slot("rax");
                }
                _ => {}
            }
        }

        // Frame size aligned to 16 bytes
        let frame_size = ((next_slot + 15) / 16) * 16;

        // --- PROLOGUE ---
        // push rbp (0x55); mov rbp, rsp (48 89 e5); sub rsp, frame_size (48 81 ec disp32)
        self.code
            .extend_from_slice(&[0x55, 0x48, 0x89, 0xe5, 0x48, 0x81, 0xec]);
        self.code.extend_from_slice(&frame_size.to_le_bytes());

        // System V AMD64 ABI registers: Rdi, Rsi, Rdx, Rcx, R8, R9
        let abi_regs = [
            X86Reg::Rdi,
            X86Reg::Rsi,
            X86Reg::Rdx,
            X86Reg::Rcx,
            X86Reg::R8,
            X86Reg::R9,
        ];

        // Save incoming parameters
        if func.name == "main" {
            // Linux raw ELF entry point stack layout:
            // [rbp + 8]: argc, [rbp + 16]: argv[0], [rbp + 24]: argv[1], [rbp + 32]: argv[2]
            for (idx, p) in func.params.iter().enumerate() {
                let clean = IvlLowerer::clean_name(&p.name);
                if let Some(&slot) = slots.get(clean) {
                    match idx {
                        0 => self.code.extend_from_slice(&[0x48, 0x8b, 0x45, 0x08]),
                        1 if clean.contains("argv0") || clean == "argv_0" => {
                            self.code.extend_from_slice(&[0x48, 0x8b, 0x45, 0x10])
                        }
                        1 => self.code.extend_from_slice(&[0x48, 0x8d, 0x45, 0x10]),
                        2 => self.code.extend_from_slice(&[0x48, 0x8b, 0x45, 0x18]),
                        3 => self.code.extend_from_slice(&[0x48, 0x8b, 0x45, 0x20]),
                        _ => continue,
                    }
                    self.emit_store_stack(X86Reg::Rax, slot);
                }
            }
        } else {
            let mut reg_idx = 0;
            for p in &func.params {
                let clean = IvlLowerer::clean_name(&p.name);
                let mut param_slots = vec![slots.get(clean).copied()];
                if matches!(p.ty, Type::Slice(_) | Type::Array(_, _)) {
                    param_slots.push(slots.get(&format!("{}_len", clean)).copied());
                }
                for slot_opt in param_slots.into_iter().flatten() {
                    if reg_idx >= abi_regs.len() {
                        return Err(format!(
                            "Function '{}' exceeds maximum 6 ABI register slots for incoming parameters (note: slice<T> consumes 2 slots)",
                            func.name
                        ));
                    }
                    self.emit_store_stack(abi_regs[reg_idx], slot_opt);
                    reg_idx += 1;
                }
            }
        }

        // --- HELPER CLOSURES FOR OPERAND ACCESS ---
        let load_op_into_reg =
            |emitter: &mut MachineCodeEmitter, op: &Operand, target: X86Reg| match op {
                Operand::Const(Value::I64(n)) => emitter.emit_mov_reg_imm64(target, *n),
                Operand::Const(Value::U64(n)) => emitter.emit_mov_reg_imm64(target, *n as i64),
                Operand::Const(Value::Bool(b)) => emitter.emit_mov_reg_imm64(target, i64::from(*b)),
                Operand::Const(Value::Ptr(p)) => emitter.emit_mov_reg_imm64(target, *p as i64),
                Operand::Reg(r) => {
                    if r.starts_with("len(") && r.ends_with(')') {
                        let inner = r[4..r.len() - 1].trim();
                        emitter.emit_load_slice_len(&func.name, inner, &slots, target);
                    } else {
                        let key = Self::buf_key(&func.name, r);
                        if let Some(&buf_off) = emitter
                            .buffer_offsets
                            .get(&key)
                            .or_else(|| emitter.buffer_offsets.get(r))
                        {
                            let vaddr = base_data_vaddr + (buf_off as u64);
                            emitter.emit_mov_reg_imm64(target, vaddr as i64);
                        } else {
                            let clean = IvlLowerer::clean_name(r);
                            if let Some(&slot) = slots.get(clean) {
                                emitter.emit_load_stack(target, slot);
                            } else {
                                let hw_reg = match clean {
                                    "rax" => Some(X86Reg::Rax),
                                    "rcx" => Some(X86Reg::Rcx),
                                    "rdx" => Some(X86Reg::Rdx),
                                    "rbx" => Some(X86Reg::Rbx),
                                    "rsi" => Some(X86Reg::Rsi),
                                    "rdi" => Some(X86Reg::Rdi),
                                    "r8" => Some(X86Reg::R8),
                                    "r9" => Some(X86Reg::R9),
                                    "r10" => Some(X86Reg::R10),
                                    "r11" => Some(X86Reg::R11),
                                    _ => None,
                                };
                                if let Some(hw) = hw_reg {
                                    if hw != target {
                                        emitter.emit_mov_reg_reg(target, hw);
                                    }
                                } else {
                                    emitter.emit_mov_reg_imm64(target, 0);
                                }
                            }
                        }
                    }
                }
            };

        // --- EMIT INSTRUCTIONS ---
        let mut label_offsets: HashMap<String, usize> = HashMap::new();
        let mut jump_fixups: Vec<(usize, String)> = Vec::new(); // (patch_pos, target)
        let mut loop_stack: Vec<(String, String)> = Vec::new(); // (start_label, end_label)

        for si in &func.instructions {
            match &si.inst {
                Instruction::Require(_)
                | Instruction::Ensure(_)
                | Instruction::Invariant(_)
                | Instruction::Decreases(_)
                | Instruction::Assert(_) => {}

                Instruction::AssignConst { dest, val, .. } => {
                    let clean = IvlLowerer::clean_name(dest);
                    load_op_into_reg(self, &Operand::Const(val.clone()), X86Reg::Rax);
                    self.emit_store_stack(X86Reg::Rax, slots[clean]);
                }

                Instruction::Alloc { dest, elem_ty, len } => {
                    let key = Self::buf_key(&func.name, dest);
                    let offset = self
                        .buffer_offsets
                        .get(&key)
                        .or_else(|| self.buffer_offsets.get(dest))
                        .copied()
                        .unwrap_or(0);
                    let clean = IvlLowerer::clean_name(dest);
                    let vaddr = base_data_vaddr + (offset as u64);
                    self.emit_mov_reg_imm64(X86Reg::Rax, vaddr as i64);
                    self.emit_store_stack(X86Reg::Rax, slots[clean]);

                    let len_name = format!("{}_len", clean);
                    if let Some(&slot_len) = slots.get(&len_name) {
                        let byte_len = len.saturating_mul(elem_ty.byte_size());
                        self.emit_mov_reg_imm64(X86Reg::Rax, byte_len as i64);
                        self.emit_store_stack(X86Reg::Rax, slot_len);
                    }
                }

                Instruction::SlicePtr { dest, slice: src } | Instruction::Mov { dest, src } => {
                    let d_clean = IvlLowerer::clean_name(dest);
                    load_op_into_reg(self, &Operand::Reg(src.clone()), X86Reg::Rax);
                    self.emit_store_stack(X86Reg::Rax, slots[d_clean]);

                    // Copy độ dài slice {src}_len -> {dest}_len nếu có
                    let d_len_name = format!("{}_len", d_clean);
                    if let Some(&d_len_slot) = slots.get(&d_len_name) {
                        self.emit_load_slice_len(&func.name, src, &slots, X86Reg::Rax);
                        self.emit_store_stack(X86Reg::Rax, d_len_slot);
                    }
                }

                Instruction::SliceLen { dest, slice } => {
                    let clean = IvlLowerer::clean_name(dest);
                    self.emit_load_slice_len(&func.name, slice, &slots, X86Reg::Rax);
                    self.emit_store_stack(X86Reg::Rax, slots[clean]);
                }

                Instruction::StoreStr {
                    buf,
                    offset,
                    content,
                } => {
                    let key = Self::buf_key(&func.name, buf);
                    let buf_off = self
                        .buffer_offsets
                        .get(&key)
                        .or_else(|| self.buffer_offsets.get(buf))
                        .copied()
                        .unwrap_or(0);
                    let bytes = content.as_bytes();

                    // Nạp chuỗi hằng vào literal pool trong data_section để copy lúc runtime
                    let lit_off = self.data_section.len();
                    self.data_section.extend_from_slice(bytes);
                    let lit_vaddr = base_data_vaddr + (lit_off as u64);

                    // Destination pointer in Rdi:
                    let clean = IvlLowerer::clean_name(buf);
                    if let Some(&slot) = slots.get(clean) {
                        self.emit_load_stack(X86Reg::Rdi, slot);
                    } else {
                        let buf_vaddr = base_data_vaddr + (buf_off as u64);
                        self.emit_mov_reg_imm64(X86Reg::Rdi, buf_vaddr as i64);
                    }
                    if *offset > 0 {
                        // add rdi, offset (48 81 c7 disp32)
                        self.code.extend_from_slice(&[0x48, 0x81, 0xc7]);
                        self.code.extend_from_slice(&(*offset as i32).to_le_bytes());
                    }

                    // Source pointer in Rsi, byte count in Rcx, then `cld; rep movsb`
                    self.emit_mov_reg_imm64(X86Reg::Rsi, lit_vaddr as i64);
                    self.emit_mov_reg_imm64(X86Reg::Rcx, bytes.len() as i64);
                    self.code.extend_from_slice(&[0xfc, 0xf3, 0xa4]);
                }

                Instruction::Load8 { dest, buf, offset }
                | Instruction::Load64 { dest, buf, offset } => {
                    let is_64 = matches!(si.inst, Instruction::Load64 { .. });
                    load_op_into_reg(self, &Operand::Reg(buf.clone()), X86Reg::Rax);
                    load_op_into_reg(self, offset, X86Reg::Rcx);
                    if is_64 {
                        self.emit_load64_indexed();
                    } else {
                        self.emit_load8_indexed();
                    }
                    let clean = IvlLowerer::clean_name(dest);
                    self.emit_store_stack(X86Reg::Rax, slots[clean]);
                }

                Instruction::Store8 { buf, offset, val }
                | Instruction::Store64 { buf, offset, val } => {
                    let is_64 = matches!(si.inst, Instruction::Store64 { .. });
                    load_op_into_reg(self, &Operand::Reg(buf.clone()), X86Reg::Rax);
                    load_op_into_reg(self, offset, X86Reg::Rcx);
                    load_op_into_reg(self, val, X86Reg::Rdx);
                    if is_64 {
                        self.emit_store64_indexed();
                    } else {
                        self.emit_store8_indexed();
                    }
                }

                Instruction::Binary {
                    op,
                    ty,
                    dest,
                    src1,
                    src2,
                } => {
                    load_op_into_reg(self, src1, X86Reg::Rax);
                    load_op_into_reg(self, src2, X86Reg::Rcx);
                    let is_unsigned = buf_ctx.is_binary_unsigned(op, ty, src1, src2);

                    match op {
                        BinOp::Add => self.code.extend_from_slice(&[0x48, 0x01, 0xc8]),
                        BinOp::Sub => self.code.extend_from_slice(&[0x48, 0x29, 0xc8]),
                        BinOp::Mul => self.code.extend_from_slice(&[0x48, 0x0f, 0xaf, 0xc1]),
                        BinOp::Div | BinOp::Mod => {
                            if is_unsigned {
                                // xor rdx, rdx; div rcx
                                self.code
                                    .extend_from_slice(&[0x48, 0x31, 0xd2, 0x48, 0xf7, 0xf1]);
                            } else {
                                // cqo; idiv rcx
                                self.code.extend_from_slice(&[0x48, 0x99, 0x48, 0xf7, 0xf9]);
                            }
                            if matches!(op, BinOp::Mod) {
                                // mov rax, rdx
                                self.code.extend_from_slice(&[0x48, 0x89, 0xd0]);
                            }
                        }
                        BinOp::And | BinOp::BitAnd => {
                            self.code.extend_from_slice(&[0x48, 0x21, 0xc8])
                        }
                        BinOp::Or | BinOp::BitOr => {
                            self.code.extend_from_slice(&[0x48, 0x09, 0xc8])
                        }
                        BinOp::Xor => self.code.extend_from_slice(&[0x48, 0x31, 0xc8]),
                        BinOp::Shl => self.code.extend_from_slice(&[0x48, 0xd3, 0xe0]),
                        BinOp::Shr => self.code.extend_from_slice(&[0x48, 0xd3, 0xe8]),
                        BinOp::Sar => self.code.extend_from_slice(&[0x48, 0xd3, 0xf8]),
                        BinOp::Eq
                        | BinOp::Neq
                        | BinOp::Lt
                        | BinOp::Lte
                        | BinOp::Gt
                        | BinOp::Gte => {
                            let setcc = match (op, is_unsigned) {
                                (BinOp::Eq, _) => 0x94,
                                (BinOp::Neq, _) => 0x95,
                                (BinOp::Lt, true) => 0x92,   // setb
                                (BinOp::Lt, false) => 0x9c,  // setl
                                (BinOp::Lte, true) => 0x96,  // setbe
                                (BinOp::Lte, false) => 0x9e, // setle
                                (BinOp::Gt, true) => 0x97,   // seta
                                (BinOp::Gt, false) => 0x9f,  // setg
                                (BinOp::Gte, true) => 0x93,  // setae
                                (BinOp::Gte, false) => 0x9d, // setge
                                _ => unreachable!(),
                            };
                            // cmp rax, rcx; setCC al; movzx rax, al
                            self.code.extend_from_slice(&[
                                0x48, 0x39, 0xc8, 0x0f, setcc, 0xc0, 0x48, 0x0f, 0xb6, 0xc0,
                            ]);
                        }
                    }

                    let clean = IvlLowerer::clean_name(dest);
                    self.emit_store_stack(X86Reg::Rax, slots[clean]);
                }

                Instruction::Not { dest, ty, src } => {
                    load_op_into_reg(self, src, X86Reg::Rax);
                    if matches!(ty, Type::Bool) {
                        self.code.extend_from_slice(&[0x48, 0x83, 0xf0, 0x01]); // xor rax, 1
                    } else {
                        self.code.extend_from_slice(&[0x48, 0xf7, 0xd0]); // not rax
                    }
                    let clean = IvlLowerer::clean_name(dest);
                    self.emit_store_stack(X86Reg::Rax, slots[clean]);
                }

                Instruction::Label(name) => {
                    label_offsets.insert(name.clone(), self.code.len());
                }

                Instruction::Jump(target) => {
                    self.emit_uncond_jump(target.clone(), &mut jump_fixups);
                }

                Instruction::BrIf { cond, target } => {
                    let clean = IvlLowerer::clean_name(cond);
                    self.emit_cond_jump(slots[clean], target.clone(), &mut jump_fixups);
                }

                Instruction::Loop(name) => {
                    let start_lbl = format!("__loop_start_{}", name);
                    let end_lbl = format!("__loop_end_{}", name);
                    label_offsets.insert(start_lbl.clone(), self.code.len());
                    loop_stack.push((start_lbl, end_lbl));
                }

                Instruction::BreakIf(cond) | Instruction::ContinueIf(cond) => {
                    let is_break = matches!(si.inst, Instruction::BreakIf(_));
                    let op_name = if is_break { "BREAK_IF" } else { "CONTINUE_IF" };
                    if let Some((start_lbl, end_lbl)) = loop_stack.last() {
                        let target_lbl = if is_break { end_lbl } else { start_lbl }.clone();
                        let clean = IvlLowerer::clean_name(cond);
                        let &slot = slots.get(clean).ok_or_else(|| {
                            format!(
                                "Undefined variable '%{}' in {} in function '{}'",
                                clean, op_name, func.name
                            )
                        })?;
                        self.emit_cond_jump(slot, target_lbl, &mut jump_fixups);
                    } else {
                        return Err(format!(
                            "{} outside of LOOP in function '{}'",
                            op_name, func.name
                        ));
                    }
                }

                Instruction::EndLoop(name) => {
                    if let Some((start_lbl, end_lbl)) = loop_stack.pop() {
                        let expected_end_lbl = format!("__loop_end_{}", name);
                        if end_lbl != expected_end_lbl {
                            return Err(format!(
                                "Mismatched END_LOOP '{}' in function '{}' (expected '{}')",
                                name,
                                func.name,
                                end_lbl.trim_start_matches("__loop_end_")
                            ));
                        }
                        self.emit_uncond_jump(start_lbl, &mut jump_fixups);
                        label_offsets.insert(end_lbl, self.code.len());
                    } else {
                        return Err(format!(
                            "Unexpected END_LOOP '{}' without matching LOOP in function '{}'",
                            name, func.name
                        ));
                    }
                }

                Instruction::Call {
                    dest,
                    func_name,
                    args,
                } => {
                    // System V AMD64 ABI: Rdi, Rsi, Rdx, Rcx, R8, R9
                    let target_func = program.functions.iter().find(|f| f.name == *func_name);
                    let mut reg_idx = 0;

                    for (arg_idx, arg) in args.iter().enumerate() {
                        if reg_idx >= abi_regs.len() {
                            return Err(format!(
                                "Call to '{}' in function '{}' exceeds maximum 6 ABI register slots (note: slice<T> consumes 2 slots)",
                                func_name, func.name
                            ));
                        }
                        load_op_into_reg(self, arg, abi_regs[reg_idx]);
                        reg_idx += 1;

                        // Nếu callee parameter tại vị trí này là Type::Slice hoặc Type::Array, truyền tiếp len vào thanh ghi tiếp theo
                        if let Some(param) = target_func.and_then(|c| c.params.get(arg_idx)) {
                            if matches!(param.ty, Type::Slice(_) | Type::Array(_, _)) {
                                if reg_idx >= abi_regs.len() {
                                    return Err(format!(
                                        "Call to '{}' in function '{}' exceeds maximum 6 ABI register slots (note: slice<T> consumes 2 slots)",
                                        func_name, func.name
                                    ));
                                }
                                let len_reg = abi_regs[reg_idx];
                                match arg {
                                    Operand::Reg(r) => {
                                        self.emit_load_slice_len(&func.name, r, &slots, len_reg);
                                    }
                                    _ => {
                                        self.emit_mov_reg_imm64(len_reg, 0);
                                    }
                                }
                                reg_idx += 1;
                            }
                        }
                    }

                    // call rel32 (E8 disp32)
                    self.code.push(0xe8);
                    let call_site = self.code.len();
                    self.code.extend_from_slice(&[0, 0, 0, 0]);
                    self.call_fixups.push((call_site, func_name.clone()));

                    if let Some(d) = dest {
                        let clean = IvlLowerer::clean_name(d);
                        self.emit_store_stack(X86Reg::Rax, slots[clean]);
                    }
                }

                Instruction::Syscall {
                    dest,
                    rax,
                    rdi,
                    rsi,
                    rdx,
                    r10,
                    r8,
                    r9,
                } => {
                    if let Some(op) = r9 {
                        load_op_into_reg(self, op, X86Reg::R9);
                    }
                    if let Some(op) = r8 {
                        load_op_into_reg(self, op, X86Reg::R8);
                    }
                    if let Some(op) = r10 {
                        load_op_into_reg(self, op, X86Reg::R10);
                    }
                    load_op_into_reg(self, rdx, X86Reg::Rdx);
                    load_op_into_reg(self, rsi, X86Reg::Rsi);
                    load_op_into_reg(self, rdi, X86Reg::Rdi);
                    load_op_into_reg(self, rax, X86Reg::Rax);
                    self.emit_syscall();

                    let out_reg = dest.as_deref().unwrap_or("rax");
                    let clean = IvlLowerer::clean_name(out_reg);
                    if let Some(&slot) = slots.get(clean) {
                        self.emit_store_stack(X86Reg::Rax, slot);
                    }
                }

                Instruction::RetIf { cond, val } => {
                    let clean = IvlLowerer::clean_name(cond);
                    self.emit_load_stack(X86Reg::Rax, slots[clean]);
                    self.code.extend_from_slice(&[0x48, 0x85, 0xc0, 0x0f, 0x84]); // test rax, rax; jz rel32
                    let jz_fix = self.code.len();
                    self.code.extend_from_slice(&[0, 0, 0, 0]);

                    if let Some(op) = val {
                        load_op_into_reg(self, op, X86Reg::Rax);
                    }
                    self.emit_return_or_exit(func.name == "main");

                    let fallthrough = self.code.len();
                    let rel = (fallthrough as i32) - (jz_fix as i32 + 4);
                    self.code[jz_fix..jz_fix + 4].copy_from_slice(&rel.to_le_bytes());
                }

                Instruction::Ret(val) => {
                    if let Some(op) = val {
                        load_op_into_reg(self, op, X86Reg::Rax);
                    }
                    self.emit_return_or_exit(func.name == "main");
                }
            }
        }

        // Validate all LOOP blocks were closed
        if let Some((start_lbl, _)) = loop_stack.last() {
            let loop_name = start_lbl.trim_start_matches("__loop_start_");
            return Err(format!(
                "Unclosed LOOP '{}' in function '{}' (missing END_LOOP)",
                loop_name, func.name
            ));
        }

        // Epilogue default if not already returned via Instruction::Ret
        let ends_with_ret = func
            .instructions
            .last()
            .is_some_and(|s| matches!(s.inst, Instruction::Ret(_)));
        if !ends_with_ret {
            if func.name == "main" {
                self.emit_mov_reg_imm64(X86Reg::Rax, 0);
            }
            self.emit_return_or_exit(func.name == "main");
        }

        // Resolve jump_fixups within function
        for (patch_pos, target) in &jump_fixups {
            if let Some(&tgt_offset) = label_offsets.get(target) {
                let rel32 = (tgt_offset as i64) - ((*patch_pos + 4) as i64);
                self.code[*patch_pos..*patch_pos + 4]
                    .copy_from_slice(&(rel32 as i32).to_le_bytes());
            } else {
                return Err(format!(
                    "Undefined label '{}' in function '{}'",
                    target, func.name
                ));
            }
        }

        Ok(())
    }

    /// Đóng gói mã máy x86_64 thành file thực thi nhị phân Linux ELF64 hoàn chỉnh
    pub fn emit_elf64(&self, output_path: &str) -> std::io::Result<()> {
        let _guard = SPAWN_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _ = std::fs::remove_file(output_path);
        static ATOMIC_SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let seq = ATOMIC_SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let tmp_path = format!(
            "{}.tmp.{}.{}.{}",
            output_path,
            std::process::id(),
            seq,
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        );
        let mut file = File::create(&tmp_path)?;

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
        elf_header[52..54].copy_from_slice(&(elf_header_size as u16).to_le_bytes()); // e_ehsize = 64
        elf_header[54..56].copy_from_slice(&(prog_header_size as u16).to_le_bytes()); // e_phentsize = 56
        elf_header[56..58].copy_from_slice(&(num_phdrs as u16).to_le_bytes()); // e_phnum = 1

        // 2. Program Header: PT_LOAD RWX (56 bytes)
        let mut phdr = vec![0u8; 56];
        phdr[0..4].copy_from_slice(&1u32.to_le_bytes()); // PT_LOAD
        phdr[4..8].copy_from_slice(&7u32.to_le_bytes()); // PF_R | PF_W | PF_X
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
        file.sync_all()?;
        drop(file);

        std::fs::rename(&tmp_path, output_path)?;

        Ok(())
    }
}
