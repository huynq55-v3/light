//! Máy ảo thực thi an toàn (Safe VM / Interpreter) cho Light (.lit)
//! - Không giới hạn Gas/Fuel (Full Turing-complete)
//! - Mô phỏng trực tiếp Linux Syscalls (x86_64) không phụ thuộc libc
//! - Quản lý bộ nhớ heap ảo độc lập

use crate::ast::*;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct MemoryBuffer {
    pub base_addr: usize,
    pub data: Vec<u8>,
}

pub struct VirtualMachine {
    pub registers: HashMap<String, Value>,
    pub buffers: HashMap<String, MemoryBuffer>,
    pub next_ptr_addr: usize,
    pub functions: HashMap<String, Function>,
    pub open_files: HashMap<i64, std::fs::File>,
    pub next_fd: i64,
}

impl VirtualMachine {
    #[allow(dead_code)]
    pub fn new() -> Self {
        Self {
            registers: HashMap::new(),
            buffers: HashMap::new(),
            next_ptr_addr: 0x1000,
            functions: HashMap::new(),
            open_files: HashMap::new(),
            next_fd: 3,
        }
    }

    pub fn with_program(program: &Program) -> Self {
        let mut functions = HashMap::new();
        for f in &program.functions {
            functions.insert(f.name.clone(), f.clone());
        }
        Self {
            registers: HashMap::new(),
            buffers: HashMap::new(),
            next_ptr_addr: 0x1000,
            functions,
            open_files: HashMap::new(),
            next_fd: 3,
        }
    }

    pub fn get_operand_val(&self, op: &Operand) -> Result<Value, String> {
        match op {
            Operand::Const(v) => Ok(v.clone()),
            Operand::Reg(name) => self
                .registers
                .get(name)
                .cloned()
                .ok_or_else(|| format!("Uninitialized register: {}", name)),
        }
    }

    pub fn get_i64(&self, op: &Operand) -> Result<i64, String> {
        match self.get_operand_val(op)? {
            Value::I64(v) => Ok(v),
            Value::U64(v) => Ok(v as i64),
            Value::Ptr(v) => Ok(v as i64),
            other => Err(format!("Expected i64, found {:?}", other)),
        }
    }

    #[allow(dead_code)]
    pub fn get_bool(&self, op: &Operand) -> Result<bool, String> {
        match self.get_operand_val(op)? {
            Value::Bool(b) => Ok(b),
            other => Err(format!("Expected bool, found {:?}", other)),
        }
    }

    pub fn val_to_i64(&self, val: &Value) -> Result<i64, String> {
        match val {
            Value::I64(v) => Ok(*v),
            Value::U64(v) => Ok(*v as i64),
            Value::Ptr(v) => Ok(*v as i64),
            Value::Bool(b) => Ok(if *b { 1 } else { 0 }),
            _ => Err(format!("Expected integer, found {:?}", val)),
        }
    }

    pub fn resolve_buffer_name_and_offset(&self, val: &Value) -> Result<(String, usize), String> {
        match val {
            Value::Slice { buf_name, .. } => Ok((buf_name.clone(), 0)),
            Value::Ptr(addr) => {
                for (name, buf) in &self.buffers {
                    if *addr >= buf.base_addr && *addr < buf.base_addr + buf.data.len() {
                        return Ok((name.clone(), *addr - buf.base_addr));
                    }
                }
                Err(format!("Pointer 0x{:x} does not point to any allocated buffer", addr))
            }
            Value::I64(addr) => {
                let uaddr = *addr as usize;
                for (name, buf) in &self.buffers {
                    if uaddr >= buf.base_addr && uaddr < buf.base_addr + buf.data.len() {
                        return Ok((name.clone(), uaddr - buf.base_addr));
                    }
                }
                Err(format!("Address {} does not match any allocated buffer", addr))
            }
            _ => Err(format!("Expected buffer pointer or slice, found {:?}", val)),
        }
    }

    pub fn run_function(&mut self, func: &Function, args: &[Value]) -> Result<Option<Value>, String> {
        if func.params.len() != args.len() {
            return Err(format!(
                "Function '{}' expects {} arguments, but received {}",
                func.name,
                func.params.len(),
                args.len()
            ));
        }

        // Nạp tham số vào thanh ghi cục bộ
        for (param, arg) in func.params.iter().zip(args.iter()) {
            self.registers.insert(param.name.clone(), arg.clone());
        }

        let mut labels = HashMap::new();
        for (i, si) in func.instructions.iter().enumerate() {
            if let Instruction::Label(name) = &si.inst {
                labels.insert(name.clone(), i);
            }
        }

        let mut pc = 0;
        let mut loop_stack: Vec<(String, usize)> = Vec::new(); // (label, start_pc)

        while pc < func.instructions.len() {
            let s_inst = &func.instructions[pc];
            let inst = &s_inst.inst;

            match inst {
                // Các chỉ thị kiểm chứng chỉ dành cho compiler & SMT Solver, VM chỉ bỏ qua hoặc assert runtime
                Instruction::Require(_) | Instruction::Invariant(_) | Instruction::Decreases(_) | Instruction::Ensure(_) => {
                    pc += 1;
                }
                Instruction::Assert(_expr) => {
                    // Trong VM ta có thể kiểm tra thêm nếu cần
                    pc += 1;
                }

                Instruction::AssignConst { dest, val, .. } => {
                    self.registers.insert(dest.clone(), val.clone());
                    pc += 1;
                }

                Instruction::Call { dest, func_name, args } => {
                    let callee = self
                        .functions
                        .get(func_name)
                        .cloned()
                        .ok_or_else(|| format!("Không tìm thấy hàm '{}' để gọi", func_name))?;

                    let mut evaluated_args = Vec::new();
                    for a in args {
                        evaluated_args.push(self.get_operand_val(a)?);
                    }

                    // Lưu trạng thái thanh ghi hiện tại (Stack frame)
                    let saved_regs = self.registers.clone();

                    let ret = self.run_function(&callee, &evaluated_args)?;

                    // Khôi phục thanh ghi
                    self.registers = saved_regs;

                    if let Some(d) = dest {
                        if let Some(val) = ret {
                            self.registers.insert(d.clone(), val);
                        }
                    }
                    pc += 1;
                }

                Instruction::Mov { dest, src } => {
                    let val = self
                        .registers
                        .get(src)
                        .cloned()
                        .ok_or_else(|| format!("Source register not set: {}", src))?;
                    self.registers.insert(dest.clone(), val);
                    pc += 1;
                }

                Instruction::Binary {
                    op,
                    ty: _,
                    dest,
                    src1,
                    src2,
                } => {
                    let v1 = self.get_operand_val(src1)?;
                    let v2 = self.get_operand_val(src2)?;
                    let res = self.eval_binop(op, &v1, &v2)?;
                    self.registers.insert(dest.clone(), res);
                    pc += 1;
                }

                Instruction::Alloc { dest, size } => {
                    let ptr_val = self.next_ptr_addr;
                    self.next_ptr_addr += (size + 63) & !63; // Align 64 bytes
                    let buf = MemoryBuffer {
                        base_addr: ptr_val,
                        data: vec![0u8; *size],
                    };
                    self.buffers.insert(dest.clone(), buf);
                    self.registers.insert(dest.clone(), Value::Ptr(ptr_val));
                    pc += 1;
                }

                Instruction::AllocSlice { dest, len, .. } => {
                    let ptr_val = self.next_ptr_addr;
                    self.next_ptr_addr += (len + 63) & !63;
                    let buf = MemoryBuffer {
                        base_addr: ptr_val,
                        data: vec![0u8; *len],
                    };
                    self.buffers.insert(dest.clone(), buf);
                    self.registers.insert(
                        dest.clone(),
                        Value::Slice {
                            ptr: ptr_val,
                            len: *len,
                            buf_name: dest.clone(),
                        },
                    );
                    pc += 1;
                }

                Instruction::SlicePtr { dest, slice } => {
                    let ptr_val = match self.registers.get(slice) {
                        Some(Value::Slice { ptr, .. }) => Value::Ptr(*ptr),
                        Some(Value::Ptr(p)) => Value::Ptr(*p),
                        _ => Value::Ptr(0),
                    };
                    self.registers.insert(dest.clone(), ptr_val);
                    pc += 1;
                }

                Instruction::SliceLen { dest, slice } => {
                    let len = match self.registers.get(slice) {
                        Some(Value::Slice { len, .. }) => *len as i64,
                        _ => self.buffers.get(slice).map(|b| b.data.len() as i64).unwrap_or(0),
                    };
                    self.registers.insert(dest.clone(), Value::I64(len));
                    pc += 1;
                }

                Instruction::Store8 { buf, offset, val } => {
                    let off = self.get_i64(offset)? as usize;
                    let byte_val = self.get_i64(val)? as u8;

                    let (buf_name, base_off) = if self.buffers.contains_key(buf) {
                        (buf.clone(), 0)
                    } else if let Some(reg_val) = self.registers.get(buf) {
                        self.resolve_buffer_name_and_offset(reg_val)?
                    } else {
                        return Err(format!("Buffer or pointer '{}' does not exist", buf));
                    };

                    let total_off = base_off + off;
                    let buffer = self
                        .buffers
                        .get_mut(&buf_name)
                        .ok_or_else(|| format!("Buffer '{}' does not exist", buf_name))?;
                    if total_off >= buffer.data.len() {
                        return Err(format!(
                            "Runtime Bounds Error: Out of bounds byte store at offset {} (buffer len: {})",
                            total_off,
                            buffer.data.len()
                        ));
                    }
                    buffer.data[total_off] = byte_val;
                    pc += 1;
                }

                Instruction::Load8 { dest, buf, offset } => {
                    let off = self.get_i64(offset)? as usize;

                    let (buf_name, base_off) = if self.buffers.contains_key(buf) {
                        (buf.clone(), 0)
                    } else if let Some(reg_val) = self.registers.get(buf) {
                        self.resolve_buffer_name_and_offset(reg_val)?
                    } else {
                        return Err(format!("Buffer or pointer '{}' does not exist", buf));
                    };

                    let total_off = base_off + off;
                    let buffer = self
                        .buffers
                        .get(&buf_name)
                        .ok_or_else(|| format!("Buffer '{}' does not exist", buf_name))?;
                    if total_off >= buffer.data.len() {
                        return Err(format!(
                            "Runtime Bounds Error: Out of bounds byte load at offset {} (buffer len: {})",
                            total_off,
                            buffer.data.len()
                        ));
                    }
                    let byte_val = buffer.data[total_off] as i64;
                    self.registers.insert(dest.clone(), Value::I64(byte_val));
                    pc += 1;
                }

                Instruction::Store64 { buf, offset, val } => {
                    let off = self.get_i64(offset)? as usize;
                    let i64_val = self.get_i64(val)?;

                    let (buf_name, base_off) = if self.buffers.contains_key(buf) {
                        (buf.clone(), 0)
                    } else if let Some(reg_val) = self.registers.get(buf) {
                        self.resolve_buffer_name_and_offset(reg_val)?
                    } else {
                        return Err(format!("Buffer or pointer '{}' does not exist", buf));
                    };

                    let total_off = base_off + off;
                    let buffer = self
                        .buffers
                        .get_mut(&buf_name)
                        .ok_or_else(|| format!("Buffer '{}' does not exist", buf_name))?;
                    if total_off + 8 > buffer.data.len() {
                        return Err(format!(
                            "Runtime Bounds Check Error: i64 store exceeds buffer at offset {} (buffer len: {})",
                            total_off,
                            buffer.data.len()
                        ));
                    }
                    let bytes = i64_val.to_le_bytes();
                    buffer.data[total_off..total_off + 8].copy_from_slice(&bytes);
                    pc += 1;
                }

                Instruction::Load64 { dest, buf, offset } => {
                    let off = self.get_i64(offset)? as usize;

                    let (buf_name, base_off) = if self.buffers.contains_key(buf) {
                        (buf.clone(), 0)
                    } else if let Some(reg_val) = self.registers.get(buf) {
                        self.resolve_buffer_name_and_offset(reg_val)?
                    } else {
                        return Err(format!("Buffer or pointer '{}' does not exist", buf));
                    };

                    let total_off = base_off + off;
                    let buffer = self
                        .buffers
                        .get(&buf_name)
                        .ok_or_else(|| format!("Buffer '{}' does not exist", buf_name))?;
                    if total_off + 8 > buffer.data.len() {
                        return Err(format!(
                            "Runtime Bounds Check Error: i64 load exceeds buffer at offset {} (buffer len: {})",
                            total_off,
                            buffer.data.len()
                        ));
                    }
                    let mut bytes = [0u8; 8];
                    bytes.copy_from_slice(&buffer.data[total_off..total_off + 8]);
                    let i64_val = i64::from_le_bytes(bytes);
                    self.registers.insert(dest.clone(), Value::I64(i64_val));
                    pc += 1;
                }

                Instruction::StoreStr {
                    buf,
                    offset,
                    content,
                } => {
                    let actual_name = match self.registers.get(buf) {
                        Some(Value::Slice { buf_name, .. }) => buf_name.clone(),
                        _ => buf.clone(),
                    };
                    let buffer = self
                        .buffers
                        .get_mut(&actual_name)
                        .ok_or_else(|| format!("Buffer '{}' does not exist", buf))?;
                    let bytes = content.as_bytes();
                    if *offset + bytes.len() > buffer.data.len() {
                        return Err(format!(
                            "String store error: String length {} bytes exceeds buffer '{}' capacity at offset {}",
                            bytes.len(),
                            buf,
                            offset
                        ));
                    }
                    buffer.data[*offset..*offset + bytes.len()].copy_from_slice(bytes);
                    pc += 1;
                }

                // Điều khiển luồng vòng lặp
                Instruction::Loop(label) => {
                    loop_stack.push((label.clone(), pc));
                    pc += 1;
                }

                Instruction::EndLoop(label) => {
                    if let Some((top_label, start_pc)) = loop_stack.last() {
                        if top_label == label {
                            // Nhảy lặp lại đầu vòng lặp (Unbounded loop - Turing Complete)
                            pc = *start_pc + 1;
                            continue;
                        }
                    }
                    return Err(format!("Lỗi nhãn END_LOOP '{}' không khớp", label));
                }

                Instruction::BreakIf(cond_reg) => {
                    let cond_val = self
                        .registers
                        .get(cond_reg)
                        .ok_or_else(|| format!("Thanh ghi điều kiện chưa gán: {}", cond_reg))?;
                    let should_break = match cond_val {
                        Value::Bool(b) => *b,
                        Value::I64(n) => *n != 0,
                        _ => false,
                    };
                    if should_break {
                        // Tìm vị trí END_LOOP tương ứng
                        let target_label = loop_stack.pop().map(|(l, _)| l).ok_or_else(|| {
                            "BREAK_IF được gọi bên ngoài bất kỳ vòng lặp nào".to_string()
                        })?;
                        let mut depth = 1;
                        let mut search_pc = pc + 1;
                        while search_pc < func.instructions.len() {
                            if let Instruction::Loop(_) = &func.instructions[search_pc].inst {
                                depth += 1;
                            } else if let Instruction::EndLoop(l) = &func.instructions[search_pc].inst {
                                depth -= 1;
                                if depth == 0 && l == &target_label {
                                    pc = search_pc + 1;
                                    break;
                                }
                            }
                            search_pc += 1;
                        }
                        continue;
                    }
                    pc += 1;
                }

                Instruction::ContinueIf(cond_reg) => {
                    let cond_val = self
                        .registers
                        .get(cond_reg)
                        .ok_or_else(|| format!("Thanh ghi điều kiện chưa gán: {}", cond_reg))?;
                    let should_continue = match cond_val {
                        Value::Bool(b) => *b,
                        Value::I64(n) => *n != 0,
                        _ => false,
                    };
                    if should_continue {
                        if let Some((_, start_pc)) = loop_stack.last() {
                            pc = *start_pc + 1;
                            continue;
                        }
                    }
                    pc += 1;
                }

                Instruction::Label(_) => {
                    pc += 1;
                }

                Instruction::Jump(target) => {
                    if let Some(&target_pc) = labels.get(target) {
                        pc = target_pc + 1;
                    } else {
                        return Err(format!("Undefined label: {}", target));
                    }
                }

                Instruction::BrIf { cond, target } => {
                    let should_branch = match self.registers.get(cond) {
                        Some(Value::Bool(b)) => *b,
                        Some(Value::I64(n)) => *n != 0,
                        Some(Value::U64(n)) => *n != 0,
                        _ => false,
                    };
                    if should_branch {
                        if let Some(&target_pc) = labels.get(target) {
                            pc = target_pc + 1;
                        } else {
                            return Err(format!("Undefined label: {}", target));
                        }
                    } else {
                        pc += 1;
                    }
                }

                // Giao tiếp hệ điều hành Linux: SYSCALL
                Instruction::Syscall { dest, rax, rdi, rsi, rdx } => {
                    let sys_id = self.get_i64(rax)?;
                    let arg1 = self.get_operand_val(rdi)?;
                    let arg2 = self.get_operand_val(rsi)?;
                    let arg3 = self.get_operand_val(rdx)?;

                    let ret_val = self.handle_linux_syscall(sys_id, &arg1, &arg2, &arg3)?;
                    if let Some(d) = dest {
                        self.registers.insert(d.clone(), Value::I64(ret_val));
                    }
                    pc += 1;
                }

                Instruction::Ret(val_op) => {
                    if let Some(op) = val_op {
                        let ret_val = self.get_operand_val(op)?;
                        return Ok(Some(ret_val));
                    }
                    return Ok(None);
                }

                Instruction::RetIf { cond, val } => {
                    let should_ret = match self.registers.get(cond) {
                        Some(Value::Bool(b)) => *b,
                        Some(Value::I64(n)) => *n != 0,
                        Some(Value::U64(n)) => *n != 0,
                        _ => false,
                    };
                    if should_ret {
                        if let Some(op) = val {
                            let ret_val = self.get_operand_val(op)?;
                            return Ok(Some(ret_val));
                        }
                        return Ok(None);
                    }
                    pc += 1;
                }
            }
        }

        Ok(None)
    }

    fn handle_linux_syscall(
        &mut self,
        sys_id: i64,
        arg1: &Value,
        arg2: &Value,
        arg3: &Value,
    ) -> Result<i64, String> {
        match sys_id {
            // sys_read: (fd = arg1, buf = arg2, count = arg3)
            0 => {
                let fd = self.val_to_i64(arg1)?;
                let count = self.val_to_i64(arg3)? as usize;
                let (buf_name, base_off) = self.resolve_buffer_name_and_offset(arg2)?;
                let buf = self.buffers.get_mut(&buf_name).ok_or_else(|| format!("Buffer '{}' not found", buf_name))?;
                if base_off + count > buf.data.len() {
                    return Err(format!("sys_read: buffer overflow (need {}, have {})", base_off + count, buf.data.len()));
                }

                if fd == 0 {
                    use std::io::Read;
                    let bytes_read = std::io::stdin()
                        .take(count as u64)
                        .read(&mut buf.data[base_off..base_off + count])
                        .map_err(|e| e.to_string())?;
                    Ok(bytes_read as i64)
                } else if let Some(file) = self.open_files.get_mut(&fd) {
                    use std::io::Read;
                    let bytes_read = file
                        .read(&mut buf.data[base_off..base_off + count])
                        .map_err(|e| e.to_string())?;
                    Ok(bytes_read as i64)
                } else {
                    Ok(-1)
                }
            }

            // sys_write: (fd = arg1, buf = arg2, count = arg3)
            1 => {
                let fd = self.val_to_i64(arg1)?;
                let count = self.val_to_i64(arg3)? as usize;
                let (buf_name, base_off) = self.resolve_buffer_name_and_offset(arg2)?;
                let buf = self.buffers.get(&buf_name).ok_or_else(|| format!("Buffer '{}' not found", buf_name))?;
                if base_off + count > buf.data.len() {
                    return Err(format!("sys_write: buffer overflow (need {}, have {})", base_off + count, buf.data.len()));
                }
                let data = &buf.data[base_off..base_off + count];

                if fd == 1 {
                    let text = String::from_utf8_lossy(data);
                    print!("{}", text);
                    Ok(count as i64)
                } else if fd == 2 {
                    let text = String::from_utf8_lossy(data);
                    eprint!("{}", text);
                    Ok(count as i64)
                } else if let Some(file) = self.open_files.get_mut(&fd) {
                    use std::io::Write;
                    file.write_all(data).map_err(|e| e.to_string())?;
                    Ok(count as i64)
                } else {
                    Ok(-1)
                }
            }

            // sys_open: (filename = arg1, flags = arg2, mode = arg3)
            2 => {
                let flags = self.val_to_i64(arg2)?;
                let _mode = self.val_to_i64(arg3)?;

                let (buf_name, base_off) = self.resolve_buffer_name_and_offset(arg1)?;
                let buf = self.buffers.get(&buf_name).ok_or_else(|| format!("Buffer '{}' not found", buf_name))?;
                let slice_data = &buf.data[base_off..];
                // Read until null terminator or end
                let len = slice_data.iter().position(|&b| b == 0).unwrap_or(slice_data.len());
                let path_str = std::str::from_utf8(&slice_data[..len]).map_err(|e| e.to_string())?;

                let is_write = (flags & 1 != 0) || (flags & 2 != 0);
                let is_create = flags & 64 != 0;
                let is_trunc = flags & 512 != 0;
                let is_append = flags & 1024 != 0;

                let mut options = std::fs::OpenOptions::new();
                if is_write {
                    options.write(true);
                    if is_create { options.create(true); }
                    if is_trunc { options.truncate(true); }
                    if is_append { options.append(true); }
                } else {
                    options.read(true);
                }

                match options.open(path_str) {
                    Ok(f) => {
                        let fd = self.next_fd;
                        self.next_fd += 1;
                        self.open_files.insert(fd, f);
                        Ok(fd)
                    }
                    Err(_) => Ok(-1),
                }
            }

            // sys_close: (fd = arg1)
            3 => {
                let fd = self.val_to_i64(arg1)?;
                self.open_files.remove(&fd);
                Ok(0)
            }

            // sys_exit: (status = arg1)
            60 => {
                let code = self.val_to_i64(arg1)?;
                Ok(code)
            }

            _ => Err(format!("Linux Syscall ID {} is not supported in this runtime", sys_id)),
        }
    }

    fn eval_binop(&self, op: &BinOp, v1: &Value, v2: &Value) -> Result<Value, String> {
        match (v1, v2) {
            (Value::I64(a), Value::I64(b)) => match op {
                BinOp::Add => Ok(Value::I64(a.wrapping_add(*b))),
                BinOp::Sub => Ok(Value::I64(a.wrapping_sub(*b))),
                BinOp::Mul => Ok(Value::I64(a.wrapping_mul(*b))),
                BinOp::Div => {
                    if *b == 0 {
                        return Err("Runtime Error: Division by zero".into());
                    }
                    Ok(Value::I64(a / b))
                }
                BinOp::Mod => {
                    if *b == 0 {
                        return Err("Runtime Error: Remainder by zero".into());
                    }
                    Ok(Value::I64(a % b))
                }
                BinOp::Eq => Ok(Value::Bool(a == b)),
                BinOp::Neq => Ok(Value::Bool(a != b)),
                BinOp::Lt => Ok(Value::Bool(a < b)),
                BinOp::Lte => Ok(Value::Bool(a <= b)),
                BinOp::Gt => Ok(Value::Bool(a > b)),
                BinOp::Gte => Ok(Value::Bool(a >= b)),
                _ => Err(format!("Toán tử {:?} không áp dụng được cho kiểu i64", op)),
            },
            (Value::Bool(a), Value::Bool(b)) => match op {
                BinOp::Eq => Ok(Value::Bool(a == b)),
                BinOp::Neq => Ok(Value::Bool(a != b)),
                BinOp::And => Ok(Value::Bool(*a && *b)),
                BinOp::Or => Ok(Value::Bool(*a || *b)),
                _ => Err(format!("Toán tử {:?} không áp dụng được cho kiểu bool", op)),
            },
            _ => Err("Toán hạng khác kiểu dữ liệu chưa hỗ trợ phép toán trực tiếp".into()),
        }
    }
}
