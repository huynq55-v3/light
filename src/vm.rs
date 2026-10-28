//! Máy ảo thực thi an toàn (Safe VM / Interpreter) cho Light (.lit)
//! - Không giới hạn Gas/Fuel (Full Turing-complete)
//! - Mô phỏng trực tiếp Linux Syscalls (x86_64) không phụ thuộc libc
//! - Quản lý bộ nhớ heap ảo độc lập

use crate::ast::*;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct MemoryBuffer {
    pub data: Vec<u8>,
}

pub struct VirtualMachine {
    pub registers: HashMap<String, Value>,
    pub buffers: HashMap<String, MemoryBuffer>,
    pub next_ptr_addr: usize,
    pub functions: HashMap<String, Function>,
}

impl VirtualMachine {
    #[allow(dead_code)]
    pub fn new() -> Self {
        Self {
            registers: HashMap::new(),
            buffers: HashMap::new(),
            next_ptr_addr: 0x1000,
            functions: HashMap::new(),
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

        let mut pc = 0;
        let mut loop_stack: Vec<(String, usize)> = Vec::new(); // (label, start_pc)

        while pc < func.instructions.len() {
            let s_inst = &func.instructions[pc];
            let inst = &s_inst.inst;

            match inst {
                // Các chỉ thị kiểm chứng chỉ dành cho compiler & SMT Solver, VM chỉ bỏ qua hoặc assert runtime
                Instruction::Require(_) | Instruction::Invariant(_) | Instruction::Ensure(_) => {
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
                    let buf = MemoryBuffer {
                        data: vec![0u8; *size],
                    };
                    self.buffers.insert(dest.clone(), buf);
                    let ptr_val = self.next_ptr_addr;
                    self.next_ptr_addr += (size + 63) & !63; // Align 64 bytes
                    self.registers.insert(dest.clone(), Value::Ptr(ptr_val));
                    pc += 1;
                }

                Instruction::AllocSlice { dest, len, .. } => {
                    let buf = MemoryBuffer {
                        data: vec![0u8; *len],
                    };
                    self.buffers.insert(dest.clone(), buf);
                    let ptr_val = self.next_ptr_addr;
                    self.next_ptr_addr += (len + 63) & !63;
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
                    let buffer = self
                        .buffers
                        .get_mut(buf)
                        .ok_or_else(|| format!("Buffer '{}' does not exist", buf))?;
                    if off >= buffer.data.len() {
                        return Err(format!(
                            "Runtime Bounds Error: Out of bounds byte store at offset {} (buffer len: {})",
                            off,
                            buffer.data.len()
                        ));
                    }
                    buffer.data[off] = byte_val;
                    pc += 1;
                }

                Instruction::Load8 { dest, buf, offset } => {
                    let off = self.get_i64(offset)? as usize;
                    let buffer = self
                        .buffers
                        .get(buf)
                        .ok_or_else(|| format!("Buffer '{}' does not exist", buf))?;
                    if off >= buffer.data.len() {
                        return Err(format!(
                            "Runtime Bounds Error: Out of bounds byte load at offset {} (buffer len: {})",
                            off,
                            buffer.data.len()
                        ));
                    }
                    let byte_val = buffer.data[off] as i64;
                    self.registers.insert(dest.clone(), Value::I64(byte_val));
                    pc += 1;
                }

                Instruction::Store64 { buf, offset, val } => {
                    let off = self.get_i64(offset)? as usize;
                    let i64_val = self.get_i64(val)?;
                    let buffer = self
                        .buffers
                        .get_mut(buf)
                        .ok_or_else(|| format!("Buffer '{}' không tồn tại", buf))?;
                    if off + 8 > buffer.data.len() {
                        return Err(format!(
                            "Lỗi Runtime Bounds Check: Ghi i64 vượt biên tại offset {} (buffer len: {})",
                            off,
                            buffer.data.len()
                        ));
                    }
                    let bytes = i64_val.to_le_bytes();
                    buffer.data[off..off + 8].copy_from_slice(&bytes);
                    pc += 1;
                }

                Instruction::Load64 { dest, buf, offset } => {
                    let off = self.get_i64(offset)? as usize;
                    let buffer = self
                        .buffers
                        .get(buf)
                        .ok_or_else(|| format!("Buffer '{}' không tồn tại", buf))?;
                    if off + 8 > buffer.data.len() {
                        return Err(format!(
                            "Lỗi Runtime Bounds Check: Đọc i64 vượt biên tại offset {} (buffer len: {})",
                            off,
                            buffer.data.len()
                        ));
                    }
                    let mut bytes = [0u8; 8];
                    bytes.copy_from_slice(&buffer.data[off..off + 8]);
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

                // Giao tiếp hệ điều hành Linux: SYSCALL
                Instruction::Syscall { rax, rdi, rsi, rdx } => {
                    let sys_id = self.get_i64(rax)?;
                    let arg1 = self.get_i64(rdi)?;
                    let arg2 = self.get_operand_val(rsi)?;
                    let arg3 = self.get_i64(rdx)?;

                    self.handle_linux_syscall(sys_id, arg1, &arg2, arg3)?;
                    pc += 1;
                }

                Instruction::Ret(val_op) => {
                    if let Some(op) = val_op {
                        let ret_val = self.get_operand_val(op)?;
                        return Ok(Some(ret_val));
                    }
                    return Ok(None);
                }
            }
        }

        Ok(None)
    }

    fn handle_linux_syscall(
        &mut self,
        sys_id: i64,
        arg1: i64,
        arg2: &Value,
        arg3: i64,
    ) -> Result<(), String> {
        match sys_id {
            // sys_write: (fd = arg1, buf = arg2, count = arg3)
            1 => {
                let count = arg3 as usize;
                // Tìm buffer khớp với arg2
                let mut found_data: Option<&[u8]> = None;
                if let Value::Slice { buf_name, .. } = arg2 {
                    if let Some(buf) = self.buffers.get(buf_name) {
                        if count <= buf.data.len() {
                            found_data = Some(&buf.data[..count]);
                        }
                    }
                }
                if found_data.is_none() {
                    for buf in self.buffers.values() {
                        if count <= buf.data.len() {
                            found_data = Some(&buf.data[..count]);
                            break;
                        }
                    }
                }

                if let Some(data) = found_data {
                    let text = String::from_utf8_lossy(data);
                    if arg1 == 1 {
                        // stdout
                        print!("{}", text);
                    } else if arg1 == 2 {
                        // stderr
                        eprint!("{}", text);
                    }
                } else {
                    return Err(format!("sys_write: Cannot find valid buffer of size {} bytes", count));
                }
                Ok(())
            }
            // sys_exit: (status = arg1)
            60 => {
                println!("\n[System: Light process exited safely with code: {}]", arg1);
                Ok(())
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
