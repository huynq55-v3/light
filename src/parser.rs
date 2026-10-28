//! Parser dòng phẳng (Flat SSA Parser) cho Light (.lit)
//! Thiết kế tối giản, tốc độ cao, hỗ trợ 6 kiểu dữ liệu và chỉ thị kiểm chứng Z3.

use crate::ast::*;
use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Debug, Clone)]
pub struct ParseError {
    pub line_no: usize,
    pub message: String,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Syntax error at line {}: {}", self.line_no, self.message)
    }
}

pub struct Parser;

impl Parser {
    /// Nạp và parse file gốc kèm tất cả các file được IMPORT đệ quy
    pub fn parse_file<P: AsRef<Path>>(file_path: P) -> Result<Program, ParseError> {
        let mut visited = HashSet::new();
        let mut all_functions = Vec::new();
        Self::parse_file_recursive(file_path.as_ref(), &mut visited, &mut all_functions)?;
        Ok(Program {
            functions: all_functions,
        })
    }

    fn parse_file_recursive(
        path: &Path,
        visited: &mut HashSet<PathBuf>,
        all_functions: &mut Vec<Function>,
    ) -> Result<(), ParseError> {
        let canonical = fs::canonicalize(path).map_err(|e| ParseError {
            line_no: 0,
            message: format!("Cannot find import file '{}': {}", path.display(), e),
        })?;

        // Deduplication & cycle prevention
        if visited.contains(&canonical) {
            return Ok(());
        }
        visited.insert(canonical.clone());

        let source = fs::read_to_string(&canonical).map_err(|e| ParseError {
            line_no: 0,
            message: format!("Cannot read file '{}': {}", canonical.display(), e),
        })?;

        let parent_dir = canonical.parent().unwrap_or_else(|| Path::new("."));

        let mut current_func: Option<Function> = None;

        for (idx, raw_line) in source.lines().enumerate() {
            let line_no = idx + 1;
            let line = raw_line.trim();

            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            let clean_line = Self::strip_inline_comment(line);
            let trimmed = clean_line.trim();
            if trimmed.is_empty() {
                continue;
            }

            let parts: Vec<&str> = trimmed.split_whitespace().collect();

            // Handle IMPORT "relative/path.lit"
            if parts[0] == "IMPORT" {
                if current_func.is_some() {
                    return Err(ParseError {
                        line_no,
                        message: "IMPORT directives must be placed at the file top-level outside functions".into(),
                    });
                }
                let first_quote = trimmed.find('"').ok_or_else(|| ParseError {
                    line_no,
                    message: "IMPORT syntax requires double quotes: IMPORT \"file.lit\"".into(),
                })?;
                let last_quote = trimmed.rfind('"').ok_or_else(|| ParseError {
                    line_no,
                    message: "Missing closing quote in IMPORT".into(),
                })?;
                let import_rel_path = &trimmed[first_quote + 1..last_quote];
                let resolved_path = parent_dir.join(import_rel_path);

                Self::parse_file_recursive(&resolved_path, visited, all_functions)?;
                continue;
            }

            if parts[0] == "FUNC" {
                if current_func.is_some() {
                    return Err(ParseError {
                        line_no,
                        message: "Nested function definitions are not allowed".into(),
                    });
                }
                let file_str = canonical.display().to_string();
                let func = Self::parse_func_signature(trimmed, &file_str, line_no)?;
                current_func = Some(func);
                continue;
            }

            if parts[0] == "END_FUNC" {
                if let Some(func) = current_func.take() {
                    if all_functions.iter().any(|f| f.name == func.name) {
                        return Err(ParseError {
                            line_no,
                            message: format!("Duplicate function definition: '{}'", func.name),
                        });
                    }
                    all_functions.push(func);
                } else {
                    return Err(ParseError {
                        line_no,
                        message: "Encountered END_FUNC without an active function block".into(),
                    });
                }
                continue;
            }

            let func = current_func.as_mut().ok_or_else(|| ParseError {
                line_no,
                message: format!("Instruction '{}' must be placed inside a FUNC ... END_FUNC block", parts[0]),
            })?;

            let inst = Self::parse_instruction(trimmed, line_no)?;
            func.instructions.push(SpannedInstruction {
                inst,
                loc: Loc {
                    file: canonical.display().to_string(),
                    line: line_no,
                    text: trimmed.to_string(),
                },
            });
        }

        if let Some(func) = current_func {
            return Err(ParseError {
                line_no: 0,
                message: format!("Function '{}' was not closed with END_FUNC", func.name),
            });
        }

        Ok(())
    }

    /// Parse từ chuỗi (không kèm import ngoài)
    #[allow(dead_code)]
    pub fn parse(source: &str) -> Result<Program, ParseError> {
        let mut functions = Vec::new();
        let mut current_func: Option<Function> = None;

        for (idx, raw_line) in source.lines().enumerate() {
            let line_no = idx + 1;
            let line = raw_line.trim();

            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            let clean_line = Self::strip_inline_comment(line);
            let trimmed = clean_line.trim();
            if trimmed.is_empty() {
                continue;
            }

            let parts: Vec<&str> = trimmed.split_whitespace().collect();

            if parts[0] == "FUNC" {
                if current_func.is_some() {
                    return Err(ParseError {
                        line_no,
                        message: "Nested function definitions are not allowed".into(),
                    });
                }
                let func = Self::parse_func_signature(trimmed, "<memory>", line_no)?;
                current_func = Some(func);
                continue;
            }

            if parts[0] == "END_FUNC" {
                if let Some(func) = current_func.take() {
                    functions.push(func);
                } else {
                    return Err(ParseError {
                        line_no,
                        message: "Encountered END_FUNC without an active function block".into(),
                    });
                }
                continue;
            }

            let func = current_func.as_mut().ok_or_else(|| ParseError {
                line_no,
                message: format!("Instruction '{}' must be placed inside a FUNC ... END_FUNC block", parts[0]),
            })?;

            let inst = Self::parse_instruction(trimmed, line_no)?;
            func.instructions.push(SpannedInstruction {
                inst,
                loc: Loc {
                    file: "<memory>".into(),
                    line: line_no,
                    text: trimmed.to_string(),
                },
            });
        }

        if let Some(func) = current_func {
            return Err(ParseError {
                line_no: 0,
                message: format!("Hàm '{}' chưa được đóng bằng END_FUNC", func.name),
            });
        }

        Ok(Program { functions })
    }

    fn strip_inline_comment(line: &str) -> String {
        let mut in_str = false;
        let mut res = String::new();
        for ch in line.chars() {
            if ch == '"' {
                in_str = !in_str;
            }
            if ch == '#' && !in_str {
                break;
            }
            res.push(ch);
        }
        res
    }

    pub fn parse_type(s: &str, line_no: usize) -> Result<Type, ParseError> {
        let s = s.trim();
        match s {
            "i64" => Ok(Type::I64),
            "u64" => Ok(Type::U64),
            "u8" => Ok(Type::U8),
            "f64" => Ok(Type::F64),
            "bool" => Ok(Type::Bool),
            "ptr" => Ok(Type::Ptr),
            _ => {
                // arr<T, N>
                if s.starts_with("arr<") && s.ends_with('>') {
                    let inner = &s[4..s.len() - 1];
                    let parts: Vec<&str> = inner.split(',').collect();
                    if parts.len() != 2 {
                        return Err(ParseError {
                            line_no,
                            message: format!("Malformed array type: '{}'. Expected: arr<type, size>", s),
                        });
                    }
                    let elem_ty = Self::parse_type(parts[0].trim(), line_no)?;
                    let size = parts[1].trim().parse::<usize>().map_err(|_| ParseError {
                        line_no,
                        message: format!("Array size must be a positive integer: {}", parts[1]),
                    })?;
                    return Ok(Type::Array(Box::new(elem_ty), size));
                }
                // slice<T>
                if s.starts_with("slice<") && s.ends_with('>') {
                    let inner = &s[6..s.len() - 1];
                    let elem_ty = Self::parse_type(inner.trim(), line_no)?;
                    return Ok(Type::Slice(Box::new(elem_ty)));
                }
                Err(ParseError {
                    line_no,
                    message: format!("Unsupported type: '{}'. Supported: i64, u64, u8, f64, bool, ptr, arr<T, N>, slice<T>", s),
                })
            }
        }
    }

    fn parse_func_signature(line: &str, file: &str, line_no: usize) -> Result<Function, ParseError> {
        let line = line.strip_prefix("FUNC").unwrap().trim();
        let paren_start = line.find('(').ok_or_else(|| ParseError {
            line_no,
            message: "Missing '(' in FUNC signature".into(),
        })?;
        let paren_end = line.find(')').ok_or_else(|| ParseError {
            line_no,
            message: "Missing ')' in FUNC signature".into(),
        })?;

        let name = line[..paren_start].trim().to_string();
        if name.is_empty() {
            return Err(ParseError {
                line_no,
                message: "Function name cannot be empty".into(),
            });
        }

        let params_str = line[paren_start + 1..paren_end].trim();
        let mut params = Vec::new();
        if !params_str.is_empty() {
            for param_item in params_str.split(',') {
                let p_parts: Vec<&str> = param_item.split(':').collect();
                if p_parts.len() != 2 {
                    return Err(ParseError {
                        line_no,
                        message: format!("Malformed parameter declaration '{}' (expected: name: type)", param_item),
                    });
                }
                let p_name = p_parts[0].trim().to_string();
                let p_ty = Self::parse_type(p_parts[1].trim(), line_no)?;
                params.push(Param {
                    name: p_name,
                    ty: p_ty,
                });
            }
        }

        let after_paren = line[paren_end + 1..].trim();
        let return_ty = if after_paren.starts_with("->") {
            let ret_str = after_paren.strip_prefix("->").unwrap().trim();
            Some(Self::parse_type(ret_str, line_no)?)
        } else {
            None
        };

        Ok(Function {
            name,
            file: file.to_string(),
            start_line: line_no,
            params,
            return_ty,
            instructions: Vec::new(),
        })
    }

    fn parse_operand(s: &str) -> Operand {
        if s.starts_with('%') {
            Operand::Reg(s.to_string())
        } else if s == "true" {
            Operand::Const(Value::Bool(true))
        } else if s == "false" {
            Operand::Const(Value::Bool(false))
        } else if let Ok(val) = s.parse::<i64>() {
            Operand::Const(Value::I64(val))
        } else if let Ok(val) = s.parse::<f64>() {
            Operand::Const(Value::F64(val))
        } else {
            Operand::Reg(s.to_string())
        }
    }

    fn parse_instruction(line: &str, line_no: usize) -> Result<Instruction, ParseError> {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.is_empty() {
            return Err(ParseError {
                line_no,
                message: "Dòng trống không hợp lệ".into(),
            });
        }

        // --- CÁC CHỈ THỊ KIỂM CHỨNG TOÁN HỌC (Z3) ---
        if parts[0] == "REQUIRE" {
            let expr_str = line.strip_prefix("REQUIRE").unwrap().trim();
            let expr = Self::parse_expr(expr_str, line_no)?;
            return Ok(Instruction::Require(expr));
        }
        if parts[0] == "ENSURE" {
            let expr_str = line.strip_prefix("ENSURE").unwrap().trim();
            let expr = Self::parse_expr(expr_str, line_no)?;
            return Ok(Instruction::Ensure(expr));
        }
        if parts[0] == "INVARIANT" {
            let expr_str = line.strip_prefix("INVARIANT").unwrap().trim();
            let expr = Self::parse_expr(expr_str, line_no)?;
            return Ok(Instruction::Invariant(expr));
        }
        if parts[0] == "ASSERT" {
            let expr_str = line.strip_prefix("ASSERT").unwrap().trim();
            let expr = Self::parse_expr(expr_str, line_no)?;
            return Ok(Instruction::Assert(expr));
        }

        if parts[0] == "CALL" {
            // CALL func_name arg1 arg2 ...
            if parts.len() < 2 {
                return Err(ParseError {
                    line_no,
                    message: "Cú pháp: CALL func_name arg1 arg2 ...".into(),
                });
            }
            let func_name = parts[1].to_string();
            let args: Vec<Operand> = parts[2..].iter().map(|s| Self::parse_operand(s)).collect();
            return Ok(Instruction::Call {
                dest: None,
                func_name,
                args,
            });
        }

        // --- ĐIỀU KHIỂN LUỒNG PHẲNG (FLAT SSA BRANCHING) ---
        if parts[0] == "LABEL" {
            if parts.len() < 2 {
                return Err(ParseError {
                    line_no,
                    message: "Syntax: LABEL <name>".into(),
                });
            }
            return Ok(Instruction::Label(parts[1].to_string()));
        }
        if parts[0] == "JUMP" {
            if parts.len() < 2 {
                return Err(ParseError {
                    line_no,
                    message: "Syntax: JUMP <label>".into(),
                });
            }
            return Ok(Instruction::Jump(parts[1].to_string()));
        }
        if parts[0] == "BR_IF" {
            if parts.len() < 3 {
                return Err(ParseError {
                    line_no,
                    message: "Syntax: BR_IF %cond <label>".into(),
                });
            }
            return Ok(Instruction::BrIf {
                cond: parts[1].to_string(),
                target: parts[2].to_string(),
            });
        }

        // --- ĐIỀU KHIỂN VÒNG LẶP ---
        if parts[0] == "LOOP" {
            let label = parts.get(1).unwrap_or(&"loop").to_string();
            return Ok(Instruction::Loop(label));
        }
        if parts[0] == "END_LOOP" {
            let label = parts.get(1).unwrap_or(&"loop").to_string();
            return Ok(Instruction::EndLoop(label));
        }
        if parts[0] == "BREAK_IF" {
            if parts.len() < 2 {
                return Err(ParseError {
                    line_no,
                    message: "Syntax: BREAK_IF %cond".into(),
                });
            }
            return Ok(Instruction::BreakIf(parts[1].to_string()));
        }
        if parts[0] == "CONTINUE_IF" {
            if parts.len() < 2 {
                return Err(ParseError {
                    line_no,
                    message: "Syntax: CONTINUE_IF %cond".into(),
                });
            }
            return Ok(Instruction::ContinueIf(parts[1].to_string()));
        }

        // --- MEMORY OPERATIONS ---
        if parts[0] == "ALLOC" {
            if parts.len() < 3 {
                return Err(ParseError {
                    line_no,
                    message: "Syntax: ALLOC %buf size".into(),
                });
            }
            let dest = parts[1].to_string();
            let size = parts[2].parse::<usize>().map_err(|_| ParseError {
                line_no,
                message: format!("Allocation size must be a positive integer: {}", parts[2]),
            })?;
            return Ok(Instruction::Alloc { dest, size });
        }
        if parts[0] == "STORE8" {
            if parts.len() < 4 {
                return Err(ParseError {
                    line_no,
                    message: "Syntax: STORE8 %buf offset val".into(),
                });
            }
            return Ok(Instruction::Store8 {
                buf: parts[1].to_string(),
                offset: Self::parse_operand(parts[2]),
                val: Self::parse_operand(parts[3]),
            });
        }
        if parts[0] == "STORE64" {
            if parts.len() < 4 {
                return Err(ParseError {
                    line_no,
                    message: "Syntax: STORE64 %buf offset val".into(),
                });
            }
            return Ok(Instruction::Store64 {
                buf: parts[1].to_string(),
                offset: Self::parse_operand(parts[2]),
                val: Self::parse_operand(parts[3]),
            });
        }
        if parts[0] == "STORE_STR" {
            let first_quote = line.find('"').ok_or_else(|| ParseError {
                line_no,
                message: "Missing double quote in STORE_STR".into(),
            })?;
            let last_quote = line.rfind('"').ok_or_else(|| ParseError {
                line_no,
                message: "Missing closing quote in STORE_STR".into(),
            })?;
            if first_quote >= last_quote {
                return Err(ParseError {
                    line_no,
                    message: "Invalid string literal in STORE_STR".into(),
                });
            }
            let raw_str = &line[first_quote + 1..last_quote];
            let unescaped = raw_str
                .replace("\\0", "\0")
                .replace("\\n", "\n")
                .replace("\\t", "\t")
                .replace("\\r", "\r")
                .replace("\\\"", "\"")
                .replace("\\\\", "\\");
            let prefix = line[..first_quote].trim();
            let p_parts: Vec<&str> = prefix.split_whitespace().collect();
            let offset = if p_parts.len() == 2 {
                0
            } else if p_parts.len() >= 3 {
                p_parts[2].parse::<usize>().map_err(|_| ParseError {
                    line_no,
                    message: "String offset must be an integer".into(),
                })?
            } else {
                return Err(ParseError {
                    line_no,
                    message: "Syntax: STORE_STR %buf [offset] \"string\"".into(),
                });
            };
            return Ok(Instruction::StoreStr {
                buf: p_parts[1].to_string(),
                offset,
                content: unescaped,
            });
        }

        // --- LINUX SYSCALL & RET ---
        if parts[0] == "SYSCALL" {
            if parts.len() < 5 {
                return Err(ParseError {
                    line_no,
                    message: "Syntax: SYSCALL rax rdi rsi rdx".into(),
                });
            }
            return Ok(Instruction::Syscall {
                dest: None,
                rax: Self::parse_operand(parts[1]),
                rdi: Self::parse_operand(parts[2]),
                rsi: Self::parse_operand(parts[3]),
                rdx: Self::parse_operand(parts[4]),
            });
        }

        if parts[0] == "RET" {
            let ret_val = parts.get(1).map(|s| Self::parse_operand(s));
            return Ok(Instruction::Ret(ret_val));
        }

        if parts[0] == "RET_IF" {
            if parts.len() < 2 {
                return Err(ParseError {
                    line_no,
                    message: "Syntax: RET_IF %cond [%val]".into(),
                });
            }
            let cond = parts[1].to_string();
            let ret_val = parts.get(2).map(|s| Self::parse_operand(s));
            return Ok(Instruction::RetIf {
                cond,
                val: ret_val,
            });
        }

        // --- GÁN %dest = ... ---
        if parts.len() >= 3 && parts[1] == "=" {
            let dest = parts[0].to_string();
            let op = parts[2];

            match op {
                "ALLOC" => {
                    // %dest = ALLOC slice<T> <len>
                    if parts.len() < 5 {
                        return Err(ParseError {
                            line_no,
                            message: "Syntax: %dest = ALLOC slice<T> <len>".into(),
                        });
                    }
                    let ty = Self::parse_type(parts[3], line_no)?;
                    let len = parts[4].parse::<usize>().map_err(|_| ParseError {
                        line_no,
                        message: format!("Slice length must be an integer: {}", parts[4]),
                    })?;
                    match ty {
                        Type::Slice(elem) => {
                            return Ok(Instruction::AllocSlice {
                                dest,
                                elem_ty: *elem,
                                len,
                            });
                        }
                        _ => {
                            return Err(ParseError {
                                line_no,
                                message: "ALLOC expects a slice<T> type".into(),
                            });
                        }
                    }
                }
                "SLICE_PTR" => {
                    if parts.len() < 4 {
                        return Err(ParseError {
                            line_no,
                            message: "Syntax: %ptr = SLICE_PTR %slice".into(),
                        });
                    }
                    return Ok(Instruction::SlicePtr {
                        dest,
                        slice: parts[3].to_string(),
                    });
                }
                "SLICE_LEN" => {
                    if parts.len() < 4 {
                        return Err(ParseError {
                            line_no,
                            message: "Syntax: %len = SLICE_LEN %slice".into(),
                        });
                    }
                    return Ok(Instruction::SliceLen {
                        dest,
                        slice: parts[3].to_string(),
                    });
                }
                "CALL" => {
                    if parts.len() < 4 {
                        return Err(ParseError {
                            line_no,
                            message: "Syntax: %dest = CALL func_name arg1 arg2 ...".into(),
                        });
                    }
                    let func_name = parts[3].to_string();
                    let args: Vec<Operand> = parts[4..].iter().map(|s| Self::parse_operand(s)).collect();
                    return Ok(Instruction::Call {
                        dest: Some(dest),
                        func_name,
                        args,
                    });
                }
                "CONST" => {
                    if parts.len() < 5 {
                        return Err(ParseError {
                            line_no,
                            message: "Syntax: %dest = CONST <type> <val>".into(),
                        });
                    }
                    let ty = Self::parse_type(parts[3], line_no)?;
                    let val = match ty {
                        Type::I64 => Value::I64(parts[4].parse::<i64>().map_err(|_| ParseError {
                            line_no,
                            message: format!("Cannot parse i64: {}", parts[4]),
                        })?),
                        Type::U64 => Value::U64(parts[4].parse::<u64>().map_err(|_| ParseError {
                            line_no,
                            message: format!("Cannot parse u64: {}", parts[4]),
                        })?),
                        Type::U8 => Value::U64(parts[4].parse::<u8>().map_err(|_| ParseError {
                            line_no,
                            message: format!("Cannot parse u8: {}", parts[4]),
                        })? as u64),
                        Type::F64 => Value::F64(parts[4].parse::<f64>().map_err(|_| ParseError {
                            line_no,
                            message: format!("Cannot parse f64: {}", parts[4]),
                        })?),
                        Type::Bool => Value::Bool(match parts[4] {
                            "true" => true,
                            "false" => false,
                            _ => return Err(ParseError {
                                line_no,
                                message: format!("Boolean must be true or false: {}", parts[4]),
                            }),
                        }),
                        Type::Ptr => Value::Ptr(parts[4].parse::<usize>().map_err(|_| ParseError {
                            line_no,
                            message: format!("Pointer address must be an integer: {}", parts[4]),
                        })?),
                        Type::Array(..) | Type::Slice(..) => {
                            return Err(ParseError {
                                line_no,
                                message: "Cannot assign CONST directly to Array/Slice. Use ALLOC".into(),
                            });
                        }
                    };
                    return Ok(Instruction::AssignConst { dest, ty, val });
                }
                "MOV" => {
                    if parts.len() < 4 {
                        return Err(ParseError {
                            line_no,
                            message: "Syntax: %dest = MOV %src".into(),
                        });
                    }
                    return Ok(Instruction::Mov {
                        dest,
                        src: parts[3].to_string(),
                    });
                }
                "LOAD8" => {
                    if parts.len() < 5 {
                        return Err(ParseError {
                            line_no,
                            message: "Syntax: %dest = LOAD8 %buf %offset".into(),
                        });
                    }
                    return Ok(Instruction::Load8 {
                        dest,
                        buf: parts[3].to_string(),
                        offset: Self::parse_operand(parts[4]),
                    });
                }
                "LOAD64" => {
                    if parts.len() < 5 {
                        return Err(ParseError {
                            line_no,
                            message: "Syntax: %dest = LOAD64 %buf %offset".into(),
                        });
                    }
                    return Ok(Instruction::Load64 {
                        dest,
                        buf: parts[3].to_string(),
                        offset: Self::parse_operand(parts[4]),
                    });
                }
                "SYSCALL" => {
                    if parts.len() < 7 {
                        return Err(ParseError {
                            line_no,
                            message: "Syntax: %dest = SYSCALL rax rdi rsi rdx".into(),
                        });
                    }
                    return Ok(Instruction::Syscall {
                        dest: Some(dest),
                        rax: Self::parse_operand(parts[3]),
                        rdi: Self::parse_operand(parts[4]),
                        rsi: Self::parse_operand(parts[5]),
                        rdx: Self::parse_operand(parts[6]),
                    });
                }
                "ADD" | "SUB" | "MUL" | "DIV" | "MOD" | "EQ" | "NEQ" | "LT" | "LTE" | "GT" | "GTE"
                | "AND" | "OR" => {
                    if parts.len() < 6 {
                        return Err(ParseError {
                            line_no,
                            message: format!("Syntax: %dest = {} <type> src1 src2", op),
                        });
                    }
                    let bin_op = match op {
                        "ADD" => BinOp::Add,
                        "SUB" => BinOp::Sub,
                        "MUL" => BinOp::Mul,
                        "DIV" => BinOp::Div,
                        "MOD" => BinOp::Mod,
                        "EQ" => BinOp::Eq,
                        "NEQ" => BinOp::Neq,
                        "LT" => BinOp::Lt,
                        "LTE" => BinOp::Lte,
                        "GT" => BinOp::Gt,
                        "GTE" => BinOp::Gte,
                        "AND" => BinOp::And,
                        "OR" => BinOp::Or,
                        _ => unreachable!(),
                    };
                    let ty = Self::parse_type(parts[3], line_no)?;
                    let src1 = Self::parse_operand(parts[4]);
                    let src2 = Self::parse_operand(parts[5]);
                    return Ok(Instruction::Binary {
                        op: bin_op,
                        ty,
                        dest,
                        src1,
                        src2,
                    });
                }
                _ => {}
            }
        }

        Err(ParseError {
            line_no,
            message: format!("Unrecognized instruction: '{}'", line),
        })
    }

    /// Parser biểu thức toán học cho REQUIRE, ENSURE, INVARIANT, ASSERT
    pub fn parse_expr(s: &str, line_no: usize) -> Result<Expr, ParseError> {
        let s = s.trim();

        // 1. Phép logic Or: ||
        if let Some(pos) = s.find("||") {
            let lhs = Self::parse_expr(&s[..pos], line_no)?;
            let rhs = Self::parse_expr(&s[pos + 2..], line_no)?;
            return Ok(Expr::Binary {
                op: BinOp::Or,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            });
        }

        // 2. Phép logic And: &&
        if let Some(pos) = s.find("&&") {
            let lhs = Self::parse_expr(&s[..pos], line_no)?;
            let rhs = Self::parse_expr(&s[pos + 2..], line_no)?;
            return Ok(Expr::Binary {
                op: BinOp::And,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            });
        }

        // 3. Phép so sánh: ==, !=, <=, >=, <, >
        let comparisons = [
            ("==", BinOp::Eq),
            ("!=", BinOp::Neq),
            ("<=", BinOp::Lte),
            (">=", BinOp::Gte),
            ("<", BinOp::Lt),
            (">", BinOp::Gt),
        ];

        for (sym, op) in comparisons {
            if let Some(pos) = s.find(sym) {
                let lhs = Self::parse_expr(&s[..pos], line_no)?;
                let rhs = Self::parse_expr(&s[pos + sym.len()..], line_no)?;
                return Ok(Expr::Binary {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                });
            }
        }

        // 4. Phép cộng / trừ: +, -
        for (sym, op) in [("+", BinOp::Add), ("-", BinOp::Sub)] {
            if let Some(pos) = s.rfind(sym) {
                if pos > 0 && !s[..pos].trim().is_empty() {
                    let lhs = Self::parse_expr(&s[..pos], line_no)?;
                    let rhs = Self::parse_expr(&s[pos + 1..], line_no)?;
                    return Ok(Expr::Binary {
                        op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    });
                }
            }
        }

        // 5. Phép nhân / chia / chia dư: *, /, %
        for (sym, op) in [("*", BinOp::Mul), ("/", BinOp::Div), ("%", BinOp::Mod)] {
            if let Some(pos) = s.rfind(sym) {
                if pos > 0 {
                    let lhs = Self::parse_expr(&s[..pos], line_no)?;
                    let rhs = Self::parse_expr(&s[pos + 1..], line_no)?;
                    return Ok(Expr::Binary {
                        op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    });
                }
            }
        }

        // 6. Phủ định !
        if let Some(stripped) = s.strip_prefix('!') {
            let inner = Self::parse_expr(stripped, line_no)?;
            return Ok(Expr::Not(Box::new(inner)));
        }

        // 7. Hàm len(%arr)
        if s.starts_with("len(") && s.ends_with(')') {
            let inner = &s[4..s.len() - 1].trim();
            return Ok(Expr::Len(inner.to_string()));
        }

        // 8. Atom: bool hoặc số hoặc biến
        if s == "true" {
            return Ok(Expr::BoolConst(true));
        }
        if s == "false" {
            return Ok(Expr::BoolConst(false));
        }
        if let Ok(num) = s.parse::<i64>() {
            return Ok(Expr::IntConst(num));
        }
        if let Ok(flt) = s.parse::<f64>() {
            return Ok(Expr::FloatConst(flt));
        }

        Ok(Expr::Var(s.to_string()))
    }
}
