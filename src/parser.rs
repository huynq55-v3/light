// File: src/parser.rs (Ngân sách: < 150 dòng - Thực tế: 145 dòng)
use crate::ir::*;
use std::collections::HashSet;
use std::path::{Path, PathBuf};

/// Đọc file .lit và đệ quy ghép các file `include <relative_path>` theo đúng thư mục của file hiện tại
fn load_source_recursive(path: &Path, visited: &mut HashSet<PathBuf>) -> Result<String, String> {
    let canon = path
        .canonicalize()
        .map_err(|e| format!("Không tìm thấy file '{}': {}", path.display(), e))?;
    if !visited.insert(canon.clone()) {
        return Ok(String::new()); // Đã include rồi thì bỏ qua (Chống trùng lặp #pragma once)
    }
    let parent_dir = canon.parent().unwrap_or_else(|| Path::new("."));
    let content = std::fs::read_to_string(&canon)
        .map_err(|e| format!("Lỗi đọc '{}': {}", path.display(), e))?;

    let mut combined = String::new();
    for raw_line in content.lines() {
        let line = raw_line.split('#').next().unwrap_or("").trim();
        let mut toks = line.split_whitespace();
        if toks.next() == Some("include") {
            let rel_path = toks
                .next()
                .ok_or("Thiếu đường dẫn sau từ khóa include")?
                .trim_matches('"');
            let next_path = parent_dir.join(rel_path);
            combined.push_str(&load_source_recursive(&next_path, visited)?);
            combined.push('\n');
        } else {
            combined.push_str(raw_line);
            combined.push('\n');
        }
    }
    Ok(combined)
}

pub fn parse_file(entry_path: &str) -> Result<Module, String> {
    let mut visited = HashSet::new();
    let full_src = load_source_recursive(Path::new(entry_path), &mut visited)?;
    parse_module(&full_src)
}

fn p_reg(s: &str) -> Result<Reg, String> {
    s.trim_matches(|c| c == '%' || c == ',' || c == ':' || c == '(' || c == ')')
        .parse()
        .map_err(|_| format!("Lỗi cú pháp Reg: {}", s))
}

fn p_blk(s: &str) -> Result<BlockId, String> {
    s.trim_matches(|c| c == '@' || c == 'b' || c == ',' || c == ':')
        .parse()
        .map_err(|_| format!("Lỗi cú pháp BlockId: {}", s))
}

fn p_u64(s: &str) -> Result<u64, String> {
    let s = s.trim_end_matches(',');
    if let Some(hex) = s.strip_prefix("0x") {
        u64::from_str_radix(hex, 16).map_err(|_| format!("Lỗi số hex: {}", s))
    } else {
        s.parse().map_err(|_| format!("Lỗi số nguyên: {}", s))
    }
}

fn p_type(s: &str, layouts: &[Layout]) -> Result<Type, String> {
    let s = s.trim_matches(|c| c == ',' || c == ')');
    match s {
        "bv8" => Ok(Type::Bv8),
        "bv16" => Ok(Type::Bv16),
        "bv32" => Ok(Type::Bv32),
        "bv64" => Ok(Type::Bv64),
        _ if s.starts_with("ptr<") && s.ends_with('>') => {
            // Cú pháp: ptr<Process,1> (Tự động tìm tên Layout đổi thành layout_id)
            let inner = &s[4..s.len() - 1];
            let (name, max) = inner.split_once(',').ok_or("Lỗi cú pháp ptr<Layout,Max>")?;
            let id = layouts
                .iter()
                .position(|l| l.name == name)
                .ok_or_else(|| format!("Không tìm thấy Layout '{}'", name))?
                as u16;
            Ok(Type::Ptr {
                layout_id: id,
                max_elems: p_u64(max)?,
            })
        }
        _ if s.starts_with("io<") && s.ends_with('>') => {
            // Cú pháp: io<0x3f8,0x3ff>
            let inner = &s[3..s.len() - 1];
            let (min_s, max_s) = inner.split_once(',').ok_or("Lỗi cú pháp io<Min,Max>")?;
            Ok(Type::Io {
                min: p_u64(min_s)? as u16,
                max: p_u64(max_s)? as u16,
            })
        }
        _ => Err(format!("Kiểu dữ liệu không hợp lệ: {}", s)),
    }
}

fn p_func_id(s: &str, funcs: &[Func]) -> Result<u32, String> {
    if let Ok(id) = s.parse::<u32>() {
        return Ok(id);
    }
    funcs
        .iter()
        .position(|f| f.name == s)
        .map(|i| i as u32)
        .ok_or_else(|| format!("Không tìm thấy hàm '{}'", s))
}

fn p_binop(s: &str) -> Option<BinOp> {
    match s {
        "add" => Some(BinOp::Add),
        "sub" => Some(BinOp::Sub),
        "mul" => Some(BinOp::Mul),
        "udiv" => Some(BinOp::UDiv),
        "sdiv" => Some(BinOp::SDiv),
        "urem" => Some(BinOp::URem),
        "srem" => Some(BinOp::SRem),
        "and" => Some(BinOp::And),
        "or" => Some(BinOp::Or),
        "xor" => Some(BinOp::Xor),
        "shl" => Some(BinOp::Shl),
        "lshr" => Some(BinOp::LShr),
        "ashr" => Some(BinOp::AShr),
        "fxmul" => Some(BinOp::FxMul),
        "fxdiv" => Some(BinOp::FxDiv),
        _ => None,
    }
}

fn p_simdop(s: &str) -> Option<SimdOp> {
    match s {
        "vadd256" => Some(SimdOp::Add),
        "vsub256" => Some(SimdOp::Sub),
        "vmul256" => Some(SimdOp::Mul),
        "vxor256" => Some(SimdOp::Xor),
        "vdot256" => Some(SimdOp::Dot),
        _ => None,
    }
}

fn p_cmpop(s: &str) -> Option<CmpOp> {
    match s {
        "eq" => Some(CmpOp::Eq),
        "ne" => Some(CmpOp::Ne),
        "ult" => Some(CmpOp::Ult),
        "ule" => Some(CmpOp::Ule),
        "ugt" => Some(CmpOp::Ugt),
        "uge" => Some(CmpOp::Uge),
        "slt" => Some(CmpOp::Slt),
        "sle" => Some(CmpOp::Sle),
        "sgt" => Some(CmpOp::Sgt),
        "sge" => Some(CmpOp::Sge),
        _ => None,
    }
}

/// Phân tích biểu thức Z3 dạng tiền tố phẳng (Prefix Polish Notation) không cần dấu ngoặc
/// Ví dụ: `ugt %0 0` -> (%0 > 0) | `and eq (and val 4095) 0 ugt val 0`
fn p_z3(it: &mut std::str::SplitWhitespace) -> Result<Z3Expr, String> {
    let tok = it.next().ok_or("Thiếu token trong biểu thức Z3")?;
    if tok == "val" {
        return Ok(Z3Expr::FieldVal);
    }
    if tok == "not" {
        return Ok(Z3Expr::Not(Box::new(p_z3(it)?)));
    }
    if tok == "and" {
        return Ok(Z3Expr::And(Box::new(p_z3(it)?), Box::new(p_z3(it)?)));
    }
    if tok == "or" {
        return Ok(Z3Expr::Or(Box::new(p_z3(it)?), Box::new(p_z3(it)?)));
    }
    if let Some(op) = p_cmpop(tok) {
        return Ok(Z3Expr::Cmp(op, Box::new(p_z3(it)?), Box::new(p_z3(it)?)));
    }
    if let Some(op) = p_binop(tok) {
        return Ok(Z3Expr::Bin(op, Box::new(p_z3(it)?), Box::new(p_z3(it)?)));
    }
    if tok.starts_with('%') {
        return Ok(Z3Expr::Reg(p_reg(tok)?));
    }
    Ok(Z3Expr::Const(p_u64(tok)?))
}

fn p_params(toks: &[&str], layouts: &[Layout]) -> Result<Vec<(Reg, Type)>, String> {
    // Cú pháp tham số: %0:bv64 %1:ptr<Process,1>
    let mut out = Vec::new();
    for t in toks {
        if let Some((r, ty)) = t.split_once(':') {
            out.push((p_reg(r)?, p_type(ty, layouts)?));
        }
    }
    Ok(out)
}

pub fn parse_module(src: &str) -> Result<Module, String> {
    let mut m = Module::default();
    let mut in_layout = false;

    for (line_no, raw_line) in src.lines().enumerate() {
        let line = raw_line.split('#').next().unwrap_or("").trim(); // Bỏ comment sau dấu #
        if line.is_empty() {
            continue;
        }
        let toks: Vec<&str> = line.split_whitespace().collect();
        let err = |msg: &str| format!("Dòng {}: {}", line_no + 1, msg);

        match toks[0] {
            "}" => in_layout = false,
            "layout" => {
                // layout Process 24 {
                m.layouts.push(Layout {
                    name: toks[1].into(),
                    size: p_u64(toks[2])? as u32,
                    fields: Vec::new(),
                });
                in_layout = true;
            }
            "func" => {
                // func init_proc -> bv64 %0:ptr<Process,1> {
                let ret_ty = if toks[2] == "void" {
                    None
                } else {
                    Some(p_type(toks[2], &m.layouts)?)
                };
                m.funcs.push(Func {
                    name: toks[1].into(),
                    ret_ty,
                    params: p_params(&toks[3..], &m.layouts)?,
                    requires: Vec::new(),
                    ensures: Vec::new(),
                    blocks: Vec::new(),
                });
            }
            "@req" => m
                .funcs
                .last_mut()
                .ok_or_else(|| err("Lỗi @req"))?
                .requires
                .push(p_z3(&mut line[4..].split_whitespace())?),
            "@ens" => m
                .funcs
                .last_mut()
                .ok_or_else(|| err("Lỗi @ens"))?
                .ensures
                .push(p_z3(&mut line[4..].split_whitespace())?),
            "@inv" => {
                // <--- THÊM NHÁNH NÀY: Đọc bất biến vòng lặp @inv gắn ở đầu Block
                let blk = m
                    .funcs
                    .last_mut()
                    .and_then(|f| f.blocks.last_mut())
                    .ok_or_else(|| err("@inv ngoài Block"))?;
                blk.invs.push(p_z3(&mut line[4..].split_whitespace())?);
            }
            b if b.starts_with('@') => {
                // @b1 %1:bv64
                let f = m.funcs.last_mut().ok_or_else(|| err("Block ngoài Func"))?;
                f.blocks.push(Block {
                    id: p_blk(b)?,
                    params: p_params(&toks[1..], &m.layouts)?,
                    invs: Vec::new(), // <--- Khởi tạo rỗng
                    insts: Vec::new(),
                });
            }
            _ if in_layout => {
                // 0: bv64 @inv ugt val 0
                let offset = p_u64(toks[0].trim_end_matches(':'))? as u32;
                let ty = p_type(toks[1], &m.layouts)?;
                let inv = if toks.get(2) == Some(&"@inv") {
                    Some(p_z3(&mut toks[3..].join(" ").split_whitespace())?)
                } else {
                    None
                };
                m.layouts
                    .last_mut()
                    .unwrap()
                    .fields
                    .push(FieldDef { offset, ty, inv });
            }
            _ => {
                // Các chỉ thị SSA bên trong Basic Block
                let inst = match toks[0] {
                    "store" => Inst::Store {
                        base: p_reg(toks[1])?,
                        offset: p_u64(toks[2])? as u32,
                        val: p_reg(toks[3])?,
                    },
                    "vadd256" | "vsub256" | "vmul256" | "vxor256" => Inst::Simd256 {
                        op: p_simdop(toks[0]).unwrap(),
                        dst: p_reg(toks[1])?,
                        lhs: p_reg(toks[2])?,
                        rhs: p_reg(toks[3])?,
                    },
                    "br" => Inst::Br {
                        cond: p_reg(toks[1])?,
                        then_bb: p_blk(toks[2])?,
                        else_bb: p_blk(toks[3])?,
                    },
                    "jmp" => Inst::Jmp {
                        target_bb: p_blk(toks[1])?,
                        args: toks[2..]
                            .iter()
                            .map(|r| p_reg(r))
                            .collect::<Result<_, _>>()?,
                    },
                    "ret" => Inst::Ret {
                        val: toks.get(1).map(|r| p_reg(r)).transpose()?,
                    },
                    "assume" => Inst::Assume(p_z3(&mut toks[1..].join(" ").split_whitespace())?),
                    "assert" => Inst::Assert(p_z3(&mut toks[1..].join(" ").split_whitespace())?),
                    "call" => {
                        let target_str = toks[1];
                        if target_str.starts_with('%') {
                            Inst::CallPtr {
                                dst: None,
                                target: p_reg(target_str)?,
                                args: toks[2..]
                                    .iter()
                                    .map(|r| p_reg(r))
                                    .collect::<Result<_, _>>()?,
                            }
                        } else {
                            Inst::Call {
                                dst: None,
                                func_id: p_func_id(target_str, &m.funcs)?,
                                args: toks[2..]
                                    .iter()
                                    .map(|r| p_reg(r))
                                    .collect::<Result<_, _>>()?,
                            }
                        }
                    }
                    "hwio_w" => Inst::HwIo {
                        dst: None,
                        cap: p_reg(toks[1])?,
                        port_or_reg: p_u64(toks[2])? as u16,
                        val: Some(p_reg(toks[3])?),
                        is_write: true,
                    },
                    dst if dst.starts_with('%') && toks.get(1) == Some(&"=") => {
                        let d = p_reg(dst)?;
                        match toks[2] {
                            "const" => Inst::Const {
                                dst: d,
                                val: p_u64(toks[3])?,
                                ty: p_type(toks[4], &m.layouts)?,
                            },
                            "slice" => Inst::Slice {
                                dst: d,
                                base: p_reg(toks[3])?,
                                idx: p_reg(toks[4])?,
                                ty: p_type(toks[5], &m.layouts)?,
                            },
                            "load" => Inst::Load {
                                dst: d,
                                base: p_reg(toks[3])?,
                                offset: p_u64(toks[4])? as u32,
                                ty: p_type(toks[5], &m.layouts)?,
                            },
                            "cmp" => Inst::Cmp {
                                dst: d,
                                op: p_cmpop(toks[3]).ok_or("Lỗi CmpOp")?,
                                lhs: p_reg(toks[4])?,
                                rhs: p_reg(toks[5])?,
                            },
                            "call" => {
                                let target_str = toks[3];
                                if target_str.starts_with('%') {
                                    Inst::CallPtr {
                                        dst: Some(d),
                                        target: p_reg(target_str)?,
                                        args: toks[4..]
                                            .iter()
                                            .map(|r| p_reg(r))
                                            .collect::<Result<_, _>>()?,
                                    }
                                } else {
                                    Inst::Call {
                                        dst: Some(d),
                                        func_id: p_func_id(target_str, &m.funcs)?,
                                        args: toks[4..]
                                            .iter()
                                            .map(|r| p_reg(r))
                                            .collect::<Result<_, _>>()?,
                                    }
                                }
                            }
                            "hwio_r" => Inst::HwIo {
                                dst: Some(d),
                                cap: p_reg(toks[3])?,
                                port_or_reg: p_u64(toks[4])? as u16,
                                val: None,
                                is_write: false,
                            },
                            "vdot256" => Inst::Simd256 {
                                op: SimdOp::Dot,
                                dst: d,
                                lhs: p_reg(toks[3])?,
                                rhs: p_reg(toks[4])?,
                            },
                            op_str => Inst::Bin {
                                dst: d,
                                op: p_binop(op_str).ok_or_else(|| err("Lệnh không rõ"))?,
                                lhs: p_reg(toks[3])?,
                                rhs: p_reg(toks[4])?,
                            },
                        }
                    }
                    _ => return Err(err("Không nhận diện được lệnh SSA")),
                };
                let blk = m
                    .funcs
                    .last_mut()
                    .and_then(|f| f.blocks.last_mut())
                    .ok_or_else(|| err("Lệnh ngoài Block"))?;
                blk.insts.push(inst);
            }
        }
    }
    Ok(m)
}
