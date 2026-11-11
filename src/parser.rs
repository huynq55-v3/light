// File: src/parser.rs (Ngân sách: < 150 dòng - Thực tế: 145 dòng)
use crate::ir::*;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

/// Tách token trên 1 dòng, bảo toàn chuỗi hằng `"..."` (có chứa khoảng trắng hoặc dấu #) và bỏ comment sau dấu #
fn tokenize_line(raw_line: &str) -> Result<Vec<String>, String> {
    let mut toks = Vec::new();
    let mut cur = String::new();
    let mut chars = raw_line.chars().peekable();
    let mut in_quotes = false;

    while let Some(c) = chars.next() {
        if in_quotes {
            cur.push(c);
            if c == '\\' {
                if let Some(next_c) = chars.next() {
                    cur.push(next_c);
                }
            } else if c == '"' {
                in_quotes = false;
                toks.push(std::mem::take(&mut cur));
            }
        } else {
            match c {
                '#' => break,
                '"' => {
                    if !cur.is_empty() {
                        toks.push(std::mem::take(&mut cur));
                    }
                    cur.push('"');
                    in_quotes = true;
                }
                w if w.is_whitespace() => {
                    if !cur.is_empty() {
                        toks.push(std::mem::take(&mut cur));
                    }
                }
                _ => cur.push(c),
            }
        }
    }
    if in_quotes {
        return Err(format!("Chuỗi hằng chưa đóng dấu ngoặc kép: {}", raw_line));
    }
    if !cur.is_empty() {
        toks.push(cur);
    }
    Ok(toks)
}

/// Giải mã chuỗi hằng `"..."` (tối đa 8 byte ASCII) thành số u64 theo chuẩn Little-Endian
fn p_str_qword(s: &str) -> Result<u64, String> {
    let inner = &s[1..s.len() - 1];
    let mut bytes = Vec::with_capacity(8);
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        let b = if c == '\\' {
            match chars.next().ok_or_else(|| format!("Ký tự escape dở dang trong {}", s))? {
                'n' => b'\n',
                'r' => b'\r',
                't' => b'\t',
                '0' => 0,
                '\\' => b'\\',
                '"' => b'"',
                other => other as u8,
            }
        } else {
            c as u8
        };
        bytes.push(b);
    }
    if bytes.len() > 8 {
        return Err(format!(
            "Chuỗi hằng {} dài {} bytes (vượt quá giới hạn 8 bytes của Qword bv64)",
            s,
            bytes.len()
        ));
    }
    let mut val = 0u64;
    for (i, &b) in bytes.iter().enumerate() {
        val |= (b as u64) << (i * 8);
    }
    Ok(val)
}

/// Đọc file .lit và đệ quy ghép các file `include <relative_path>` theo đúng thư mục của file hiện tại
fn load_source_recursive(
    path: &Path,
    visited: &mut HashSet<PathBuf>,
    origins: &mut Vec<String>,
) -> Result<String, String> {
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
    for (i, raw_line) in content.lines().enumerate() {
        let origin = format!("{}:{}", path.display(), i + 1);
        let line = raw_line.split('#').next().unwrap_or("").trim();
        let mut toks = line.split_whitespace();
        if toks.next() == Some("include") {
            let rel_path = toks
                .next()
                .ok_or("Thiếu đường dẫn sau từ khóa include")?
                .trim_matches('"');
            let next_path = parent_dir.join(rel_path);
            combined.push_str(&load_source_recursive(&next_path, visited, origins)?);
            combined.push('\n');
            origins.push(origin);
        } else {
            combined.push_str(raw_line);
            combined.push('\n');
            origins.push(origin);
        }
    }
    Ok(combined)
}

pub fn parse_file(entry_path: &str) -> Result<Module, String> {
    let mut visited = HashSet::new();
    let mut origins = Vec::new();
    let full_src = load_source_recursive(Path::new(entry_path), &mut visited, &mut origins)?;
    parse_module_at(&full_src, Some(&origins))
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

fn p_u64(s: &str, defs: &HashMap<String, u64>) -> Result<u64, String> {
    let s = s.trim_end_matches(',');
    if let Some(&val) = defs.get(s) {
        return Ok(val);
    }
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        return p_str_qword(s);
    }
    if let Some(hex) = s.strip_prefix("0x") {
        u64::from_str_radix(hex, 16).map_err(|_| format!("Lỗi số hex: {}", s))
    } else {
        s.parse()
            .map_err(|_| format!("Lỗi số nguyên hoặc hằng số chưa định nghĩa: {}", s))
    }
}

fn p_type(s: &str, layouts: &[Layout], defs: &HashMap<String, u64>) -> Result<Type, String> {
    let s = s.trim_matches(|c| c == ',' || c == ')');
    match s {
        "bv8" => Ok(Type::Bv8),
        "bv16" => Ok(Type::Bv16),
        "bv32" => Ok(Type::Bv32),
        "bv64" => Ok(Type::Bv64),
        "smp" => Ok(Type::Smp),
        _ if s.starts_with("ptr<") && s.ends_with('>') => {
            // Cú pháp: ptr<Process,1> hoặc ptr<DiskQword,*> (Size-Polymorphic)
            let inner = &s[4..s.len() - 1];
            let (name, max) = inner.split_once(',').ok_or("Lỗi cú pháp ptr<Layout,Max>")?;
            let id = layouts
                .iter()
                .position(|l| l.name == name)
                .ok_or_else(|| format!("Không tìm thấy Layout '{}'", name))?
                as u16;
            if let Some(r) = max.trim().strip_prefix('%') {
                let len = r.parse().map_err(|_| format!("Lỗi độ dài động ptr<{},{}>", name, max))?;
                return Ok(Type::DPtr { layout_id: id, len });
            }
            let max_elems = if max.trim() == "*" {
                1
            } else {
                p_u64(max.trim(), defs)?
            };
            Ok(Type::Ptr {
                layout_id: id,
                max_elems,
            })
        }
        _ if s.starts_with("io<") && s.ends_with('>') => {
            // Cú pháp: io<0x3f8,0x3ff>
            let inner = &s[3..s.len() - 1];
            let (min_s, max_s) = inner.split_once(',').ok_or("Lỗi cú pháp io<Min,Max>")?;
            Ok(Type::Io {
                min: p_u64(min_s.trim(), defs)? as u16,
                max: p_u64(max_s.trim(), defs)? as u16,
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
        "add_wrap" => Some(BinOp::AddWrap),
        "sub_wrap" => Some(BinOp::SubWrap),
        "mul_wrap" => Some(BinOp::MulWrap),
        "add_sat" => Some(BinOp::AddSat),
        "sub_sat" => Some(BinOp::SubSat),
        "mul_sat" => Some(BinOp::MulSat),
        "add_ovf" => Some(BinOp::AddOvf),
        "sub_ovf" => Some(BinOp::SubOvf),
        "mul_ovf" => Some(BinOp::MulOvf),
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
fn p_z3<'a, I>(it: &mut I, defs: &HashMap<String, u64>) -> Result<Z3Expr, String>
where
    I: Iterator<Item = &'a str>,
{
    let tok = it.next().ok_or("Thiếu token trong biểu thức Z3")?;
    if tok == "val" {
        return Ok(Z3Expr::FieldVal);
    }
    if tok == "not" {
        return Ok(Z3Expr::Not(Box::new(p_z3(it, defs)?)));
    }
    if tok == "and" {
        return Ok(Z3Expr::And(
            Box::new(p_z3(it, defs)?),
            Box::new(p_z3(it, defs)?),
        ));
    }
    if tok == "or" {
        return Ok(Z3Expr::Or(
            Box::new(p_z3(it, defs)?),
            Box::new(p_z3(it, defs)?),
        ));
    }
    if let Some(op) = p_cmpop(tok) {
        return Ok(Z3Expr::Cmp(
            op,
            Box::new(p_z3(it, defs)?),
            Box::new(p_z3(it, defs)?),
        ));
    }
    if let Some(op) = p_binop(tok) {
        return Ok(Z3Expr::Bin(
            op,
            Box::new(p_z3(it, defs)?),
            Box::new(p_z3(it, defs)?),
        ));
    }
    if tok.starts_with('%') {
        return Ok(Z3Expr::Reg(p_reg(tok)?));
    }
    Ok(Z3Expr::Const(p_u64(tok, defs)?))
}

/// Phân tích biểu thức Z3 và bắt buộc dùng hết token (token thừa thường là lỗi gõ của AI, trước đây bị bỏ qua im lặng)
fn p_z3_all(toks: &[&str], defs: &HashMap<String, u64>) -> Result<Z3Expr, String> {
    let mut it = toks.iter().copied();
    let e = p_z3(&mut it, defs)?;
    let rest: Vec<&str> = it.collect();
    if !rest.is_empty() {
        return Err(format!("Biểu thức Z3 có token thừa: {}", rest.join(" ")));
    }
    Ok(e)
}

/// Số token hợp lệ của từng lệnh SSA: (tối thiểu, tối đa). Kiểm tra trước khi truy cập toks[i] để báo lỗi
/// có số dòng thay vì panic, và để token thừa (ví dụ `%3 = add %1 %2 %9`) không bị bỏ qua im lặng.
fn inst_arity(toks: &[&str]) -> Option<(usize, usize)> {
    const ANY: usize = usize::MAX;
    Some(match toks[0] {
        "store" | "vadd256" | "vsub256" | "vmul256" | "vxor256" | "br" | "hwio_w" => (4, 4),
        "parallel" => (6, 6),
        "ata_read" => (5, 5),
        "jmp" | "call" => (2, ANY),
        "ret" => (1, 2),
        "assume" | "assert" => (2, ANY),
        d if d.starts_with('%') && toks.get(1) == Some(&"=") => match toks.get(2).copied()? {
            "const" | "hwio_r" | "vdot256" => (5, 5),
            "smp_workers" => (4, 4),
            "slice" | "load" | "cmp" => (6, 6),
            "call" => (4, ANY),
            _ => (5, 5),
        },
        _ => return None,
    })
}

fn p_params(
    toks: &[&str],
    layouts: &[Layout],
    defs: &HashMap<String, u64>,
) -> Result<Vec<(Reg, Type)>, String> {
    // Cú pháp tham số: %0:bv64 %1:ptr<Process,1>
    let mut out = Vec::new();
    for t in toks {
        if let Some((r, ty)) = t.split_once(':') {
            out.push((p_reg(r)?, p_type(ty, layouts, defs)?));
        } else if *t != "{" {
            return Err(format!("Tham số không hợp lệ '{}' (cần dạng %r:kiểu)", t));
        }
    }
    Ok(out)
}

#[allow(dead_code)]
pub fn parse_module(src: &str) -> Result<Module, String> {
    parse_module_at(src, None)
}

/// `origins[i]` = "file:dòng" gốc của dòng thứ i trong `src` đã ghép include (để báo lỗi đúng vị trí)
fn parse_module_at(src: &str, origins: Option<&[String]>) -> Result<Module, String> {
    let mut m = Module::default();
    let mut defs: HashMap<String, u64> = HashMap::new();
    let mut in_layout = false;

    for (line_no, raw_line) in src.lines().enumerate() {
        let loc = origins
            .and_then(|o| o.get(line_no).cloned())
            .unwrap_or_else(|| format!("dòng {}", line_no + 1));
        let err = |msg: &str| format!("Dòng {}: {}", loc, msg);
        // Bọc cả dòng để mọi lỗi (kể cả từ p_reg/p_blk) đều kèm số dòng và nội dung dòng
        let mut parse_line = || -> Result<(), String> {
        let owned_toks = tokenize_line(raw_line).map_err(|e| err(&e))?;
        if owned_toks.is_empty() {
            return Ok(());
        }
        let toks: Vec<&str> = owned_toks.iter().map(|s| s.as_str()).collect();

        match toks[0] {
            "}" => in_layout = false,
            "def" => {
                // def IPC_WIN_DRAWN 112 | def TITLE_TERM "TERMINAL"
                if toks.len() < 3 {
                    return Err(err("Cú pháp: def <TÊN_HẰNG> <GIÁ_TRỊ>"));
                }
                let val = p_u64(toks[2], &defs).map_err(|e| err(&e))?;
                defs.insert(toks[1].to_string(), val);
            }
            "layout" => {
                // layout Process 24 {
                if toks.len() < 3 {
                    return Err(err("Cú pháp: layout <Tên> <kích_thước> {"));
                }
                if m.layouts.iter().any(|l| l.name == toks[1]) {
                    return Err(err(&format!("Layout '{}' bị khai báo hai lần", toks[1])));
                }
                m.layouts.push(Layout {
                    name: toks[1].into(),
                    size: p_u64(toks[2], &defs).map_err(|e| err(&e))? as u32,
                    fields: Vec::new(),
                });
                in_layout = true;
            }
            "func" => {
                // func init_proc -> bv64 %0:ptr<Process,1> {
                if toks.len() < 3 {
                    return Err(err("Cú pháp: func <tên> <kiểu_trả_về|void> [%r:kiểu ...] {"));
                }
                if m.funcs.iter().any(|f| f.name == toks[1]) {
                    return Err(err(&format!("Hàm '{}' bị khai báo hai lần", toks[1])));
                }
                let ret_ty = if toks[2] == "void" {
                    None
                } else {
                    Some(p_type(toks[2], &m.layouts, &defs).map_err(|e| err(&e))?)
                };
                m.funcs.push(Func {
                    name: toks[1].into(),
                    ret_ty,
                    params: p_params(&toks[3..], &m.layouts, &defs).map_err(|e| err(&e))?,
                    requires: Vec::new(),
                    ensures: Vec::new(),
                    blocks: Vec::new(),
                    origin: loc.clone(),
                });
            }
            "@req" => m
                .funcs
                .last_mut()
                .ok_or_else(|| err("Lỗi @req"))?
                .requires
                .push(p_z3_all(&toks[1..], &defs).map_err(|e| err(&e))?),
            "@ens" => m
                .funcs
                .last_mut()
                .ok_or_else(|| err("Lỗi @ens"))?
                .ensures
                .push(p_z3_all(&toks[1..], &defs).map_err(|e| err(&e))?),
            "@inv" => {
                let blk = m
                    .funcs
                    .last_mut()
                    .and_then(|f| f.blocks.last_mut())
                    .ok_or_else(|| err("@inv ngoài Block"))?;
                blk.invs
                    .push(p_z3_all(&toks[1..], &defs).map_err(|e| err(&e))?);
            }
            b if b.starts_with('@') => {
                // @b1 %1:bv64
                let f = m.funcs.last_mut().ok_or_else(|| err("Block ngoài Func"))?;
                f.blocks.push(Block {
                    id: p_blk(b)?,
                    params: p_params(&toks[1..], &m.layouts, &defs).map_err(|e| err(&e))?,
                    invs: Vec::new(),
                    insts: Vec::new(),
                });
            }
            _ if in_layout => {
                // 0: bv64 @inv ugt val 0
                if toks.len() < 2 || (toks.len() > 2 && toks[2] != "@inv") || toks.len() == 3 {
                    return Err(err("Cú pháp trường: <offset>: <kiểu> [@inv <biểu_thức>]"));
                }
                let offset =
                    p_u64(toks[0].trim_end_matches(':'), &defs).map_err(|e| err(&e))? as u32;
                let ty = p_type(toks[1], &m.layouts, &defs).map_err(|e| err(&e))?;
                let inv = if toks.get(2) == Some(&"@inv") {
                    Some(p_z3_all(&toks[3..], &defs).map_err(|e| err(&e))?)
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
                let (lo, hi) = inst_arity(&toks).ok_or_else(|| err("Không nhận diện được lệnh SSA"))?;
                if toks.len() < lo || toks.len() > hi {
                    return Err(err(&format!(
                        "Lệnh '{}' cần {} token nhưng có {}",
                        toks.join(" "),
                        if lo == hi { lo.to_string() } else if hi == usize::MAX { format!(">= {}", lo) } else { format!("{}..{}", lo, hi) },
                        toks.len()
                    )));
                }
                let inst = match toks[0] {
                    "store" => Inst::Store {
                        base: p_reg(toks[1])?,
                        offset: p_u64(toks[2], &defs).map_err(|e| err(&e))? as u32,
                        val: p_reg(toks[3])?,
                    },
                    "vadd256" | "vsub256" | "vmul256" | "vxor256" => Inst::Simd256 {
                        op: p_simdop(toks[0]).unwrap(),
                        dst: p_reg(toks[1])?,
                        lhs: p_reg(toks[2])?,
                        rhs: p_reg(toks[3])?,
                    },
                    "parallel" => Inst::Parallel {
                        smp: p_reg(toks[1])?,
                        n: p_reg(toks[2])?,
                        func_id: p_func_id(toks[3], &m.funcs)?,
                        base: p_reg(toks[4])?,
                        arg: p_reg(toks[5])?,
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
                    "assume" => Inst::Assume(
                        p_z3_all(&toks[1..], &defs).map_err(|e| err(&e))?,
                    ),
                    "assert" => Inst::Assert(
                        p_z3_all(&toks[1..], &defs).map_err(|e| err(&e))?,
                    ),
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
                    // ata_read %cap %ptr %sec_idx %nsec: rep insd nsec sector từ cổng 0x1F0 vào [ptr + sec_idx*512]
                    "ata_read" => Inst::AtaRead {
                        cap: p_reg(toks[1])?,
                        ptr: p_reg(toks[2])?,
                        idx: p_reg(toks[3])?,
                        nsec: p_reg(toks[4])?,
                    },
                    "hwio_w" => Inst::HwIo {
                        dst: None,
                        cap: p_reg(toks[1])?,
                        port_or_reg: p_u64(toks[2], &defs).map_err(|e| err(&e))? as u16,
                        val: Some(p_reg(toks[3])?),
                        is_write: true,
                    },
                    dst if dst.starts_with('%') && toks.get(1) == Some(&"=") => {
                        let d = p_reg(dst)?;
                        match toks[2] {
                            "const" => Inst::Const {
                                dst: d,
                                val: p_u64(toks[3], &defs).map_err(|e| err(&e))?,
                                ty: p_type(toks[4], &m.layouts, &defs).map_err(|e| err(&e))?,
                            },
                            "slice" => Inst::Slice {
                                dst: d,
                                base: p_reg(toks[3])?,
                                idx: p_reg(toks[4])?,
                                ty: p_type(toks[5], &m.layouts, &defs).map_err(|e| err(&e))?,
                            },
                            "narrow" => Inst::Narrow {
                                dst: d,
                                src: p_reg(toks[3])?,
                                ty: p_type(toks[4], &m.layouts, &defs).map_err(|e| err(&e))?,
                            },
                            "load" => Inst::Load {
                                dst: d,
                                base: p_reg(toks[3])?,
                                offset: p_u64(toks[4], &defs).map_err(|e| err(&e))? as u32,
                                ty: p_type(toks[5], &m.layouts, &defs).map_err(|e| err(&e))?,
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
                                port_or_reg: p_u64(toks[4], &defs).map_err(|e| err(&e))? as u16,
                                val: None,
                                is_write: false,
                            },
                            "vdot256" => Inst::Simd256 {
                                op: SimdOp::Dot,
                                dst: d,
                                lhs: p_reg(toks[3])?,
                                rhs: p_reg(toks[4])?,
                            },
                            "smp_workers" => Inst::SmpWorkers {
                                dst: d,
                                smp: p_reg(toks[3])?,
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
        Ok(())
        };
        parse_line().map_err(|e| {
            let e = if e.starts_with("Dòng ") { e } else { err(&e) };
            format!("{}\n    > {}", e, raw_line.trim())
        })?;
    }
    for f in &mut m.funcs {
        lower_func(f);
    }
    Ok(m)
}

/// Hạ các phép *_sat / *_ovf thành lệnh gốc bv64 thuần (không rẽ nhánh, không cmp) để verifier và bộ sinh mã không cần biết chúng.
/// Cờ tràn là bv64 0/1: cộng = bit cao của (a&b | (a|b)&~s); trừ = bit cao của (~a&b | ~(a^b)&d);
/// nhân = (a != 0) & ((a*b)/(a|[a==0]) != b). *_sat = kết quả quay vòng OR mặt nạ toàn 1 (cộng/nhân) hoặc AND mặt nạ (trừ).
struct Low<'a> {
    out: &'a mut Vec<Inst>,
    next: &'a mut u32,
}
impl Low<'_> {
    fn r(&mut self) -> u32 {
        *self.next += 1;
        *self.next - 1
    }
    fn k(&mut self, val: u64) -> u32 {
        let d = self.r();
        self.out.push(Inst::Const { dst: d, ty: Type::Bv64, val });
        d
    }
    fn op(&mut self, op: BinOp, lhs: u32, rhs: u32, dst: Option<u32>) -> u32 {
        let d = dst.unwrap_or_else(|| self.r());
        self.out.push(Inst::Bin { dst: d, op, lhs, rhs });
        d
    }
    fn top(&mut self, x: u32, dst: Option<u32>) -> u32 {
        let c = self.k(63);
        self.op(BinOp::LShr, x, c, dst)
    }
    fn nonzero(&mut self, x: u32, dst: Option<u32>) -> u32 {
        let z = self.k(0);
        let n = self.op(BinOp::SubWrap, z, x, None);
        let o = self.op(BinOp::Or, x, n, None);
        self.top(o, dst)
    }
    fn mask(&mut self, flag: u32) -> u32 {
        let z = self.k(0);
        self.op(BinOp::SubWrap, z, flag, None)
    }
    fn add_ovf(&mut self, l: u32, r: u32, dst: Option<u32>) -> (u32, u32) {
        let s = self.op(BinOp::AddWrap, l, r, None);
        let ones = self.k(u64::MAX);
        let (t1, t2) = (self.op(BinOp::And, l, r, None), self.op(BinOp::Or, l, r, None));
        let ns = self.op(BinOp::Xor, s, ones, None);
        let t3 = self.op(BinOp::And, t2, ns, None);
        let t4 = self.op(BinOp::Or, t1, t3, None);
        (s, self.top(t4, dst))
    }
    fn sub_ovf(&mut self, l: u32, r: u32, dst: Option<u32>) -> (u32, u32) {
        let d = self.op(BinOp::SubWrap, l, r, None);
        let ones = self.k(u64::MAX);
        let na = self.op(BinOp::Xor, l, ones, None);
        let t1 = self.op(BinOp::And, na, r, None);
        let x = self.op(BinOp::Xor, l, r, None);
        let nx = self.op(BinOp::Xor, x, ones, None);
        let t2 = self.op(BinOp::And, nx, d, None);
        let t3 = self.op(BinOp::Or, t1, t2, None);
        (d, self.top(t3, dst))
    }
    fn mul_ovf(&mut self, l: u32, r: u32, dst: Option<u32>) -> (u32, u32) {
        let p = self.op(BinOp::MulWrap, l, r, None);
        let nza = self.nonzero(l, None);
        let one = self.k(1);
        let isz = self.op(BinOp::Xor, nza, one, None);
        let anz = self.op(BinOp::Or, l, isz, None); // a == 0 -> chia cho 1
        let q = self.op(BinOp::UDiv, p, anz, None);
        let x = self.op(BinOp::Xor, q, r, None);
        let nzq = self.nonzero(x, None);
        (p, self.op(BinOp::And, nza, nzq, dst))
    }
}

fn lower_func(f: &mut Func) {
    let mut max = f.params.iter().map(|p| p.0).max().unwrap_or(0);
    for b in &f.blocks {
        for p in &b.params {
            max = max.max(p.0);
        }
        for i in &b.insts {
            if let Inst::Bin { dst, .. } | Inst::Cmp { dst, .. } | Inst::Const { dst, .. } = i {
                max = max.max(*dst);
            }
        }
    }
    let mut next = max + 1;
    for b in &mut f.blocks {
        let old = std::mem::take(&mut b.insts);
        for inst in old {
            let Inst::Bin { dst, op, lhs: l, rhs: r } = inst else {
                b.insts.push(inst);
                continue;
            };
            let mut lw = Low { out: &mut b.insts, next: &mut next };
            match op {
                BinOp::AddOvf => {
                    lw.add_ovf(l, r, Some(dst));
                }
                BinOp::SubOvf => {
                    lw.sub_ovf(l, r, Some(dst));
                }
                BinOp::MulOvf => {
                    lw.mul_ovf(l, r, Some(dst));
                }
                BinOp::AddSat => {
                    let (s, c) = lw.add_ovf(l, r, None);
                    let m = lw.mask(c);
                    lw.op(BinOp::Or, s, m, Some(dst));
                }
                BinOp::SubSat => {
                    let (d, c) = lw.sub_ovf(l, r, None);
                    let one = lw.k(1);
                    let keep = lw.op(BinOp::Xor, c, one, None);
                    let m = lw.mask(keep);
                    lw.op(BinOp::And, d, m, Some(dst));
                }
                BinOp::MulSat => {
                    let (p, c) = lw.mul_ovf(l, r, None);
                    let m = lw.mask(c);
                    lw.op(BinOp::Or, p, m, Some(dst));
                }
                _ => b.insts.push(inst),
            }
        }
    }
}
