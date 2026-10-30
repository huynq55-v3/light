#![allow(dead_code)]
//! Intermediate Verification Language (IVL) & Control Flow Graph (CFG)
//! Lấy cảm hứng từ kiến trúc Boogie (Microsoft Research) & Why3 (INRIA).
//!
//! Toàn bộ chương trình được hạ cấp (Lowering) thành đồ thị CFG với chỉ đúng 4 vi lệnh toán học:
//! 1. `Assign`: Gán biểu thức giá trị toán học thuần túy (hỗ trợ cả biến số BitVec và Memory Array)
//! 2. `Assert`: Khẳng định một thuộc tính phải đúng (nếu sai -> Báo lỗi & counter-example)
//! 3. `Assume`: Giả định tiền đề hoặc điều kiện rẽ nhánh hợp lệ
//! 4. `Havoc`: Quên giá trị cũ của các biến (phục vụ bất biến quy nạp cho vòng lặp)

use crate::ast::*;
use crate::verifier::PropertyCategory;
use std::collections::{HashMap, HashSet};

/// Biểu thức kiểm chứng toán học (hỗ trợ Biến số, Phép tính, và Lý thuyết Mảng / Bộ nhớ SMT)
#[derive(Debug, Clone, PartialEq)]
pub enum IvlExpr {
    Var(String),
    IntConst(i64),
    BoolConst(bool),
    Binary {
        op: BinOp,
        lhs: Box<IvlExpr>,
        rhs: Box<IvlExpr>,
        is_unsigned: bool,
    },
    /// Biểu thức điều kiện Phi-node: ite(cond, then_expr, else_expr)
    Ite {
        cond: Box<IvlExpr>,
        then_val: Box<IvlExpr>,
        else_val: Box<IvlExpr>,
    },
    Not(Box<IvlExpr>),
    BitNot(Box<IvlExpr>),
    Len(String),
    /// SMT Theory of Arrays: select(mem, offset) - Đọc từ ô nhớ
    Select {
        mem: String,
        offset: Box<IvlExpr>,
    },
    /// SMT Theory of Arrays: store(mem, offset, val) - Ghi vào ô nhớ tạo trạng thái bộ nhớ mới
    Store {
        mem: String,
        offset: Box<IvlExpr>,
        val: Box<IvlExpr>,
    },
    /// Cắt lấy 8-bit thấp (0..255) chuẩn SMT BitVec: (bvand val (_ bv255 64))
    Mask8(Box<IvlExpr>),
}

impl From<&Expr> for IvlExpr {
    fn from(e: &Expr) -> Self {
        let empty = HashSet::new();
        IvlLowerer::expr_to_ivl_typed(e, &empty)
    }
}

/// Vi lệnh kiểm chứng toán học nguyên tử
#[derive(Debug, Clone, PartialEq)]
pub enum IvlStmt {
    /// Gán giá trị: `dest := expr` (hỗ trợ cả biến vô hướng và toán đồ bộ nhớ Array Memory)
    Assign {
        dest: String,
        expr: IvlExpr,
        is_memory: bool,
    },
    /// Khẳng định chân lý: `assert cond`
    Assert {
        cond: IvlExpr,
        goal_name: String,
        category: PropertyCategory,
        loc: Loc,
    },
    /// Giả định tiên đề / nhánh rẽ: `assume cond`
    Assume {
        cond: IvlExpr,
    },
    /// Giải phóng biến thành tự do (Havoc): `havoc x, y, z`
    Havoc {
        vars: Vec<String>,
        is_memory: bool,
    },
    /// Ghi chú / debug trace
    Comment(String),
}

/// Bộ chuyển đổi toán học: hạ cấp Function trong Light sang các chuỗi kiểm chứng IVL
pub struct IvlLowerer;

impl IvlLowerer {
    pub fn operand_to_expr(op: &Operand) -> IvlExpr {
        match op {
            Operand::Reg(r) => IvlExpr::Var(r.trim_start_matches('%').to_string()),
            Operand::Const(v) => match v {
                Value::I64(n) => IvlExpr::IntConst(*n),
                Value::U64(n) => IvlExpr::IntConst(*n as i64),
                Value::F64(f) => IvlExpr::IntConst(*f as i64),
                Value::Bool(b) => IvlExpr::BoolConst(*b),
                Value::Ptr(p) => IvlExpr::IntConst(*p as i64),
                Value::Slice { len, .. } => IvlExpr::IntConst(*len as i64),
            },
        }
    }

    pub fn subst_expr(expr: &IvlExpr, from: &str, to: &IvlExpr) -> IvlExpr {
        let clean_from = from.trim_start_matches('%');
        match expr {
            IvlExpr::Var(v) => {
                if v.trim_start_matches('%') == clean_from {
                    to.clone()
                } else {
                    expr.clone()
                }
            }
            IvlExpr::IntConst(_) | IvlExpr::BoolConst(_) => expr.clone(),
            IvlExpr::Len(v) => {
                if v.trim_start_matches('%') == clean_from {
                    if let IvlExpr::Var(to_var) = to {
                        IvlExpr::Len(to_var.clone())
                    } else {
                        expr.clone()
                    }
                } else {
                    expr.clone()
                }
            }
            IvlExpr::Binary { op, lhs, rhs, is_unsigned } => IvlExpr::Binary {
                op: op.clone(),
                lhs: Box::new(Self::subst_expr(lhs, from, to)),
                rhs: Box::new(Self::subst_expr(rhs, from, to)),
                is_unsigned: *is_unsigned,
            },
            IvlExpr::Ite { cond, then_val, else_val } => IvlExpr::Ite {
                cond: Box::new(Self::subst_expr(cond, from, to)),
                then_val: Box::new(Self::subst_expr(then_val, from, to)),
                else_val: Box::new(Self::subst_expr(else_val, from, to)),
            },
            IvlExpr::Not(e) => IvlExpr::Not(Box::new(Self::subst_expr(e, from, to))),
            IvlExpr::BitNot(e) => IvlExpr::BitNot(Box::new(Self::subst_expr(e, from, to))),
            IvlExpr::Mask8(e) => IvlExpr::Mask8(Box::new(Self::subst_expr(e, from, to))),
            IvlExpr::Select { mem, offset } => {
                let clean_mem = mem.trim_start_matches('%');
                let new_mem = if clean_mem == clean_from {
                    if let IvlExpr::Var(to_var) = to {
                        to_var.clone()
                    } else {
                        mem.clone()
                    }
                } else {
                    mem.clone()
                };
                IvlExpr::Select {
                    mem: new_mem,
                    offset: Box::new(Self::subst_expr(offset, from, to)),
                }
            }
            IvlExpr::Store { mem, offset, val } => {
                let clean_mem = mem.trim_start_matches('%');
                let new_mem = if clean_mem == clean_from {
                    if let IvlExpr::Var(to_var) = to {
                        to_var.clone()
                    } else {
                        mem.clone()
                    }
                } else {
                    mem.clone()
                };
                IvlExpr::Store {
                    mem: new_mem,
                    offset: Box::new(Self::subst_expr(offset, from, to)),
                    val: Box::new(Self::subst_expr(val, from, to)),
                }
            }
        }
    }

    /// Thay thế đồng thời nhiều biến cùng lúc (tránh lỗi Variable Capture khi gọi hàm)
    pub fn subst_expr_map(expr: &IvlExpr, map: &HashMap<String, IvlExpr>) -> IvlExpr {
        match expr {
            IvlExpr::Var(v) => {
                let clean = v.trim_start_matches('%');
                if let Some(to) = map.get(clean) {
                    to.clone()
                } else {
                    expr.clone()
                }
            }
            IvlExpr::IntConst(_) | IvlExpr::BoolConst(_) => expr.clone(),
            IvlExpr::Len(v) => {
                let clean = v.trim_start_matches('%');
                let len_key = format!("{}_len", clean);
                if let Some(to_len) = map.get(&len_key) {
                    to_len.clone()
                } else if let Some(IvlExpr::Var(to_var)) = map.get(clean) {
                    IvlExpr::Len(to_var.clone())
                } else {
                    expr.clone()
                }
            }
            IvlExpr::Binary { op, lhs, rhs, is_unsigned } => IvlExpr::Binary {
                op: op.clone(),
                lhs: Box::new(Self::subst_expr_map(lhs, map)),
                rhs: Box::new(Self::subst_expr_map(rhs, map)),
                is_unsigned: *is_unsigned,
            },
            IvlExpr::Ite { cond, then_val, else_val } => IvlExpr::Ite {
                cond: Box::new(Self::subst_expr_map(cond, map)),
                then_val: Box::new(Self::subst_expr_map(then_val, map)),
                else_val: Box::new(Self::subst_expr_map(else_val, map)),
            },
            IvlExpr::Not(e) => IvlExpr::Not(Box::new(Self::subst_expr_map(e, map))),
            IvlExpr::BitNot(e) => IvlExpr::BitNot(Box::new(Self::subst_expr_map(e, map))),
            IvlExpr::Mask8(e) => IvlExpr::Mask8(Box::new(Self::subst_expr_map(e, map))),
            IvlExpr::Select { mem, offset } => {
                let clean_mem = mem.trim_start_matches('%');
                let new_mem = if let Some(IvlExpr::Var(to_var)) = map.get(clean_mem) {
                    to_var.clone()
                } else {
                    mem.clone()
                };
                IvlExpr::Select {
                    mem: new_mem,
                    offset: Box::new(Self::subst_expr_map(offset, map)),
                }
            }
            IvlExpr::Store { mem, offset, val } => {
                let clean_mem = mem.trim_start_matches('%');
                let new_mem = if let Some(IvlExpr::Var(to_var)) = map.get(clean_mem) {
                    to_var.clone()
                } else {
                    mem.clone()
                };
                IvlExpr::Store {
                    mem: new_mem,
                    offset: Box::new(Self::subst_expr_map(offset, map)),
                    val: Box::new(Self::subst_expr_map(val, map)),
                }
            }
        }
    }

    /// Thu thập danh sách các biến/tham số có kiểu số nguyên không dấu (u64 / u8)
    pub fn collect_unsigned_vars(func: &Function) -> HashSet<String> {
        let mut unsigned = HashSet::new();
        if matches!(func.return_ty, Some(Type::U64 | Type::U8)) {
            unsigned.insert("ret".to_string());
            unsigned.insert("%ret".to_string());
        }
        for p in &func.params {
            if matches!(p.ty, Type::U64 | Type::U8) {
                let clean = p.name.trim_start_matches('%').to_string();
                unsigned.insert(clean.clone());
                unsigned.insert(format!("%{}", clean));
            }
        }
        for si in &func.instructions {
            match &si.inst {
                Instruction::AssignConst { dest, ty, val } => {
                    if matches!(ty, Type::U64 | Type::U8) || matches!(val, Value::U64(_)) {
                        let clean = dest.trim_start_matches('%').to_string();
                        unsigned.insert(clean.clone());
                        unsigned.insert(format!("%{}", clean));
                    }
                }
                Instruction::Binary { dest, ty, .. } => {
                    if matches!(ty, Type::U64 | Type::U8) {
                        let clean = dest.trim_start_matches('%').to_string();
                        unsigned.insert(clean.clone());
                        unsigned.insert(format!("%{}", clean));
                    }
                }
                Instruction::Load8 { dest, .. } => {
                    let clean = dest.trim_start_matches('%').to_string();
                    unsigned.insert(clean.clone());
                    unsigned.insert(format!("%{}", clean));
                }
                Instruction::AllocSlice { dest, elem_ty, .. } => {
                    if matches!(elem_ty, Type::U64 | Type::U8) {
                        let clean = dest.trim_start_matches('%').to_string();
                        unsigned.insert(clean.clone());
                        unsigned.insert(format!("%{}", clean));
                    }
                }
                _ => {}
            }
        }
        unsigned
    }

    /// Kiểm tra biểu thức có chứa biến hoặc hằng số không dấu hay không
    pub fn expr_has_unsigned(e: &Expr, unsigned_vars: &HashSet<String>) -> bool {
        match e {
            Expr::Var(v) => {
                let clean = v.trim_start_matches('%');
                unsigned_vars.contains(v) || unsigned_vars.contains(clean) || unsigned_vars.contains(&format!("%{}", clean))
            }
            Expr::Binary { lhs, rhs, .. } => {
                Self::expr_has_unsigned(lhs, unsigned_vars) || Self::expr_has_unsigned(rhs, unsigned_vars)
            }
            Expr::Not(inner) => Self::expr_has_unsigned(inner, unsigned_vars),
            Expr::IntConst(n) => (*n as u64) > (i64::MAX as u64),
            Expr::Len(_) | Expr::FloatConst(_) | Expr::BoolConst(_) => false,
        }
    }

    /// Hạ cấp biểu thức Expr sang IvlExpr có xét kiểu dấu (signed vs unsigned) cho các phép toán
    pub fn expr_to_ivl_typed(e: &Expr, unsigned_vars: &HashSet<String>) -> IvlExpr {
        match e {
            Expr::Var(v) => IvlExpr::Var(v.clone()),
            Expr::IntConst(n) => IvlExpr::IntConst(*n),
            Expr::FloatConst(f) => IvlExpr::IntConst(*f as i64),
            Expr::BoolConst(b) => IvlExpr::BoolConst(*b),
            Expr::Len(v) => IvlExpr::Len(v.clone()),
            Expr::Binary { op, lhs, rhs } => {
                let is_unsigned = match op {
                    BinOp::Lt | BinOp::Lte | BinOp::Gt | BinOp::Gte | BinOp::Div | BinOp::Mod => {
                        Self::expr_has_unsigned(lhs, unsigned_vars) || Self::expr_has_unsigned(rhs, unsigned_vars)
                    }
                    _ => false,
                };
                IvlExpr::Binary {
                    op: op.clone(),
                    lhs: Box::new(Self::expr_to_ivl_typed(lhs, unsigned_vars)),
                    rhs: Box::new(Self::expr_to_ivl_typed(rhs, unsigned_vars)),
                    is_unsigned,
                }
            }
            Expr::Not(inner) => IvlExpr::Not(Box::new(Self::expr_to_ivl_typed(inner, unsigned_vars))),
        }
    }

    /// Thu thập tất cả các biến bị sửa đổi trong một dải lệnh
    pub fn collect_modified_vars(
        instructions: &[SpannedInstruction],
        aliases: Option<&HashMap<String, String>>,
    ) -> HashSet<String> {
        let mut modified = HashSet::new();
        for si in instructions {
            match &si.inst {
                Instruction::AssignConst { dest, .. }
                | Instruction::Binary { dest, .. }
                | Instruction::Not { dest, .. }
                | Instruction::SliceLen { dest, .. }
                | Instruction::Load8 { dest, .. }
                | Instruction::Load64 { dest, .. } => {
                    modified.insert(dest.trim_start_matches('%').to_string());
                }
                Instruction::Alloc { dest, .. }
                | Instruction::AllocSlice { dest, .. } => {
                    let clean = dest.trim_start_matches('%').to_string();
                    modified.insert(clean.clone());
                    modified.insert(format!("{}_len", clean));
                }
                Instruction::Mov { dest, .. }
                | Instruction::SlicePtr { dest, .. } => {
                    let clean = dest.trim_start_matches('%').to_string();
                    modified.insert(clean.clone());
                    if aliases.is_some_and(|a| a.contains_key(&clean) || a.contains_key(dest)) {
                        modified.insert(format!("{}_len", clean));
                    }
                }
                Instruction::Call { dest: Some(dest), .. }
                | Instruction::Syscall { dest: Some(dest), .. } => {
                    modified.insert(dest.trim_start_matches('%').to_string());
                }
                _ => {}
            }
        }
        modified
    }

    /// Thu thập bí danh các buffer (kể cả tham số slice<T>: %ptr = SLICE_PTR s hoặc %alias = MOV s)
    pub fn extract_buffer_aliases(func: &Function) -> HashMap<String, String> {
        let mut aliases = HashMap::new();
        let buffer_sizes = Self::extract_buffer_sizes(func);
        let slice_params: HashSet<String> = func
            .params
            .iter()
            .filter(|p| matches!(p.ty, Type::Slice(_) | Type::Array(_, _)))
            .map(|p| p.name.trim_start_matches('%').to_string())
            .collect();

        for sp in &slice_params {
            aliases.insert(sp.clone(), sp.clone());
            aliases.insert(format!("%{}", sp), sp.clone());
        }

        let mut changed = true;
        while changed {
            changed = false;
            for s_inst in &func.instructions {
                match &s_inst.inst {
                    Instruction::SlicePtr { dest, slice } => {
                        let s_clean = slice.trim_start_matches('%').to_string();
                        let d_clean = dest.trim_start_matches('%').to_string();
                        let root = aliases
                            .get(slice)
                            .or_else(|| aliases.get(&s_clean))
                            .cloned()
                            .unwrap_or_else(|| s_clean.clone());
                        if !aliases.contains_key(&d_clean) {
                            aliases.insert(dest.clone(), root.clone());
                            aliases.insert(d_clean, root);
                            changed = true;
                        }
                    }
                    Instruction::Mov { dest, src } => {
                        let s_clean = src.trim_start_matches('%').to_string();
                        let d_clean = dest.trim_start_matches('%').to_string();
                        if let Some(root) = aliases.get(src).or_else(|| aliases.get(&s_clean)).cloned() {
                            if !aliases.contains_key(&d_clean) {
                                aliases.insert(dest.clone(), root.clone());
                                aliases.insert(d_clean, root);
                                changed = true;
                            }
                        } else if buffer_sizes.contains_key(src) || buffer_sizes.contains_key(&s_clean) || slice_params.contains(&s_clean) {
                            if !aliases.contains_key(&d_clean) {
                                aliases.insert(dest.clone(), s_clean.clone());
                                aliases.insert(d_clean, s_clean);
                                changed = true;
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        aliases
    }

    /// Thu thập tất cả các bộ đệm bộ nhớ bị ghi trong một dải lệnh
    pub fn collect_modified_mems(instructions: &[SpannedInstruction], aliases: Option<&HashMap<String, String>>) -> HashSet<String> {
        let mut modified = HashSet::new();
        for si in instructions {
            match &si.inst {
                Instruction::Store8 { buf, .. }
                | Instruction::Store64 { buf, .. }
                | Instruction::StoreStr { buf, .. } => {
                    let root = if let Some(als) = aliases {
                        als.get(buf).unwrap_or(buf)
                    } else {
                        buf
                    };
                    modified.insert(root.trim_start_matches('%').to_string());
                }
                _ => {}
            }
        }
        modified
    }

    /// Thu thập độ dài các buffer tĩnh và lan truyền qua các bí danh
    pub fn extract_buffer_sizes(func: &Function) -> HashMap<String, usize> {
        let mut buffer_sizes = HashMap::new();
        for s_inst in &func.instructions {
            match &s_inst.inst {
                Instruction::Alloc { dest, size } => {
                    let clean = dest.trim_start_matches('%').to_string();
                    buffer_sizes.insert(dest.clone(), *size);
                    buffer_sizes.insert(clean, *size);
                }
                Instruction::AllocSlice { dest, len, .. } => {
                    let clean = dest.trim_start_matches('%').to_string();
                    buffer_sizes.insert(dest.clone(), *len);
                    buffer_sizes.insert(clean, *len);
                }
                _ => {}
            }
        }

        let mut changed = true;
        while changed {
            changed = false;
            for s_inst in &func.instructions {
                match &s_inst.inst {
                    Instruction::SlicePtr { dest, slice } => {
                        let s_clean = slice.trim_start_matches('%');
                        let d_clean = dest.trim_start_matches('%').to_string();
                        if let Some(&sz) = buffer_sizes.get(slice).or_else(|| buffer_sizes.get(s_clean)) {
                            if !buffer_sizes.contains_key(&d_clean) {
                                buffer_sizes.insert(dest.clone(), sz);
                                buffer_sizes.insert(d_clean, sz);
                                changed = true;
                            }
                        }
                    }
                    Instruction::Mov { dest, src } => {
                        let s_clean = src.trim_start_matches('%');
                        let d_clean = dest.trim_start_matches('%').to_string();
                        if let Some(&sz) = buffer_sizes.get(src).or_else(|| buffer_sizes.get(s_clean)) {
                            if !buffer_sizes.contains_key(&d_clean) {
                                buffer_sizes.insert(dest.clone(), sz);
                                buffer_sizes.insert(d_clean, sz);
                                changed = true;
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        buffer_sizes
    }

    /// Hạ cấp một lệnh đơn lẻ thành chuỗi vi lệnh IVL
    pub fn lower_inst(
        si: &SpannedInstruction,
        buffer_sizes: &HashMap<String, usize>,
        buffer_aliases: Option<&HashMap<String, String>>,
    ) -> Vec<IvlStmt> {
        let mut stmts = Vec::new();
        let resolve_buf = |b: &str| -> String {
            buffer_aliases
                .and_then(|a| a.get(b))
                .cloned()
                .unwrap_or_else(|| b.to_string())
        };
        match &si.inst {
            Instruction::AssignConst { dest, val, .. } => {
                stmts.push(IvlStmt::Assign {
                    dest: dest.clone(),
                    expr: Self::operand_to_expr(&Operand::Const(val.clone())),
                    is_memory: false,
                });
            }
            Instruction::Mov { dest, src } => {
                let s_clean = src.trim_start_matches('%');
                let d_clean = dest.trim_start_matches('%');
                if buffer_sizes.contains_key(s_clean)
                    || buffer_sizes.contains_key(src)
                    || buffer_aliases.map(|a| a.contains_key(s_clean) || a.contains_key(src)).unwrap_or(false)
                {
                    stmts.push(IvlStmt::Assign {
                        dest: dest.clone(),
                        expr: IvlExpr::IntConst(0),
                        is_memory: false,
                    });
                    let actual_src = resolve_buf(src);
                    let actual_clean = actual_src.trim_start_matches('%');
                    let len_expr = if let Some(&sz) = buffer_sizes.get(&actual_src).or_else(|| buffer_sizes.get(src)) {
                        IvlExpr::IntConst(sz as i64)
                    } else {
                        IvlExpr::Var(format!("{}_len", actual_clean))
                    };
                    stmts.push(IvlStmt::Assign {
                        dest: format!("{}_len", d_clean),
                        expr: len_expr,
                        is_memory: false,
                    });
                } else {
                    stmts.push(IvlStmt::Assign {
                        dest: dest.clone(),
                        expr: IvlExpr::Var(s_clean.to_string()),
                        is_memory: false,
                    });
                }
            }
            Instruction::Binary { op, ty, dest, src1, src2 } => {
                let e1 = Self::operand_to_expr(src1);
                let e2 = Self::operand_to_expr(src2);
                let is_unsigned = matches!(ty, Type::U64 | Type::U8);
                stmts.push(IvlStmt::Assign {
                    dest: dest.clone(),
                    expr: IvlExpr::Binary {
                        op: op.clone(),
                        lhs: Box::new(e1),
                        rhs: Box::new(e2),
                        is_unsigned,
                    },
                    is_memory: false,
                });
            }
            Instruction::Not { dest, ty, src } => {
                let e = Self::operand_to_expr(src);
                let expr = if matches!(ty, Type::Bool) {
                    IvlExpr::Not(Box::new(e))
                } else {
                    IvlExpr::BitNot(Box::new(e))
                };
                stmts.push(IvlStmt::Assign {
                    dest: dest.clone(),
                    expr,
                    is_memory: false,
                });
            }
            Instruction::AllocSlice { dest, len, .. } => {
                let clean = dest.trim_start_matches('%');
                stmts.push(IvlStmt::Assign {
                    dest: format!("{}_len", clean),
                    expr: IvlExpr::IntConst(*len as i64),
                    is_memory: false,
                });
            }
            Instruction::SliceLen { dest, slice } => {
                let actual_slice = resolve_buf(slice);
                let sl_clean = slice.trim_start_matches('%');
                if let Some(&size) = buffer_sizes.get(&actual_slice).or_else(|| buffer_sizes.get(slice)) {
                    stmts.push(IvlStmt::Assign {
                        dest: dest.clone(),
                        expr: IvlExpr::IntConst(size as i64),
                        is_memory: false,
                    });
                } else {
                    stmts.push(IvlStmt::Assign {
                        dest: dest.clone(),
                        expr: IvlExpr::Var(format!("{}_len", sl_clean)),
                        is_memory: false,
                    });
                }
            }
            Instruction::SlicePtr { dest, slice } => {
                let s_clean = slice.trim_start_matches('%');
                let d_clean = dest.trim_start_matches('%');
                if buffer_sizes.contains_key(s_clean)
                    || buffer_sizes.contains_key(slice)
                    || buffer_aliases.map(|a| a.contains_key(s_clean) || a.contains_key(slice)).unwrap_or(false)
                {
                    stmts.push(IvlStmt::Assign {
                        dest: dest.clone(),
                        expr: IvlExpr::IntConst(0),
                        is_memory: false,
                    });
                    let actual_src = resolve_buf(slice);
                    let actual_clean = actual_src.trim_start_matches('%');
                    let len_expr = if let Some(&sz) = buffer_sizes.get(&actual_src).or_else(|| buffer_sizes.get(slice)) {
                        IvlExpr::IntConst(sz as i64)
                    } else {
                        IvlExpr::Var(format!("{}_len", actual_clean))
                    };
                    stmts.push(IvlStmt::Assign {
                        dest: format!("{}_len", d_clean),
                        expr: len_expr,
                        is_memory: false,
                    });
                } else {
                    stmts.push(IvlStmt::Assign {
                        dest: dest.clone(),
                        expr: IvlExpr::Var(s_clean.to_string()),
                        is_memory: false,
                    });
                }
            }
            Instruction::Load8 { dest, buf, offset } => {
                let actual_buf = resolve_buf(buf);
                let off_expr = Self::operand_to_expr(offset);
                stmts.push(IvlStmt::Assign {
                    dest: dest.clone(),
                    expr: IvlExpr::Mask8(Box::new(IvlExpr::Select {
                        mem: actual_buf,
                        offset: Box::new(off_expr),
                    })),
                    is_memory: false,
                });
                let clean_d = dest.trim_start_matches('%');
                stmts.push(IvlStmt::Assume {
                    cond: IvlExpr::Binary {
                        op: BinOp::And,
                        lhs: Box::new(IvlExpr::Binary {
                            op: BinOp::Gte,
                            lhs: Box::new(IvlExpr::Var(clean_d.to_string())),
                            rhs: Box::new(IvlExpr::IntConst(0)),
                            is_unsigned: false,
                        }),
                        rhs: Box::new(IvlExpr::Binary {
                            op: BinOp::Lte,
                            lhs: Box::new(IvlExpr::Var(clean_d.to_string())),
                            rhs: Box::new(IvlExpr::IntConst(255)),
                            is_unsigned: false,
                        }),
                        is_unsigned: false,
                    },
                });
            }
            Instruction::Store8 { buf, offset, val } => {
                let actual_buf = resolve_buf(buf);
                let off_expr = Self::operand_to_expr(offset);
                let val_expr = Self::operand_to_expr(val);
                stmts.push(IvlStmt::Assign {
                    dest: actual_buf.clone(),
                    expr: IvlExpr::Store {
                        mem: actual_buf,
                        offset: Box::new(off_expr),
                        val: Box::new(IvlExpr::Mask8(Box::new(val_expr))),
                    },
                    is_memory: true,
                });
            }
            Instruction::Load64 { dest, buf, offset } => {
                let actual_buf = resolve_buf(buf);
                let off_expr = Self::operand_to_expr(offset);
                stmts.push(IvlStmt::Assign {
                    dest: dest.clone(),
                    expr: IvlExpr::Select {
                        mem: actual_buf,
                        offset: Box::new(off_expr),
                    },
                    is_memory: false,
                });
            }
            Instruction::Store64 { buf, offset, val } => {
                let actual_buf = resolve_buf(buf);
                let off_expr = Self::operand_to_expr(offset);
                let val_expr = Self::operand_to_expr(val);
                stmts.push(IvlStmt::Assign {
                    dest: actual_buf.clone(),
                    expr: IvlExpr::Store {
                        mem: actual_buf,
                        offset: Box::new(off_expr),
                        val: Box::new(val_expr),
                    },
                    is_memory: true,
                });
            }
            Instruction::StoreStr { buf, offset, content } => {
                let actual_buf = resolve_buf(buf);
                let bytes = content.as_bytes();
                for (i, &b) in bytes.iter().enumerate() {
                    let off_expr = IvlExpr::IntConst((*offset + i) as i64);
                    let val_expr = IvlExpr::IntConst(b as i64);
                    stmts.push(IvlStmt::Assign {
                        dest: actual_buf.clone(),
                        expr: IvlExpr::Store {
                            mem: actual_buf.clone(),
                            offset: Box::new(off_expr),
                            val: Box::new(val_expr),
                        },
                        is_memory: true,
                    });
                }
            }
            Instruction::Alloc { dest, size } => {
                let clean = dest.trim_start_matches('%');
                stmts.push(IvlStmt::Assign {
                    dest: format!("{}_len", clean),
                    expr: IvlExpr::IntConst(*size as i64),
                    is_memory: false,
                });
            }
            Instruction::Syscall { dest, rax, rdi, rsi, rdx, r10, r8, r9 } => {
                let target = dest.clone().or_else(|| Some("%rax".to_string()));
                if let Some(d) = target {
                    let clean_d = d.trim_start_matches('%').to_string();
                    stmts.push(IvlStmt::Havoc {
                        vars: vec![clean_d.clone()],
                        is_memory: false,
                    });
                    // Mô hình hóa khế ước hệ điều hành Linux Kernel x86_64:
                    // 1. Mọi syscall khi lỗi đều trả về trong khoảng -4095..-1 (tức luôn >= -4096)
                    stmts.push(IvlStmt::Assume {
                        cond: IvlExpr::Binary {
                            op: BinOp::Gte,
                            lhs: Box::new(IvlExpr::Var(clean_d.clone())),
                            rhs: Box::new(IvlExpr::IntConst(-4096)),
                            is_unsigned: false,
                        },
                    });
                    // 2. sys_read (rax=0) và sys_write (rax=1) không bao giờ đọc/ghi vượt quá count (rdx)
                    let rax_expr = Self::operand_to_expr(rax);
                    let rdx_expr = Self::operand_to_expr(rdx);
                    let is_read_or_write = IvlExpr::Binary {
                        op: BinOp::Or,
                        lhs: Box::new(IvlExpr::Binary {
                            op: BinOp::Eq,
                            lhs: Box::new(rax_expr.clone()),
                            rhs: Box::new(IvlExpr::IntConst(0)),
                            is_unsigned: false,
                        }),
                        rhs: Box::new(IvlExpr::Binary {
                            op: BinOp::Eq,
                            lhs: Box::new(rax_expr),
                            rhs: Box::new(IvlExpr::IntConst(1)),
                            is_unsigned: false,
                        }),
                        is_unsigned: false,
                    };
                    let lte_count = IvlExpr::Binary {
                        op: BinOp::Lte,
                        lhs: Box::new(IvlExpr::Var(clean_d)),
                        rhs: Box::new(rdx_expr),
                        is_unsigned: false,
                    };
                    stmts.push(IvlStmt::Assume {
                        cond: IvlExpr::Ite {
                            cond: Box::new(is_read_or_write),
                            then_val: Box::new(lte_count),
                            else_val: Box::new(IvlExpr::BoolConst(true)),
                        },
                    });
                }

                // Havoc buffer memory for any buffer passed in syscall arguments (rdi, rsi, rdx, r10, r8, r9)
                let mut havoc_mems = Vec::new();
                for arg_opt in [Some(rdi), Some(rsi), Some(rdx), r10.as_ref(), r8.as_ref(), r9.as_ref()] {
                    if let Some(Operand::Reg(r)) = arg_opt {
                        let actual = buffer_aliases.and_then(|a| a.get(r)).unwrap_or(r);
                        let clean = actual.trim_start_matches('%').to_string();
                        if buffer_sizes.contains_key(actual)
                            || buffer_sizes.contains_key(r)
                            || buffer_sizes.contains_key(&clean)
                            || buffer_aliases.map_or(false, |a| a.contains_key(r) || a.contains_key(&clean))
                        {
                            if !havoc_mems.contains(&clean) {
                                havoc_mems.push(clean);
                            }
                        }
                    }
                }
                if !havoc_mems.is_empty() {
                    stmts.push(IvlStmt::Havoc {
                        vars: havoc_mems,
                        is_memory: true,
                    });
                }
            }
            _ => {}
        }
        stmts
    }
}
