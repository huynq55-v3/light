#![allow(dead_code)]
//! Intermediate Verification Language (IVL) & Control Flow Graph (CFG)
//! Lấy cảm hứng từ kiến trúc Boogie (Microsoft Research) & Why3 (INRIA).
//!
//! Toàn bộ chương trình được hạ cấp (Lowering) thành đồ thị CFG với chỉ đúng 4 vi lệnh toán học:
//! 1. `Assign`: Gán biểu thức giá trị toán học thuần túy
//! 2. `Assert`: Khẳng định một thuộc tính phải đúng (nếu sai -> Báo lỗi & counter-example)
//! 3. `Assume`: Giả định tiền đề hoặc điều kiện rẽ nhánh hợp lệ
//! 4. `Havoc`: Quên giá trị cũ của các biến (phục vụ bất biến quy nạp cho vòng lặp)

use crate::ast::*;
use crate::verifier::PropertyCategory;
use std::collections::{HashMap, HashSet};

/// Vi lệnh kiểm chứng toán học nguyên tử
#[derive(Debug, Clone, PartialEq)]
pub enum IvlStmt {
    /// Gán giá trị: `dest := expr`
    Assign {
        dest: String,
        expr: Expr,
    },
    /// Khẳng định chân lý: `assert cond`
    Assert {
        cond: Expr,
        goal_name: String,
        category: PropertyCategory,
        loc: Loc,
    },
    /// Giả định tiên đề / nhánh rẽ: `assume cond`
    Assume {
        cond: Expr,
    },
    /// Giải phóng biến thành tự do (Havoc): `havoc x, y, z`
    Havoc {
        vars: Vec<String>,
    },
    /// Ghi chú / debug trace
    Comment(String),
}

/// Khối cơ bản (Basic Block) trong đồ thị luồng điều khiển CFG
#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub id: String,
    pub stmts: Vec<IvlStmt>,
    pub successors: Vec<String>,
}

impl BasicBlock {
    pub fn new(id: impl Into<String>) -> Self {
        Self {
            id: id.into(),
            stmts: Vec::new(),
            successors: Vec::new(),
        }
    }

    pub fn push(&mut self, stmt: IvlStmt) {
        self.stmts.push(stmt);
    }
}

/// Đồ thị luồng điều khiển của một hàm
#[derive(Debug, Clone)]
pub struct CfgGraph {
    pub func_name: String,
    pub entry: String,
    pub blocks: HashMap<String, BasicBlock>,
    pub order: Vec<String>,
}

impl CfgGraph {
    pub fn new(func_name: impl Into<String>, entry: impl Into<String>) -> Self {
        let entry_str = entry.into();
        let mut blocks = HashMap::new();
        blocks.insert(entry_str.clone(), BasicBlock::new(entry_str.clone()));
        Self {
            func_name: func_name.into(),
            entry: entry_str.clone(),
            blocks,
            order: vec![entry_str],
        }
    }

    pub fn block_mut(&mut self, id: &str) -> &mut BasicBlock {
        self.blocks.get_mut(id).expect("Block must exist in CFG")
    }

    pub fn add_block(&mut self, id: impl Into<String>) -> &mut BasicBlock {
        let id_str = id.into();
        if !self.blocks.contains_key(&id_str) {
            self.order.push(id_str.clone());
            self.blocks.insert(id_str.clone(), BasicBlock::new(id_str.clone()));
        }
        self.blocks.get_mut(&id_str).unwrap()
    }

    pub fn add_edge(&mut self, from: &str, to: &str) {
        if let Some(b) = self.blocks.get_mut(from) {
            if !b.successors.contains(&to.to_string()) {
                b.successors.push(to.to_string());
            }
        }
    }
}

/// Bộ chuyển đổi toán học: hạ cấp Function trong Light sang đồ thị CFG chứa các lệnh IVL
pub struct IvlLowerer;

impl IvlLowerer {
    pub fn operand_to_expr(op: &Operand) -> Expr {
        match op {
            Operand::Reg(r) => Expr::Var(r.trim_start_matches('%').to_string()),
            Operand::Const(v) => match v {
                Value::I64(n) => Expr::IntConst(*n),
                Value::U64(n) => Expr::IntConst(*n as i64),
                Value::F64(f) => Expr::FloatConst(*f),
                Value::Bool(b) => Expr::BoolConst(*b),
                Value::Ptr(p) => Expr::IntConst(*p as i64),
                Value::Slice { len, .. } => Expr::IntConst(*len as i64),
            },
        }
    }

    pub fn subst_expr(expr: &Expr, from: &str, to: &Expr) -> Expr {
        let clean_from = from.trim_start_matches('%');
        match expr {
            Expr::Var(v) => {
                if v.trim_start_matches('%') == clean_from {
                    to.clone()
                } else {
                    expr.clone()
                }
            }
            Expr::IntConst(_) | Expr::FloatConst(_) | Expr::BoolConst(_) => expr.clone(),
            Expr::Len(v) => {
                if v.trim_start_matches('%') == clean_from {
                    if let Expr::Var(to_var) = to {
                        Expr::Len(to_var.clone())
                    } else {
                        expr.clone()
                    }
                } else {
                    expr.clone()
                }
            }
            Expr::Binary { op, lhs, rhs } => Expr::Binary {
                op: op.clone(),
                lhs: Box::new(Self::subst_expr(lhs, from, to)),
                rhs: Box::new(Self::subst_expr(rhs, from, to)),
            },
            Expr::Not(e) => Expr::Not(Box::new(Self::subst_expr(e, from, to))),
        }
    }

    /// Thu thập tất cả các biến bị sửa đổi trong một dải lệnh
    pub fn collect_modified_vars(instructions: &[SpannedInstruction]) -> HashSet<String> {
        let mut modified = HashSet::new();
        for si in instructions {
            match &si.inst {
                Instruction::AssignConst { dest, .. }
                | Instruction::Mov { dest, .. }
                | Instruction::Binary { dest, .. }
                | Instruction::AllocSlice { dest, .. }
                | Instruction::SlicePtr { dest, .. }
                | Instruction::SliceLen { dest, .. }
                | Instruction::Load8 { dest, .. }
                | Instruction::Load64 { dest, .. } => {
                    modified.insert(dest.trim_start_matches('%').to_string());
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
}
