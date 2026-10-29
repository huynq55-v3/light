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
    },
    Not(Box<IvlExpr>),
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
}

impl From<&Expr> for IvlExpr {
    fn from(e: &Expr) -> Self {
        match e {
            Expr::Var(v) => IvlExpr::Var(v.clone()),
            Expr::IntConst(n) => IvlExpr::IntConst(*n),
            Expr::FloatConst(f) => IvlExpr::IntConst(*f as i64),
            Expr::BoolConst(b) => IvlExpr::BoolConst(*b),
            Expr::Len(v) => IvlExpr::Len(v.clone()),
            Expr::Binary { op, lhs, rhs } => IvlExpr::Binary {
                op: op.clone(),
                lhs: Box::new(IvlExpr::from(lhs.as_ref())),
                rhs: Box::new(IvlExpr::from(rhs.as_ref())),
            },
            Expr::Not(inner) => IvlExpr::Not(Box::new(IvlExpr::from(inner.as_ref()))),
        }
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
            IvlExpr::Binary { op, lhs, rhs } => IvlExpr::Binary {
                op: op.clone(),
                lhs: Box::new(Self::subst_expr(lhs, from, to)),
                rhs: Box::new(Self::subst_expr(rhs, from, to)),
            },
            IvlExpr::Not(e) => IvlExpr::Not(Box::new(Self::subst_expr(e, from, to))),
            IvlExpr::Select { mem, offset } => IvlExpr::Select {
                mem: mem.clone(),
                offset: Box::new(Self::subst_expr(offset, from, to)),
            },
            IvlExpr::Store { mem, offset, val } => IvlExpr::Store {
                mem: mem.clone(),
                offset: Box::new(Self::subst_expr(offset, from, to)),
                val: Box::new(Self::subst_expr(val, from, to)),
            },
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

    /// Thu thập độ dài các buffer tĩnh và lan truyền qua các bí danh
    pub fn extract_buffer_sizes(func: &Function) -> HashMap<String, usize> {
        let mut buffer_sizes = HashMap::new();
        for s_inst in &func.instructions {
            match &s_inst.inst {
                Instruction::Alloc { dest, size } => {
                    buffer_sizes.insert(dest.clone(), *size);
                }
                Instruction::AllocSlice { dest, len, .. } => {
                    buffer_sizes.insert(dest.clone(), *len);
                }
                Instruction::SlicePtr { dest, slice } => {
                    if let Some(&sz) = buffer_sizes.get(slice) {
                        buffer_sizes.insert(dest.clone(), sz);
                    }
                }
                Instruction::Mov { dest, src } => {
                    if let Some(&sz) = buffer_sizes.get(src) {
                        buffer_sizes.insert(dest.clone(), sz);
                    }
                }
                _ => {}
            }
        }
        buffer_sizes
    }

    /// Hạ cấp một lệnh đơn lẻ thành chuỗi vi lệnh IVL
    pub fn lower_inst(si: &SpannedInstruction, buffer_sizes: &HashMap<String, usize>) -> Vec<IvlStmt> {
        let mut stmts = Vec::new();
        match &si.inst {
            Instruction::AssignConst { dest, val, .. } => {
                stmts.push(IvlStmt::Assign {
                    dest: dest.clone(),
                    expr: Self::operand_to_expr(&Operand::Const(val.clone())),
                    is_memory: false,
                });
            }
            Instruction::Mov { dest, src } => {
                stmts.push(IvlStmt::Assign {
                    dest: dest.clone(),
                    expr: IvlExpr::Var(src.trim_start_matches('%').to_string()),
                    is_memory: false,
                });
            }
            Instruction::Binary { op, dest, src1, src2, .. } => {
                let e1 = Self::operand_to_expr(src1);
                let e2 = Self::operand_to_expr(src2);
                stmts.push(IvlStmt::Assign {
                    dest: dest.clone(),
                    expr: IvlExpr::Binary {
                        op: op.clone(),
                        lhs: Box::new(e1),
                        rhs: Box::new(e2),
                    },
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
                let s_clean = slice.trim_start_matches('%');
                if let Some(&size) = buffer_sizes.get(slice) {
                    stmts.push(IvlStmt::Assign {
                        dest: dest.clone(),
                        expr: IvlExpr::IntConst(size as i64),
                        is_memory: false,
                    });
                } else {
                    stmts.push(IvlStmt::Assign {
                        dest: dest.clone(),
                        expr: IvlExpr::Var(format!("{}_len", s_clean)),
                        is_memory: false,
                    });
                }
            }
            Instruction::SlicePtr { dest, slice } => {
                stmts.push(IvlStmt::Assign {
                    dest: dest.clone(),
                    expr: IvlExpr::Var(slice.trim_start_matches('%').to_string()),
                    is_memory: false,
                });
            }
            Instruction::Load8 { dest, buf, offset } => {
                let off_expr = Self::operand_to_expr(offset);
                stmts.push(IvlStmt::Assign {
                    dest: dest.clone(),
                    expr: IvlExpr::Select {
                        mem: buf.clone(),
                        offset: Box::new(off_expr),
                    },
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
                        }),
                        rhs: Box::new(IvlExpr::Binary {
                            op: BinOp::Lte,
                            lhs: Box::new(IvlExpr::Var(clean_d.to_string())),
                            rhs: Box::new(IvlExpr::IntConst(255)),
                        }),
                    },
                });
            }
            Instruction::Store8 { buf, offset, val } => {
                let off_expr = Self::operand_to_expr(offset);
                let val_expr = Self::operand_to_expr(val);
                stmts.push(IvlStmt::Assign {
                    dest: buf.clone(),
                    expr: IvlExpr::Store {
                        mem: buf.clone(),
                        offset: Box::new(off_expr),
                        val: Box::new(val_expr),
                    },
                    is_memory: true,
                });
            }
            Instruction::Load64 { dest, buf, offset } => {
                let off_expr = Self::operand_to_expr(offset);
                stmts.push(IvlStmt::Assign {
                    dest: dest.clone(),
                    expr: IvlExpr::Select {
                        mem: buf.clone(),
                        offset: Box::new(off_expr),
                    },
                    is_memory: false,
                });
            }
            Instruction::Store64 { buf, offset, val } => {
                let off_expr = Self::operand_to_expr(offset);
                let val_expr = Self::operand_to_expr(val);
                stmts.push(IvlStmt::Assign {
                    dest: buf.clone(),
                    expr: IvlExpr::Store {
                        mem: buf.clone(),
                        offset: Box::new(off_expr),
                        val: Box::new(val_expr),
                    },
                    is_memory: true,
                });
            }
            Instruction::Alloc { dest, size } => {
                let clean = dest.trim_start_matches('%');
                stmts.push(IvlStmt::Assign {
                    dest: format!("{}_len", clean),
                    expr: IvlExpr::IntConst(*size as i64),
                    is_memory: false,
                });
            }
            _ => {}
        }
        stmts
    }
}
