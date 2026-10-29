#![allow(dead_code)]
//! Universal Verification Condition Generator (VCGen)
//! Thực thi kiểm chứng toán học thuần túy trên các vi lệnh IVL (`Assign`, `Assume`, `Havoc`, `Assert`).
//!
//! Nguyên lý hoạt động:
//! - Duyệt qua chuỗi vi lệnh IVL.
//! - `Assign`: Cập nhật trạng thái SSA và gắn ràng buộc giá trị trong SMT.
//! - `Assume`: Bổ sung điều kiện tiên đề / nhánh rẽ vào tiền đề của solver.
//! - `Havoc`: Quên giá trị cũ của biến, tạo biến tự do ngẫu nhiên mới trong SMT.
//! - `Assert`: Sinh truy vấn SMT phủ định mệnh đề và gọi Z3 để chứng minh (UNSAT = Verified).

use crate::ast::*;
use crate::ivl::IvlStmt;
#[allow(unused_imports)]
pub use crate::verifier::PropertyCategory;
use crate::verifier::{StackFrame, VerificationResult, Verifier};
use std::collections::{HashMap, HashSet};

pub struct VcGen {
    pub declared: HashSet<String>,
    pub current_val: HashMap<String, String>,
    pub assertions_smt: Vec<String>,
    pub step_counter: usize,
}

impl VcGen {
    pub fn new() -> Self {
        Self {
            declared: HashSet::new(),
            current_val: HashMap::new(),
            assertions_smt: Vec::new(),
            step_counter: 0,
        }
    }

    /// Định nghĩa hằng số 64-bit an toàn chuẩn SMT-LIB2 QF_BV (hỗ trợ cả số âm)
    pub fn smt_bv64(n: i64) -> String {
        if n >= 0 {
            format!("(_ bv{} 64)", n)
        } else {
            format!("(bvneg (_ bv{} 64))", -n)
        }
    }

    /// Chuyển đổi biểu thức số học / logic sang chuỗi SMT-LIB2 BitVec 64
    pub fn expr_to_bv(&self, expr: &Expr) -> String {
        match expr {
            Expr::Var(v) => {
                let clean = v.trim_start_matches('%');
                self.current_val.get(clean).cloned().unwrap_or_else(|| clean.to_string())
            }
            Expr::IntConst(n) => Self::smt_bv64(*n),
            Expr::FloatConst(_) => "(_ bv0 64)".to_string(),
            Expr::BoolConst(b) => {
                if *b {
                    "(_ bv1 64)".to_string()
                } else {
                    "(_ bv0 64)".to_string()
                }
            }
            Expr::Len(v) => {
                let clean = v.trim_start_matches('%');
                let len_key = format!("{}_len", clean);
                self.current_val.get(&len_key).cloned().unwrap_or(len_key)
            }
            Expr::Binary { op, lhs, rhs } => {
                let s1 = self.expr_to_bv(lhs);
                let s2 = self.expr_to_bv(rhs);
                match op {
                    BinOp::Add => format!("(bvadd {} {})", s1, s2),
                    BinOp::Sub => format!("(bvsub {} {})", s1, s2),
                    BinOp::Mul => format!("(bvmul {} {})", s1, s2),
                    BinOp::Div => format!("(bvsdiv {} {})", s1, s2),
                    BinOp::Mod => format!("(bvsrem {} {})", s1, s2),
                    BinOp::Eq => format!("(ite (= {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                    BinOp::Neq => format!("(ite (distinct {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                    BinOp::Lt => format!("(ite (bvslt {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                    BinOp::Lte => format!("(ite (bvsle {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                    BinOp::Gt => format!("(ite (bvsgt {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                    BinOp::Gte => format!("(ite (bvsge {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                    BinOp::And => format!("(ite (and (distinct {} (_ bv0 64)) (distinct {} (_ bv0 64))) (_ bv1 64) (_ bv0 64))", s1, s2),
                    BinOp::Or => format!("(ite (or (distinct {} (_ bv0 64)) (distinct {} (_ bv0 64))) (_ bv1 64) (_ bv0 64))", s1, s2),
                }
            }
            Expr::Not(e) => {
                let s = self.expr_to_bv(e);
                format!("(ite (= {} (_ bv0 64)) (_ bv1 64) (_ bv0 64))", s)
            }
        }
    }

    /// Chuyển đổi biểu thức sang biểu thức logic Boolean chuẩn của SMT
    pub fn expr_to_bool(&self, expr: &Expr) -> String {
        match expr {
            Expr::Binary { op, lhs, rhs } => {
                let s1 = self.expr_to_bv(lhs);
                let s2 = self.expr_to_bv(rhs);
                match op {
                    BinOp::Eq => format!("(= {} {})", s1, s2),
                    BinOp::Neq => format!("(distinct {} {})", s1, s2),
                    BinOp::Lt => format!("(bvslt {} {})", s1, s2),
                    BinOp::Lte => format!("(bvsle {} {})", s1, s2),
                    BinOp::Gt => format!("(bvsgt {} {})", s1, s2),
                    BinOp::Gte => format!("(bvsge {} {})", s1, s2),
                    BinOp::And => {
                        let b1 = self.expr_to_bool(lhs);
                        let b2 = self.expr_to_bool(rhs);
                        format!("(and {} {})", b1, b2)
                    }
                    BinOp::Or => {
                        let b1 = self.expr_to_bool(lhs);
                        let b2 = self.expr_to_bool(rhs);
                        format!("(or {} {})", b1, b2)
                    }
                    _ => {
                        let bv = self.expr_to_bv(expr);
                        format!("(distinct {} (_ bv0 64))", bv)
                    }
                }
            }
            Expr::Not(e) => format!("(not {})", self.expr_to_bool(e)),
            Expr::BoolConst(b) => if *b { "true".to_string() } else { "false".to_string() },
            _ => {
                let bv = self.expr_to_bv(expr);
                format!("(distinct {} (_ bv0 64))", bv)
            }
        }
    }

    /// Khai báo một biến trong SMT nếu chưa từng được khai báo
    pub fn ensure_declared(&mut self, var: &str, smt_decls: &mut String) {
        if self.declared.insert(var.to_string()) {
            smt_decls.push_str(&format!("(declare-const {} (_ BitVec 64))\n", var));
        }
    }

    /// Thực thi kiểm chứng một chuỗi vi lệnh IVL
    pub fn verify_sequence(
        &mut self,
        stmts: &[IvlStmt],
        func_name: &str,
        file: &str,
    ) -> Vec<VerificationResult> {
        let mut results = Vec::new();

        for stmt in stmts {
            match stmt {
                IvlStmt::Assign { dest, expr } => {
                    self.step_counter += 1;
                    let clean = dest.trim_start_matches('%');
                    let val_smt = self.expr_to_bv(expr);
                    let ver = format!("{}_v{}", clean, self.step_counter);
                    self.declared.insert(ver.clone());
                    self.assertions_smt.push(format!("(assert (= {} {}))", ver, val_smt));
                    self.current_val.insert(clean.to_string(), ver);
                }
                IvlStmt::Assume { cond } => {
                    let cond_smt = self.expr_to_bool(cond);
                    self.assertions_smt.push(format!("(assert {})", cond_smt));
                }
                IvlStmt::Havoc { vars } => {
                    for v in vars {
                        self.step_counter += 1;
                        let clean = v.trim_start_matches('%');
                        let havoc_ver = format!("{}_havoc_{}", clean, self.step_counter);
                        self.declared.insert(havoc_ver.clone());
                        self.current_val.insert(clean.to_string(), havoc_ver);
                    }
                }
                IvlStmt::Assert { cond, goal_name, category, loc } => {
                    let cond_smt = self.expr_to_bool(cond);

                    let mut query = String::from("(set-logic QF_BV)\n");
                    for d in &self.declared {
                        query.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                    }
                    for a in &self.assertions_smt {
                        query.push_str(a);
                        query.push('\n');
                    }
                    query.push_str(&format!("(assert (not {}))\n", cond_smt));
                    query.push_str("(check-sat)\n(get-model)\n");

                    let stack_trace = vec![StackFrame {
                        file: file.to_string(),
                        line: loc.line,
                        function: func_name.to_string(),
                        snippet: loc.text.clone(),
                        role: goal_name.clone(),
                    }];

                    let res = Verifier::solve_query(goal_name, *category, &query, stack_trace);
                    results.push(res);
                }
                IvlStmt::Comment(_) => {}
            }
        }

        results
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ivl_simple_verification() {
        let mut vc = VcGen::new();
        let dummy_loc = Loc {
            file: "test.lit".to_string(),
            line: 1,
            text: "test".to_string(),
        };

        let stmts = vec![
            IvlStmt::Assign {
                dest: "x".to_string(),
                expr: Expr::IntConst(10),
            },
            IvlStmt::Assign {
                dest: "y".to_string(),
                expr: Expr::Binary {
                    op: BinOp::Add,
                    lhs: Box::new(Expr::Var("x".to_string())),
                    rhs: Box::new(Expr::IntConst(5)),
                },
            },
            // y must be 15 -> should PASS
            IvlStmt::Assert {
                cond: Expr::Binary {
                    op: BinOp::Eq,
                    lhs: Box::new(Expr::Var("y".to_string())),
                    rhs: Box::new(Expr::IntConst(15)),
                },
                goal_name: "test y == 15".to_string(),
                category: PropertyCategory::Functional,
                loc: dummy_loc.clone(),
            },
            // y == 999 -> should FAIL
            IvlStmt::Assert {
                cond: Expr::Binary {
                    op: BinOp::Eq,
                    lhs: Box::new(Expr::Var("y".to_string())),
                    rhs: Box::new(Expr::IntConst(999)),
                },
                goal_name: "test y == 999".to_string(),
                category: PropertyCategory::Functional,
                loc: dummy_loc,
            },
        ];

        let results = vc.verify_sequence(&stmts, "test_func", "test.lit");
        assert_eq!(results.len(), 2);
        assert!(matches!(results[0], VerificationResult::Verified { .. }));
        assert!(matches!(results[1], VerificationResult::Failed { .. }));
    }
}
