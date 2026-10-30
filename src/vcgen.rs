#![allow(dead_code)]
//! Universal Verification Condition Generator (VCGen)
//! Thực thi kiểm chứng toán học thuần túy trên các vi lệnh IVL (`Assign`, `Assume`, `Havoc`, `Assert`)
//! kết hợp với Lý thuyết Mảng và Bộ nhớ SMT (QF_ABV: Quantifier-Free BitVectors & Arrays).
//!
//! Hỗ trợ chuẩn SMT-LIB2:
//! - Biến số vô hướng: `(_ BitVec 64)`
//! - Toán đồ bộ nhớ Heap/Array: `(Array (_ BitVec 64) (_ BitVec 64))`
//! - Thao tác đọc bộ nhớ: `(select mem offset)`
//! - Thao tác ghi bộ nhớ: `(store mem offset val)`

use crate::ast::*;
use crate::ivl::{IvlExpr, IvlStmt};
use crate::verifier::{StackFrame, VerificationResult, Verifier};
use std::collections::{HashMap, HashSet};

#[derive(Clone)]
pub struct VcGen {
    pub declared_vars: HashSet<String>,
    pub declared_mems: HashSet<String>,
    pub current_val: HashMap<String, String>,
    pub current_mem: HashMap<String, String>,
    pub assertions_smt: Vec<String>,
    pub step_counter: usize,
}

impl VcGen {
    pub fn new() -> Self {
        Self {
            declared_vars: HashSet::new(),
            declared_mems: HashSet::new(),
            current_val: HashMap::new(),
            current_mem: HashMap::new(),
            assertions_smt: Vec::new(),
            step_counter: 0,
        }
    }

    /// Định nghĩa hằng số 64-bit an toàn chuẩn SMT-LIB2 QF_BV (hỗ trợ cả số âm)
    pub fn smt_bv64(n: i64) -> String {
        Verifier::smt_bv64(n)
    }

    /// Chuyển đổi biểu thức số học / logic / bộ nhớ sang chuỗi SMT-LIB2
    pub fn expr_to_bv(&self, expr: &IvlExpr) -> String {
        match expr {
            IvlExpr::Var(v) => {
                let clean = v.trim_start_matches('%');
                if let Some(val) = self.current_val.get(clean) {
                    val.clone()
                } else if let Some(m) = self.current_mem.get(clean) {
                    m.clone()
                } else {
                    clean.to_string()
                }
            }
            IvlExpr::IntConst(n) => Self::smt_bv64(*n),
            IvlExpr::BoolConst(b) => {
                if *b {
                    "(_ bv1 64)".to_string()
                } else {
                    "(_ bv0 64)".to_string()
                }
            }
            IvlExpr::Len(v) => {
                let clean = v.trim_start_matches('%');
                let len_key = format!("{}_len", clean);
                self.current_val.get(&len_key).cloned().unwrap_or(len_key)
            }
            IvlExpr::Select { mem, offset } => {
                let clean_m = mem.trim_start_matches('%');
                let m = self.current_mem.get(clean_m).cloned().unwrap_or_else(|| clean_m.to_string());
                let off = self.expr_to_bv(offset);
                format!("(select {} {})", m, off)
            }
            IvlExpr::Store { mem, offset, val } => {
                let clean_m = mem.trim_start_matches('%');
                let m = self.current_mem.get(clean_m).cloned().unwrap_or_else(|| clean_m.to_string());
                let off = self.expr_to_bv(offset);
                let v = self.expr_to_bv(val);
                format!("(store {} {} {})", m, off, v)
            }
            IvlExpr::Binary { op, lhs, rhs } => {
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
            IvlExpr::Ite { cond, then_val, else_val } => {
                let c = self.expr_to_bool(cond);
                let t = self.expr_to_bv(then_val);
                let e = self.expr_to_bv(else_val);
                format!("(ite {} {} {})", c, t, e)
            }
            IvlExpr::Not(e) => {
                let s = self.expr_to_bv(e);
                format!("(ite (= {} (_ bv0 64)) (_ bv1 64) (_ bv0 64))", s)
            }
            IvlExpr::Mask8(e) => {
                let s = self.expr_to_bv(e);
                format!("(bvand {} (_ bv255 64))", s)
            }
        }
    }

    /// Chuyển đổi biểu thức sang biểu thức logic Boolean chuẩn của SMT
    pub fn expr_to_bool(&self, expr: &IvlExpr) -> String {
        match expr {
            IvlExpr::Binary { op, lhs, rhs } => {
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
            IvlExpr::Ite { cond, then_val, else_val } => {
                let c = self.expr_to_bool(cond);
                let t = self.expr_to_bool(then_val);
                let e = self.expr_to_bool(else_val);
                format!("(ite {} {} {})", c, t, e)
            }
            IvlExpr::Not(e) => format!("(not {})", self.expr_to_bool(e)),
            IvlExpr::BoolConst(b) => if *b { "true".to_string() } else { "false".to_string() },
            _ => {
                let bv = self.expr_to_bv(expr);
                format!("(distinct {} (_ bv0 64))", bv)
            }
        }
    }

    pub fn collect_scalar_vars(&self, expr: &IvlExpr, vars: &mut HashSet<String>) {
        match expr {
            IvlExpr::Var(v) => {
                let clean = v.trim_start_matches('%');
                if !self.current_mem.contains_key(clean) && !self.declared_mems.contains(clean) {
                    let mapped = self.current_val.get(clean).cloned().unwrap_or_else(|| clean.to_string());
                    vars.insert(mapped);
                }
            }
            IvlExpr::Len(v) => {
                let clean = v.trim_start_matches('%');
                let len_key = format!("{}_len", clean);
                let mapped = self.current_val.get(&len_key).cloned().unwrap_or(len_key);
                vars.insert(mapped);
            }
            IvlExpr::Select { offset, .. } => {
                self.collect_scalar_vars(offset, vars);
            }
            IvlExpr::Store { offset, val, .. } => {
                self.collect_scalar_vars(offset, vars);
                self.collect_scalar_vars(val, vars);
            }
            IvlExpr::Binary { lhs, rhs, .. } => {
                self.collect_scalar_vars(lhs, vars);
                self.collect_scalar_vars(rhs, vars);
            }
            IvlExpr::Ite { cond, then_val, else_val } => {
                self.collect_scalar_vars(cond, vars);
                self.collect_scalar_vars(then_val, vars);
                self.collect_scalar_vars(else_val, vars);
            }
            IvlExpr::Not(inner) => self.collect_scalar_vars(inner, vars),
            IvlExpr::Mask8(inner) => self.collect_scalar_vars(inner, vars),
            _ => {}
        }
    }

    pub fn collect_mem_names(expr: &IvlExpr, mems: &mut HashSet<String>) {
        match expr {
            IvlExpr::Select { mem, offset } => {
                mems.insert(mem.trim_start_matches('%').to_string());
                Self::collect_mem_names(offset, mems);
            }
            IvlExpr::Store { mem, offset, val } => {
                mems.insert(mem.trim_start_matches('%').to_string());
                Self::collect_mem_names(offset, mems);
                Self::collect_mem_names(val, mems);
            }
            IvlExpr::Binary { lhs, rhs, .. } => {
                Self::collect_mem_names(lhs, mems);
                Self::collect_mem_names(rhs, mems);
            }
            IvlExpr::Ite { cond, then_val, else_val } => {
                Self::collect_mem_names(cond, mems);
                Self::collect_mem_names(then_val, mems);
                Self::collect_mem_names(else_val, mems);
            }
            IvlExpr::Not(inner) => Self::collect_mem_names(inner, mems),
            IvlExpr::Mask8(inner) => Self::collect_mem_names(inner, mems),
            _ => {}
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
                IvlStmt::Assign { dest, expr, is_memory } => {
                    let mut needed_vars = HashSet::new();
                    let mut needed_mems = HashSet::new();

                    if *is_memory {
                        if let IvlExpr::Ite { cond, then_val, else_val } = expr {
                            self.collect_scalar_vars(cond, &mut needed_vars);
                            if let IvlExpr::Var(m) = then_val.as_ref() {
                                needed_mems.insert(m.trim_start_matches('%').to_string());
                            } else {
                                Self::collect_mem_names(then_val, &mut needed_mems);
                            }
                            if let IvlExpr::Var(m) = else_val.as_ref() {
                                needed_mems.insert(m.trim_start_matches('%').to_string());
                            } else {
                                Self::collect_mem_names(else_val, &mut needed_mems);
                            }
                        } else {
                            self.collect_scalar_vars(expr, &mut needed_vars);
                            Self::collect_mem_names(expr, &mut needed_mems);
                        }
                    } else {
                        self.collect_scalar_vars(expr, &mut needed_vars);
                        Self::collect_mem_names(expr, &mut needed_mems);
                    }

                    for nv in needed_vars {
                        if !self.declared_mems.contains(&nv) {
                            self.declared_vars.insert(nv);
                        }
                    }
                    for nm in needed_mems {
                        if !self.current_mem.contains_key(&nm) {
                            self.declared_mems.insert(nm.clone());
                            self.current_mem.insert(nm.clone(), nm);
                        }
                    }

                    self.step_counter += 1;
                    let clean = dest.trim_start_matches('%');
                    let val_smt = self.expr_to_bv(expr);
                    if *is_memory {
                        let ver = format!("{}_mem_{}", clean, self.step_counter);
                        self.declared_mems.insert(ver.clone());
                        self.assertions_smt.push(format!("(assert (= {} {}))", ver, val_smt));
                        self.current_mem.insert(clean.to_string(), ver);
                    } else {
                        let ver = format!("{}_v{}", clean, self.step_counter);
                        self.declared_vars.insert(ver.clone());
                        self.assertions_smt.push(format!("(assert (= {} {}))", ver, val_smt));
                        self.current_val.insert(clean.to_string(), ver);
                    }
                }
                IvlStmt::Assume { cond } => {
                    let mut needed_vars = HashSet::new();
                    self.collect_scalar_vars(cond, &mut needed_vars);
                    for nv in needed_vars {
                        self.declared_vars.insert(nv);
                    }
                    let mut needed_mems = HashSet::new();
                    Self::collect_mem_names(cond, &mut needed_mems);
                    for nm in needed_mems {
                        if !self.current_mem.contains_key(&nm) {
                            self.declared_mems.insert(nm);
                        }
                    }
                    let cond_smt = self.expr_to_bool(cond);
                    self.assertions_smt.push(format!("(assert {})", cond_smt));
                }
                IvlStmt::Havoc { vars, is_memory } => {
                    for v in vars {
                        self.step_counter += 1;
                        let clean = v.trim_start_matches('%');
                        if *is_memory {
                            let havoc_ver = format!("{}_havoc_mem_{}", clean, self.step_counter);
                            self.declared_mems.insert(havoc_ver.clone());
                            self.current_mem.insert(clean.to_string(), havoc_ver);
                        } else {
                            let havoc_ver = format!("{}_havoc_{}", clean, self.step_counter);
                            self.declared_vars.insert(havoc_ver.clone());
                            self.current_val.insert(clean.to_string(), havoc_ver);
                        }
                    }
                }
                IvlStmt::Assert { cond, goal_name, category, loc } => {
                    let mut needed_vars = HashSet::new();
                    self.collect_scalar_vars(cond, &mut needed_vars);
                    for nv in needed_vars {
                        self.declared_vars.insert(nv);
                    }
                    let mut needed_mems = HashSet::new();
                    Self::collect_mem_names(cond, &mut needed_mems);
                    for nm in needed_mems {
                        if !self.current_mem.contains_key(&nm) {
                            self.declared_mems.insert(nm);
                        }
                    }
                    let cond_smt = self.expr_to_bool(cond);

                    let mut query = String::from("(set-logic QF_ABV)\n");
                    for m in &self.declared_mems {
                        query.push_str(&format!("(declare-const {} (Array (_ BitVec 64) (_ BitVec 64)))\n", m));
                    }
                    for d in &self.declared_vars {
                        if !self.declared_mems.contains(d) {
                            query.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                        }
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
    use crate::verifier::PropertyCategory;

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
                expr: IvlExpr::IntConst(10),
                is_memory: false,
            },
            IvlStmt::Assign {
                dest: "y".to_string(),
                expr: IvlExpr::Binary {
                    op: BinOp::Add,
                    lhs: Box::new(IvlExpr::Var("x".to_string())),
                    rhs: Box::new(IvlExpr::IntConst(5)),
                },
                is_memory: false,
            },
            // y must be 15 -> should PASS
            IvlStmt::Assert {
                cond: IvlExpr::Binary {
                    op: BinOp::Eq,
                    lhs: Box::new(IvlExpr::Var("y".to_string())),
                    rhs: Box::new(IvlExpr::IntConst(15)),
                },
                goal_name: "test y == 15".to_string(),
                category: PropertyCategory::Functional,
                loc: dummy_loc.clone(),
            },
            // y == 999 -> should FAIL
            IvlStmt::Assert {
                cond: IvlExpr::Binary {
                    op: BinOp::Eq,
                    lhs: Box::new(IvlExpr::Var("y".to_string())),
                    rhs: Box::new(IvlExpr::IntConst(999)),
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

    #[test]
    fn test_ivl_memory_store_and_load_verification() {
        let mut vc = VcGen::new();
        let dummy_loc = Loc {
            file: "test_mem.lit".to_string(),
            line: 1,
            text: "STORE8 %buf 0 42; %val = LOAD8 %buf 0".to_string(),
        };

        // 1. Ghi số 100 vào ô nhớ 1 của buffer %buf:
        //    buf_mem := store(buf_mem, 1, 100)
        // 2. Ghi số 42 vào ô nhớ 0 của buffer %buf:
        //    buf_mem := store(buf_mem, 0, 42)
        // 3. Đọc lại từ ô nhớ 0: val0 := select(buf_mem, 0) -> Phải bằng 42!
        // 4. Đọc lại từ ô nhớ 1: val1 := select(buf_mem, 1) -> Vẫn phải bằng 100!
        let stmts = vec![
            IvlStmt::Assign {
                dest: "buf".to_string(),
                expr: IvlExpr::Store {
                    mem: "buf".to_string(),
                    offset: Box::new(IvlExpr::IntConst(1)),
                    val: Box::new(IvlExpr::IntConst(100)),
                },
                is_memory: true,
            },
            IvlStmt::Assign {
                dest: "buf".to_string(),
                expr: IvlExpr::Store {
                    mem: "buf".to_string(),
                    offset: Box::new(IvlExpr::IntConst(0)),
                    val: Box::new(IvlExpr::IntConst(42)),
                },
                is_memory: true,
            },
            IvlStmt::Assign {
                dest: "val0".to_string(),
                expr: IvlExpr::Select {
                    mem: "buf".to_string(),
                    offset: Box::new(IvlExpr::IntConst(0)),
                },
                is_memory: false,
            },
            IvlStmt::Assign {
                dest: "val1".to_string(),
                expr: IvlExpr::Select {
                    mem: "buf".to_string(),
                    offset: Box::new(IvlExpr::IntConst(1)),
                },
                is_memory: false,
            },
            // Kiểm tra đọc lại ô nhớ 0
            IvlStmt::Assert {
                cond: IvlExpr::Binary {
                    op: BinOp::Eq,
                    lhs: Box::new(IvlExpr::Var("val0".to_string())),
                    rhs: Box::new(IvlExpr::IntConst(42)),
                },
                goal_name: "test memory read after write val0 == 42".to_string(),
                category: PropertyCategory::Safety,
                loc: dummy_loc.clone(),
            },
            // Kiểm tra tính không tương hỗ (non-aliasing): ô nhớ 1 vẫn giữ nguyên giá trị 100
            IvlStmt::Assert {
                cond: IvlExpr::Binary {
                    op: BinOp::Eq,
                    lhs: Box::new(IvlExpr::Var("val1".to_string())),
                    rhs: Box::new(IvlExpr::IntConst(100)),
                },
                goal_name: "test memory non-aliasing at offset 1 val1 == 100".to_string(),
                category: PropertyCategory::Safety,
                loc: dummy_loc,
            },
        ];

        let results = vc.verify_sequence(&stmts, "test_mem_func", "test_mem.lit");
        assert_eq!(results.len(), 2);
        assert!(matches!(results[0], VerificationResult::Verified { .. }));
        assert!(matches!(results[1], VerificationResult::Verified { .. }));
    }
}
