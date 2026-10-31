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
    #[inline]
    pub fn smt_bv64(n: i64) -> String {
        Verifier::smt_bv64(n)
    }

    /// Tra cứu tên phiên bản mảng bộ nhớ hiện tại trong SMT
    #[inline]
    fn resolve_mem(&self, mem: &str) -> String {
        let clean = mem.trim_start_matches('%');
        self.current_mem
            .get(clean)
            .cloned()
            .unwrap_or_else(|| format!("{}_mem_0", clean))
    }

    /// Chuyển đổi biểu thức số học / logic / bộ nhớ sang chuỗi SMT-LIB2 BitVec 64-bit
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
            IvlExpr::BoolConst(b) => if *b { "(_ bv1 64)" } else { "(_ bv0 64)" }.to_string(),
            IvlExpr::Len(v) => {
                let len_key = format!("{}_len", v.trim_start_matches('%'));
                self.current_val.get(&len_key).cloned().unwrap_or(len_key)
            }
            IvlExpr::Select { mem, offset } => {
                format!(
                    "(select {} {})",
                    self.resolve_mem(mem),
                    self.expr_to_bv(offset)
                )
            }
            IvlExpr::Store { mem, offset, val } => {
                format!(
                    "(store {} {} {})",
                    self.resolve_mem(mem),
                    self.expr_to_bv(offset),
                    self.expr_to_bv(val)
                )
            }
            IvlExpr::Binary {
                op,
                lhs,
                rhs,
                is_unsigned,
            } => {
                // Mọi toán tử trả về giá trị logic đều ủy quyền trực tiếp cho `expr_to_bool` (Single Source of Truth)
                if matches!(
                    op,
                    BinOp::Eq
                        | BinOp::Neq
                        | BinOp::Lt
                        | BinOp::Lte
                        | BinOp::Gt
                        | BinOp::Gte
                        | BinOp::And
                        | BinOp::Or
                ) {
                    return format!("(ite {} (_ bv1 64) (_ bv0 64))", self.expr_to_bool(expr));
                }

                let s1 = self.expr_to_bv(lhs);
                let s2 = self.expr_to_bv(rhs);
                match op {
                    BinOp::Add => format!("(bvadd {} {})", s1, s2),
                    BinOp::Sub => format!("(bvsub {} {})", s1, s2),
                    BinOp::Mul => format!("(bvmul {} {})", s1, s2),
                    BinOp::Div => {
                        let op_smt = if *is_unsigned { "bvudiv" } else { "bvsdiv" };
                        format!("({} {} {})", op_smt, s1, s2)
                    }
                    BinOp::Mod => {
                        let op_smt = if *is_unsigned { "bvurem" } else { "bvsrem" };
                        format!("({} {} {})", op_smt, s1, s2)
                    }
                    BinOp::BitAnd => format!("(bvand {} {})", s1, s2),
                    BinOp::BitOr => format!("(bvor {} {})", s1, s2),
                    BinOp::Xor => format!("(bvxor {} {})", s1, s2),
                    BinOp::Shl => format!("(bvshl {} (bvand {} (_ bv63 64)))", s1, s2),
                    BinOp::Shr => format!("(bvlshr {} (bvand {} (_ bv63 64)))", s1, s2),
                    BinOp::Sar => format!("(bvashr {} (bvand {} (_ bv63 64)))", s1, s2),
                    _ => unreachable!(),
                }
            }
            IvlExpr::Ite {
                cond,
                then_val,
                else_val,
            } => format!(
                "(ite {} {} {})",
                self.expr_to_bool(cond),
                self.expr_to_bv(then_val),
                self.expr_to_bv(else_val)
            ),
            IvlExpr::Not(e) => {
                format!(
                    "(ite (= {} (_ bv0 64)) (_ bv1 64) (_ bv0 64))",
                    self.expr_to_bv(e)
                )
            }
            IvlExpr::BitNot(e) => format!("(bvnot {})", self.expr_to_bv(e)),
            IvlExpr::Mask8(e) => format!("(bvand {} (_ bv255 64))", self.expr_to_bv(e)),
        }
    }

    /// Chuyển đổi biểu thức bộ nhớ (Array) sang chuỗi SMT-LIB2
    pub fn expr_to_mem(&self, expr: &IvlExpr) -> String {
        match expr {
            IvlExpr::Var(v) => {
                let clean = v.trim_start_matches('%');
                if let Some(m) = self.current_mem.get(clean) {
                    m.clone()
                } else if self.declared_mems.contains(clean) {
                    clean.to_string()
                } else {
                    format!("{}_mem_0", clean)
                }
            }
            IvlExpr::Store { mem, offset, val } => format!(
                "(store {} {} {})",
                self.resolve_mem(mem),
                self.expr_to_bv(offset),
                self.expr_to_bv(val)
            ),
            IvlExpr::Ite {
                cond,
                then_val,
                else_val,
            } => format!(
                "(ite {} {} {})",
                self.expr_to_bool(cond),
                self.expr_to_mem(then_val),
                self.expr_to_mem(else_val)
            ),
            _ => self.expr_to_bv(expr),
        }
    }

    /// Chuyển đổi biểu thức sang biểu thức logic Boolean chuẩn của SMT
    pub fn expr_to_bool(&self, expr: &IvlExpr) -> String {
        match expr {
            IvlExpr::Binary {
                op,
                lhs,
                rhs,
                is_unsigned,
            } => match op {
                BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Lte | BinOp::Gt | BinOp::Gte => {
                    let s1 = self.expr_to_bv(lhs);
                    let s2 = self.expr_to_bv(rhs);
                    let pred = match (op, *is_unsigned) {
                        (BinOp::Eq, _) => "=",
                        (BinOp::Neq, _) => "distinct",
                        (BinOp::Lt, true) => "bvult",
                        (BinOp::Lt, false) => "bvslt",
                        (BinOp::Lte, true) => "bvule",
                        (BinOp::Lte, false) => "bvsle",
                        (BinOp::Gt, true) => "bvugt",
                        (BinOp::Gt, false) => "bvsgt",
                        (BinOp::Gte, true) => "bvuge",
                        (BinOp::Gte, false) => "bvsge",
                        _ => unreachable!(),
                    };
                    format!("({} {} {})", pred, s1, s2)
                }
                BinOp::And => format!(
                    "(and {} {})",
                    self.expr_to_bool(lhs),
                    self.expr_to_bool(rhs)
                ),
                BinOp::Or => format!("(or {} {})", self.expr_to_bool(lhs), self.expr_to_bool(rhs)),
                BinOp::Xor => format!(
                    "(xor {} {})",
                    self.expr_to_bool(lhs),
                    self.expr_to_bool(rhs)
                ),
                _ => format!("(distinct {} (_ bv0 64))", self.expr_to_bv(expr)),
            },
            IvlExpr::Ite {
                cond,
                then_val,
                else_val,
            } => format!(
                "(ite {} {} {})",
                self.expr_to_bool(cond),
                self.expr_to_bool(then_val),
                self.expr_to_bool(else_val)
            ),
            IvlExpr::Not(e) => format!("(not {})", self.expr_to_bool(e)),
            IvlExpr::BoolConst(b) => if *b { "true" } else { "false" }.to_string(),
            _ => format!("(distinct {} (_ bv0 64))", self.expr_to_bv(expr)),
        }
    }

    /// Duyệt biểu thức 1 lượt duy nhất để thu thập đồng thời mọi biến vô hướng (`vars`) và mảng bộ nhớ (`mems`)
    pub fn collect_expr_symbols(
        &self,
        expr: &IvlExpr,
        in_mem_pos: bool,
        vars: &mut HashSet<String>,
        mems: &mut HashSet<String>,
    ) {
        match expr {
            IvlExpr::Var(v) => {
                let clean = v.trim_start_matches('%');
                if in_mem_pos {
                    mems.insert(clean.to_string());
                } else if !self.declared_mems.contains(clean) {
                    let mapped = self
                        .current_val
                        .get(clean)
                        .cloned()
                        .unwrap_or_else(|| clean.to_string());
                    vars.insert(mapped);
                }
            }
            IvlExpr::Len(v) => {
                let len_key = format!("{}_len", v.trim_start_matches('%'));
                let mapped = self.current_val.get(&len_key).cloned().unwrap_or(len_key);
                vars.insert(mapped);
            }
            IvlExpr::Select { mem, offset } => {
                mems.insert(mem.trim_start_matches('%').to_string());
                self.collect_expr_symbols(offset, false, vars, mems);
            }
            IvlExpr::Store { mem, offset, val } => {
                mems.insert(mem.trim_start_matches('%').to_string());
                self.collect_expr_symbols(offset, false, vars, mems);
                self.collect_expr_symbols(val, false, vars, mems);
            }
            IvlExpr::Binary { lhs, rhs, .. } => {
                self.collect_expr_symbols(lhs, false, vars, mems);
                self.collect_expr_symbols(rhs, false, vars, mems);
            }
            IvlExpr::Ite {
                cond,
                then_val,
                else_val,
            } => {
                self.collect_expr_symbols(cond, false, vars, mems);
                self.collect_expr_symbols(then_val, in_mem_pos, vars, mems);
                self.collect_expr_symbols(else_val, in_mem_pos, vars, mems);
            }
            IvlExpr::Not(inner) | IvlExpr::BitNot(inner) | IvlExpr::Mask8(inner) => {
                self.collect_expr_symbols(inner, false, vars, mems);
            }
            IvlExpr::IntConst(_) | IvlExpr::BoolConst(_) => {}
        }
    }

    /// Đảm bảo mọi biến vô hướng và mảng bộ nhớ xuất hiện trong `expr` đều được khai báo trong SMT
    fn register_expr_decls(&mut self, expr: &IvlExpr, is_memory_assign: bool) {
        let mut needed_vars = HashSet::new();
        let mut needed_mems = HashSet::new();
        self.collect_expr_symbols(expr, is_memory_assign, &mut needed_vars, &mut needed_mems);

        for nm in needed_mems {
            if !self.current_mem.contains_key(&nm) {
                let init_mem = format!("{}_mem_0", nm);
                self.declared_mems.insert(init_mem.clone());
                self.current_mem.insert(nm, init_mem);
            }
        }
        for nv in needed_vars {
            if !self.declared_mems.contains(&nv) && !self.current_mem.contains_key(&nv) {
                self.declared_vars.insert(nv);
            }
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
                IvlStmt::Assign {
                    dest,
                    expr,
                    is_memory,
                } => {
                    self.register_expr_decls(expr, *is_memory);

                    self.step_counter += 1;
                    let clean = dest.trim_start_matches('%');
                    if *is_memory {
                        let val_smt = self.expr_to_mem(expr);
                        let ver = format!("{}_mem_{}", clean, self.step_counter);
                        self.declared_mems.insert(ver.clone());
                        self.assertions_smt
                            .push(format!("(assert (= {} {}))", ver, val_smt));
                        self.current_mem.insert(clean.to_string(), ver);
                    } else {
                        let val_smt = self.expr_to_bv(expr);
                        let ver = format!("{}_v{}", clean, self.step_counter);
                        self.declared_vars.insert(ver.clone());
                        self.assertions_smt
                            .push(format!("(assert (= {} {}))", ver, val_smt));
                        self.current_val.insert(clean.to_string(), ver);
                    }
                }
                IvlStmt::Assume { cond } => {
                    self.register_expr_decls(cond, false);
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
                IvlStmt::Assert {
                    cond,
                    goal_name,
                    category,
                    loc,
                } => {
                    self.register_expr_decls(cond, false);
                    let cond_smt = self.expr_to_bool(cond);

                    let mut query = String::from("(set-logic QF_ABV)\n");
                    for m in &self.declared_mems {
                        query.push_str(&format!(
                            "(declare-const {} (Array (_ BitVec 64) (_ BitVec 64)))\n",
                            m
                        ));
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
                expr: IvlExpr::bin(
                    BinOp::Add,
                    IvlExpr::Var("x".to_string()),
                    IvlExpr::IntConst(5),
                ),
                is_memory: false,
            },
            // y must be 15 -> should PASS
            IvlStmt::Assert {
                cond: IvlExpr::eq(IvlExpr::Var("y".to_string()), IvlExpr::IntConst(15)),
                goal_name: "test y == 15".to_string(),
                category: PropertyCategory::Functional,
                loc: dummy_loc.clone(),
            },
            // y == 999 -> should FAIL
            IvlStmt::Assert {
                cond: IvlExpr::eq(IvlExpr::Var("y".to_string()), IvlExpr::IntConst(999)),
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
            IvlStmt::Assert {
                cond: IvlExpr::eq(IvlExpr::Var("val0".to_string()), IvlExpr::IntConst(42)),
                goal_name: "test memory read after write val0 == 42".to_string(),
                category: PropertyCategory::Safety,
                loc: dummy_loc.clone(),
            },
            IvlStmt::Assert {
                cond: IvlExpr::eq(IvlExpr::Var("val1".to_string()), IvlExpr::IntConst(100)),
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
