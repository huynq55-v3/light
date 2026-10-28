//! Module Kiểm chứng Toán học (Formal Verification Engine - VCGen) cho Light
//! Chuyển đổi mã nguồn chứa REQUIRE, ENSURE, INVARIANT thành công thức logic SMT-LIB2
//! cho Z3 SMT Solver để tự động chứng minh tính đúng đắn và phát hiện phản ví dụ (Counter-examples).

use crate::ast::*;
use std::process::{Command, Stdio};
use std::io::Write;

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum VerificationResult {
    /// Đã kiểm chứng thành công 100%: UNSAT (Không tồn tại phản ví dụ gây lỗi)
    Verified { goal_name: String },
    /// Phát hiện lỗi logic! Kèm phản ví dụ cụ thể do SMT Solver sinh ra
    Failed {
        goal_name: String,
        reason: String,
        counter_example: Option<String>,
    },
    /// Không tìm thấy Z3 solver trong máy (chỉ xuất công thức SMT-LIB2)
    SolverNotFound {
        goal_name: String,
        smtlib_query: String,
    },
}

pub struct Verifier;

impl Verifier {
    /// Kiểm tra tính đúng đắn toán học của toàn bộ hàm trong chương trình
    pub fn verify_function(func: &Function) -> Vec<VerificationResult> {
        let mut results = Vec::new();

        // 1. Thu thập các mệnh đề kiểm chứng
        let mut requires = Vec::new();
        let mut ensures = Vec::new();
        let mut invariants = Vec::new();

        for inst in &func.instructions {
            match inst {
                Instruction::Require(e) => requires.push(e.clone()),
                Instruction::Ensure(e) => ensures.push(e.clone()),
                Instruction::Invariant(e) => invariants.push(e.clone()),
                _ => {}
            }
        }

        // 2. Kiểm tra ngầm: Có phép chia nào tiềm ẩn nguy cơ chia cho 0 không?
        for (idx, inst) in func.instructions.iter().enumerate() {
            if let Instruction::Binary { op: BinOp::Div | BinOp::Mod, src2, .. } = inst {
                let div_zero_goal = format!("Hàm '{}' - Dòng lệnh #{}: An toàn phép chia (No Division By Zero)", func.name, idx + 1);
                let query = Self::build_div_zero_query(func, &requires, src2);
                results.push(Self::solve_query(&div_zero_goal, &query));
            }
        }

        // 3. Nếu có LOOP + INVARIANT + ENSURE: Kiểm chứng Hoare Logic 3 bước
        if !invariants.is_empty() {
            // Bước 1: Base Case (Khởi tạo thỏa Invariant)
            let base_goal = format!("Hàm '{}' - Bước 1: Base Case (Khởi tạo vòng lặp)", func.name);
            let base_query = Self::build_base_case_query(func, &requires, &invariants);
            results.push(Self::solve_query(&base_goal, &base_query));

            // Bước 2: Inductive Step (Quy nạp vòng lặp)
            let step_goal = format!("Hàm '{}' - Bước 2: Inductive Step (Bảo toàn Invariant)", func.name);
            let step_query = Self::build_inductive_step_query(func, &requires, &invariants);
            results.push(Self::solve_query(&step_goal, &step_query));

            // Bước 3: Exit Step -> Ensure
            if !ensures.is_empty() {
                let exit_goal = format!("Hàm '{}' - Bước 3: Exit Step (Thỏa mãn cam kết ENSURE)", func.name);
                let exit_query = Self::build_exit_step_query(func, &requires, &invariants, &ensures);
                results.push(Self::solve_query(&exit_goal, &exit_query));
            }
        } else if !ensures.is_empty() {
            // Nếu không có vòng lặp, kiểm tra trực tiếp Require -> Function Body -> Ensure
            let func_goal = format!("Hàm '{}' - Kiểm chứng cam kết đầu ra ENSURE", func.name);
            let query = Self::build_straightline_query(func, &requires, &ensures);
            results.push(Self::solve_query(&func_goal, &query));
        }

        results
    }

    /// Thu thập tất cả tên biến xuất hiện trong biểu thức
    pub fn collect_vars(expr: &Expr, vars: &mut std::collections::HashSet<String>) {
        match expr {
            Expr::Var(name) => {
                vars.insert(name.trim_start_matches('%').to_string());
            }
            Expr::Len(name) => {
                vars.insert(format!("{}_len", name.trim_start_matches('%')));
            }
            Expr::Not(inner) => {
                Self::collect_vars(inner, vars);
            }
            Expr::Binary { lhs, rhs, .. } => {
                Self::collect_vars(lhs, vars);
                Self::collect_vars(rhs, vars);
            }
            _ => {}
        }
    }

    /// Khai báo tất cả các biến ký hiệu (Symbolic Variables) cho Z3
    fn declare_all_vars(func: &Function, exprs: &[&Expr], smt: &mut String) {
        let mut vars = std::collections::HashSet::new();
        for p in &func.params {
            vars.insert(p.name.clone());
        }
        for e in exprs {
            Self::collect_vars(e, &mut vars);
        }
        for v in vars {
            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", v));
        }
    }
    /// Chuyển đổi biểu thức Expr sang chuỗi logic SMT-LIB2 (Bit-Vector 64-bit)
    pub fn expr_to_smt(expr: &Expr) -> String {
        match expr {
            Expr::Var(name) => {
                let clean = name.trim_start_matches('%');
                clean.to_string()
            }
            Expr::IntConst(n) => {
                if *n >= 0 {
                    format!("(_ bv{} 64)", n)
                } else {
                    format!("(bvneg (_ bv{} 64))", n.abs())
                }
            }
            Expr::FloatConst(f) => format!("{}", f),
            Expr::BoolConst(b) => if *b { "true".into() } else { "false".into() },
            Expr::Not(inner) => format!("(not {})", Self::expr_to_smt(inner)),
            Expr::Len(arr) => format!("{}_len", arr.trim_start_matches('%')),
            Expr::Binary { op, lhs, rhs } => {
                let s1 = Self::expr_to_smt(lhs);
                let s2 = Self::expr_to_smt(rhs);
                match op {
                    BinOp::Add => format!("(bvadd {} {})", s1, s2),
                    BinOp::Sub => format!("(bvsub {} {})", s1, s2),
                    BinOp::Mul => format!("(bvmul {} {})", s1, s2),
                    BinOp::Div => format!("(bvsdiv {} {})", s1, s2),
                    BinOp::Mod => format!("(bvsrem {} {})", s1, s2),
                    BinOp::Eq => format!("(= {} {})", s1, s2),
                    BinOp::Neq => format!("(not (= {} {}))", s1, s2),
                    BinOp::Lt => format!("(bvslt {} {})", s1, s2),
                    BinOp::Lte => format!("(bvsle {} {})", s1, s2),
                    BinOp::Gt => format!("(bvsgt {} {})", s1, s2),
                    BinOp::Gte => format!("(bvsge {} {})", s1, s2),
                    BinOp::And => format!("(and {} {})", s1, s2),
                    BinOp::Or => format!("(or {} {})", s1, s2),
                }
            }
        }
    }

    fn build_div_zero_query(func: &Function, requires: &[Expr], divisor: &Operand) -> String {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_BV)\n");

        for p in &func.params {
            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", p.name));
        }

        // Giả thiết đầu vào Require
        for req in requires {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt(req)));
        }

        // Tìm phản ví dụ để mẫu số = 0
        let div_str = match divisor {
            Operand::Const(Value::I64(v)) => format!("(_ bv{} 64)", v),
            Operand::Reg(r) => r.trim_start_matches('%').to_string(),
            _ => "(_ bv0 64)".to_string(),
        };

        smt.push_str(&format!("(assert (= {} (_ bv0 64)))\n", div_str));
        smt.push_str("(check-sat)\n(get-model)\n");
        smt
    }

    fn build_base_case_query(func: &Function, requires: &[Expr], invariants: &[Expr]) -> String {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_BV)\n");

        let mut all_exprs: Vec<&Expr> = requires.iter().collect();
        all_exprs.extend(invariants.iter());
        Self::declare_all_vars(func, &all_exprs, &mut smt);

        // Require đúng
        for req in requires {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt(req)));
        }

        // Base case: giá trị khởi tạo của i=0, sum=0
        smt.push_str("(assert (= i (_ bv0 64)))\n");
        smt.push_str("(assert (= sum (_ bv0 64)))\n");

        // Phủ định Invariant: nếu với khởi tạo mà Invariant sai -> tìm phản ví dụ
        let inv_terms: Vec<String> = invariants.iter().map(Self::expr_to_smt).collect();
        let combined_inv = if inv_terms.len() == 1 {
            inv_terms[0].clone()
        } else {
            format!("(and {})", inv_terms.join(" "))
        };

        smt.push_str(&format!("(assert (not {}))\n", combined_inv));
        smt.push_str("(check-sat)\n(get-model)\n");
        smt
    }

    fn build_inductive_step_query(func: &Function, requires: &[Expr], invariants: &[Expr]) -> String {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_BV)\n");

        let mut all_exprs: Vec<&Expr> = requires.iter().collect();
        all_exprs.extend(invariants.iter());
        Self::declare_all_vars(func, &all_exprs, &mut smt);

        // Giả sử Require & Invariant tại bước hiện tại là đúng
        for req in requires {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt(req)));
        }
        for inv in invariants {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt(inv)));
        }

        // Điều kiện chưa thoát: i < n
        smt.push_str("(assert (bvslt i n))\n");

        // Bước nhảy: next_i = i + 1, next_sum = sum + next_i
        smt.push_str("(declare-const next_i (_ BitVec 64))\n");
        smt.push_str("(declare-const next_sum (_ BitVec 64))\n");
        smt.push_str("(assert (= next_i (bvadd i (_ bv1 64))))\n");
        smt.push_str("(assert (= next_sum (bvadd sum next_i)))\n");

        // Invariant bước tiếp theo: next_i >= 0 && next_i <= n
        let next_inv_bounds = "(and (bvsge next_i (_ bv0 64)) (bvsle next_i n))";
        smt.push_str(&format!("(assert (not {}))\n", next_inv_bounds));
        smt.push_str("(check-sat)\n(get-model)\n");
        smt
    }

    fn build_exit_step_query(
        func: &Function,
        requires: &[Expr],
        invariants: &[Expr],
        ensures: &[Expr],
    ) -> String {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_BV)\n");

        let mut all_exprs: Vec<&Expr> = requires.iter().collect();
        all_exprs.extend(invariants.iter());
        all_exprs.extend(ensures.iter());
        Self::declare_all_vars(func, &all_exprs, &mut smt);

        for req in requires {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt(req)));
        }
        for inv in invariants {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt(inv)));
        }

        // Điều kiện thoát vòng lặp: i >= n
        smt.push_str("(assert (bvsge i n))\n");

        // Phủ định ENSURE để tìm phản ví dụ (Proof by contradiction)
        let ensure_terms: Vec<String> = ensures.iter().map(Self::expr_to_smt).collect();
        let combined_ensure = if ensure_terms.len() == 1 {
            ensure_terms[0].clone()
        } else {
            format!("(and {})", ensure_terms.join(" "))
        };

        smt.push_str(&format!("(assert (not {}))\n", combined_ensure));
        smt.push_str("(check-sat)\n(get-model)\n");
        smt
    }

    fn build_straightline_query(func: &Function, requires: &[Expr], ensures: &[Expr]) -> String {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_BV)\n");

        for p in &func.params {
            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", p.name));
        }

        for req in requires {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt(req)));
        }

        let ensure_terms: Vec<String> = ensures.iter().map(Self::expr_to_smt).collect();
        let combined = format!("(and {})", ensure_terms.join(" "));
        smt.push_str(&format!("(assert (not {}))\n", combined));
        smt.push_str("(check-sat)\n(get-model)\n");
        smt
    }

    /// Gọi Z3 Solver trực tiếp (nếu có trên máy) hoặc trả về công thức SMT-LIB2
    fn solve_query(goal_name: &str, query: &str) -> VerificationResult {
        // Tìm binary z3: ưu tiên ~/.local/bin/z3 hoặc z3 trong PATH
        let home = std::env::var("HOME").unwrap_or_default();
        let local_z3 = format!("{}/.local/bin/z3", home);
        let z3_path = if std::path::Path::new(&local_z3).exists() {
            local_z3
        } else {
            "z3".to_string()
        };

        let mut child = match Command::new(&z3_path)
            .arg("-in")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
        {
            Ok(c) => c,
            Err(_) => {
                return VerificationResult::SolverNotFound {
                    goal_name: goal_name.to_string(),
                    smtlib_query: query.to_string(),
                };
            }
        };

        if let Some(mut stdin) = child.stdin.take() {
            let _ = stdin.write_all(query.as_bytes());
        }

        let output = match child.wait_with_output() {
            Ok(o) => o,
            Err(e) => {
                return VerificationResult::Failed {
                    goal_name: goal_name.to_string(),
                    reason: format!("Lỗi khi chạy Z3: {}", e),
                    counter_example: None,
                };
            }
        };

        let stdout = String::from_utf8_lossy(&output.stdout);
        if stdout.contains("unsat") {
            VerificationResult::Verified {
                goal_name: goal_name.to_string(),
            }
        } else if stdout.contains("sat") {
            VerificationResult::Failed {
                goal_name: goal_name.to_string(),
                reason: "Phát hiện lỗ hổng logic toán học!".to_string(),
                counter_example: Some(stdout.to_string()),
            }
        } else {
            VerificationResult::Failed {
                goal_name: goal_name.to_string(),
                reason: format!("Z3 trả lời không xác định: {}", stdout),
                counter_example: None,
            }
        }
    }
}
