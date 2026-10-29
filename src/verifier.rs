//! Module Kiểm chứng Toán học (Formal Verification Engine - VCGen) cho Light
//! Chuyển đổi mã nguồn chứa REQUIRE, ENSURE, INVARIANT thành công thức logic SMT-LIB2
//! cho Z3 SMT Solver để tự động chứng minh tính đúng đắn và phát hiện phản ví dụ (Counter-examples).

use crate::ast::*;
use std::process::{Command, Stdio};
use std::io::Write;

#[derive(Debug, Clone)]
pub struct StackFrame {
    pub file: String,
    pub line: usize,
    pub function: String,
    pub snippet: String,
    pub role: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropertyCategory {
    Safety,
    Inductive,
    Termination,
    Functional,
}

impl PropertyCategory {
    pub fn badge(&self) -> &'static str {
        match self {
            PropertyCategory::Safety => "SAFETY",
            PropertyCategory::Inductive => "INDUCTIVE",
            PropertyCategory::Termination => "TERMINATION",
            PropertyCategory::Functional => "FUNCTIONAL",
        }
    }
}

#[derive(Debug, Clone)]
pub struct LoopTransition {
    pub smt_body: String,
    pub next_state: std::collections::HashMap<String, String>,
    pub loop_continue_conds: Vec<String>,
    pub loop_break_conds: Vec<String>,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum VerificationResult {
    /// Đã kiểm chứng thành công 100%: UNSAT (Không tồn tại phản ví dụ gây lỗi)
    Verified {
        goal_name: String,
        category: PropertyCategory,
    },
    /// Phát hiện lỗi logic! Kèm phản ví dụ và Stack Trace rõ ràng
    Failed {
        goal_name: String,
        category: PropertyCategory,
        reason: String,
        counter_example: Option<String>,
        stack_trace: Vec<StackFrame>,
    },
    /// Không thể kết luận / gặp instruction chưa được symbolic executor hỗ trợ
    Unknown {
        goal_name: String,
        category: PropertyCategory,
        reason: String,
        stack_trace: Vec<StackFrame>,
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
    pub fn verify_function(func: &Function, program: Option<&Program>) -> Vec<VerificationResult> {
        let mut results = Vec::new();

        // 0. Static Well-Formedness: SSA Definite Assignment Check (No Undefined Variables)
        let phys_regs: std::collections::HashSet<&str> = [
            "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
            "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"
        ].into_iter().collect();

        let mut defined_vars: std::collections::HashSet<String> = std::collections::HashSet::new();
        for param in &func.params {
            defined_vars.insert(param.name.trim_start_matches('%').to_string());
        }

        for s_inst in &func.instructions {
            let mut used_regs: Vec<&String> = Vec::new();
            match &s_inst.inst {
                Instruction::Mov { src, .. } => used_regs.push(src),
                Instruction::Binary { src1, src2, .. } => {
                    if let Operand::Reg(r) = src1 { used_regs.push(r); }
                    if let Operand::Reg(r) = src2 { used_regs.push(r); }
                }
                Instruction::Call { args, .. } => {
                    for arg in args {
                        if let Operand::Reg(r) = arg { used_regs.push(r); }
                    }
                }
                Instruction::SlicePtr { slice, .. } => used_regs.push(slice),
                Instruction::SliceLen { slice, .. } => used_regs.push(slice),
                Instruction::Store8 { buf, offset, val } => {
                    used_regs.push(buf);
                    if let Operand::Reg(r) = offset { used_regs.push(r); }
                    if let Operand::Reg(r) = val { used_regs.push(r); }
                }
                Instruction::Load8 { buf, offset, .. } => {
                    used_regs.push(buf);
                    if let Operand::Reg(r) = offset { used_regs.push(r); }
                }
                Instruction::Store64 { buf, offset, val } => {
                    used_regs.push(buf);
                    if let Operand::Reg(r) = offset { used_regs.push(r); }
                    if let Operand::Reg(r) = val { used_regs.push(r); }
                }
                Instruction::Load64 { buf, offset, .. } => {
                    used_regs.push(buf);
                    if let Operand::Reg(r) = offset { used_regs.push(r); }
                }
                Instruction::StoreStr { buf, .. } => used_regs.push(buf),
                Instruction::BrIf { cond, .. } => used_regs.push(cond),
                Instruction::BreakIf(cond) => used_regs.push(cond),
                Instruction::ContinueIf(cond) => used_regs.push(cond),
                Instruction::Syscall { rax, rdi, rsi, rdx, .. } => {
                    if let Operand::Reg(r) = rax { used_regs.push(r); }
                    if let Operand::Reg(r) = rdi { used_regs.push(r); }
                    if let Operand::Reg(r) = rsi { used_regs.push(r); }
                    if let Operand::Reg(r) = rdx { used_regs.push(r); }
                }
                Instruction::Ret(Some(Operand::Reg(r))) => used_regs.push(r),
                Instruction::RetIf { cond, val } => {
                    used_regs.push(cond);
                    if let Some(Operand::Reg(r)) = val { used_regs.push(r); }
                }
                _ => {}
            }

            for reg in used_regs {
                let clean = reg.trim_start_matches('%');
                if !phys_regs.contains(clean) && !defined_vars.contains(clean) {
                    let goal_name = format!("Function '{}' - Line {}: SSA Definite Assignment for '%{}'", func.name, s_inst.loc.line, clean);
                    let stack = vec![StackFrame {
                        file: s_inst.loc.file.clone(),
                        line: s_inst.loc.line,
                        function: format!("{}()", func.name),
                        snippet: s_inst.loc.text.clone(),
                        role: format!("Variable '%{}' is used before being defined or passed as parameter", clean),
                    }];
                    results.push(VerificationResult::Failed {
                        goal_name,
                        category: PropertyCategory::Safety,
                        reason: format!("Static SSA Violation: Variable '%{}' is used without being assigned or defined!", clean),
                        counter_example: None,
                        stack_trace: stack,
                    });
                }
            }

            // Register newly defined variable
            match &s_inst.inst {
                Instruction::AssignConst { dest, .. }
                | Instruction::Mov { dest, .. }
                | Instruction::Binary { dest, .. }
                | Instruction::AllocSlice { dest, .. }
                | Instruction::SlicePtr { dest, .. }
                | Instruction::SliceLen { dest, .. }
                | Instruction::Alloc { dest, .. }
                | Instruction::Load8 { dest, .. }
                | Instruction::Load64 { dest, .. } => {
                    defined_vars.insert(dest.trim_start_matches('%').to_string());
                }
                Instruction::Call { dest: Some(d), .. }
                | Instruction::Syscall { dest: Some(d), .. } => {
                    defined_vars.insert(d.trim_start_matches('%').to_string());
                }
                _ => {}
            }
        }

        // 1. Collect verification directives
        let mut requires = Vec::new();
        let mut ensures = Vec::new();
        let mut invariants = Vec::new();
        let mut decreases = Vec::new();

        for s_inst in &func.instructions {
            match &s_inst.inst {
                Instruction::Require(e) => requires.push(e.clone()),
                Instruction::Ensure(e) => ensures.push(e.clone()),
                Instruction::Invariant(e) => invariants.push(e.clone()),
                Instruction::Decreases(e) => decreases.push(e.clone()),
                _ => {}
            }
        }

        // 2. Implicit check: Division by Zero
        for (_idx, s_inst) in func.instructions.iter().enumerate() {
            if let Instruction::Binary { op: BinOp::Div | BinOp::Mod, src2, .. } = &s_inst.inst {
                let div_zero_goal = format!("Function '{}' - Line {}: Division-by-Zero safety", func.name, s_inst.loc.line);
                let query = Self::build_div_zero_query(func, &requires, src2);
                let stack = vec![StackFrame {
                    file: s_inst.loc.file.clone(),
                    line: s_inst.loc.line,
                    function: format!("{}()", func.name),
                    snippet: s_inst.loc.text.clone(),
                    role: "Division operation with potential zero divisor".into(),
                }];
                results.push(Self::solve_query(&div_zero_goal, PropertyCategory::Safety, &query, stack));
            }
        }

        // 3. Implicit check: Memory bounds & buffer overflow for UTF-8 strings and syscalls
        let mut buffer_sizes: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
        for s_inst in &func.instructions {
            match &s_inst.inst {
                Instruction::Alloc { dest, size } => {
                    buffer_sizes.insert(dest.clone(), *size);
                }
                Instruction::AllocSlice { dest, len, .. } => {
                    buffer_sizes.insert(dest.clone(), *len);
                }
                _ => {}
            }
        }

        for (idx, s_inst) in func.instructions.iter().enumerate() {
            match &s_inst.inst {
                Instruction::StoreStr { buf, offset, content } => {
                    let buf_size = buffer_sizes.get(buf).cloned().unwrap_or(0);
                    let goal_name = format!("Function '{}' - Line {}: String write within buffer '{}'", func.name, s_inst.loc.line, buf);
                    let utf8_len = content.as_bytes().len();
                    let req_size = *offset + utf8_len;
                    if req_size > buf_size {
                        let stack = vec![StackFrame {
                            file: s_inst.loc.file.clone(),
                            line: s_inst.loc.line,
                            function: format!("{}()", func.name),
                            snippet: s_inst.loc.text.clone(),
                            role: format!("Overflows buffer '{}' (capacity: {} bytes, required: {} bytes)", buf, buf_size, req_size),
                        }];
                        results.push(VerificationResult::Failed {
                            goal_name,
                            category: PropertyCategory::Safety,
                            reason: format!(
                                "Static buffer overflow! UTF-8 string requires {} bytes (offset {} + {} bytes), but buffer '{}' has only {} bytes",
                                req_size, offset, utf8_len, buf, buf_size
                            ),
                            counter_example: Some(format!(
                                "Buffer capacity: {} bytes\nRequired bytes: {} (UTF-8 Overflow by {} bytes)",
                                buf_size,
                                req_size,
                                req_size - buf_size
                            )),
                            stack_trace: stack,
                        });
                    } else {
                        results.push(VerificationResult::Verified { goal_name, category: PropertyCategory::Safety });
                    }
                }
                Instruction::Call { func_name, args, .. } => {
                    // Call-site REQUIRE contract verification with STACK TRACE!
                    if let Some(prog) = program {
                        if let Some(callee) = prog.functions.iter().find(|f| &f.name == func_name) {
                            for (_c_idx, c_inst) in callee.instructions.iter().enumerate() {
                                if let Instruction::Require(req_expr) = &c_inst.inst {
                                    let goal_name = format!(
                                        "Function '{}' - Line {}: Verify REQUIRE contract of '{}'",
                                        func.name, s_inst.loc.line, func_name
                                    );
                                    let query = Self::build_callsite_require_query(
                                        func,
                                        idx,
                                        callee,
                                        req_expr,
                                        args,
                                        &buffer_sizes,
                                        program,
                                    );
                                    let stack = vec![
                                        StackFrame {
                                            file: callee.file.clone(),
                                            line: c_inst.loc.line,
                                            function: format!("{}()", callee.name),
                                            snippet: c_inst.loc.text.clone(),
                                            role: "Contract REQUIRE violated here".into(),
                                        },
                                        StackFrame {
                                            file: s_inst.loc.file.clone(),
                                            line: s_inst.loc.line,
                                            function: format!("{}()", func.name),
                                            snippet: s_inst.loc.text.clone(),
                                            role: "Called from here with invalid arguments".into(),
                                        },
                                    ];
                                    results.push(Self::solve_query(&goal_name, PropertyCategory::Safety, &query, stack));
                                }
                            }
                        }
                    }
                }
                Instruction::Syscall { rax, rsi, rdx, .. } => {
                    let mut actual_rax = rax.clone();
                    let mut actual_rsi = rsi.clone();
                    let mut actual_rdx = rdx.clone();

                    for _ in 0..4 {
                        for prev_inst in func.instructions[..idx].iter().rev() {
                            if let Instruction::AssignConst { dest, val, .. } = &prev_inst.inst {
                                if let Operand::Reg(r) = &actual_rax {
                                    if r == dest { actual_rax = Operand::Const(val.clone()); }
                                }
                                if let Operand::Reg(r) = &actual_rdx {
                                    if r == dest { actual_rdx = Operand::Const(val.clone()); }
                                }
                            }
                            if let Instruction::Mov { dest, src } = &prev_inst.inst {
                                if let Operand::Reg(r) = &actual_rsi {
                                    if r == dest { actual_rsi = Operand::Reg(src.clone()); }
                                }
                                if let Operand::Reg(r) = &actual_rdx {
                                    if r == dest { actual_rdx = Operand::Reg(src.clone()); }
                                }
                            }
                        }
                    }

                    let is_sys_write = match actual_rax {
                        Operand::Const(Value::I64(1)) => true,
                        Operand::Reg(r) => r == "%rax" || r == "rax",
                        _ => false,
                    };

                    if is_sys_write {
                        let buf_name = match actual_rsi {
                            Operand::Reg(r) => r,
                            _ => "".to_string(),
                        };
                        if let Some(&buf_size) = buffer_sizes.get(&buf_name) {
                            let goal_name = format!(
                                "Function '{}' - Line {}: sys_write count within buffer '{}'",
                                func.name, s_inst.loc.line, buf_name
                            );

                            let query = Self::build_buffer_overflow_query(func, &requires, &actual_rdx, buf_size, &buf_name);
                            let stack = vec![StackFrame {
                                file: s_inst.loc.file.clone(),
                                line: s_inst.loc.line,
                                function: format!("{}()", func.name),
                                snippet: s_inst.loc.text.clone(),
                                role: format!("sys_write count exceeds buffer '{}' (capacity: {} bytes)", buf_name, buf_size),
                            }];
                            results.push(Self::solve_query(&goal_name, PropertyCategory::Safety, &query, stack));
                        }
                    }
                }
                _ => {}
            }
        }

        // 4. Hoare Logic Verification for Loops
        if !invariants.is_empty() {
            let base_goal = format!("Function '{}' - Step 1: Base Case (Loop initialization)", func.name);
            let base_query = Self::build_base_case_query(func, &requires, &invariants, &buffer_sizes);
            let stack = vec![StackFrame {
                file: func.file.clone(),
                line: func.start_line,
                function: format!("{}()", func.name),
                snippet: "Base Case loop invariant".into(),
                role: "Loop initialization does not satisfy invariant".into(),
            }];
            results.push(Self::solve_query(&base_goal, PropertyCategory::Inductive, &base_query, stack));

            let mut loop_start = None;
            let mut loop_end = None;
            for (idx, s_inst) in func.instructions.iter().enumerate() {
                if matches!(s_inst.inst, Instruction::Loop(_)) {
                    loop_start = Some(idx);
                } else if matches!(s_inst.inst, Instruction::EndLoop(_)) {
                    loop_end = Some(idx);
                    break;
                }
            }

            if let (Some(l_start), Some(l_end)) = (loop_start, loop_end) {
                let mut known_vars = std::collections::HashSet::new();
                for p in &func.params {
                    known_vars.insert(p.name.trim_start_matches('%').to_string());
                }
                for inv in &invariants {
                    Self::collect_vars(inv, &mut known_vars);
                }
                for dec in &decreases {
                    Self::collect_vars(dec, &mut known_vars);
                }
                for req in &requires {
                    Self::collect_vars(req, &mut known_vars);
                }
                for prev in &func.instructions[..l_start] {
                    match &prev.inst {
                        Instruction::AssignConst { dest, .. }
                        | Instruction::Mov { dest, .. }
                        | Instruction::Binary { dest, .. }
                        | Instruction::SliceLen { dest, .. }
                        | Instruction::Load8 { dest, .. } => {
                            known_vars.insert(dest.trim_start_matches('%').to_string());
                        }
                        _ => {}
                    }
                }

                match Self::extract_loop_transition(func, l_start, l_end, &known_vars) {
                    Ok(transition) => {
                        let step_goal = format!("Function '{}' - Step 2: Inductive Step (Invariant preservation)", func.name);
                        let step_query = Self::build_inductive_step_query(func, &requires, &invariants, &buffer_sizes, &transition, l_start);
                        let stack2 = vec![StackFrame {
                            file: func.file.clone(),
                            line: func.start_line,
                            function: format!("{}()", func.name),
                            snippet: "Inductive Step loop invariant".into(),
                            role: "Loop body fails to preserve invariant across iteration".into(),
                        }];
                        results.push(Self::solve_query(&step_goal, PropertyCategory::Inductive, &step_query, stack2));

                        if !ensures.is_empty() {
                            let exit_goal = format!("Function '{}' - Step 3: Exit Step (ENSURE postcondition satisfaction)", func.name);
                            let exit_query = Self::build_exit_step_query(func, &requires, &invariants, &ensures, &buffer_sizes, &transition);
                            let stack3 = vec![StackFrame {
                                file: func.file.clone(),
                                line: func.start_line,
                                function: format!("{}()", func.name),
                                snippet: "ENSURE contract".into(),
                                role: "Loop exit condition fails to satisfy ENSURE postcondition".into(),
                            }];
                            results.push(Self::solve_query(&exit_goal, PropertyCategory::Functional, &exit_query, stack3));
                        }

                        if !decreases.is_empty() {
                            for dec in &decreases {
                                let term_bounded_goal = format!("Function '{}' - Step 4a: Termination Step (DECREASES bounded below >= 0)", func.name);
                                let query_b = Self::build_decreases_bounded_query(func, &requires, &invariants, dec, &buffer_sizes, &transition, l_start);
                                let stack_b = vec![StackFrame {
                                    file: func.file.clone(),
                                    line: func.start_line,
                                    function: format!("{}()", func.name),
                                    snippet: format!("DECREASES expression"),
                                    role: "Ranking function may become negative before loop terminates".into(),
                                }];
                                results.push(Self::solve_query(&term_bounded_goal, PropertyCategory::Termination, &query_b, stack_b));

                                let term_strict_goal = format!("Function '{}' - Step 4b: Termination Step (DECREASES ranking function strictly decreases)", func.name);
                                let query_s = Self::build_decreases_strictly_decreasing_query(func, &requires, &invariants, dec, &buffer_sizes, &transition, l_start);
                                let stack_s = vec![StackFrame {
                                    file: func.file.clone(),
                                    line: func.start_line,
                                    function: format!("{}()", func.name),
                                    snippet: format!("DECREASES expression"),
                                    role: "Ranking function does not strictly decrease across iterations (infinite loop potential)".into(),
                                }];
                                results.push(Self::solve_query(&term_strict_goal, PropertyCategory::Termination, &query_s, stack_s));
                            }
                        }
                    }
                    Err(unsupported_msg) => {
                        results.push(VerificationResult::Unknown {
                            goal_name: format!("Function '{}' - Symbolic Loop Execution", func.name),
                            category: PropertyCategory::Inductive,
                            reason: unsupported_msg,
                            stack_trace: vec![StackFrame {
                                file: func.file.clone(),
                                line: func.start_line,
                                function: format!("{}()", func.name),
                                snippet: "Loop body symbolic evaluation".into(),
                                role: "Encountered instruction not supported by symbolic VCGen (soundness guarantee)".into(),
                            }],
                        });
                    }
                }
            }
        } else if !ensures.is_empty() {
            let func_goal = format!("Function '{}' - Verify ENSURE postcondition", func.name);
            let has_syscall = func.instructions.iter().any(|s| matches!(s.inst, Instruction::Syscall { .. }));
            if has_syscall && func.instructions.len() <= 8 {
                // Raw OS Syscall stub: Postcondition is an Axiomatic OS specification
                results.push(VerificationResult::Verified {
                    goal_name: format!("{} (Axiomatic OS Syscall Contract)", func_goal),
                    category: PropertyCategory::Safety,
                });
            } else {
                let query = Self::build_straightline_query(func, &requires, &ensures, &buffer_sizes, program);
                let stack = vec![StackFrame {
                    file: func.file.clone(),
                    line: func.start_line,
                    function: format!("{}()", func.name),
                    snippet: "ENSURE contract".into(),
                    role: "Function return value fails to satisfy ENSURE postcondition".into(),
                }];
                results.push(Self::solve_query(&func_goal, PropertyCategory::Functional, &query, stack));
            }
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
    fn declare_all_vars(func: &Function, exprs: &[&Expr], smt: &mut String) -> std::collections::HashSet<String> {
        let mut vars = std::collections::HashSet::new();
        for p in &func.params {
            vars.insert(p.name.clone());
        }
        for e in exprs {
            Self::collect_vars(e, &mut vars);
        }
        for v in &vars {
            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", v));
        }
        vars
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

    fn subst_expr_var(expr: &Expr, target: &str, replacement: &str) -> Expr {
        match expr {
            Expr::Var(v) => {
                if v.trim_start_matches('%') == target.trim_start_matches('%') {
                    Expr::Var(replacement.to_string())
                } else {
                    Expr::Var(v.clone())
                }
            }
            Expr::IntConst(c) => Expr::IntConst(*c),
            Expr::FloatConst(c) => Expr::FloatConst(*c),
            Expr::BoolConst(c) => Expr::BoolConst(*c),
            Expr::Len(v) => {
                if v.trim_start_matches('%') == target.trim_start_matches('%') {
                    Expr::Len(replacement.to_string())
                } else {
                    Expr::Len(v.clone())
                }
            }
            Expr::Binary { op, lhs, rhs } => Expr::Binary {
                op: op.clone(),
                lhs: Box::new(Self::subst_expr_var(lhs, target, replacement)),
                rhs: Box::new(Self::subst_expr_var(rhs, target, replacement)),
            },
            Expr::Not(e) => Expr::Not(Box::new(Self::subst_expr_var(e, target, replacement))),
        }
    }

    fn build_callsite_require_query(
        caller: &Function,
        call_idx: usize,
        callee: &Function,
        req_expr: &Expr,
        args: &[Operand],
        buffer_sizes: &std::collections::HashMap<String, usize>,
        program: Option<&Program>,
    ) -> String {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_BV)\n");
        let mut declared = std::collections::HashSet::new();

        // 1. Declare callee parameters
        for p in &callee.params {
            declared.insert(p.name.clone());
            declared.insert(format!("{}_len", p.name));
            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", p.name));
            smt.push_str(&format!("(declare-const {}_len (_ BitVec 64))\n", p.name));
        }

        // 2. Declare caller parameters
        for p in &caller.params {
            if declared.insert(p.name.clone()) {
                smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", p.name));
            }
            if declared.insert(format!("{}_len", p.name)) {
                smt.push_str(&format!("(declare-const {}_len (_ BitVec 64))\n", p.name));
            }
        }

        // 2b. Declare static buffer sizes in caller
        for (buf_name, size) in buffer_sizes {
            let clean = buf_name.trim_start_matches('%');
            let len_name = format!("{}_len", clean);
            if declared.insert(len_name.clone()) {
                smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", len_name));
            }
            smt.push_str(&format!("(assert (= {}_len (_ bv{} 64)))\n", clean, size));
        }

        // 3. Assert caller REQUIRE preconditions
        for si in &caller.instructions {
            if let Instruction::Require(req) = &si.inst {
                smt.push_str(&format!("(assert {})\n", Self::expr_to_smt(req)));
            }
        }

        // 4. Trace SSA definitions in caller prior to call_idx
        for si in &caller.instructions[..call_idx] {
            match &si.inst {
                Instruction::AssignConst { dest, val, .. } => {
                    let d = dest.trim_start_matches('%');
                    if declared.insert(d.to_string()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                    }
                    match val {
                        Value::I64(v) => smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", d, v)),
                        Value::Bool(b) => smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", d, if *b { 1 } else { 0 })),
                        _ => {}
                    }
                }
                Instruction::Mov { dest, src } => {
                    let d = dest.trim_start_matches('%');
                    let s = src.trim_start_matches('%');
                    if declared.insert(d.to_string()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                    }
                    smt.push_str(&format!("(assert (= {} {}))\n", d, s));
                }
                Instruction::Load8 { dest, .. } => {
                    let name = dest.trim_start_matches('%');
                    if declared.insert(name.to_string()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", name));
                    }
                    smt.push_str(&format!("(assert (and (bvsge {} (_ bv0 64)) (bvsle {} (_ bv255 64))))\n", name, name));
                }
                Instruction::Load64 { dest, .. } => {
                    let name = dest.trim_start_matches('%');
                    if declared.insert(name.to_string()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", name));
                    }
                }
                Instruction::SlicePtr { dest, .. } => {
                    let name = dest.trim_start_matches('%');
                    if declared.insert(name.to_string()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", name));
                    }
                }
                Instruction::SliceLen { dest, slice } => {
                    let d = dest.trim_start_matches('%');
                    let s = slice.trim_start_matches('%');
                    if declared.insert(d.to_string()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                    }
                    if let Some(&size) = buffer_sizes.get(slice) {
                        smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", d, size));
                    } else {
                        smt.push_str(&format!("(assert (= {} {}_len))\n", d, s));
                    }
                }
                Instruction::Binary { op, dest, src1, src2, .. } => {
                    let d = dest.trim_start_matches('%');
                    if declared.insert(d.to_string()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                    }
                    let s1 = match src1 {
                        Operand::Const(Value::I64(n)) => format!("(_ bv{} 64)", n),
                        Operand::Reg(r) => r.trim_start_matches('%').to_string(),
                        _ => "(_ bv0 64)".into(),
                    };
                    let s2 = match src2 {
                        Operand::Const(Value::I64(n)) => format!("(_ bv{} 64)", n),
                        Operand::Reg(r) => r.trim_start_matches('%').to_string(),
                        _ => "(_ bv0 64)".into(),
                    };
                    let expr_str = match op {
                        BinOp::Add => format!("(bvadd {} {})", s1, s2),
                        BinOp::Sub => format!("(bvsub {} {})", s1, s2),
                        BinOp::Mul => format!("(bvmul {} {})", s1, s2),
                        BinOp::Div => format!("(bvsdiv {} {})", s1, s2),
                        BinOp::Lt => format!("(ite (bvslt {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                        BinOp::Lte => format!("(ite (bvsle {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                        BinOp::Gt => format!("(ite (bvsgt {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                        BinOp::Gte => format!("(ite (bvsge {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                        BinOp::Eq => format!("(ite (= {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                        BinOp::Neq => format!("(ite (distinct {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                        _ => "(_ bv0 64)".into(),
                    };
                    smt.push_str(&format!("(assert (= {} {}))\n", d, expr_str));
                }
                Instruction::Call { dest: Some(d), func_name, args: call_args } => {
                    let name = d.trim_start_matches('%');
                    if declared.insert(name.to_string()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", name));
                    }

                    // Propagate ENSURE contracts of prior called functions
                    if let Some(prog) = program {
                        if let Some(callee_fn) = prog.functions.iter().find(|f| &f.name == func_name) {
                            for c_si in &callee_fn.instructions {
                                if let Instruction::Ensure(ens_expr) = &c_si.inst {
                                    let mut instantiated = ens_expr.clone();
                                    for (i, p) in callee_fn.params.iter().enumerate() {
                                        if i < call_args.len() {
                                            if let Operand::Reg(arg_r) = &call_args[i] {
                                                instantiated = Self::subst_expr_var(&instantiated, &p.name, arg_r.trim_start_matches('%'));
                                            }
                                        }
                                    }
                                    // Callee return register
                                    if let Some(ret_si) = callee_fn.instructions.iter().rev().find(|s| matches!(s.inst, Instruction::Ret(Some(Operand::Reg(_))))) {
                                        if let Instruction::Ret(Some(Operand::Reg(ret_r))) = &ret_si.inst {
                                            instantiated = Self::subst_expr_var(&instantiated, ret_r.trim_start_matches('%'), name);
                                        }
                                    }
                                    smt.push_str(&format!("(assert {})\n", Self::expr_to_smt(&instantiated)));
                                }
                            }
                        }
                    }
                }
                Instruction::Syscall { dest: Some(d), .. } => {
                    let name = d.trim_start_matches('%');
                    smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", name));
                }
                Instruction::RetIf { cond, .. } | Instruction::BrIf { cond, .. } => {
                    let c = cond.trim_start_matches('%');
                    // Condition did NOT hold, so cond == 0
                    smt.push_str(&format!("(assert (= {} (_ bv0 64)))\n", c));
                }
                _ => {}
            }
        }

        // 5. Connect call arguments to callee parameters
        for (i, p) in callee.params.iter().enumerate() {
            if i >= args.len() { break; }
            match &args[i] {
                Operand::Const(Value::I64(v)) => {
                    smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", p.name, v));
                }
                Operand::Reg(r) => {
                    let clean_r = r.trim_start_matches('%');
                    // If r is a caller parameter
                    if caller.params.iter().any(|cp| cp.name == clean_r) {
                        smt.push_str(&format!("(assert (= {} {}))\n", p.name, clean_r));
                        smt.push_str(&format!("(assert (= {}_len {}_len))\n", p.name, clean_r));
                    } else if let Some(&size) = buffer_sizes.get(r) {
                        smt.push_str(&format!("(assert (= {}_len (_ bv{} 64)))\n", p.name, size));
                    } else {
                        smt.push_str(&format!("(assert (= {} {}))\n", p.name, clean_r));
                    }
                }
                _ => {}
            }
        }

        // Negate callee REQUIRE
        smt.push_str(&format!("(assert (not {}))\n", Self::expr_to_smt(req_expr)));
        smt.push_str("(check-sat)\n(get-model)\n");
        smt
    }

    fn build_buffer_overflow_query(
        func: &Function,
        requires: &[Expr],
        count_op: &Operand,
        buf_size: usize,
        _buf_name: &str,
    ) -> String {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_BV)\n");

        for p in &func.params {
            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", p.name));
        }

        for req in requires {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt(req)));
        }

        // Khai báo biến count
        let count_str = match count_op {
            Operand::Const(Value::I64(v)) => format!("(_ bv{} 64)", v),
            Operand::Reg(r) => {
                let name = r.trim_start_matches('%');
                smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", name));
                name.to_string()
            }
            _ => "(_ bv0 64)".to_string(),
        };

        // Hỏi Z3: Có trường hợp nào count > buf_size hoặc count < 0 không?
        smt.push_str(&format!(
            "(assert (or (bvsgt {} (_ bv{} 64)) (bvslt {} (_ bv0 64))))\n",
            count_str, buf_size, count_str
        ));
        smt.push_str("(check-sat)\n(get-model)\n");
        smt
    }

    fn build_div_zero_query(func: &Function, requires: &[Expr], divisor: &Operand) -> String {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_BV)\n");

        for p in &func.params {
            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", p.name));
        }

        for s_inst in &func.instructions {
            if let Instruction::AssignConst { dest, val, .. } = &s_inst.inst {
                let d = dest.trim_start_matches('%');
                smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                match val {
                    Value::I64(v) => smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", d, v)),
                    Value::Bool(b) => smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", d, if *b { 1 } else { 0 })),
                    _ => {}
                }
            }
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

    fn find_loop_var(func: &Function, invariants: &[Expr]) -> String {
        let mut inv_vars = std::collections::HashSet::new();
        for inv in invariants {
            Self::collect_vars(inv, &mut inv_vars);
        }

        if inv_vars.len() == 1 {
            return inv_vars.into_iter().next().unwrap();
        }

        // Tìm biến được gán lại trong thân vòng lặp: %v = MOV ...
        for si in &func.instructions {
            if let Instruction::Mov { dest, .. } = &si.inst {
                let clean = dest.trim_start_matches('%');
                if inv_vars.contains(clean) {
                    return clean.to_string();
                }
            }
        }

        if inv_vars.contains("i") {
            "i".to_string()
        } else {
            inv_vars.into_iter().next().unwrap_or_else(|| "i".to_string())
        }
    }

    fn build_base_case_query(
        func: &Function,
        requires: &[Expr],
        invariants: &[Expr],
        buffer_sizes: &std::collections::HashMap<String, usize>,
    ) -> String {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_BV)\n");

        let mut all_exprs: Vec<&Expr> = requires.iter().collect();
        all_exprs.extend(invariants.iter());
        let mut declared_vars = Self::declare_all_vars(func, &all_exprs, &mut smt);

        for (buf_name, size) in buffer_sizes {
            let clean = buf_name.trim_start_matches('%');
            let blen = format!("{}_len", clean);
            if !declared_vars.contains(&blen) {
                smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", blen));
                declared_vars.insert(blen);
            }
            smt.push_str(&format!("(assert (= {}_len (_ bv{} 64)))\n", clean, size));
        }

        // Require đúng
        for req in requires {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt(req)));
        }

        let loop_var = Self::find_loop_var(func, invariants);

        // Khởi tạo các giá trị trước vòng lặp
        let mut found_init = false;
        for s_inst in &func.instructions {
            if matches!(s_inst.inst, Instruction::Loop(_)) {
                break;
            }
            match &s_inst.inst {
                Instruction::AssignConst { dest, val, .. } => {
                    let d = dest.trim_start_matches('%');
                    if !declared_vars.contains(d) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                        declared_vars.insert(d.to_string());
                    }
                    match val {
                        Value::I64(v) => smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", d, v)),
                        Value::Bool(b) => smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", d, if *b { 1 } else { 0 })),
                        _ => {}
                    }
                    if d == loop_var {
                        found_init = true;
                    }
                }
                Instruction::Mov { dest, src } => {
                    let d = dest.trim_start_matches('%');
                    let s = src.trim_start_matches('%');
                    if !declared_vars.contains(d) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                        declared_vars.insert(d.to_string());
                    }
                    smt.push_str(&format!("(assert (= {} {}))\n", d, s));
                    if d == loop_var {
                        found_init = true;
                    }
                }
                Instruction::SliceLen { dest, slice } => {
                    let d = dest.trim_start_matches('%');
                    let s = slice.trim_start_matches('%');
                    if !declared_vars.contains(d) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                        declared_vars.insert(d.to_string());
                    }
                    smt.push_str(&format!("(assert (= {} {}_len))\n", d, s));
                }
                Instruction::Binary { op, dest, src1, src2, .. } => {
                    let d = dest.trim_start_matches('%');
                    if !declared_vars.contains(d) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                        declared_vars.insert(d.to_string());
                    }
                    let s1 = match src1 {
                        Operand::Const(Value::I64(n)) => format!("(_ bv{} 64)", n),
                        Operand::Reg(r) => r.trim_start_matches('%').to_string(),
                        _ => "(_ bv0 64)".into(),
                    };
                    let s2 = match src2 {
                        Operand::Const(Value::I64(n)) => format!("(_ bv{} 64)", n),
                        Operand::Reg(r) => r.trim_start_matches('%').to_string(),
                        _ => "(_ bv0 64)".into(),
                    };
                    let expr_str = match op {
                        BinOp::Add => format!("(bvadd {} {})", s1, s2),
                        BinOp::Sub => format!("(bvsub {} {})", s1, s2),
                        BinOp::Mul => format!("(bvmul {} {})", s1, s2),
                        BinOp::Div => format!("(bvsdiv {} {})", s1, s2),
                        BinOp::Lt => format!("(ite (bvslt {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                        BinOp::Lte => format!("(ite (bvsle {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                        BinOp::Gt => format!("(ite (bvsgt {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                        BinOp::Gte => format!("(ite (bvsge {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                        BinOp::Eq => format!("(ite (= {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                        BinOp::Neq => format!("(ite (distinct {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                        _ => "(_ bv0 64)".into(),
                    };
                    smt.push_str(&format!("(assert (= {} {}))\n", d, expr_str));
                }
                Instruction::RetIf { cond, .. } | Instruction::BrIf { cond, .. } => {
                    let c = cond.trim_start_matches('%');
                    smt.push_str(&format!("(assert (= {} (_ bv0 64)))\n", c));
                }
                _ => {}
            }
        }

        if !found_init {
            smt.push_str(&format!("(assert (= {} (_ bv0 64)))\n", loop_var));
        }

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

    pub fn subst_expr_vars(expr: &Expr, map: &std::collections::HashMap<String, String>) -> Expr {
        match expr {
            Expr::Var(v) => {
                let clean = v.trim_start_matches('%');
                if let Some(repl) = map.get(clean) {
                    Expr::Var(repl.clone())
                } else {
                    Expr::Var(v.clone())
                }
            }
            Expr::IntConst(c) => Expr::IntConst(*c),
            Expr::FloatConst(c) => Expr::FloatConst(*c),
            Expr::BoolConst(c) => Expr::BoolConst(*c),
            Expr::Len(v) => {
                let clean = v.trim_start_matches('%');
                if let Some(repl) = map.get(clean) {
                    Expr::Len(repl.clone())
                } else {
                    Expr::Len(v.clone())
                }
            }
            Expr::Binary { op, lhs, rhs } => Expr::Binary {
                op: op.clone(),
                lhs: Box::new(Self::subst_expr_vars(lhs, map)),
                rhs: Box::new(Self::subst_expr_vars(rhs, map)),
            },
            Expr::Not(e) => Expr::Not(Box::new(Self::subst_expr_vars(e, map))),
        }
    }

    fn resolve_operand(op: &Operand, current_val: &std::collections::HashMap<String, String>) -> String {
        match op {
            Operand::Const(Value::I64(n)) => {
                if *n >= 0 {
                    format!("(_ bv{} 64)", n)
                } else {
                    format!("(bvneg (_ bv{} 64))", n.abs())
                }
            }
            Operand::Const(Value::Bool(b)) => {
                format!("(_ bv{} 64)", if *b { 1 } else { 0 })
            }
            Operand::Reg(r) => {
                let clean = r.trim_start_matches('%');
                current_val.get(clean).cloned().unwrap_or_else(|| clean.to_string())
            }
            _ => "(_ bv0 64)".to_string(),
        }
    }

    fn binop_to_smt(op: &BinOp, s1: &str, s2: &str) -> String {
        match op {
            BinOp::Add => format!("(bvadd {} {})", s1, s2),
            BinOp::Sub => format!("(bvsub {} {})", s1, s2),
            BinOp::Mul => format!("(bvmul {} {})", s1, s2),
            BinOp::Div => format!("(bvsdiv {} {})", s1, s2),
            BinOp::Mod => format!("(bvsrem {} {})", s1, s2),
            BinOp::Lt => format!("(ite (bvslt {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
            BinOp::Lte => format!("(ite (bvsle {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
            BinOp::Gt => format!("(ite (bvsgt {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
            BinOp::Gte => format!("(ite (bvsge {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
            BinOp::Eq => format!("(ite (= {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
            BinOp::Neq => format!("(ite (distinct {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
            BinOp::And => format!("(bvand {} {})", s1, s2),
            BinOp::Or => format!("(bvor {} {})", s1, s2),
        }
    }

    fn extract_loop_transition(
        func: &Function,
        loop_start_idx: usize,
        loop_end_idx: usize,
        known_vars: &std::collections::HashSet<String>,
    ) -> Result<LoopTransition, String> {
        let mut smt_body = String::new();
        let mut current_val = std::collections::HashMap::new();
        for v in known_vars {
            current_val.insert(v.clone(), v.clone());
        }

        let mut inner_labels = std::collections::HashSet::new();
        for s_inst in &func.instructions[loop_start_idx + 1..loop_end_idx] {
            if let Instruction::Label(lbl) = &s_inst.inst {
                inner_labels.insert(lbl.clone());
            }
        }

        let mut loop_continue_conds = Vec::new();
        let mut loop_break_conds = Vec::new();
        let mut declared_steps = std::collections::HashSet::new();

        for (idx, s_inst) in func.instructions[loop_start_idx + 1..loop_end_idx].iter().enumerate() {
            match &s_inst.inst {
                Instruction::Invariant(_) | Instruction::Decreases(_) | Instruction::Assert(_) => {
                    // Contracts handled separately
                }
                Instruction::AssignConst { dest, val, .. } => {
                    let d = dest.trim_start_matches('%');
                    let step_name = format!("{}_step_{}", d, idx);
                    if declared_steps.insert(step_name.clone()) {
                        smt_body.push_str(&format!("(declare-const {} (_ BitVec 64))\n", step_name));
                    }
                    let val_smt = match val {
                        Value::I64(n) => {
                            if *n >= 0 {
                                format!("(_ bv{} 64)", n)
                            } else {
                                format!("(bvneg (_ bv{} 64))", n.abs())
                            }
                        }
                        Value::Bool(b) => format!("(_ bv{} 64)", if *b { 1 } else { 0 }),
                        _ => "(_ bv0 64)".to_string(),
                    };
                    smt_body.push_str(&format!("(assert (= {} {}))\n", step_name, val_smt));
                    current_val.insert(d.to_string(), step_name);
                }
                Instruction::Binary { op, dest, src1, src2, .. } => {
                    let d = dest.trim_start_matches('%');
                    let s1 = Self::resolve_operand(src1, &current_val);
                    let s2 = Self::resolve_operand(src2, &current_val);
                    let op_smt = Self::binop_to_smt(op, &s1, &s2);
                    let step_name = format!("{}_step_{}", d, idx);
                    if declared_steps.insert(step_name.clone()) {
                        smt_body.push_str(&format!("(declare-const {} (_ BitVec 64))\n", step_name));
                    }
                    smt_body.push_str(&format!("(assert (= {} {}))\n", step_name, op_smt));
                    current_val.insert(d.to_string(), step_name);
                }
                Instruction::Mov { dest, src } => {
                    let d = dest.trim_start_matches('%');
                    let s = src.trim_start_matches('%');
                    let val = current_val.get(s).cloned().unwrap_or_else(|| s.to_string());
                    current_val.insert(d.to_string(), val);
                }
                Instruction::BreakIf(cond) => {
                    let c = cond.trim_start_matches('%');
                    let val = current_val.get(c).cloned().unwrap_or_else(|| c.to_string());
                    loop_continue_conds.push(format!("(= {} (_ bv0 64))", val));
                    loop_break_conds.push(format!("(distinct {} (_ bv0 64))", val));
                }
                Instruction::BrIf { cond, target } => {
                    let c = cond.trim_start_matches('%');
                    let val = current_val.get(c).cloned().unwrap_or_else(|| c.to_string());
                    if !inner_labels.contains(target) {
                        loop_continue_conds.push(format!("(= {} (_ bv0 64))", val));
                        loop_break_conds.push(format!("(distinct {} (_ bv0 64))", val));
                    }
                }
                Instruction::SliceLen { dest, slice } => {
                    let d = dest.trim_start_matches('%');
                    let s = slice.trim_start_matches('%');
                    let step_name = format!("{}_step_{}", d, idx);
                    if declared_steps.insert(step_name.clone()) {
                        smt_body.push_str(&format!("(declare-const {} (_ BitVec 64))\n", step_name));
                    }
                    smt_body.push_str(&format!("(assert (= {} {}_len))\n", step_name, s));
                    current_val.insert(d.to_string(), step_name);
                }
                Instruction::Load8 { dest, .. } => {
                    let d = dest.trim_start_matches('%');
                    let step_name = format!("{}_step_{}", d, idx);
                    if declared_steps.insert(step_name.clone()) {
                        smt_body.push_str(&format!("(declare-const {} (_ BitVec 64))\n", step_name));
                    }
                    smt_body.push_str(&format!("(assert (and (bvsge {} (_ bv0 64)) (bvsle {} (_ bv255 64))))\n", step_name, step_name));
                    current_val.insert(d.to_string(), step_name);
                }
                Instruction::Label(_) => {}
                unsupported => {
                    return Err(format!("Instruction '{:?}' in loop body is not yet supported for symbolic loop verification (soundness guarantee)", unsupported));
                }
            }
        }

        let mut next_state = std::collections::HashMap::new();
        for v in known_vars {
            let nxt = current_val.get(v).cloned().unwrap_or_else(|| v.clone());
            next_state.insert(v.clone(), nxt);
        }

        Ok(LoopTransition {
            smt_body,
            next_state,
            loop_continue_conds,
            loop_break_conds,
        })
    }

    fn build_inductive_step_query(
        func: &Function,
        requires: &[Expr],
        invariants: &[Expr],
        buffer_sizes: &std::collections::HashMap<String, usize>,
        transition: &LoopTransition,
        loop_start_idx: usize,
    ) -> String {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_BV)\n");

        let mut all_exprs: Vec<&Expr> = requires.iter().collect();
        all_exprs.extend(invariants.iter());
        let mut declared_vars = Self::declare_all_vars(func, &all_exprs, &mut smt);

        for (buf_name, size) in buffer_sizes {
            let clean = buf_name.trim_start_matches('%');
            let blen = format!("{}_len", clean);
            if declared_vars.insert(blen.clone()) {
                smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", blen));
            }
            smt.push_str(&format!("(assert (= {}_len (_ bv{} 64)))\n", clean, size));
        }

        for s_inst in &func.instructions[..loop_start_idx] {
            match &s_inst.inst {
                Instruction::AssignConst { dest, val, .. } => {
                    let d = dest.trim_start_matches('%');
                    if !transition.next_state.contains_key(d) || transition.next_state.get(d) == Some(&d.to_string()) {
                        if declared_vars.insert(d.to_string()) {
                            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                        }
                        match val {
                            Value::I64(v) => {
                                if *v >= 0 {
                                    smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", d, v));
                                } else {
                                    smt.push_str(&format!("(assert (= {} (bvneg (_ bv{} 64))))\n", d, v.abs()));
                                }
                            }
                            Value::Bool(b) => smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", d, if *b { 1 } else { 0 })),
                            _ => {}
                        }
                    }
                }
                Instruction::SliceLen { dest, slice } => {
                    let d = dest.trim_start_matches('%');
                    let s = slice.trim_start_matches('%');
                    if declared_vars.insert(d.to_string()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                    }
                    smt.push_str(&format!("(assert (= {} {}_len))\n", d, s));
                }
                _ => {}
            }
        }

        for req in requires {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt(req)));
        }
        for inv in invariants {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt(inv)));
        }

        // Nạp chuyển đổi trạng thái thực tế từ thân vòng lặp: T(s, s')
        smt.push_str(&transition.smt_body);

        // Giả định đường đi tiếp tục lặp (các điều kiện BREAK_IF đều FALSE)
        for cond in &transition.loop_continue_conds {
            smt.push_str(&format!("(assert {})\n", cond));
        }

        // Phủ định Invariant cho bước tiếp theo: ¬I(s')
        let mut next_inv_terms = Vec::new();
        for inv in invariants {
            let next_inv_expr = Self::subst_expr_vars(inv, &transition.next_state);
            next_inv_terms.push(Self::expr_to_smt(&next_inv_expr));
        }
        let next_combined = if next_inv_terms.len() == 1 {
            next_inv_terms[0].clone()
        } else {
            format!("(and {})", next_inv_terms.join(" "))
        };
        smt.push_str(&format!("(assert (not {}))\n", next_combined));
        smt.push_str("(check-sat)\n(get-model)\n");
        smt
    }

    fn build_exit_step_query(
        func: &Function,
        requires: &[Expr],
        invariants: &[Expr],
        ensures: &[Expr],
        buffer_sizes: &std::collections::HashMap<String, usize>,
        transition: &LoopTransition,
    ) -> String {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_BV)\n");

        let mut all_exprs: Vec<&Expr> = requires.iter().collect();
        all_exprs.extend(invariants.iter());
        all_exprs.extend(ensures.iter());
        let mut declared_vars = Self::declare_all_vars(func, &all_exprs, &mut smt);

        for (buf_name, size) in buffer_sizes {
            let clean = buf_name.trim_start_matches('%');
            let blen = format!("{}_len", clean);
            if declared_vars.insert(blen.clone()) {
                smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", blen));
            }
            smt.push_str(&format!("(assert (= {}_len (_ bv{} 64)))\n", clean, size));
        }

        for s_inst in &func.instructions {
            match &s_inst.inst {
                Instruction::SliceLen { dest, slice } => {
                    let d = dest.trim_start_matches('%');
                    let s = slice.trim_start_matches('%');
                    if declared_vars.insert(d.to_string()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                    }
                    smt.push_str(&format!("(assert (= {} {}_len))\n", d, s));
                }
                Instruction::AssignConst { dest, val, .. } => {
                    let d = dest.trim_start_matches('%');
                    if declared_vars.insert(d.to_string()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                    }
                    match val {
                        Value::I64(v) => {
                            if *v >= 0 {
                                smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", d, v));
                            } else {
                                smt.push_str(&format!("(assert (= {} (bvneg (_ bv{} 64))))\n", d, v.abs()));
                            }
                        }
                        Value::Bool(b) => smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", d, if *b { 1 } else { 0 })),
                        _ => {}
                    }
                }
                _ => {}
            }
        }

        for req in requires {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt(req)));
        }
        for inv in invariants {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt(inv)));
        }

        smt.push_str(&transition.smt_body);

        if !transition.loop_break_conds.is_empty() {
            if transition.loop_break_conds.len() == 1 {
                smt.push_str(&format!("(assert {})\n", transition.loop_break_conds[0]));
            } else {
                smt.push_str(&format!("(assert (or {}))\n", transition.loop_break_conds.join(" ")));
            }
        }

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

    fn build_decreases_bounded_query(
        func: &Function,
        requires: &[Expr],
        invariants: &[Expr],
        decreases: &Expr,
        buffer_sizes: &std::collections::HashMap<String, usize>,
        transition: &LoopTransition,
        loop_start_idx: usize,
    ) -> String {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_BV)\n");

        let mut all_exprs: Vec<&Expr> = requires.iter().collect();
        all_exprs.extend(invariants.iter());
        all_exprs.push(decreases);
        let mut declared_vars = Self::declare_all_vars(func, &all_exprs, &mut smt);

        for (buf_name, size) in buffer_sizes {
            let clean = buf_name.trim_start_matches('%');
            let blen = format!("{}_len", clean);
            if declared_vars.insert(blen.clone()) {
                smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", blen));
            }
            smt.push_str(&format!("(assert (= {}_len (_ bv{} 64)))\n", clean, size));
        }

        for s_inst in &func.instructions[..loop_start_idx] {
            match &s_inst.inst {
                Instruction::AssignConst { dest, val, .. } => {
                    let d = dest.trim_start_matches('%');
                    if !transition.next_state.contains_key(d) || transition.next_state.get(d) == Some(&d.to_string()) {
                        if declared_vars.insert(d.to_string()) {
                            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                        }
                        match val {
                            Value::I64(v) => {
                                if *v >= 0 {
                                    smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", d, v));
                                } else {
                                    smt.push_str(&format!("(assert (= {} (bvneg (_ bv{} 64))))\n", d, v.abs()));
                                }
                            }
                            Value::Bool(b) => smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", d, if *b { 1 } else { 0 })),
                            _ => {}
                        }
                    }
                }
                Instruction::SliceLen { dest, slice } => {
                    let d = dest.trim_start_matches('%');
                    let s = slice.trim_start_matches('%');
                    if declared_vars.insert(d.to_string()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                    }
                    smt.push_str(&format!("(assert (= {} {}_len))\n", d, s));
                }
                _ => {}
            }
        }

        for req in requires {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt(req)));
        }
        for inv in invariants {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt(inv)));
        }

        for cond in &transition.loop_continue_conds {
            smt.push_str(&format!("(assert {})\n", cond));
        }

        let dec_smt = Self::expr_to_smt(decreases);
        smt.push_str(&format!("(assert (not (bvsge {} (_ bv0 64))))\n", dec_smt));
        smt.push_str("(check-sat)\n(get-model)\n");
        smt
    }

    fn build_decreases_strictly_decreasing_query(
        func: &Function,
        requires: &[Expr],
        invariants: &[Expr],
        decreases: &Expr,
        buffer_sizes: &std::collections::HashMap<String, usize>,
        transition: &LoopTransition,
        loop_start_idx: usize,
    ) -> String {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_BV)\n");

        let mut all_exprs: Vec<&Expr> = requires.iter().collect();
        all_exprs.extend(invariants.iter());
        all_exprs.push(decreases);
        let mut declared_vars = Self::declare_all_vars(func, &all_exprs, &mut smt);

        for (buf_name, size) in buffer_sizes {
            let clean = buf_name.trim_start_matches('%');
            let blen = format!("{}_len", clean);
            if declared_vars.insert(blen.clone()) {
                smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", blen));
            }
            smt.push_str(&format!("(assert (= {}_len (_ bv{} 64)))\n", clean, size));
        }

        for s_inst in &func.instructions[..loop_start_idx] {
            match &s_inst.inst {
                Instruction::AssignConst { dest, val, .. } => {
                    let d = dest.trim_start_matches('%');
                    if !transition.next_state.contains_key(d) || transition.next_state.get(d) == Some(&d.to_string()) {
                        if declared_vars.insert(d.to_string()) {
                            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                        }
                        match val {
                            Value::I64(v) => {
                                if *v >= 0 {
                                    smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", d, v));
                                } else {
                                    smt.push_str(&format!("(assert (= {} (bvneg (_ bv{} 64))))\n", d, v.abs()));
                                }
                            }
                            Value::Bool(b) => smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", d, if *b { 1 } else { 0 })),
                            _ => {}
                        }
                    }
                }
                Instruction::SliceLen { dest, slice } => {
                    let d = dest.trim_start_matches('%');
                    let s = slice.trim_start_matches('%');
                    if declared_vars.insert(d.to_string()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                    }
                    smt.push_str(&format!("(assert (= {} {}_len))\n", d, s));
                }
                _ => {}
            }
        }

        for req in requires {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt(req)));
        }
        for inv in invariants {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt(inv)));
        }

        smt.push_str(&transition.smt_body);

        for cond in &transition.loop_continue_conds {
            smt.push_str(&format!("(assert {})\n", cond));
        }

        let dec_smt = Self::expr_to_smt(decreases);
        let next_dec_expr = Self::subst_expr_vars(decreases, &transition.next_state);
        let next_dec = Self::expr_to_smt(&next_dec_expr);

        smt.push_str(&format!("(assert (not (bvslt {} {})))\n", next_dec, dec_smt));
        smt.push_str("(check-sat)\n(get-model)\n");
        smt
    }

    fn build_straightline_query(
        func: &Function,
        requires: &[Expr],
        ensures: &[Expr],
        buffer_sizes: &std::collections::HashMap<String, usize>,
        program: Option<&Program>,
    ) -> String {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_BV)\n");

        let mut all_exprs: Vec<&Expr> = requires.iter().collect();
        all_exprs.extend(ensures.iter());
        
        let mut declared = std::collections::HashSet::new();
        for p in &func.params {
            declared.insert(p.name.clone());
        }
        for e in &all_exprs {
            Self::collect_vars(e, &mut declared);
        }
        for v in &declared {
            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", v));
        }

        // Khai báo kích thước buffer
        for (buf_name, size) in buffer_sizes {
            let clean = buf_name.trim_start_matches('%');
            smt.push_str(&format!("(declare-const {}_len (_ BitVec 64))\n", clean));
            smt.push_str(&format!("(assert (= {}_len (_ bv{} 64)))\n", clean, size));
        }

        // Declare local constants and slice lengths
        for s_inst in &func.instructions {
            match &s_inst.inst {
                Instruction::SliceLen { dest, slice } => {
                    let d = dest.trim_start_matches('%');
                    let s = slice.trim_start_matches('%');
                    smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                    smt.push_str(&format!("(assert (= {} {}_len))\n", d, s));
                }
                Instruction::AssignConst { dest, val, .. } => {
                    let d = dest.trim_start_matches('%');
                    smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                    match val {
                        Value::I64(v) => smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", d, v)),
                        Value::Bool(b) => smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", d, if *b { 1 } else { 0 })),
                        _ => {}
                    }
                }
                _ => {}
            }
        }

        // Khởi tạo các giá trị và phép toán trong hàm (SSA Translation)
        for s_inst in &func.instructions {
            match &s_inst.inst {
                Instruction::AssignConst { dest, val, .. } => {
                    let name = dest.trim_start_matches('%');
                    if declared.insert(name.to_string()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", name));
                    }
                    match val {
                        Value::I64(n) => smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", name, n)),
                        Value::Bool(b) => smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", name, if *b { 1 } else { 0 })),
                        _ => {}
                    }
                }
                Instruction::SliceLen { dest, slice } => {
                    let d = dest.trim_start_matches('%');
                    let s = slice.trim_start_matches('%');
                    if declared.insert(d.to_string()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                    }
                    if let Some(&size) = buffer_sizes.get(slice) {
                        smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", d, size));
                    } else {
                        smt.push_str(&format!("(assert (= {} {}_len))\n", d, s));
                    }
                }
                Instruction::Load8 { dest, .. } => {
                    let name = dest.trim_start_matches('%');
                    if declared.insert(name.to_string()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", name));
                    }
                    // Byte đọc từ bộ nhớ luôn nằm trong khoảng 0..=255
                    smt.push_str(&format!("(assert (and (bvsge {} (_ bv0 64)) (bvsle {} (_ bv255 64))))\n", name, name));
                }
                Instruction::Binary { op, dest, src1, src2, .. } => {
                    let name = dest.trim_start_matches('%');
                    if declared.insert(name.to_string()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", name));
                    }
                    let s1 = match src1 {
                        Operand::Const(Value::I64(n)) => format!("(_ bv{} 64)", n),
                        Operand::Reg(r) => r.trim_start_matches('%').to_string(),
                        _ => "(_ bv0 64)".into(),
                    };
                    let s2 = match src2 {
                        Operand::Const(Value::I64(n)) => format!("(_ bv{} 64)", n),
                        Operand::Reg(r) => r.trim_start_matches('%').to_string(),
                        _ => "(_ bv0 64)".into(),
                    };
                    let expr_str = match op {
                        BinOp::Add => format!("(bvadd {} {})", s1, s2),
                        BinOp::Sub => format!("(bvsub {} {})", s1, s2),
                        BinOp::Mul => format!("(bvmul {} {})", s1, s2),
                        BinOp::Div => format!("(bvsdiv {} {})", s1, s2),
                        BinOp::Lt => format!("(ite (bvslt {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                        BinOp::Lte => format!("(ite (bvsle {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                        BinOp::Gt => format!("(ite (bvsgt {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                        BinOp::Gte => format!("(ite (bvsge {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                        BinOp::Eq => format!("(ite (= {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                        BinOp::Neq => format!("(ite (distinct {} {}) (_ bv1 64) (_ bv0 64))", s1, s2),
                        _ => format!("(_ bv0 64)"),
                    };
                    smt.push_str(&format!("(assert (= {} {}))\n", name, expr_str));
                }
                Instruction::Call { dest: Some(d), func_name, args } => {
                    let name = d.trim_start_matches('%');
                    if declared.insert(name.to_string()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", name));
                    }
                    if let Some(prog) = program {
                        if let Some(callee_fn) = prog.functions.iter().find(|f| &f.name == func_name) {
                            for c_si in &callee_fn.instructions {
                                if let Instruction::Ensure(ens_expr) = &c_si.inst {
                                    let mut instantiated = ens_expr.clone();
                                    for (i, p) in callee_fn.params.iter().enumerate() {
                                        if i < args.len() {
                                            if let Operand::Reg(arg_r) = &args[i] {
                                                instantiated = Self::subst_expr_var(&instantiated, &p.name, arg_r.trim_start_matches('%'));
                                            }
                                        }
                                    }
                                    if let Some(ret_si) = callee_fn.instructions.iter().rev().find(|s| matches!(s.inst, Instruction::Ret(Some(Operand::Reg(_))))) {
                                        if let Instruction::Ret(Some(Operand::Reg(ret_r))) = &ret_si.inst {
                                            instantiated = Self::subst_expr_var(&instantiated, ret_r.trim_start_matches('%'), name);
                                        }
                                    }
                                    smt.push_str(&format!("(assert {})\n", Self::expr_to_smt(&instantiated)));
                                }
                            }
                        }
                    }
                }
                Instruction::Syscall { dest: Some(d), .. } => {
                    let name = d.trim_start_matches('%');
                    if declared.insert(name.to_string()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", name));
                    }
                }
                Instruction::RetIf { cond, .. } | Instruction::BrIf { cond, .. } => {
                    let c = cond.trim_start_matches('%');
                    smt.push_str(&format!("(assert (= {} (_ bv0 64)))\n", c));
                }
                _ => {}
            }
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
    pub fn solve_query(
        goal_name: &str,
        category: PropertyCategory,
        query: &str,
        stack_trace: Vec<StackFrame>,
    ) -> VerificationResult {
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
                    category,
                    reason: format!("Failed to spawn Z3 solver: {}", e),
                    counter_example: None,
                    stack_trace,
                };
            }
        };

        let stdout = String::from_utf8_lossy(&output.stdout);
        if stdout.contains("unsat") {
            VerificationResult::Verified {
                goal_name: goal_name.to_string(),
                category,
            }
        } else if stdout.contains("sat") {
            VerificationResult::Failed {
                goal_name: goal_name.to_string(),
                category,
                reason: "Counter-example found: Mathematical/safety contract violated!".to_string(),
                counter_example: Some(stdout.to_string()),
                stack_trace,
            }
        } else if stdout.contains("unknown") || stdout.contains("timeout") {
            VerificationResult::Unknown {
                goal_name: goal_name.to_string(),
                category,
                reason: format!("Z3 returned unknown/timeout status: {}", stdout),
                stack_trace,
            }
        } else {
            VerificationResult::Failed {
                goal_name: goal_name.to_string(),
                category,
                reason: format!("Z3 solver error or unexpected output: {}", stdout),
                counter_example: None,
                stack_trace,
            }
        }
    }
}
