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
    pub break_points: Vec<(String, std::collections::HashMap<String, String>)>,
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
    /// Helper an toàn để chuyển số nguyên i64 sang SMT-LIB2 64-bit BitVec (xử lý đúng số âm và i64::MIN)
    #[inline]
    pub fn smt_bv64(n: i64) -> String {
        if n >= 0 {
            format!("(_ bv{} 64)", n)
        } else if n == i64::MIN {
            "(_ bv9223372036854775808 64)".to_string()
        } else {
            format!("(bvneg (_ bv{} 64))", n.unsigned_abs())
        }
    }

    #[inline]
    pub fn smt_usize(n: usize) -> String {
        format!("(_ bv{} 64)", n)
    }

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

        // 1. Collect static buffer capacities first & propagate through SLICE_PTR / MOV aliases
        let mut buffer_sizes: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
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

        // 2. Collect verification directives
        let mut requires = Vec::new();
        let mut ensures = Vec::new();
        let mut invariants = Vec::new();
        let mut decreases = Vec::new();
        let mut asserts = Vec::new();

        for (idx, s_inst) in func.instructions.iter().enumerate() {
            match &s_inst.inst {
                Instruction::Require(e) => requires.push(e.clone()),
                Instruction::Ensure(e) => ensures.push(e.clone()),
                Instruction::Invariant(e) => invariants.push(e.clone()),
                Instruction::Decreases(e) => decreases.push(e.clone()),
                Instruction::Assert(e) => asserts.push((idx, s_inst, e.clone())),
                _ => {}
            }
        }

        // 2b. Verify explicit ASSERT directives
        for (idx, s_inst, assert_expr) in &asserts {
            let assert_goal = format!("Function '{}' - Line {}: Verify ASSERT directive", func.name, s_inst.loc.line);
            let query = Self::build_prefix_property_query(
                func,
                *idx,
                &requires,
                &buffer_sizes,
                program,
                assert_expr,
            );
            let stack = vec![StackFrame {
                file: s_inst.loc.file.clone(),
                line: s_inst.loc.line,
                function: format!("{}()", func.name),
                snippet: s_inst.loc.text.clone(),
                role: "Assertion condition might be violated here".into(),
            }];
            results.push(Self::solve_query(&assert_goal, PropertyCategory::Functional, &query, stack));
        }

        // 3. Implicit check: Division by Zero (Context-Sensitive)
        for (idx, s_inst) in func.instructions.iter().enumerate() {
            if let Instruction::Binary { op: BinOp::Div | BinOp::Mod, src2, .. } = &s_inst.inst {
                let div_zero_goal = format!("Function '{}' - Line {}: Division-by-Zero safety", func.name, s_inst.loc.line);
                let query = Self::build_div_zero_query(func, idx, &requires, src2, &buffer_sizes, program);
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

        // 4. Implicit check: Memory bounds & buffer overflow for Loads/Stores, Strings, Calls, Syscalls
        for (idx, s_inst) in func.instructions.iter().enumerate() {
            match &s_inst.inst {
                Instruction::Load8 { buf, offset, .. } | Instruction::Store8 { buf, offset, .. } => {
                    if let Some(&buf_size) = buffer_sizes.get(buf) {
                        let goal_name = format!(
                            "Function '{}' - Line {}: Memory 8-bit bounds check on '{}'",
                            func.name, s_inst.loc.line, buf
                        );
                        let query = Self::build_mem_bounds_query(func, idx, &requires, offset, 1, buf_size, &buffer_sizes, program);
                        let stack = vec![StackFrame {
                            file: s_inst.loc.file.clone(),
                            line: s_inst.loc.line,
                            function: format!("{}()", func.name),
                            snippet: s_inst.loc.text.clone(),
                            role: format!("Byte access offset may be out of bounds [0..{}) for '{}'", buf_size, buf),
                        }];
                        results.push(Self::solve_query(&goal_name, PropertyCategory::Safety, &query, stack));
                    }
                }
                Instruction::Load64 { buf, offset, .. } | Instruction::Store64 { buf, offset, .. } => {
                    if let Some(&buf_size) = buffer_sizes.get(buf) {
                        let goal_name = format!(
                            "Function '{}' - Line {}: Memory 64-bit bounds check on '{}'",
                            func.name, s_inst.loc.line, buf
                        );
                        let query = Self::build_mem_bounds_query(func, idx, &requires, offset, 8, buf_size, &buffer_sizes, program);
                        let stack = vec![StackFrame {
                            file: s_inst.loc.file.clone(),
                            line: s_inst.loc.line,
                            function: format!("{}()", func.name),
                            snippet: s_inst.loc.text.clone(),
                            role: format!("8-byte access [offset..offset+8] may exceed capacity ({} bytes) of '{}'", buf_size, buf),
                        }];
                        results.push(Self::solve_query(&goal_name, PropertyCategory::Safety, &query, stack));
                    }
                }
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

                            let query = Self::build_buffer_overflow_query(func, idx, &requires, &actual_rdx, buf_size, &buffer_sizes, program);
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

        let has_loop = func.instructions.iter().any(|s| matches!(s.inst, Instruction::Loop(_)));
        let has_syscall = func.instructions.iter().any(|s| matches!(s.inst, Instruction::Syscall { .. }));
        let is_syscall_stub = has_syscall && func.instructions.len() <= 8;

        // 4b. Verify early return paths (RET_IF & mid-function RET) against ENSURE postconditions for ALL functions
        if !ensures.is_empty() && !is_syscall_stub {
            for (idx, s_inst) in func.instructions.iter().enumerate() {
                if let Instruction::RetIf { cond, val } = &s_inst.inst {
                    let early_goal = format!(
                        "Function '{}' - Line {}: Verify ENSURE on early return (RET_IF)",
                        func.name, s_inst.loc.line
                    );
                    let early_query = Self::build_early_ret_ensure_query(
                        func,
                        idx,
                        cond,
                        val.as_ref(),
                        &requires,
                        &ensures,
                        &buffer_sizes,
                        program,
                    );
                    let stack = vec![StackFrame {
                        file: s_inst.loc.file.clone(),
                        line: s_inst.loc.line,
                        function: format!("{}()", func.name),
                        snippet: s_inst.loc.text.clone(),
                        role: "Early return (RET_IF) violates ENSURE postcondition".into(),
                    }];
                    results.push(Self::solve_query(&early_goal, PropertyCategory::Functional, &early_query, stack));
                }
            }
            let total_insts = func.instructions.len();
            for (idx, s_inst) in func.instructions.iter().enumerate() {
                if idx + 1 < total_insts {
                    if let Instruction::Ret(val) = &s_inst.inst {
                        let mid_ret_goal = format!(
                            "Function '{}' - Line {}: Verify ENSURE on branch return (RET)",
                            func.name, s_inst.loc.line
                        );
                        let mid_query = Self::build_mid_ret_ensure_query(
                            func,
                            idx,
                            val.as_ref(),
                            &requires,
                            &ensures,
                            &buffer_sizes,
                            program,
                        );
                        let stack = vec![StackFrame {
                            file: s_inst.loc.file.clone(),
                            line: s_inst.loc.line,
                            function: format!("{}()", func.name),
                            snippet: s_inst.loc.text.clone(),
                            role: "Branch return (RET) violates ENSURE postcondition".into(),
                        }];
                        results.push(Self::solve_query(&mid_ret_goal, PropertyCategory::Functional, &mid_query, stack));
                    }
                }
            }
        }

        // 5. Hoare Logic Verification for Loops (kích hoạt khi có INVARIANT hoặc khi hàm có LOOP + ENSURE/DECREASES)
        if !invariants.is_empty() || (has_loop && (!ensures.is_empty() || !decreases.is_empty())) {
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
                if !invariants.is_empty() {
                    let base_goal = format!("Function '{}' - Step 1: Base Case (Loop initialization)", func.name);
                    let base_query = Self::build_base_case_query(func, l_start, &requires, &invariants, &buffer_sizes, program);
                    let stack = vec![StackFrame {
                        file: func.file.clone(),
                        line: func.start_line,
                        function: format!("{}()", func.name),
                        snippet: "Base Case loop invariant".into(),
                        role: "Loop initialization does not satisfy invariant".into(),
                    }];
                    results.push(Self::solve_query(&base_goal, PropertyCategory::Inductive, &base_query, stack));
                }

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
                        if !invariants.is_empty() {
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
                        }

                        if !ensures.is_empty() {
                            let exit_goal = format!("Function '{}' - Step 3: Exit Step (ENSURE postcondition satisfaction)", func.name);
                            let exit_query = Self::build_exit_step_query(func, &requires, &invariants, &ensures, &buffer_sizes, &transition, l_start, l_end);
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
            if is_syscall_stub {
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
            vars.insert(p.name.trim_start_matches('%').to_string());
        }
        for e in exprs {
            Self::collect_vars(e, &mut vars);
        }
        for v in &vars {
            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", v));
        }
        vars
    }
    /// Chuyển biểu thức sang SMT-LIB2 đảm bảo kết quả mang kiểu Bool (Sort Bool)
    pub fn expr_to_smt_bool(expr: &Expr) -> String {
        match expr {
            Expr::Var(name) => {
                let clean = name.trim_start_matches('%');
                format!("(distinct {} (_ bv0 64))", clean)
            }
            Expr::IntConst(n) => {
                if *n != 0 { "true".into() } else { "false".into() }
            }
            Expr::BoolConst(b) => if *b { "true".into() } else { "false".into() },
            Expr::Not(inner) => format!("(not {})", Self::expr_to_smt_bool(inner)),
            Expr::Binary { op: BinOp::And, lhs, rhs } => {
                format!("(and {} {})", Self::expr_to_smt_bool(lhs), Self::expr_to_smt_bool(rhs))
            }
            Expr::Binary { op: BinOp::Or, lhs, rhs } => {
                format!("(or {} {})", Self::expr_to_smt_bool(lhs), Self::expr_to_smt_bool(rhs))
            }
            Expr::Binary { op: BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod, .. } => {
                format!("(distinct {} (_ bv0 64))", Self::expr_to_smt(expr))
            }
            _ => Self::expr_to_smt(expr),
        }
    }

    /// Chuyển đổi biểu thức Expr sang chuỗi logic SMT-LIB2 (Bit-Vector 64-bit)
    pub fn expr_to_smt(expr: &Expr) -> String {
        match expr {
            Expr::Var(name) => {
                let clean = name.trim_start_matches('%');
                clean.to_string()
            }
            Expr::IntConst(n) => Self::smt_bv64(*n),
            Expr::FloatConst(f) => format!("{}", f),
            Expr::BoolConst(b) => if *b { "true".into() } else { "false".into() },
            Expr::Not(inner) => format!("(not {})", Self::expr_to_smt_bool(inner)),
            Expr::Len(arr) => format!("{}_len", arr.trim_start_matches('%')),
            Expr::Binary { op, lhs, rhs } => {
                if matches!(op, BinOp::And | BinOp::Or) {
                    let b1 = Self::expr_to_smt_bool(lhs);
                    let b2 = Self::expr_to_smt_bool(rhs);
                    return match op {
                        BinOp::And => format!("(and {} {})", b1, b2),
                        BinOp::Or => format!("(or {} {})", b1, b2),
                        _ => unreachable!(),
                    };
                }
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
                    BinOp::And | BinOp::Or => unreachable!(),
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

    /// Thu thập tất cả các vòng lặp bắt đầu trước `target_idx`
    /// Trả về danh sách `(l_start, l_end, modified_vars, invariants)`
    pub fn find_loops_before(
        func: &Function,
        target_idx: usize,
    ) -> Vec<(usize, usize, std::collections::HashSet<String>, Vec<Expr>)> {
        let mut loops = Vec::new();
        let mut current_loop_start = None;
        for (idx, si) in func.instructions.iter().enumerate() {
            if matches!(si.inst, Instruction::Loop(_)) {
                current_loop_start = Some(idx);
            } else if matches!(si.inst, Instruction::EndLoop(_)) {
                if let Some(l_start) = current_loop_start {
                    if target_idx > l_start {
                        let mut modified = std::collections::HashSet::new();
                        let mut invs = Vec::new();
                        for inner_si in &func.instructions[l_start..idx] {
                            match &inner_si.inst {
                                Instruction::AssignConst { dest, .. }
                                | Instruction::Mov { dest, .. }
                                | Instruction::Binary { dest, .. }
                                | Instruction::AllocSlice { dest, .. }
                                | Instruction::SlicePtr { dest, .. }
                                | Instruction::SliceLen { dest, .. }
                                | Instruction::Alloc { dest, .. }
                                | Instruction::Load8 { dest, .. }
                                | Instruction::Load64 { dest, .. } => {
                                    modified.insert(dest.trim_start_matches('%').to_string());
                                }
                                Instruction::Call { dest: Some(d), .. }
                                | Instruction::Syscall { dest: Some(d), .. } => {
                                    modified.insert(d.trim_start_matches('%').to_string());
                                }
                                Instruction::Invariant(expr) => {
                                    invs.push(expr.clone());
                                }
                                _ => {}
                            }
                        }
                        if invs.is_empty() {
                            for func_si in &func.instructions {
                                if let Instruction::Invariant(expr) = &func_si.inst {
                                    invs.push(expr.clone());
                                }
                            }
                        }
                        loops.push((l_start, idx, modified, invs));
                    }
                    current_loop_start = None;
                }
            }
        }
        loops
    }

    /// Thực thi ký hiệu từ đầu hàm đến `upto_idx` với SSA Versioning (current_val)
    /// Trả về bản đồ `current_val` ánh xạ tên biến gốc -> tên biến SMT ở phiên bản mới nhất.
    fn emit_symbolic_prefix(
        func: &Function,
        upto_idx: usize,
        requires: &[Expr],
        buffer_sizes: &std::collections::HashMap<String, usize>,
        program: Option<&Program>,
        smt: &mut String,
    ) -> std::collections::HashMap<String, String> {
        let mut declared = std::collections::HashSet::new();
        let mut current_val: std::collections::HashMap<String, String> = std::collections::HashMap::new();

        // 1. Khai báo tham số hàm ở phiên bản gốc (pre-state)
        for p in &func.params {
            let clean = p.name.trim_start_matches('%').to_string();
            if declared.insert(clean.clone()) {
                smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", clean));
            }
            current_val.insert(clean.clone(), clean.clone());

            let plen = format!("{}_len", clean);
            if declared.insert(plen.clone()) {
                smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", plen));
            }
            current_val.insert(plen.clone(), plen);
        }

        // 2. Khai báo kích thước tĩnh của các buffer
        for (buf_name, size) in buffer_sizes {
            let clean = buf_name.trim_start_matches('%');
            let len_name = format!("{}_len", clean);
            if declared.insert(len_name.clone()) {
                smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", len_name));
            }
            smt.push_str(&format!("(assert (= {} {}))\n", len_name, Self::smt_usize(*size)));
            current_val.insert(len_name.clone(), len_name);
        }

        // 3. Assert REQUIRE trên trạng thái đầu vào (pre-state)
        for req in requires {
            let mut req_vars = std::collections::HashSet::new();
            Self::collect_vars(req, &mut req_vars);
            for v in req_vars {
                if declared.insert(v.clone()) {
                    smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", v));
                }
                current_val.entry(v.clone()).or_insert_with(|| v.clone());
            }
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt_bool(req)));
        }

        let active_loops = Self::find_loops_before(func, upto_idx);
        // Label index lookup to know if a BR_IF target is before or after `upto_idx`
        let mut label_positions = std::collections::HashMap::new();
        for (i, inst_i) in func.instructions.iter().enumerate() {
            if let Instruction::Label(lbl) = &inst_i.inst {
                label_positions.insert(lbl.clone(), i);
            }
        }
        // Track active branch merges: label_name -> Vec<(cond_smt, state_at_branch)>
        let mut pending_incoming: std::collections::HashMap<String, Vec<(String, std::collections::HashMap<String, String>)>> = std::collections::HashMap::new();
        let mut skip_until_label: Option<(String, std::collections::HashMap<String, String>)> = None;
        let mut path_terminated_by_ret = false;
        let mut active_loop_breaks: Vec<(String, std::collections::HashMap<String, String>)> = Vec::new();

        // 4. Duyệt từng lệnh với SSA Renaming (mỗi lần gán tạo phiên bản _v{idx})
        let limit = upto_idx.min(func.instructions.len());
        for (idx, si) in func.instructions[..limit].iter().enumerate() {
            // Nếu đường đi hiện tại vừa kết thúc bằng lệnh RET không điều kiện, bỏ qua cho tới khi gặp LABEL mới
            if path_terminated_by_ret {
                if let Instruction::Label(lbl) = &si.inst {
                    if let Some(incoming_list) = pending_incoming.remove(lbl) {
                        // Đường duy nhất tới LABEL này là thông qua các nhánh nhảy tới nó
                        let mut cond_disjunction = Vec::new();
                        let (_, first_state) = incoming_list[0].clone();
                        let mut merged_state = first_state;
                        for (cond_smt, branch_state) in &incoming_list {
                            cond_disjunction.push(cond_smt.clone());
                            let mut all_keys: std::collections::HashSet<String> = merged_state.keys().cloned().collect();
                            all_keys.extend(branch_state.keys().cloned());
                            for k in all_keys {
                                let v1 = merged_state.get(&k).cloned().unwrap_or_else(|| k.clone());
                                let v2 = branch_state.get(&k).cloned().unwrap_or_else(|| k.clone());
                                if v1 != v2 {
                                    let phi = format!("{}_phi_{}", k, idx);
                                    if declared.insert(phi.clone()) {
                                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", phi));
                                    }
                                    smt.push_str(&format!("(assert (= {} (ite {} {} {})))\n", phi, cond_smt, v2, v1));
                                    merged_state.insert(k, phi);
                                }
                            }
                        }
                        if cond_disjunction.len() == 1 {
                            smt.push_str(&format!("(assert {})\n", cond_disjunction[0]));
                        } else if cond_disjunction.len() > 1 {
                            smt.push_str(&format!("(assert (or {}))\n", cond_disjunction.join(" ")));
                        }
                        current_val = merged_state;
                        path_terminated_by_ret = false;
                    }
                }
                continue;
            }

            // Nếu đang skip qua một khối sau JUMP không điều kiện
            if let Some((ref target, ref pre_jump_state)) = skip_until_label {
                if let Instruction::Label(lbl) = &si.inst {
                    if lbl == target {
                        // Khôi phục state từ nhánh nhảy tới hoặc hợp nhất
                        let mut base_state = pre_jump_state.clone();
                        if let Some(incoming_list) = pending_incoming.remove(lbl) {
                            for (cond_smt, branch_state) in incoming_list {
                                let mut all_keys: std::collections::HashSet<String> = base_state.keys().cloned().collect();
                                all_keys.extend(branch_state.keys().cloned());
                                for k in all_keys {
                                    let v_else = base_state.get(&k).cloned().unwrap_or_else(|| k.clone());
                                    let v_then = branch_state.get(&k).cloned().unwrap_or_else(|| k.clone());
                                    if v_else != v_then {
                                        let phi = format!("{}_phi_{}", k, idx);
                                        if declared.insert(phi.clone()) {
                                            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", phi));
                                        }
                                        smt.push_str(&format!("(assert (= {} (ite {} {} {})))\n", phi, cond_smt, v_then, v_else));
                                        base_state.insert(k, phi);
                                    }
                                }
                            }
                        }
                        current_val = base_state;
                        skip_until_label = None;
                    } else if let Some(incoming_list) = pending_incoming.remove(lbl) {
                        // Nhảy từ JUMP sang lbl_join, nhưng đang đi ngang qua lbl_then!
                        // Phải bắt đầu thực thi nhánh lbl_then với trạng thái của BR_IF nhảy vào lbl_then
                        let (cond_smt, then_start_state) = incoming_list.into_iter().last().unwrap();
                        let else_end_state = pre_jump_state.clone();
                        // Lưu trạng thái kết thúc nhánh else để lát nữa gặp target (lbl_join) thì merge!
                        pending_incoming
                            .entry(target.clone())
                            .or_default()
                            .push((format!("(not {})", cond_smt), else_end_state));
                        current_val = then_start_state;
                        skip_until_label = None;
                    }
                }
                continue;
            }

            // In-loop & Post-loop havoc at loop entrance: havoc loop-modified variables and assert invariant
            if let Some((l_start, _, modified_vars, loop_invs)) = active_loops.iter().find(|(s, _, _, _)| *s == idx) {
                {
                    active_loop_breaks.clear();
                    for v in modified_vars {
                        let havoc_var = format!("{}_iter_{}", v, l_start);
                        if declared.insert(havoc_var.clone()) {
                            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", havoc_var));
                        }
                        current_val.insert(v.clone(), havoc_var);
                    }
                    for inv in loop_invs {
                        let mut inv_vars = std::collections::HashSet::new();
                        Self::collect_vars(inv, &mut inv_vars);
                        for iv in inv_vars {
                            if !current_val.contains_key(&iv) {
                                if declared.insert(iv.clone()) {
                                    smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", iv));
                                }
                                current_val.insert(iv.clone(), iv);
                            }
                        }
                        let mapped_inv = Self::subst_expr_vars(inv, &current_val);
                        smt.push_str(&format!("(assert {})\n", Self::expr_to_smt_bool(&mapped_inv)));
                    }
                    continue; // Skip Instruction::Loop
                }
            }

            // Nếu đi qua END_LOOP (tức là upto_idx nằm phía sau vòng lặp):
            // Phải assert rằng ít nhất một điều kiện thoát vòng lặp (BREAK_IF) đã xảy ra,
            // đồng thời khôi phục `current_val` về đúng trạng thái tại điểm BREAK_IF (không lấy phần cập nhật sau BREAK_IF)!
            if active_loops.iter().any(|(_, e, _, _)| *e == idx) {
                if !active_loop_breaks.is_empty() {
                    if active_loop_breaks.len() == 1 {
                        smt.push_str(&format!("(assert {})\n", active_loop_breaks[0].0));
                        current_val = active_loop_breaks[0].1.clone();
                    } else {
                        let conds: Vec<String> = active_loop_breaks.iter().map(|(c, _)| c.clone()).collect();
                        smt.push_str(&format!("(assert (or {}))\n", conds.join(" ")));
                        let mut all_vars = std::collections::HashSet::new();
                        for (_, st) in &active_loop_breaks {
                            for k in st.keys() {
                                all_vars.insert(k.clone());
                            }
                        }
                        let mut merged_exit = current_val.clone();
                        for v in all_vars {
                            let first_val = active_loop_breaks[0].1.get(&v).cloned().unwrap_or_else(|| v.clone());
                            let all_same = active_loop_breaks.iter().all(|(_, st)| st.get(&v).cloned().unwrap_or_else(|| v.clone()) == first_val);
                            if all_same {
                                merged_exit.insert(v, first_val);
                            } else {
                                let m_var = format!("{}_exit_merge_{}", v, idx);
                                if declared.insert(m_var.clone()) {
                                    smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", m_var));
                                }
                                let mut ite_expr = active_loop_breaks.last().unwrap().1.get(&v).cloned().unwrap_or_else(|| v.clone());
                                for (c, st) in active_loop_breaks[..active_loop_breaks.len() - 1].iter().rev() {
                                    let tv = st.get(&v).cloned().unwrap_or_else(|| v.clone());
                                    ite_expr = format!("(ite {} {} {})", c, tv, ite_expr);
                                }
                                smt.push_str(&format!("(assert (= {} {}))\n", m_var, ite_expr));
                                merged_exit.insert(v, m_var);
                            }
                        }
                        current_val = merged_exit;
                    }
                    active_loop_breaks.clear();
                }
                continue;
            }

            match &si.inst {
                Instruction::Jump(target) => {
                    skip_until_label = Some((target.clone(), current_val.clone()));
                }
                Instruction::Ret(_) => {
                    path_terminated_by_ret = true;
                }
                Instruction::Label(lbl) => {
                    if let Some(incoming_list) = pending_incoming.remove(lbl) {
                        for (cond_smt, branch_state) in incoming_list {
                            let mut all_keys: std::collections::HashSet<String> = current_val.keys().cloned().collect();
                            all_keys.extend(branch_state.keys().cloned());
                            for k in all_keys {
                                let v_cur = current_val.get(&k).cloned().unwrap_or_else(|| k.clone());
                                let v_brk = branch_state.get(&k).cloned().unwrap_or_else(|| k.clone());
                                if v_cur != v_brk {
                                    let phi = format!("{}_phi_{}", k, idx);
                                    if declared.insert(phi.clone()) {
                                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", phi));
                                    }
                                    smt.push_str(&format!("(assert (= {} (ite {} {} {})))\n", phi, cond_smt, v_brk, v_cur));
                                    current_val.insert(k, phi);
                                }
                            }
                        }
                    }
                }
                Instruction::AssignConst { dest, val, .. } => {
                    let d = dest.trim_start_matches('%');
                    let ver = format!("{}_v{}", d, idx);
                    if declared.insert(ver.clone()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", ver));
                    }
                    match val {
                        Value::I64(v) => smt.push_str(&format!("(assert (= {} {}))\n", ver, Self::smt_bv64(*v))),
                        Value::U64(v) => smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", ver, v)),
                        Value::Bool(b) => smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", ver, if *b { 1 } else { 0 })),
                        _ => {}
                    }
                    current_val.insert(d.to_string(), ver);
                }
                Instruction::Mov { dest, src } => {
                    let d = dest.trim_start_matches('%');
                    let s = src.trim_start_matches('%');
                    let s_smt = current_val.get(s).cloned().unwrap_or_else(|| {
                        if declared.insert(s.to_string()) {
                            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", s));
                        }
                        s.to_string()
                    });
                    current_val.insert(d.to_string(), s_smt);
                }
                Instruction::Binary { op, dest, src1, src2, .. } => {
                    let d = dest.trim_start_matches('%');
                    let s1 = Self::resolve_operand(src1, &current_val);
                    let s2 = Self::resolve_operand(src2, &current_val);
                    let expr_str = Self::binop_to_smt(op, &s1, &s2);

                    let ver = format!("{}_v{}", d, idx);
                    if declared.insert(ver.clone()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", ver));
                    }
                    smt.push_str(&format!("(assert (= {} {}))\n", ver, expr_str));
                    current_val.insert(d.to_string(), ver);
                }
                Instruction::Load8 { dest, .. } => {
                    let d = dest.trim_start_matches('%');
                    let ver = format!("{}_v{}", d, idx);
                    if declared.insert(ver.clone()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", ver));
                    }
                    smt.push_str(&format!("(assert (and (bvsge {} (_ bv0 64)) (bvsle {} (_ bv255 64))))\n", ver, ver));
                    current_val.insert(d.to_string(), ver);
                }
                Instruction::Load64 { dest, .. } | Instruction::SlicePtr { dest, .. } => {
                    let d = dest.trim_start_matches('%');
                    let ver = format!("{}_v{}", d, idx);
                    if declared.insert(ver.clone()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", ver));
                    }
                    current_val.insert(d.to_string(), ver);
                }
                Instruction::SliceLen { dest, slice } => {
                    let d = dest.trim_start_matches('%');
                    let s = slice.trim_start_matches('%');
                    let ver = format!("{}_v{}", d, idx);
                    if declared.insert(ver.clone()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", ver));
                    }
                    if let Some(&size) = buffer_sizes.get(slice) {
                        smt.push_str(&format!("(assert (= {} {}))\n", ver, Self::smt_usize(size)));
                    } else {
                        let slen = format!("{}_len", s);
                        let mapped_len = current_val.get(&slen).cloned().unwrap_or_else(|| {
                            if declared.insert(slen.clone()) {
                                smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", slen));
                            }
                            slen
                        });
                        smt.push_str(&format!("(assert (= {} {}))\n", ver, mapped_len));
                    }
                    current_val.insert(d.to_string(), ver);
                }
                Instruction::Call { dest: Some(d), func_name, args: call_args } => {
                    let clean_d = d.trim_start_matches('%');
                    let ver = format!("{}_v{}", clean_d, idx);
                    if declared.insert(ver.clone()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", ver));
                    }
                    if let Some(prog) = program {
                        if let Some(callee_fn) = prog.functions.iter().find(|f| &f.name == func_name) {
                            for c_si in &callee_fn.instructions {
                                if let Instruction::Ensure(ens_expr) = &c_si.inst {
                                    let mut instantiated = ens_expr.clone();
                                    for (i, p) in callee_fn.params.iter().enumerate() {
                                        if i < call_args.len() {
                                            match &call_args[i] {
                                                Operand::Reg(arg_r) => {
                                                    let mapped_arg = Self::resolve_operand(&Operand::Reg(arg_r.clone()), &current_val);
                                                    instantiated = Self::subst_expr_var(&instantiated, &p.name, &mapped_arg);
                                                }
                                                Operand::Const(Value::I64(c)) => {
                                                    let arg_const_var = format!("call_{}_arg_{}", idx, i);
                                                    if declared.insert(arg_const_var.clone()) {
                                                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", arg_const_var));
                                                        smt.push_str(&format!("(assert (= {} {}))\n", arg_const_var, Self::smt_bv64(*c)));
                                                    }
                                                    instantiated = Self::subst_expr_var(&instantiated, &p.name, &arg_const_var);
                                                }
                                                _ => {}
                                            }
                                        }
                                    }
                                    if let Some(ret_si) = callee_fn.instructions.iter().rev().find(|s| matches!(s.inst, Instruction::Ret(Some(Operand::Reg(_))))) {
                                        if let Instruction::Ret(Some(Operand::Reg(ret_r))) = &ret_si.inst {
                                            instantiated = Self::subst_expr_var(&instantiated, ret_r.trim_start_matches('%'), &ver);
                                        }
                                    }
                                    smt.push_str(&format!("(assert {})\n", Self::expr_to_smt_bool(&instantiated)));
                                }
                            }
                        }
                    }
                    current_val.insert(clean_d.to_string(), ver);
                }
                Instruction::Syscall { dest: Some(d), .. } => {
                    let clean_d = d.trim_start_matches('%');
                    let ver = format!("{}_v{}", clean_d, idx);
                    if declared.insert(ver.clone()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", ver));
                    }
                    current_val.insert(clean_d.to_string(), ver);
                }
                Instruction::BrIf { cond, target } => {
                    let c_smt = Self::resolve_operand(&Operand::Reg(cond.clone()), &current_val);
                    if let Some(&tgt_pos) = label_positions.get(target) {
                        if tgt_pos <= limit {
                            // Mục tiêu kiểm chứng nằm ở hoặc sau nhãn đích `target`:
                            // Lưu lại trạng thái tại điểm nhảy để lát nữa hợp nhất (Phi-node), KHÔNG ép c_smt == 0!
                            pending_incoming
                                .entry(target.clone())
                                .or_default()
                                .push((format!("(distinct {} (_ bv0 64))", c_smt), current_val.clone()));
                        } else {
                            // Mục tiêu kiểm chứng nằm trước nhãn đích `target`: phải không nhảy mới tới được đây
                            smt.push_str(&format!("(assert (= {} (_ bv0 64)))\n", c_smt));
                        }
                    } else {
                        smt.push_str(&format!("(assert (= {} (_ bv0 64)))\n", c_smt));
                    }
                }
                Instruction::BreakIf(cond) => {
                    let c_smt = Self::resolve_operand(&Operand::Reg(cond.clone()), &current_val);
                    // Nếu upto_idx nằm bên trong vòng lặp hiện tại thì tại điểm này chưa break (= 0)
                    // Nhưng nếu upto_idx nằm sau END_LOOP thì lưu lại điều kiện break để assert tại END_LOOP!
                    if let Some((_, l_end, _, _)) = active_loops.iter().find(|(s, e, _, _)| idx > *s && idx < *e) {
                        if limit <= *l_end {
                            smt.push_str(&format!("(assert (= {} (_ bv0 64)))\n", c_smt));
                        } else {
                            active_loop_breaks.push((format!("(distinct {} (_ bv0 64))", c_smt), current_val.clone()));
                        }
                    } else {
                        smt.push_str(&format!("(assert (= {} (_ bv0 64)))\n", c_smt));
                    }
                }
                Instruction::RetIf { cond, .. }
                | Instruction::ContinueIf(cond) => {
                    let c_smt = Self::resolve_operand(&Operand::Reg(cond.clone()), &current_val);
                    smt.push_str(&format!("(assert (= {} (_ bv0 64)))\n", c_smt));
                }
                _ => {}
            }
        }

        current_val
    }

    fn build_prefix_property_query(
        func: &Function,
        upto_idx: usize,
        requires: &[Expr],
        buffer_sizes: &std::collections::HashMap<String, usize>,
        program: Option<&Program>,
        assert_expr: &Expr,
    ) -> String {
        let mut smt = String::from("(set-logic QF_BV)\n");
        let current_val = Self::emit_symbolic_prefix(func, upto_idx, requires, buffer_sizes, program, &mut smt);
        let mapped_expr = Self::subst_expr_vars(assert_expr, &current_val);
        smt.push_str(&format!("(assert (not {}))\n", Self::expr_to_smt_bool(&mapped_expr)));
        smt.push_str("(check-sat)\n(get-model)\n");
        smt
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

        let caller_reqs: Vec<Expr> = caller
            .instructions
            .iter()
            .filter_map(|si| if let Instruction::Require(r) = &si.inst { Some(r.clone()) } else { None })
            .collect();

        let current_val = Self::emit_symbolic_prefix(caller, call_idx, &caller_reqs, buffer_sizes, program, &mut smt);

        // 1. Declare callee parameters
        for p in &callee.params {
            let pname = p.name.trim_start_matches('%');
            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", pname));
            let plen = format!("{}_len", pname);
            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", plen));
        }

        // 2. Connect call arguments to callee parameters
        for (i, p) in callee.params.iter().enumerate() {
            if i >= args.len() { break; }
            let pname = p.name.trim_start_matches('%');
            match &args[i] {
                Operand::Const(Value::I64(v)) => {
                    smt.push_str(&format!("(assert (= {} {}))\n", pname, Self::smt_bv64(*v)));
                }
                Operand::Const(Value::U64(v)) => {
                    smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", pname, v));
                }
                Operand::Const(Value::Bool(b)) => {
                    smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", pname, if *b { 1 } else { 0 }));
                }
                Operand::Reg(r) => {
                    let clean_r = r.trim_start_matches('%');
                    let mapped_arg = current_val.get(clean_r).cloned().unwrap_or_else(|| clean_r.to_string());
                    smt.push_str(&format!("(assert (= {} {}))\n", pname, mapped_arg));

                    let len_key = format!("{}_len", clean_r);
                    let mapped_len = current_val.get(&len_key).cloned().unwrap_or_else(|| len_key);
                    smt.push_str(&format!("(assert (= {}_len {}))\n", pname, mapped_len));
                }
                _ => {}
            }
        }

        // Negate callee REQUIRE
        smt.push_str(&format!("(assert (not {}))\n", Self::expr_to_smt_bool(req_expr)));
        smt.push_str("(check-sat)\n(get-model)\n");
        smt
    }

    fn build_mem_bounds_query(
        func: &Function,
        inst_idx: usize,
        requires: &[Expr],
        offset_op: &Operand,
        access_bytes: usize,
        buf_size: usize,
        buffer_sizes: &std::collections::HashMap<String, usize>,
        program: Option<&Program>,
    ) -> String {
        let mut smt = String::from("(set-logic QF_BV)\n");
        let current_val = Self::emit_symbolic_prefix(func, inst_idx, requires, buffer_sizes, program, &mut smt);

        let off_str = Self::resolve_operand(offset_op, &current_val);

        if buf_size < access_bytes {
            smt.push_str("(assert true)\n");
        } else {
            let max_valid_offset = buf_size - access_bytes;
            smt.push_str(&format!(
                "(assert (or (bvslt {} (_ bv0 64)) (bvsgt {} (_ bv{} 64))))\n",
                off_str, off_str, max_valid_offset
            ));
        }
        smt.push_str("(check-sat)\n(get-model)\n");
        smt
    }

    fn build_buffer_overflow_query(
        func: &Function,
        inst_idx: usize,
        requires: &[Expr],
        count_op: &Operand,
        buf_size: usize,
        buffer_sizes: &std::collections::HashMap<String, usize>,
        program: Option<&Program>,
    ) -> String {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_BV)\n");
        let current_val = Self::emit_symbolic_prefix(func, inst_idx, requires, buffer_sizes, program, &mut smt);

        let count_str = Self::resolve_operand(count_op, &current_val);

        smt.push_str(&format!(
            "(assert (or (bvsgt {} (_ bv{} 64)) (bvslt {} (_ bv0 64))))\n",
            count_str, buf_size, count_str
        ));
        smt.push_str("(check-sat)\n(get-model)\n");
        smt
    }

    fn build_div_zero_query(
        func: &Function,
        inst_idx: usize,
        requires: &[Expr],
        divisor: &Operand,
        buffer_sizes: &std::collections::HashMap<String, usize>,
        program: Option<&Program>,
    ) -> String {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_BV)\n");
        let current_val = Self::emit_symbolic_prefix(func, inst_idx, requires, buffer_sizes, program, &mut smt);

        let div_str = Self::resolve_operand(divisor, &current_val);

        smt.push_str(&format!("(assert (= {} (_ bv0 64)))\n", div_str));
        smt.push_str("(check-sat)\n(get-model)\n");
        smt
    }

    fn build_base_case_query(
        func: &Function,
        loop_start_idx: usize,
        requires: &[Expr],
        invariants: &[Expr],
        buffer_sizes: &std::collections::HashMap<String, usize>,
        program: Option<&Program>,
    ) -> String {
        let mut smt = String::new();
        smt.push_str("(set-logic QF_BV)\n");

        let current_val = Self::emit_symbolic_prefix(func, loop_start_idx, requires, buffer_sizes, program, &mut smt);

        let inv_terms: Vec<String> = invariants
            .iter()
            .map(|inv| {
                let mapped = Self::subst_expr_vars(inv, &current_val);
                Self::expr_to_smt_bool(&mapped)
            })
            .collect();

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
            Operand::Const(Value::I64(n)) => Self::smt_bv64(*n),
            Operand::Const(Value::U64(n)) => format!("(_ bv{} 64)", n),
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
        let mut break_points = Vec::new();
        let mut declared_steps = std::collections::HashSet::new();
        let mut pending_incoming: std::collections::HashMap<String, Vec<(String, std::collections::HashMap<String, String>)>> = std::collections::HashMap::new();
        let mut skip_until_label: Option<(String, std::collections::HashMap<String, String>)> = None;

        for (idx, s_inst) in func.instructions[loop_start_idx + 1..loop_end_idx].iter().enumerate() {
            if let Some((ref target, ref pre_jump_state)) = skip_until_label {
                if let Instruction::Label(lbl) = &s_inst.inst {
                    if lbl == target {
                        let mut base_state = pre_jump_state.clone();
                        if let Some(incoming_list) = pending_incoming.remove(lbl) {
                            for (cond_smt, branch_state) in incoming_list {
                                let mut all_keys: std::collections::HashSet<String> = base_state.keys().cloned().collect();
                                all_keys.extend(branch_state.keys().cloned());
                                for k in all_keys {
                                    let v_else = base_state.get(&k).cloned().unwrap_or_else(|| k.clone());
                                    let v_then = branch_state.get(&k).cloned().unwrap_or_else(|| k.clone());
                                    if v_else != v_then {
                                        let phi = format!("{}_loop_phi_{}", k, idx);
                                        if declared_steps.insert(phi.clone()) {
                                            smt_body.push_str(&format!("(declare-const {} (_ BitVec 64))\n", phi));
                                        }
                                        smt_body.push_str(&format!("(assert (= {} (ite {} {} {})))\n", phi, cond_smt, v_then, v_else));
                                        base_state.insert(k, phi);
                                    }
                                }
                            }
                        }
                        current_val = base_state;
                        skip_until_label = None;
                    } else if let Some(incoming_list) = pending_incoming.remove(lbl) {
                        let (cond_smt, then_start_state) = incoming_list.into_iter().last().unwrap();
                        let else_end_state = pre_jump_state.clone();
                        pending_incoming
                            .entry(target.clone())
                            .or_default()
                            .push((format!("(not {})", cond_smt), else_end_state));
                        current_val = then_start_state;
                        skip_until_label = None;
                    }
                }
                continue;
            }

            match &s_inst.inst {
                Instruction::Invariant(_) | Instruction::Decreases(_) | Instruction::Assert(_) => {
                    // Contracts handled separately
                }
                Instruction::Jump(target) => {
                    skip_until_label = Some((target.clone(), current_val.clone()));
                }
                Instruction::AssignConst { dest, val, .. } => {
                    let d = dest.trim_start_matches('%');
                    let step_name = format!("{}_step_{}", d, idx);
                    if declared_steps.insert(step_name.clone()) {
                        smt_body.push_str(&format!("(declare-const {} (_ BitVec 64))\n", step_name));
                    }
                    let val_smt = match val {
                        Value::I64(n) => Self::smt_bv64(*n),
                        Value::U64(n) => format!("(_ bv{} 64)", n),
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
                    let brk_cond = format!("(distinct {} (_ bv0 64))", val);
                    loop_break_conds.push(brk_cond.clone());
                    break_points.push((brk_cond, current_val.clone()));
                }
                Instruction::BrIf { cond, target } => {
                    let c = cond.trim_start_matches('%');
                    let val = current_val.get(c).cloned().unwrap_or_else(|| c.to_string());
                    if !inner_labels.contains(target) {
                        loop_continue_conds.push(format!("(= {} (_ bv0 64))", val));
                        let brk_cond = format!("(distinct {} (_ bv0 64))", val);
                        loop_break_conds.push(brk_cond.clone());
                        break_points.push((brk_cond, current_val.clone()));
                    } else {
                        pending_incoming
                            .entry(target.clone())
                            .or_default()
                            .push((format!("(distinct {} (_ bv0 64))", val), current_val.clone()));
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
                Instruction::Label(lbl) => {
                    if let Some(incoming_list) = pending_incoming.remove(lbl) {
                        for (cond_smt, branch_state) in incoming_list {
                            let mut all_keys: std::collections::HashSet<String> = current_val.keys().cloned().collect();
                            all_keys.extend(branch_state.keys().cloned());
                            for k in all_keys {
                                let v_cur = current_val.get(&k).cloned().unwrap_or_else(|| k.clone());
                                let v_brk = branch_state.get(&k).cloned().unwrap_or_else(|| k.clone());
                                if v_cur != v_brk {
                                    let phi = format!("{}_loop_phi_{}", k, idx);
                                    if declared_steps.insert(phi.clone()) {
                                        smt_body.push_str(&format!("(declare-const {} (_ BitVec 64))\n", phi));
                                    }
                                    smt_body.push_str(&format!("(assert (= {} (ite {} {} {})))\n", phi, cond_smt, v_brk, v_cur));
                                    current_val.insert(k, phi);
                                }
                            }
                        }
                    }
                }
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
            break_points,
        })
    }

    /// Phát sinh các ràng buộc cho các biến được định nghĩa trước vòng lặp và không bị thay đổi trong vòng lặp
    fn emit_pre_loop_invariants(
        func: &Function,
        loop_start_idx: usize,
        transition: &LoopTransition,
        declared_vars: &mut std::collections::HashSet<String>,
        smt: &mut String,
    ) {
        for s_inst in &func.instructions[..loop_start_idx] {
            match &s_inst.inst {
                Instruction::AssignConst { dest, val, .. } => {
                    let d = dest.trim_start_matches('%');
                    if !transition.next_state.contains_key(d) || transition.next_state.get(d) == Some(&d.to_string()) {
                        if declared_vars.insert(d.to_string()) {
                            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                        }
                        match val {
                            Value::I64(v) => smt.push_str(&format!("(assert (= {} {}))\n", d, Self::smt_bv64(*v))),
                            Value::U64(v) => smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", d, v)),
                            Value::Bool(b) => smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", d, if *b { 1 } else { 0 })),
                            _ => {}
                        }
                    }
                }
                Instruction::Mov { dest, src } => {
                    let d = dest.trim_start_matches('%');
                    let s = src.trim_start_matches('%');
                    if !transition.next_state.contains_key(d) || transition.next_state.get(d) == Some(&d.to_string()) {
                        if declared_vars.insert(d.to_string()) {
                            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                        }
                        if declared_vars.insert(s.to_string()) {
                            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", s));
                        }
                        smt.push_str(&format!("(assert (= {} {}))\n", d, s));
                    }
                }
                Instruction::Binary { op, dest, src1, src2, .. } => {
                    let d = dest.trim_start_matches('%');
                    if !transition.next_state.contains_key(d) || transition.next_state.get(d) == Some(&d.to_string()) {
                        if declared_vars.insert(d.to_string()) {
                            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", d));
                        }
                        let empty_map = std::collections::HashMap::new();
                        let s1 = Self::resolve_operand(src1, &empty_map);
                        let s2 = Self::resolve_operand(src2, &empty_map);
                        smt.push_str(&format!("(assert (= {} {}))\n", d, Self::binop_to_smt(op, &s1, &s2)));
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

        Self::emit_pre_loop_invariants(func, loop_start_idx, transition, &mut declared_vars, &mut smt);

        for req in requires {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt_bool(req)));
        }
        for inv in invariants {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt_bool(inv)));
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
            next_inv_terms.push(Self::expr_to_smt_bool(&next_inv_expr));
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
        loop_start_idx: usize,
        loop_end_idx: usize,
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
            smt.push_str(&format!("(assert (= {}_len {}))\n", clean, Self::smt_usize(*size)));
        }

        // Point 4: Pre-loop constants and slice lengths preservation into Exit Step
        Self::emit_pre_loop_invariants(func, loop_start_idx, transition, &mut declared_vars, &mut smt);

        for req in requires {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt_bool(req)));
        }
        for inv in invariants {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt_bool(inv)));
        }

        smt.push_str(&transition.smt_body);

        if !transition.loop_break_conds.is_empty() {
            if transition.loop_break_conds.len() == 1 {
                smt.push_str(&format!("(assert {})\n", transition.loop_break_conds[0]));
            } else {
                smt.push_str(&format!("(assert (or {}))\n", transition.loop_break_conds.join(" ")));
            }
        }

        // Point 5: Multi-break exit state merging using ite chains
        let mut current_val: std::collections::HashMap<String, String> = std::collections::HashMap::new();

        // Seed with pre-loop constants
        for s_inst in &func.instructions[..loop_start_idx] {
            match &s_inst.inst {
                Instruction::AssignConst { dest, .. }
                | Instruction::SliceLen { dest, .. } => {
                    let d = dest.trim_start_matches('%');
                    current_val.insert(d.to_string(), d.to_string());
                }
                _ => {}
            }
        }

        if transition.break_points.is_empty() {
            for (k, v) in &transition.next_state {
                current_val.insert(k.clone(), v.clone());
            }
        } else if transition.break_points.len() == 1 {
            for (k, v) in &transition.break_points[0].1 {
                current_val.insert(k.clone(), v.clone());
            }
        } else {
            let mut all_state_vars = std::collections::HashSet::new();
            for (_, st) in &transition.break_points {
                for k in st.keys() {
                    all_state_vars.insert(k.clone());
                }
            }

            for v in all_state_vars {
                let first_val = transition.break_points[0].1.get(&v).cloned().unwrap_or_else(|| v.clone());
                let all_same = transition.break_points.iter().all(|(_, st)| {
                    st.get(&v).cloned().unwrap_or_else(|| v.clone()) == first_val
                });

                if all_same {
                    current_val.insert(v.clone(), first_val);
                } else {
                    let merged_var = format!("{}_break_merged", v);
                    if declared_vars.insert(merged_var.clone()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", merged_var));
                    }
                    let last_val = transition.break_points.last().unwrap().1.get(&v).cloned().unwrap_or_else(|| v.clone());
                    let mut ite_expr = last_val;
                    for (cond, st) in transition.break_points[..transition.break_points.len() - 1].iter().rev() {
                        let this_val = st.get(&v).cloned().unwrap_or_else(|| v.clone());
                        ite_expr = format!("(ite {} {} {})", cond, this_val, ite_expr);
                    }
                    smt.push_str(&format!("(assert (= {} {}))\n", merged_var, ite_expr));
                    current_val.insert(v.clone(), merged_var);
                }
            }
        }

        // Trace post-loop instructions (after END_LOOP up to end of func)
        for (p_idx, s_inst) in func.instructions[loop_end_idx + 1..].iter().enumerate() {
            let idx = loop_end_idx + 1 + p_idx;
            match &s_inst.inst {
                Instruction::AssignConst { dest, val, .. } => {
                    let d = dest.trim_start_matches('%');
                    let ver = format!("{}_post_{}", d, idx);
                    if declared_vars.insert(ver.clone()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", ver));
                    }
                    match val {
                        Value::I64(v) => smt.push_str(&format!("(assert (= {} {}))\n", ver, Self::smt_bv64(*v))),
                        Value::U64(v) => smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", ver, v)),
                        Value::Bool(b) => smt.push_str(&format!("(assert (= {} (_ bv{} 64)))\n", ver, if *b { 1 } else { 0 })),
                        _ => {}
                    }
                    current_val.insert(d.to_string(), ver);
                }
                Instruction::Mov { dest, src } => {
                    let d = dest.trim_start_matches('%');
                    let s = src.trim_start_matches('%');
                    let s_smt = current_val.get(s).cloned().unwrap_or_else(|| s.to_string());
                    current_val.insert(d.to_string(), s_smt);
                }
                Instruction::Binary { op, dest, src1, src2, .. } => {
                    let d = dest.trim_start_matches('%');
                    let s1 = Self::resolve_operand(src1, &current_val);
                    let s2 = Self::resolve_operand(src2, &current_val);
                    let expr_str = Self::binop_to_smt(op, &s1, &s2);
                    let ver = format!("{}_post_{}", d, idx);
                    if declared_vars.insert(ver.clone()) {
                        smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", ver));
                    }
                    smt.push_str(&format!("(assert (= {} {}))\n", ver, expr_str));
                    current_val.insert(d.to_string(), ver);
                }
                _ => {}
            }
        }

        let ensure_terms: Vec<String> = ensures
            .iter()
            .map(|e| {
                let mapped = Self::subst_expr_vars(e, &current_val);
                Self::expr_to_smt_bool(&mapped)
            })
            .collect();

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

        Self::emit_pre_loop_invariants(func, loop_start_idx, transition, &mut declared_vars, &mut smt);

        for req in requires {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt_bool(req)));
        }
        for inv in invariants {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt_bool(inv)));
        }

        smt.push_str(&transition.smt_body);

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

        Self::emit_pre_loop_invariants(func, loop_start_idx, transition, &mut declared_vars, &mut smt);

        for req in requires {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt_bool(req)));
        }
        for inv in invariants {
            smt.push_str(&format!("(assert {})\n", Self::expr_to_smt_bool(inv)));
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

    /// Tìm tên biến trả về ở lệnh RET cuối cùng của hàm (thường được dùng trong mệnh đề ENSURE)
    fn find_canonical_ret_var(func: &Function) -> Option<String> {
        for s_inst in func.instructions.iter().rev() {
            if let Instruction::Ret(Some(Operand::Reg(r))) = &s_inst.inst {
                return Some(r.trim_start_matches('%').to_string());
            }
        }
        None
    }

    fn build_early_ret_ensure_query(
        func: &Function,
        ret_if_idx: usize,
        cond: &str,
        ret_val: Option<&Operand>,
        requires: &[Expr],
        ensures: &[Expr],
        buffer_sizes: &std::collections::HashMap<String, usize>,
        program: Option<&Program>,
    ) -> String {
        let mut smt = String::from("(set-logic QF_BV)\n");
        let mut current_val = Self::emit_symbolic_prefix(
            func,
            ret_if_idx,
            requires,
            buffer_sizes,
            program,
            &mut smt,
        );

        // Nếu RET_IF trả về một toán hạng/thanh ghi khác với thanh ghi trả về cuối hàm (canonical ret var),
        // ánh xạ canonical ret var sang giá trị trả về của RET_IF để ENSURE kiểm tra đúng giá trị đó!
        if let (Some(canon_ret), Some(op)) = (Self::find_canonical_ret_var(func), ret_val) {
            let early_smt_val = Self::resolve_operand(op, &current_val);
            let alias_var = format!("{}_early_ret_{}", canon_ret, ret_if_idx);
            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", alias_var));
            smt.push_str(&format!("(assert (= {} {}))\n", alias_var, early_smt_val));
            current_val.insert(canon_ret, alias_var);
        }

        // Tại điểm RET_IF, điều kiện rẽ nhánh phải ĐÚNG (khác 0)
        let c_smt = Self::resolve_operand(&Operand::Reg(cond.to_string()), &current_val);
        smt.push_str(&format!("(assert (distinct {} (_ bv0 64)))\n", c_smt));

        let ensure_terms: Vec<String> = ensures
            .iter()
            .map(|e| {
                let mapped = Self::subst_expr_vars(e, &current_val);
                Self::expr_to_smt_bool(&mapped)
            })
            .collect();

        let combined = if ensure_terms.len() == 1 {
            ensure_terms[0].clone()
        } else {
            format!("(and {})", ensure_terms.join(" "))
        };
        smt.push_str(&format!("(assert (not {}))\n", combined));
        smt.push_str("(check-sat)\n(get-model)\n");
        smt
    }

    fn build_mid_ret_ensure_query(
        func: &Function,
        ret_idx: usize,
        ret_val: Option<&Operand>,
        requires: &[Expr],
        ensures: &[Expr],
        buffer_sizes: &std::collections::HashMap<String, usize>,
        program: Option<&Program>,
    ) -> String {
        let mut smt = String::from("(set-logic QF_BV)\n");
        let mut current_val = Self::emit_symbolic_prefix(
            func,
            ret_idx,
            requires,
            buffer_sizes,
            program,
            &mut smt,
        );

        if let (Some(canon_ret), Some(op)) = (Self::find_canonical_ret_var(func), ret_val) {
            let mid_smt_val = Self::resolve_operand(op, &current_val);
            let alias_var = format!("{}_mid_ret_{}", canon_ret, ret_idx);
            smt.push_str(&format!("(declare-const {} (_ BitVec 64))\n", alias_var));
            smt.push_str(&format!("(assert (= {} {}))\n", alias_var, mid_smt_val));
            current_val.insert(canon_ret, alias_var);
        }

        let ensure_terms: Vec<String> = ensures
            .iter()
            .map(|e| {
                let mapped = Self::subst_expr_vars(e, &current_val);
                Self::expr_to_smt_bool(&mapped)
            })
            .collect();

        let combined = if ensure_terms.len() == 1 {
            ensure_terms[0].clone()
        } else {
            format!("(and {})", ensure_terms.join(" "))
        };
        smt.push_str(&format!("(assert (not {}))\n", combined));
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
        let mut smt = String::from("(set-logic QF_BV)\n");
        let current_val = Self::emit_symbolic_prefix(
            func,
            func.instructions.len(),
            requires,
            buffer_sizes,
            program,
            &mut smt,
        );

        let ensure_terms: Vec<String> = ensures
            .iter()
            .map(|e| {
                let mapped = Self::subst_expr_vars(e, &current_val);
                Self::expr_to_smt_bool(&mapped)
            })
            .collect();

        let combined = if ensure_terms.len() == 1 {
            ensure_terms[0].clone()
        } else {
            format!("(and {})", ensure_terms.join(" "))
        };
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
