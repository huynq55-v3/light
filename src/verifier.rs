//! Module Kiểm chứng Toán học (Formal Verification Engine - VCGen) cho Light
//! Kiến trúc Boogie Pure 4-Instruction IVL Pipeline:
//! 1. Static Well-Formedness Checks (Loops, Jumps, CFG Definite Assignment, Memory Sort, Types)
//! 2. Pure IVL Lowering + Guarded Symbolic Execution (`Instruction` -> `Vec<IvlStmt>`)
//! 3. Universal VcGen (`Vec<IvlStmt>` -> SMT-LIB2 `QF_ABV` -> Z3 Solver)

use crate::ast::*;
use crate::ivl::{FunctionBufferContext, IvlExpr, IvlLowerer, IvlStmt};
use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::process::{Command, Stdio};

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

#[derive(Clone)]
pub struct LoopContext<'a> {
    pub invariants: &'a [IvlExpr],
    pub decreases: &'a [IvlExpr],
    pub verify_inductive: bool,
    pub loop_id: usize,
}

pub struct Verifier;

impl Verifier {
    /// Khởi tạo kết quả `VerificationResult::Failed` tại một vị trí nguồn cụ thể
    fn fail_at(
        func: &Function,
        loc: &Loc,
        goal_name: impl Into<String>,
        category: PropertyCategory,
        reason: impl Into<String>,
        role: impl Into<String>,
    ) -> VerificationResult {
        VerificationResult::Failed {
            goal_name: goal_name.into(),
            category,
            reason: reason.into(),
            counter_example: None,
            stack_trace: vec![StackFrame {
                file: func.file.clone(),
                line: loc.line,
                function: func.name.clone(),
                snippet: loc.text.clone(),
                role: role.into(),
            }],
        }
    }

    /// Khởi tạo kết quả `VerificationResult::Unknown` tại một vị trí nguồn cụ thể
    fn unknown_at(
        func: &Function,
        loc: &Loc,
        goal_name: impl Into<String>,
        category: PropertyCategory,
        reason: impl Into<String>,
        role: impl Into<String>,
    ) -> VerificationResult {
        VerificationResult::Unknown {
            goal_name: goal_name.into(),
            category,
            reason: reason.into(),
            stack_trace: vec![StackFrame {
                file: func.file.clone(),
                line: loc.line,
                function: func.name.clone(),
                snippet: loc.text.clone(),
                role: role.into(),
            }],
        }
    }

    #[inline]
    fn is_true(e: &IvlExpr) -> bool {
        matches!(e, IvlExpr::BoolConst(true))
    }

    #[inline]
    fn is_false(e: &IvlExpr) -> bool {
        matches!(e, IvlExpr::BoolConst(false))
    }

    fn mk_not(e: IvlExpr) -> IvlExpr {
        match e {
            IvlExpr::BoolConst(b) => IvlExpr::BoolConst(!b),
            IvlExpr::Not(inner) => *inner,
            other => IvlExpr::Not(Box::new(other)),
        }
    }

    fn mk_and(a: IvlExpr, b: IvlExpr) -> IvlExpr {
        if Self::is_false(&a) || Self::is_false(&b) {
            IvlExpr::BoolConst(false)
        } else if Self::is_true(&a) {
            b
        } else if Self::is_true(&b) {
            a
        } else {
            IvlExpr::and(a, b)
        }
    }

    fn mk_or(a: IvlExpr, b: IvlExpr) -> IvlExpr {
        if Self::is_true(&a) || Self::is_true(&b) {
            IvlExpr::BoolConst(true)
        } else if Self::is_false(&a) {
            b
        } else if Self::is_false(&b) {
            a
        } else {
            IvlExpr::or(a, b)
        }
    }

    /// Biểu thức kéo theo: `guard => prop` (tương đương `!guard || prop`)
    fn mk_implies(guard: &IvlExpr, prop: IvlExpr) -> IvlExpr {
        if Self::is_true(guard) {
            prop
        } else if Self::is_false(guard) {
            IvlExpr::BoolConst(true)
        } else {
            Self::mk_or(Self::mk_not(guard.clone()), prop)
        }
    }

    /// Tách nhánh điều kiện (Path-Splitting) cho `BR_IF`, `RET`, `RET_IF`, `BREAK_IF`, `CONTINUE_IF`:
    /// 1. Tính điều kiện nhánh được kích hoạt (`take_cond = active && cond`).
    /// 2. Ghi nhận vào biến trạng thái nhánh (`__{prefix}_{id}`) để tránh nhân bản biểu thức SMT.
    /// 3. Cập nhật `active` cho phần luồng chạy thẳng phía sau (`active = active && !branch_var`).
    fn split_branch(
        stmts: &mut Vec<IvlStmt>,
        active: &mut IvlExpr,
        havoc_counter: &mut usize,
        prefix: &str,
        cond_reg: Option<&str>,
    ) -> (IvlExpr, IvlExpr) {
        let take_cond = match cond_reg {
            Some(c) => {
                let cond_expr = IvlExpr::Var(IvlLowerer::clean_name(c).to_string());
                Self::mk_and(active.clone(), cond_expr)
            }
            None => active.clone(),
        };
        *havoc_counter += 1;
        let branch_var = format!("{}_{}", prefix, *havoc_counter);
        stmts.push(IvlStmt::Assign {
            dest: branch_var.clone(),
            expr: take_cond.clone(),
            is_memory: false,
        });
        let branch_var_expr = IvlExpr::Var(branch_var);
        *active = if cond_reg.is_some() {
            Self::mk_and(active.clone(), Self::mk_not(branch_var_expr.clone()))
        } else {
            IvlExpr::BoolConst(false)
        };
        (take_cond, branch_var_expr)
    }

    /// Phát sinh các mệnh đề kiểm chứng quy nạp (Step 2: Invariant) và dừng vòng lặp (Step 4a/4b: Decreases)
    fn emit_loop_backedge_asserts(
        guard: &IvlExpr,
        invariants: &[IvlExpr],
        decreases: &[IvlExpr],
        loop_id: usize,
        loc: &Loc,
        inv_goal: String,
        dec_goal_a: String,
        dec_goal_b: String,
        stmts: &mut Vec<IvlStmt>,
    ) {
        for inv in invariants {
            stmts.push(IvlStmt::Assert {
                cond: Self::mk_implies(guard, inv.clone()),
                goal_name: inv_goal.clone(),
                category: PropertyCategory::Inductive,
                loc: loc.clone(),
            });
        }
        for (d_idx, dec) in decreases.iter().enumerate() {
            let old_r = IvlExpr::Var(format!("__rank_init_{}_{}", loop_id, d_idx));
            stmts.push(IvlStmt::Assert {
                cond: Self::mk_implies(guard, IvlExpr::gte(old_r.clone(), IvlExpr::IntConst(0))),
                goal_name: dec_goal_a.clone(),
                category: PropertyCategory::Termination,
                loc: loc.clone(),
            });
            stmts.push(IvlStmt::Assert {
                cond: Self::mk_implies(guard, IvlExpr::lt(dec.clone(), old_r)),
                goal_name: dec_goal_b.clone(),
                category: PropertyCategory::Termination,
                loc: loc.clone(),
            });
        }
    }

    /// Bọc điều kiện luồng chạy `active` vào mọi vi lệnh IVL cơ bản (Assign, Assert, Assume, Havoc).
    /// Khi `include_asserts == false` (ví dụ trong pha thăm dò `probe_stmts` của vòng lặp ngoài),
    /// các lệnh `Assert` được lược bỏ để không sinh trùng lặp mệnh đề kiểm chứng cho vòng lặp con.
    fn guard_stmts(
        raw_stmts: Vec<IvlStmt>,
        active: &IvlExpr,
        havoc_counter: &mut usize,
        include_asserts: bool,
    ) -> Vec<IvlStmt> {
        if Self::is_false(active) {
            return Vec::new();
        }
        if Self::is_true(active) && include_asserts {
            return raw_stmts;
        }

        let mut out = Vec::new();
        for st in raw_stmts {
            match st {
                IvlStmt::Assign {
                    dest,
                    expr,
                    is_memory,
                } => {
                    let clean = IvlLowerer::clean_name(&dest).to_string();
                    let new_expr = if Self::is_true(active) {
                        expr
                    } else {
                        IvlExpr::Ite {
                            cond: Box::new(active.clone()),
                            then_val: Box::new(expr),
                            else_val: Box::new(IvlExpr::Var(clean.clone())),
                        }
                    };
                    out.push(IvlStmt::Assign {
                        dest: clean,
                        expr: new_expr,
                        is_memory,
                    });
                }
                IvlStmt::Assert {
                    cond,
                    goal_name,
                    category,
                    loc,
                } => {
                    if include_asserts {
                        out.push(IvlStmt::Assert {
                            cond: Self::mk_implies(active, cond),
                            goal_name,
                            category,
                            loc,
                        });
                    }
                }
                IvlStmt::Assume { cond } => {
                    out.push(IvlStmt::Assume {
                        cond: Self::mk_implies(active, cond),
                    });
                }
                IvlStmt::Havoc { vars, is_memory } => {
                    if Self::is_true(active) {
                        out.push(IvlStmt::Havoc { vars, is_memory });
                    } else {
                        for v in vars {
                            *havoc_counter += 1;
                            let clean = IvlLowerer::clean_name(&v).to_string();
                            let tmp = format!("__guarded_havoc_{}_{}", clean, *havoc_counter);
                            out.push(IvlStmt::Havoc {
                                vars: vec![tmp.clone()],
                                is_memory,
                            });
                            out.push(IvlStmt::Assign {
                                dest: clean.clone(),
                                expr: IvlExpr::Ite {
                                    cond: Box::new(active.clone()),
                                    then_val: Box::new(IvlExpr::Var(tmp)),
                                    else_val: Box::new(IvlExpr::Var(clean)),
                                },
                                is_memory,
                            });
                        }
                    }
                }
            }
        }
        out
    }

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

    /// Hạ cấp một lát cắt lệnh sang chuỗi 4 vi lệnh IVL bằng Guarded Symbolic Execution & Boogie Loop Desugaring.
    /// Toàn bộ hàm và mọi vòng lặp lồng nhau đều kết tinh thành một `Vec<IvlStmt>` tuyến tính duy nhất!
    fn lower_slice(
        func: &Function,
        slice: &[SpannedInstruction],
        ctx: &FunctionBufferContext,
        program: Option<&Program>,
        diagnostics: &mut Vec<VerificationResult>,
        ensures: &[Expr],
        canon_ret: &str,
        has_loop: bool,
        loop_ctx: Option<&LoopContext>,
        loop_exit_out: Option<&mut IvlExpr>,
        loop_break_out: Option<&mut IvlExpr>,
        havoc_counter: &mut usize,
    ) -> Vec<IvlStmt> {
        let mut stmts = Vec::new();
        let has_branch = slice
            .iter()
            .any(|s| matches!(s.inst, Instruction::BrIf { .. } | Instruction::RetIf { .. }));

        // Trạng thái luồng chạy hiện tại (Path Condition) và bảng các nhánh nhảy tới từng LABEL
        let mut active = IvlExpr::BoolConst(true);
        let mut incoming_jumps: HashMap<String, IvlExpr> = HashMap::new();
        let mut local_loop_exit = IvlExpr::BoolConst(false);
        let mut local_loop_break = IvlExpr::BoolConst(false);

        let mut idx = 0;
        while idx < slice.len() {
            let s_inst = &slice[idx];
            match &s_inst.inst {
                Instruction::Require(req) => {
                    let cond = Self::mk_implies(
                        &active,
                        IvlLowerer::expr_to_ivl_typed(req, &ctx.unsigned_vars),
                    );
                    stmts.push(IvlStmt::Assume { cond });
                }
                Instruction::Ensure(_) | Instruction::Invariant(_) | Instruction::Decreases(_) => {}

                Instruction::Label(lbl) => {
                    if let Some(inc) = incoming_jumps.remove(lbl) {
                        active = Self::mk_or(active, inc);
                        // Tạo một biến định danh ngắn gọn cho Path Condition tại điểm hội tụ để tránh công thức SMT phình to theo cấp số nhân
                        *havoc_counter += 1;
                        let path_var =
                            format!("__path_{}_{}", lbl.trim_start_matches('.'), *havoc_counter);
                        stmts.push(IvlStmt::Assign {
                            dest: path_var.clone(),
                            expr: active,
                            is_memory: false,
                        });
                        active = IvlExpr::Var(path_var);
                    }
                }

                // Hợp nhất JUMP và BR_IF: JUMP <target> tương đương BR_IF không điều kiện
                Instruction::Jump(target) | Instruction::BrIf { target, .. } => {
                    let cond_opt = match &s_inst.inst {
                        Instruction::BrIf { cond, .. } => Some(cond.as_str()),
                        _ => None,
                    };
                    let is_forward = slice[idx + 1..]
                        .iter()
                        .any(|s| matches!(&s.inst, Instruction::Label(l) if l == target));
                    if !is_forward {
                        let op_name = if cond_opt.is_none() { "JUMP" } else { "BR_IF" };
                        diagnostics.push(Self::unknown_at(
                            func,
                            &s_inst.loc,
                            format!(
                                "Function '{}' - Line {}: Unsupported backward/external {}",
                                func.name, s_inst.loc.line, op_name
                            ),
                            PropertyCategory::Safety,
                            format!(
                                "Backward or external branch to '{}' is not supported (use LOOP for loops)",
                                target
                            ),
                            format!("Unsupported backward/external {}", op_name),
                        ));
                        return stmts;
                    }

                    let taken_expr = if let Some(cond) = cond_opt {
                        let (_, br_var_expr) = Self::split_branch(
                            &mut stmts,
                            &mut active,
                            havoc_counter,
                            "__br",
                            Some(cond),
                        );
                        br_var_expr
                    } else {
                        std::mem::replace(&mut active, IvlExpr::BoolConst(false))
                    };
                    let prev = incoming_jumps
                        .remove(target)
                        .unwrap_or(IvlExpr::BoolConst(false));
                    incoming_jumps.insert(target.clone(), Self::mk_or(prev, taken_expr));
                }

                // Hợp nhất RET và RET_IF: kiểm chứng ENSURE bằng phép thế trực tiếp (tránh làm bẩn biến tham số/cục bộ)
                Instruction::Ret(val_opt) | Instruction::RetIf { val: val_opt, .. } => {
                    let cond_opt = match &s_inst.inst {
                        Instruction::RetIf { cond, .. } => Some(cond.as_str()),
                        _ => None,
                    };
                    let is_early = cond_opt.is_some();
                    let (take_ret, ret_var_expr) = Self::split_branch(
                        &mut stmts,
                        &mut active,
                        havoc_counter,
                        "__ret",
                        cond_opt,
                    );
                    local_loop_exit = Self::mk_or(local_loop_exit, ret_var_expr);

                    let include_asserts = loop_ctx.map_or(true, |c| c.verify_inductive);
                    if !Self::is_false(&take_ret) && include_asserts {
                        let goal_name = if is_early {
                            format!(
                                "Function '{}' - Line {}: Verify ENSURE on early return (RET_IF)",
                                func.name, s_inst.loc.line
                            )
                        } else if has_loop {
                            format!(
                                "Function '{}' - Step 3: Exit Step (ENSURE postcondition satisfaction)",
                                func.name
                            )
                        } else if has_branch {
                            format!(
                                "Function '{}' - Line {}: Verify ENSURE on branch return (RET) - Verify ENSURE postcondition",
                                func.name, s_inst.loc.line
                            )
                        } else {
                            format!("Function '{}' - Verify ENSURE postcondition", func.name)
                        };

                        for ens in ensures {
                            let ens_ivl = IvlLowerer::expr_to_ivl_typed(ens, &ctx.unsigned_vars);
                            let checked_ens = if let Some(op) = val_opt {
                                let op_expr = IvlLowerer::operand_to_expr(op);
                                IvlLowerer::subst_expr(&ens_ivl, canon_ret, &op_expr)
                            } else {
                                ens_ivl
                            };
                            stmts.push(IvlStmt::Assert {
                                cond: Self::mk_implies(&take_ret, checked_ens),
                                goal_name: goal_name.clone(),
                                category: PropertyCategory::Functional,
                                loc: s_inst.loc.clone(),
                            });
                        }
                    }
                }

                Instruction::BreakIf(cond) => {
                    let (_, brk_var_expr) = Self::split_branch(
                        &mut stmts,
                        &mut active,
                        havoc_counter,
                        "__brk",
                        Some(cond),
                    );
                    local_loop_break = Self::mk_or(local_loop_break, brk_var_expr.clone());
                    local_loop_exit = Self::mk_or(local_loop_exit, brk_var_expr);
                }

                Instruction::ContinueIf(cond) => {
                    let (take_cont, cont_var_expr) = Self::split_branch(
                        &mut stmts,
                        &mut active,
                        havoc_counter,
                        "__cont",
                        Some(cond),
                    );
                    local_loop_exit = Self::mk_or(local_loop_exit, cont_var_expr);
                    if let Some(lctx) = loop_ctx {
                        if lctx.verify_inductive && !Self::is_false(&take_cont) {
                            Self::emit_loop_backedge_asserts(
                                &take_cont,
                                lctx.invariants,
                                lctx.decreases,
                                lctx.loop_id,
                                &s_inst.loc,
                                format!(
                                    "Function '{}' - Line {}: Loop Step 2: Invariant preservation on CONTINUE_IF",
                                    func.name, s_inst.loc.line
                                ),
                                format!(
                                    "Function '{}' - Line {}: Step 4a: Termination Step on CONTINUE_IF (DECREASES bounded below >= 0)",
                                    func.name, s_inst.loc.line
                                ),
                                format!(
                                    "Function '{}' - Line {}: Step 4b: Termination Step on CONTINUE_IF (DECREASES ranking strictly decreases)",
                                    func.name, s_inst.loc.line
                                ),
                                &mut stmts,
                            );
                        }
                    }
                }

                Instruction::Loop(_) => {
                    *havoc_counter += 1;
                    let loop_id = *havoc_counter;
                    let mut depth = 1;
                    let mut l_end = idx + 1;
                    for (p, s) in slice[idx + 1..].iter().enumerate() {
                        match &s.inst {
                            Instruction::Loop(_) => depth += 1,
                            Instruction::EndLoop(_) => {
                                depth -= 1;
                                if depth == 0 {
                                    l_end = idx + 1 + p;
                                    break;
                                }
                            }
                            _ => {}
                        }
                    }
                    let body_slice = &slice[idx + 1..l_end];

                    if body_slice
                        .iter()
                        .any(|si| matches!(si.inst, Instruction::Syscall { .. }))
                    {
                        diagnostics.push(Self::unknown_at(
                            func,
                            &slice[idx].loc,
                            format!(
                                "Function '{}' - Symbolic Loop Execution - Step 2: Inductive Step (Invariant preservation)",
                                func.name
                            ),
                            PropertyCategory::Inductive,
                            "Unsupported instruction inside loop body: SYSCALL",
                            "Unsupported instruction inside loop body: SYSCALL",
                        ));
                        return stmts;
                    }

                    let mut loop_invs = Vec::new();
                    let mut loop_decs = Vec::new();
                    let mut inner_depth = 0usize;

                    for b_si in body_slice {
                        match &b_si.inst {
                            Instruction::Loop(_) => inner_depth += 1,
                            Instruction::EndLoop(_) => inner_depth = inner_depth.saturating_sub(1),
                            Instruction::Invariant(e) if inner_depth == 0 => {
                                loop_invs.push(IvlLowerer::expr_to_ivl_typed(e, &ctx.unsigned_vars))
                            }
                            Instruction::Decreases(e) if inner_depth == 0 => {
                                loop_decs.push(IvlLowerer::expr_to_ivl_typed(e, &ctx.unsigned_vars))
                            }
                            _ => {}
                        }
                    }

                    let verify_this_loop = loop_ctx.map_or(true, |c| c.verify_inductive);

                    // --- BƯỚC 1: Base Case (Kiểm chứng Invariant đúng ngay khi vừa tiến vào vòng lặp) ---
                    if verify_this_loop {
                        for inv in &loop_invs {
                            stmts.push(IvlStmt::Assert {
                                cond: Self::mk_implies(&active, inv.clone()),
                                goal_name: format!(
                                    "Function '{}' - Step 1: Base Case (Loop initialization)",
                                    func.name
                                ),
                                category: PropertyCategory::Inductive,
                                loc: slice[idx].loc.clone(),
                            });
                        }
                    }

                    // Hạ cấp thân vòng lặp 1 lần ở chế độ thăm dò (verify_inductive: false) để tự động trích xuất 100% biến/bộ nhớ bị sửa đổi
                    let mut probe_counter = *havoc_counter;
                    let mut probe_diag = Vec::new();
                    let probe_ctx = LoopContext {
                        invariants: &[],
                        decreases: &[],
                        verify_inductive: false,
                        loop_id,
                    };
                    let probe_stmts = Self::lower_slice(
                        func,
                        body_slice,
                        ctx,
                        program,
                        &mut probe_diag,
                        ensures,
                        canon_ret,
                        true,
                        Some(&probe_ctx),
                        None,
                        None,
                        &mut probe_counter,
                    );
                    let (modified_scalars, modified_mems) =
                        IvlLowerer::extract_modified_targets_from_ivl(&probe_stmts);

                    // --- BƯỚC 2, 3, 4: Boogie Loop Desugaring về chuỗi 4 vi lệnh IVL ---
                    for (vars, is_memory) in [(modified_scalars, false), (modified_mems, true)] {
                        if !vars.is_empty() {
                            stmts.extend(Self::guard_stmts(
                                vec![IvlStmt::Havoc { vars, is_memory }],
                                &active,
                                havoc_counter,
                                verify_this_loop,
                            ));
                        }
                    }

                    // Giả định (Assume) các Invariant đúng ở đầu bước lặp tổng quát
                    for inv in &loop_invs {
                        stmts.push(IvlStmt::Assume {
                            cond: Self::mk_implies(&active, inv.clone()),
                        });
                    }

                    // Ghi nhận giá trị khởi đầu của biểu thức Ranking (DECREASES) ở đầu vòng lặp
                    for (d_idx, dec) in loop_decs.iter().enumerate() {
                        let rank_assign = IvlStmt::Assign {
                            dest: format!("__rank_init_{}_{}", loop_id, d_idx),
                            expr: dec.clone(),
                            is_memory: false,
                        };
                        stmts.extend(Self::guard_stmts(
                            vec![rank_assign],
                            &active,
                            havoc_counter,
                            verify_this_loop,
                        ));
                    }

                    // Hạ cấp thân vòng lặp (với kiểm chứng quy nạp nếu đang ở ngoài hoặc đang trong pha quy nạp của vòng lặp cha)
                    let ind_ctx = LoopContext {
                        invariants: &loop_invs,
                        decreases: &loop_decs,
                        verify_inductive: verify_this_loop,
                        loop_id,
                    };
                    let mut body_any_exit = IvlExpr::BoolConst(false);
                    let mut body_break_cond = IvlExpr::BoolConst(false);
                    let body_stmts = Self::lower_slice(
                        func,
                        body_slice,
                        ctx,
                        program,
                        diagnostics,
                        ensures,
                        canon_ret,
                        true,
                        Some(&ind_ctx),
                        Some(&mut body_any_exit),
                        Some(&mut body_break_cond),
                        havoc_counter,
                    );

                    stmts.extend(Self::guard_stmts(
                        body_stmts,
                        &active,
                        havoc_counter,
                        verify_this_loop,
                    ));

                    // Cuối thân vòng lặp (Latch): những nhánh vẫn active và KHÔNG thoát (không BREAK, không CONTINUE, không RET)
                    // sẽ quay lại đầu vòng lặp -> Phải thỏa mãn Invariant (Step 2) và Decreases (Step 4a, 4b)!
                    if verify_this_loop {
                        let latch_active =
                            Self::mk_and(active.clone(), Self::mk_not(body_any_exit));
                        Self::emit_loop_backedge_asserts(
                            &latch_active,
                            &loop_invs,
                            &loop_decs,
                            loop_id,
                            &slice[idx].loc,
                            format!(
                                "Function '{}' - Symbolic Loop Execution - Step 2: Inductive Step (Invariant preservation)",
                                func.name
                            ),
                            format!(
                                "Function '{}' - Step 4a: Termination Step (DECREASES bounded below >= 0)",
                                func.name
                            ),
                            format!(
                                "Function '{}' - Step 4b: Termination Step (DECREASES ranking function strictly decreases)",
                                func.name
                            ),
                            &mut stmts,
                        );
                    }

                    // Sau END_LOOP (Step 3 - Exit Step): để đi tiếp xuống các lệnh sau vòng lặp,
                    // nhánh bắt buộc phải thoát ra qua ít nhất một lệnh BREAK_IF của chính vòng lặp này!
                    stmts.push(IvlStmt::Assume {
                        cond: Self::mk_implies(&active, body_break_cond),
                    });

                    idx = l_end + 1;
                    continue;
                }

                Instruction::EndLoop(_) => {}

                _other => {
                    let include_asserts = loop_ctx.map_or(true, |c| c.verify_inductive);
                    let raw = IvlLowerer::lower_atomic_instruction(func, s_inst, ctx, program);
                    stmts.extend(Self::guard_stmts(
                        raw,
                        &active,
                        havoc_counter,
                        include_asserts,
                    ));
                }
            }
            idx += 1;
        }

        if let Some(out_exit) = loop_exit_out {
            *out_exit = local_loop_exit;
        }
        if let Some(out_break) = loop_break_out {
            *out_break = local_loop_break;
        }
        stmts
    }

    /// Kiểm tra tính đúng đắn tĩnh (Static Well-Formedness) trước khi hạ cấp sang IVL:
    /// 1. Tính duy nhất của tên LABEL / LOOP trong hàm.
    /// 2. Cấu trúc đóng mở `LOOP ... END_LOOP`, vị trí `BREAK_IF`/`CONTINUE_IF`, và cấm nhảy xuyên ranh giới vòng lặp.
    /// 3. Mọi đích nhảy `JUMP`/`BR_IF` phải tồn tại.
    /// 4. SSA Definite Assignment trên đồ thị dòng điều khiển (CFG).
    /// 5. Tính nhất quán kiểu bộ nhớ (không trộn lẫn truy cập 8-bit và 64-bit trên cùng một vùng nhớ).
    fn check_static_well_formedness(
        func: &Function,
        ctx: &FunctionBufferContext,
    ) -> Option<VerificationResult> {
        // Pass 1: Thu thập bảng nhãn, kiểm tra trùng tên LABEL/LOOP, và ghi nhận độ sâu vòng lặp tại từng LABEL
        let mut seen_symbols: HashMap<&str, usize> = HashMap::new();
        let mut label_loop_nesting: HashMap<&str, Vec<&str>> = HashMap::new();
        let mut cur_nesting: Vec<&str> = Vec::new();

        for s_inst in &func.instructions {
            match &s_inst.inst {
                Instruction::Loop(lbl) | Instruction::Label(lbl) => {
                    if let Some(&prev_line) = seen_symbols.get(lbl.as_str()) {
                        return Some(Self::fail_at(
                            func,
                            &s_inst.loc,
                            format!(
                                "Function '{}' - Line {}: Duplicate Label/Loop '{}'",
                                func.name, s_inst.loc.line, lbl
                            ),
                            PropertyCategory::Safety,
                            format!(
                                "Duplicate label or loop name '{}' (already defined at line {})",
                                lbl, prev_line
                            ),
                            format!("Duplicate symbol '{}'", lbl),
                        ));
                    }
                    seen_symbols.insert(lbl.as_str(), s_inst.loc.line);
                    if matches!(&s_inst.inst, Instruction::Loop(_)) {
                        cur_nesting.push(lbl.as_str());
                    } else {
                        label_loop_nesting.insert(lbl.as_str(), cur_nesting.clone());
                    }
                }
                Instruction::EndLoop(_) => {
                    cur_nesting.pop();
                }
                _ => {}
            }
        }

        // Pass 2: Kiểm tra cấu trúc LOOP/END_LOOP, BREAK_IF/CONTINUE_IF, nhảy xuyên vòng lặp & đích nhảy không tồn tại
        let mut loop_stack: Vec<(&str, &Loc)> = Vec::new();
        cur_nesting.clear();
        let mut has_mem8 = HashSet::new();
        let mut has_mem64 = HashSet::new();

        for s_inst in &func.instructions {
            match &s_inst.inst {
                Instruction::Loop(lbl) => {
                    cur_nesting.push(lbl.as_str());
                    loop_stack.push((lbl.as_str(), &s_inst.loc));
                }
                Instruction::EndLoop(lbl) => {
                    cur_nesting.pop();
                    match loop_stack.pop() {
                        Some((open_lbl, _)) if open_lbl == lbl => {}
                        Some((open_lbl, open_loc)) => {
                            return Some(Self::fail_at(
                                func,
                                &s_inst.loc,
                                format!(
                                    "Function '{}' - Line {}: Loop Structure Error",
                                    func.name, s_inst.loc.line
                                ),
                                PropertyCategory::Safety,
                                format!(
                                    "Mismatched END_LOOP '{}' (expected '{}' opened at line {})",
                                    lbl, open_lbl, open_loc.line
                                ),
                                format!("Mismatched END_LOOP '{}'", lbl),
                            ));
                        }
                        None => {
                            return Some(Self::fail_at(
                                func,
                                &s_inst.loc,
                                format!(
                                    "Function '{}' - Line {}: Loop Structure Error",
                                    func.name, s_inst.loc.line
                                ),
                                PropertyCategory::Safety,
                                format!("Unexpected END_LOOP '{}' without matching LOOP", lbl),
                                format!("Unmatched END_LOOP '{}'", lbl),
                            ));
                        }
                    }
                }
                Instruction::BreakIf(_) | Instruction::ContinueIf(_) => {
                    if loop_stack.is_empty() {
                        let op_name = if matches!(&s_inst.inst, Instruction::BreakIf(_)) {
                            "BREAK_IF"
                        } else {
                            "CONTINUE_IF"
                        };
                        return Some(Self::fail_at(
                            func,
                            &s_inst.loc,
                            format!(
                                "Function '{}' - Line {}: Loop Structure Error",
                                func.name, s_inst.loc.line
                            ),
                            PropertyCategory::Safety,
                            format!(
                                "{} must be placed inside a LOOP ... END_LOOP block",
                                op_name
                            ),
                            format!("{} outside of LOOP", op_name),
                        ));
                    }
                }
                Instruction::Jump(target) | Instruction::BrIf { target, .. } => {
                    if let Some(target_nesting) = label_loop_nesting.get(target.as_str()) {
                        if target_nesting != &cur_nesting {
                            return Some(Self::fail_at(
                                func,
                                &s_inst.loc,
                                format!(
                                    "Function '{}' - Line {}: Loop Structure Error",
                                    func.name, s_inst.loc.line
                                ),
                                PropertyCategory::Safety,
                                format!(
                                    "Jump or branch to '{}' crosses loop boundaries (jumping across loop blocks is not allowed; use structured BREAK_IF/CONTINUE_IF instead)",
                                    target
                                ),
                                format!("Cross-loop jump to '{}'", target),
                            ));
                        }
                    } else {
                        return Some(Self::fail_at(
                            func,
                            &s_inst.loc,
                            format!(
                                "Function '{}' - Line {}: Undefined label '{}'",
                                func.name, s_inst.loc.line, target
                            ),
                            PropertyCategory::Safety,
                            format!(
                                "Jump target '{}' is not defined anywhere in function '{}'",
                                target, func.name
                            ),
                            format!("Undefined jump label '{}'", target),
                        ));
                    }
                }
                Instruction::Load8 { buf, .. }
                | Instruction::Store8 { buf, .. }
                | Instruction::StoreStr { buf, .. } => {
                    has_mem8.insert(ctx.resolve_root_buf(buf));
                }
                Instruction::Load64 { buf, .. } | Instruction::Store64 { buf, .. } => {
                    has_mem64.insert(ctx.resolve_root_buf(buf));
                }
                _ => {}
            }
        }

        if let Some((unclosed_lbl, unclosed_loc)) = loop_stack.last() {
            return Some(Self::fail_at(
                func,
                unclosed_loc,
                format!(
                    "Function '{}' - Line {}: Loop Structure Error",
                    func.name, unclosed_loc.line
                ),
                PropertyCategory::Safety,
                format!(
                    "Unclosed LOOP '{}' (missing END_LOOP '{}')",
                    unclosed_lbl, unclosed_lbl
                ),
                format!("Unclosed LOOP '{}'", unclosed_lbl),
            ));
        }

        // Pass 3: SSA Definite Assignment Check via CFG Forward Dataflow Analysis
        if let Some(err) = Self::check_definite_assignment_cfg(func, ctx) {
            return Some(err);
        }

        // Pass 4: Memory Sort Consistency Check (Prevent mixing 8-bit and 64-bit accesses on same buffer)
        for buf in &has_mem8 {
            if has_mem64.contains(buf) {
                let loc = Loc {
                    file: func.file.clone(),
                    line: 1,
                    text: format!(
                        "Buffer '%{}' used with both 8-bit and 64-bit memory instructions",
                        buf
                    ),
                };
                return Some(Self::fail_at(
                    func,
                    &loc,
                    format!("Function '{}': Memory Sort Consistency", func.name),
                    PropertyCategory::Safety,
                    format!(
                        "Mixed 8-bit (LOAD8/STORE8/STORE_STR) and 64-bit (LOAD64/STORE64) accesses on buffer '%{}'. In SMT QF_ABV memory theory, mixing byte-level and 64-bit word-level operations without byte concatenation causes memory model unsoundness.",
                        buf
                    ),
                    "Memory Sort Mismatch",
                ));
            }
        }

        None
    }

    /// Kiểm tra tính đúng đắn toán học bằng kiến trúc Boogie IVL Engine (Universal VCGen)
    pub fn verify_function(func: &Function, program: Option<&Program>) -> Vec<VerificationResult> {
        let mut results = Vec::new();
        let ctx = FunctionBufferContext::analyze(func, program);

        // 0. Kiểm tra tính hợp lệ tĩnh (Well-Formedness, CFG Definite Assignment, Memory Sort)
        if let Some(err) = Self::check_static_well_formedness(func, &ctx) {
            results.push(err);
            return results;
        }

        // 1. Khởi tạo Universal VcGen và khai báo các tham số đầu vào của hàm
        let mut vc = crate::vcgen::VcGen::new();
        for p in &func.params {
            let clean = IvlLowerer::clean_name(&p.name).to_string();
            vc.declared_vars.insert(clean.clone());
            vc.current_val.insert(clean.clone(), clean.clone());
            let plen = format!("{}_len", clean);
            vc.declared_vars.insert(plen.clone());
            vc.current_val.insert(plen.clone(), plen);
        }

        let ensures: Vec<Expr> = func
            .instructions
            .iter()
            .filter_map(|si| {
                if let Instruction::Ensure(e) = &si.inst {
                    Some(e.clone())
                } else {
                    None
                }
            })
            .collect();
        let canon_ret = Self::find_canonical_ret_var(func).unwrap_or_else(|| "ret".to_string());

        let has_ret = func
            .instructions
            .iter()
            .any(|si| matches!(si.inst, Instruction::Ret(_) | Instruction::RetIf { .. }));
        if !ensures.is_empty() && !has_ret {
            let loc = Loc {
                file: func.file.clone(),
                line: func.instructions.last().map(|s| s.loc.line).unwrap_or(1),
                text: "Missing RET statement".to_string(),
            };
            results.push(Self::fail_at(
                func,
                &loc,
                format!("Function '{}' - Verify ENSURE postcondition", func.name),
                PropertyCategory::Functional,
                format!(
                    "Function '{}' declares ENSURE contract but has no RET or RET_IF instruction!",
                    func.name
                ),
                "Missing RET for ENSURE postcondition",
            ));
            return results;
        }

        // 2. Hạ cấp toàn bộ hàm sang duy nhất 1 dải 4 vi lệnh IVL (Assign, Assume, Havoc, Assert)
        let has_loop = func
            .instructions
            .iter()
            .any(|s| matches!(s.inst, Instruction::Loop(_)));
        let mut havoc_counter = 0usize;
        let ivl_stmts = Self::lower_slice(
            func,
            &func.instructions,
            &ctx,
            program,
            &mut results,
            &ensures,
            &canon_ret,
            has_loop,
            None,
            None,
            None,
            &mut havoc_counter,
        );

        // 3. Chạy Universal VcGen 1 lần duy nhất trên dải vi lệnh IVL
        results.extend(vc.verify_sequence(&ivl_stmts, &func.name, &func.file));

        results
    }

    /// Thu thập các biến được định nghĩa bởi một instruction
    fn collect_defined_vars(
        inst: &Instruction,
        ctx: &FunctionBufferContext,
        out: &mut HashSet<String>,
    ) {
        match inst {
            Instruction::AssignConst { dest, .. }
            | Instruction::Binary { dest, .. }
            | Instruction::Not { dest, .. }
            | Instruction::SliceLen { dest, .. }
            | Instruction::Load8 { dest, .. }
            | Instruction::Load64 { dest, .. }
            | Instruction::Mov { dest, .. }
            | Instruction::SlicePtr { dest, .. }
            | Instruction::Alloc { dest, .. } => {
                let clean = IvlLowerer::clean_name(dest).to_string();
                out.insert(clean.clone());
                if ctx.is_known_buffer(dest) {
                    out.insert(format!("{}_len", clean));
                }
            }
            Instruction::Call { dest: Some(d), .. }
            | Instruction::Syscall { dest: Some(d), .. } => {
                out.insert(IvlLowerer::clean_name(d).to_string());
            }
            Instruction::Syscall { dest: None, .. } => {
                out.insert("rax".to_string());
            }
            _ => {}
        }
    }

    #[inline]
    fn push_used_reg(r: &str, used_regs: &mut Vec<String>) {
        let inner = if r.starts_with("len(") && r.ends_with(')') {
            r[4..r.len() - 1].trim()
        } else {
            r
        };
        used_regs.push(IvlLowerer::clean_name(inner).to_string());
    }

    #[inline]
    fn push_used_op(op: &Operand, used_regs: &mut Vec<String>) {
        if let Operand::Reg(r) = op {
            Self::push_used_reg(r, used_regs);
        }
    }

    /// Thu thập các biến được sử dụng bởi một instruction
    fn collect_used_vars(
        inst: &Instruction,
        all_ret_vars: &HashSet<String>,
        used_regs: &mut Vec<String>,
    ) {
        match inst {
            Instruction::Require(e)
            | Instruction::Invariant(e)
            | Instruction::Decreases(e)
            | Instruction::Assert(e) => {
                let mut expr_vars = HashSet::new();
                Self::collect_vars(e, &mut expr_vars);
                used_regs.extend(expr_vars);
            }
            Instruction::Ensure(e) => {
                let mut expr_vars = HashSet::new();
                Self::collect_vars(e, &mut expr_vars);
                used_regs.extend(expr_vars.into_iter().filter(|v| !all_ret_vars.contains(v)));
            }
            Instruction::Mov { src, .. }
            | Instruction::StoreStr { buf: src, .. }
            | Instruction::SlicePtr { slice: src, .. }
            | Instruction::SliceLen { slice: src, .. }
            | Instruction::BrIf { cond: src, .. }
            | Instruction::BreakIf(src)
            | Instruction::ContinueIf(src) => Self::push_used_reg(src, used_regs),
            Instruction::Not { src, .. } | Instruction::Ret(Some(src)) => {
                Self::push_used_op(src, used_regs);
            }
            Instruction::Binary { src1, src2, .. } => {
                Self::push_used_op(src1, used_regs);
                Self::push_used_op(src2, used_regs);
            }
            Instruction::Store8 { buf, offset, val }
            | Instruction::Store64 { buf, offset, val } => {
                Self::push_used_reg(buf, used_regs);
                Self::push_used_op(offset, used_regs);
                Self::push_used_op(val, used_regs);
            }
            Instruction::Load8 { buf, offset, .. } | Instruction::Load64 { buf, offset, .. } => {
                Self::push_used_reg(buf, used_regs);
                Self::push_used_op(offset, used_regs);
            }
            Instruction::RetIf { cond, val } => {
                Self::push_used_reg(cond, used_regs);
                if let Some(op) = val {
                    Self::push_used_op(op, used_regs);
                }
            }
            Instruction::Call { args, .. } => {
                for a in args {
                    Self::push_used_op(a, used_regs);
                }
            }
            Instruction::Syscall {
                rax,
                rdi,
                rsi,
                rdx,
                r10,
                r8,
                r9,
                ..
            } => {
                for op in [
                    Some(rax),
                    Some(rdi),
                    Some(rsi),
                    Some(rdx),
                    r10.as_ref(),
                    r8.as_ref(),
                    r9.as_ref(),
                ]
                .into_iter()
                .flatten()
                {
                    Self::push_used_op(op, used_regs);
                }
            }
            _ => {}
        }
    }

    /// Phân tích Definite Assignment chuẩn xác qua duyệt luồng tiến (Forward Jump & Structured Loop)
    fn check_definite_assignment_cfg(
        func: &Function,
        ctx: &FunctionBufferContext,
    ) -> Option<VerificationResult> {
        let mut defined: HashSet<String> = func
            .params
            .iter()
            .flat_map(|p| {
                let c = IvlLowerer::clean_name(&p.name).to_string();
                if matches!(p.ty, Type::Slice(_) | Type::Array(_, _)) {
                    vec![c.clone(), format!("{}_len", c)]
                } else {
                    vec![c]
                }
            })
            .collect();

        let mut all_ret_vars: HashSet<String> = ["ret", "result", "res"]
            .into_iter()
            .map(String::from)
            .collect();
        if let Some(cr) = Self::find_canonical_ret_var(func) {
            all_ret_vars.insert(IvlLowerer::clean_name(&cr).to_string());
        }
        for s in &func.instructions {
            if let Instruction::Ret(Some(Operand::Reg(r)))
            | Instruction::RetIf {
                val: Some(Operand::Reg(r)),
                ..
            } = &s.inst
            {
                all_ret_vars.insert(IvlLowerer::clean_name(r).to_string());
            }
        }

        // Lưu trạng thái tập biến tại các nhánh nhảy tiến tới LABEL hoặc thoát LOOP
        let mut incoming_label: HashMap<String, HashSet<String>> = HashMap::new();
        let mut loop_exit_states: Vec<Option<HashSet<String>>> = Vec::new();
        let mut reachable = true;

        for s_inst in &func.instructions {
            match &s_inst.inst {
                Instruction::Label(lbl) => {
                    if let Some(inc) = incoming_label.remove(lbl) {
                        if reachable {
                            defined.retain(|v| inc.contains(v));
                        } else {
                            defined = inc;
                            reachable = true;
                        }
                    }
                }
                Instruction::Loop(_) => {
                    loop_exit_states.push(None);
                }
                Instruction::EndLoop(_) => {
                    if let Some(opt_exit) = loop_exit_states.pop() {
                        if let Some(exit_defs) = opt_exit {
                            defined = exit_defs;
                            reachable = true;
                        } else {
                            reachable = false;
                        }
                    }
                }
                _ => {}
            }

            if !reachable {
                continue;
            }

            let mut used_regs = Vec::new();
            Self::collect_used_vars(&s_inst.inst, &all_ret_vars, &mut used_regs);
            for clean in used_regs {
                if !defined.contains(&clean) {
                    return Some(Self::fail_at(
                        func,
                        &s_inst.loc,
                        format!(
                            "Function '{}' - Line {}: SSA Definite Assignment",
                            func.name, s_inst.loc.line
                        ),
                        PropertyCategory::Safety,
                        format!(
                            "Variable '%{}' used before definition (not assigned on all execution paths)!",
                            clean
                        ),
                        format!("Use of undefined variable '%{}'", clean),
                    ));
                }
            }

            Self::collect_defined_vars(&s_inst.inst, ctx, &mut defined);

            match &s_inst.inst {
                Instruction::BrIf { target, .. } => {
                    incoming_label
                        .entry(target.clone())
                        .and_modify(|set| set.retain(|v| defined.contains(v)))
                        .or_insert_with(|| defined.clone());
                }
                Instruction::Jump(target) => {
                    incoming_label
                        .entry(target.clone())
                        .and_modify(|set| set.retain(|v| defined.contains(v)))
                        .or_insert_with(|| defined.clone());
                    reachable = false;
                }
                Instruction::BreakIf(_) => {
                    if let Some(opt_exit) = loop_exit_states.last_mut() {
                        match opt_exit {
                            Some(set) => set.retain(|v| defined.contains(v)),
                            None => *opt_exit = Some(defined.clone()),
                        }
                    }
                }
                Instruction::Ret(_) => {
                    reachable = false;
                }
                _ => {}
            }
        }
        None
    }

    /// Tìm tên biến đại diện cho giá trị trả về của hàm trong ENSURE (Deterministic 100%)
    pub fn find_canonical_ret_var(func: &Function) -> Option<String> {
        let mut ensure_vars_set = HashSet::new();
        for si in &func.instructions {
            if let Instruction::Ensure(e) = &si.inst {
                Self::collect_vars(e, &mut ensure_vars_set);
            }
        }
        let mut ensure_vars: Vec<String> = ensure_vars_set.iter().cloned().collect();
        ensure_vars.sort();

        let param_names: HashSet<String> = func
            .params
            .iter()
            .map(|p| IvlLowerer::clean_name(&p.name).to_string())
            .collect();

        // Thu thập tất cả các thanh ghi trả về (cả RET và RET_IF)
        let mut non_param_ret_regs = Vec::new();
        let mut all_ret_regs = Vec::new();
        for s_inst in func.instructions.iter().rev() {
            match &s_inst.inst {
                Instruction::Ret(Some(Operand::Reg(r)))
                | Instruction::RetIf {
                    val: Some(Operand::Reg(r)),
                    ..
                } => {
                    let clean = IvlLowerer::clean_name(r).to_string();
                    all_ret_regs.push(clean.clone());
                    if !param_names.contains(&clean) {
                        non_param_ret_regs.push(clean);
                    }
                }
                _ => {}
            }
        }
        // Ưu tiên 1: Biến trả về không phải param có mặt trực tiếp trong ensure_vars
        for r in &non_param_ret_regs {
            if ensure_vars_set.contains(r) {
                return Some(r.clone());
            }
        }
        // Ưu tiên 2: Tên quy ước chuẩn: "ret", "res", "result" nếu có trong ensure_vars
        for standard in &["ret", "res", "result"] {
            if ensure_vars_set.contains(*standard) && !param_names.contains(*standard) {
                return Some(standard.to_string());
            }
        }
        // Ưu tiên 3: Thanh ghi trả về đầu tiên không phải là tham số hàm
        if let Some(first_ret) = non_param_ret_regs.first() {
            return Some(first_ret.clone());
        }
        // Ưu tiên 4: Biến trong ENSURE không phải là param của hàm (đã sort deterministic)
        for ev in &ensure_vars {
            if !param_names.contains(ev) {
                return Some(ev.clone());
            }
        }
        // Ưu tiên 5: Hàm trả về trực tiếp chính tham số đầu vào (vd: RET x, ENSURE x >= 0)
        for r in &all_ret_regs {
            if ensure_vars_set.contains(r) {
                return Some(r.clone());
            }
        }
        all_ret_regs.first().cloned()
    }

    /// Thu thập tất cả tên biến xuất hiện trong biểu thức
    pub fn collect_vars(expr: &Expr, vars: &mut HashSet<String>) {
        match expr {
            Expr::Var(name) | Expr::Len(name) => {
                vars.insert(IvlLowerer::clean_name(name).to_string());
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

    /// Gọi Z3 Solver trực tiếp (nếu có trên máy) hoặc trả về công thức SMT-LIB2
    pub fn solve_query(
        goal_name: &str,
        category: PropertyCategory,
        query: &str,
        stack_trace: Vec<StackFrame>,
    ) -> VerificationResult {
        let _spawn_guard = crate::codegen::SPAWN_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
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
            .arg("-t:5000")
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
        drop(_spawn_guard);

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
        let first_token = stdout
            .lines()
            .map(|l| l.trim())
            .find(|l| !l.is_empty())
            .unwrap_or("");

        if first_token == "unsat" {
            VerificationResult::Verified {
                goal_name: goal_name.to_string(),
                category,
            }
        } else if first_token == "sat" {
            VerificationResult::Failed {
                goal_name: goal_name.to_string(),
                category,
                reason: "Counter-example found: Mathematical/safety contract violated!".to_string(),
                counter_example: Some(stdout.to_string()),
                stack_trace,
            }
        } else if first_token == "unknown" || first_token == "timeout" || stdout.contains("timeout")
        {
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
