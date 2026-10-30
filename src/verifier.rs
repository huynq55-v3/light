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

    #[allow(dead_code)]
    #[inline]
    pub fn smt_usize(n: usize) -> String {
        format!("(_ bv{} 64)", n)
    }

    /// Hạ cấp một lệnh sang chuỗi IVL kèm đầy đủ các kiểm chứng an toàn (Safety & Functional Asserts)
    fn lower_inst_with_checks(
        func: &Function,
        s_inst: &SpannedInstruction,
        buffer_sizes: &std::collections::HashMap<String, usize>,
        buffer_aliases: &std::collections::HashMap<String, String>,
        program: Option<&Program>,
    ) -> Vec<crate::ivl::IvlStmt> {
        let mut stmts = Vec::new();
        match &s_inst.inst {
            Instruction::Assert(e) => {
                stmts.push(crate::ivl::IvlStmt::Assert {
                    cond: crate::ivl::IvlExpr::from(e),
                    goal_name: format!("Function '{}' - Line {}: Verify ASSERT directive", func.name, s_inst.loc.line),
                    category: PropertyCategory::Functional,
                    loc: s_inst.loc.clone(),
                });
            }
            Instruction::StoreStr { buf, offset, content } => {
                let actual_buf = buffer_aliases.get(buf).unwrap_or(buf);
                let buf_size = buffer_sizes.get(actual_buf).or_else(|| buffer_sizes.get(buf)).cloned().unwrap_or(0);
                let req_size = *offset + content.as_bytes().len();
                stmts.push(crate::ivl::IvlStmt::Assert {
                    cond: crate::ivl::IvlExpr::BoolConst(req_size <= buf_size),
                    goal_name: format!("Function '{}' - Line {}: String write within buffer '{}'", func.name, s_inst.loc.line, buf),
                    category: PropertyCategory::Safety,
                    loc: s_inst.loc.clone(),
                });
                stmts.extend(crate::ivl::IvlLowerer::lower_inst(s_inst, buffer_sizes, Some(buffer_aliases)));
            }
            Instruction::Binary { op: BinOp::Div | BinOp::Mod, src1, src2, .. } => {
                let s1_expr = crate::ivl::IvlLowerer::operand_to_expr(src1);
                let s2_expr = crate::ivl::IvlLowerer::operand_to_expr(src2);
                let div_zero = crate::ivl::IvlExpr::Binary {
                    op: BinOp::Neq,
                    lhs: Box::new(s2_expr.clone()),
                    rhs: Box::new(crate::ivl::IvlExpr::IntConst(0)),
                };
                let overflow_cond = crate::ivl::IvlExpr::Binary {
                    op: BinOp::And,
                    lhs: Box::new(crate::ivl::IvlExpr::Binary {
                        op: BinOp::Eq,
                        lhs: Box::new(s1_expr),
                        rhs: Box::new(crate::ivl::IvlExpr::IntConst(i64::MIN)),
                    }),
                    rhs: Box::new(crate::ivl::IvlExpr::Binary {
                        op: BinOp::Eq,
                        lhs: Box::new(s2_expr),
                        rhs: Box::new(crate::ivl::IvlExpr::IntConst(-1)),
                    }),
                };
                let safe_div = crate::ivl::IvlExpr::Binary {
                    op: BinOp::And,
                    lhs: Box::new(div_zero),
                    rhs: Box::new(crate::ivl::IvlExpr::Not(Box::new(overflow_cond))),
                };
                stmts.push(crate::ivl::IvlStmt::Assert {
                    cond: safe_div,
                    goal_name: format!("Function '{}' - Line {}: Division-by-Zero safety and Overflow check", func.name, s_inst.loc.line),
                    category: PropertyCategory::Safety,
                    loc: s_inst.loc.clone(),
                });
                stmts.extend(crate::ivl::IvlLowerer::lower_inst(s_inst, buffer_sizes, Some(buffer_aliases)));
            }
            Instruction::Load8 { buf, offset, .. } | Instruction::Store8 { buf, offset, .. } => {
                let actual_buf = buffer_aliases.get(buf).unwrap_or(buf);
                if let Some(&sz) = buffer_sizes.get(actual_buf).or_else(|| buffer_sizes.get(buf)) {
                    let off_expr = crate::ivl::IvlLowerer::operand_to_expr(offset);
                    let in_bounds = crate::ivl::IvlExpr::Binary {
                        op: BinOp::And,
                        lhs: Box::new(crate::ivl::IvlExpr::Binary {
                            op: BinOp::Gte,
                            lhs: Box::new(off_expr.clone()),
                            rhs: Box::new(crate::ivl::IvlExpr::IntConst(0)),
                        }),
                        rhs: Box::new(crate::ivl::IvlExpr::Binary {
                            op: BinOp::Lt,
                            lhs: Box::new(off_expr),
                            rhs: Box::new(crate::ivl::IvlExpr::IntConst(sz as i64)),
                        }),
                    };
                    stmts.push(crate::ivl::IvlStmt::Assert {
                        cond: in_bounds,
                        goal_name: format!("Function '{}' - Line {}: Memory 8-bit bounds check on '{}'", func.name, s_inst.loc.line, buf),
                        category: PropertyCategory::Safety,
                        loc: s_inst.loc.clone(),
                    });
                }
                stmts.extend(crate::ivl::IvlLowerer::lower_inst(s_inst, buffer_sizes, Some(buffer_aliases)));
            }
            Instruction::Load64 { buf, offset, .. } | Instruction::Store64 { buf, offset, .. } => {
                let actual_buf = buffer_aliases.get(buf).unwrap_or(buf);
                if let Some(&sz) = buffer_sizes.get(actual_buf).or_else(|| buffer_sizes.get(buf)) {
                    let off_expr = crate::ivl::IvlLowerer::operand_to_expr(offset);
                    let max_off = (sz as i64) - 8;
                    let in_bounds = if sz < 8 {
                        crate::ivl::IvlExpr::BoolConst(false)
                    } else {
                        crate::ivl::IvlExpr::Binary {
                            op: BinOp::And,
                            lhs: Box::new(crate::ivl::IvlExpr::Binary {
                                op: BinOp::Gte,
                                lhs: Box::new(off_expr.clone()),
                                rhs: Box::new(crate::ivl::IvlExpr::IntConst(0)),
                            }),
                            rhs: Box::new(crate::ivl::IvlExpr::Binary {
                                op: BinOp::Lte,
                                lhs: Box::new(off_expr),
                                rhs: Box::new(crate::ivl::IvlExpr::IntConst(max_off)),
                            }),
                        }
                    };
                    stmts.push(crate::ivl::IvlStmt::Assert {
                        cond: in_bounds,
                        goal_name: format!("Function '{}' - Line {}: Memory 64-bit bounds check on '{}'", func.name, s_inst.loc.line, buf),
                        category: PropertyCategory::Safety,
                        loc: s_inst.loc.clone(),
                    });
                }
                stmts.extend(crate::ivl::IvlLowerer::lower_inst(s_inst, buffer_sizes, Some(buffer_aliases)));
            }
            Instruction::Call { dest, func_name, args } => {
                if let Some(prog) = program {
                    if let Some(callee) = prog.functions.iter().find(|f| &f.name == func_name) {
                        if args.len() != callee.params.len() {
                            stmts.push(crate::ivl::IvlStmt::Assert {
                                cond: crate::ivl::IvlExpr::BoolConst(false),
                                goal_name: format!("Function '{}' - Line {}: Call argument count mismatch for '{}' (expected {}, got {})", func.name, s_inst.loc.line, func_name, callee.params.len(), args.len()),
                                category: PropertyCategory::Safety,
                                loc: s_inst.loc.clone(),
                            });
                        }
                        for c_si in &callee.instructions {
                            if let Instruction::Require(req) = &c_si.inst {
                                let mut req_ivl = crate::ivl::IvlExpr::from(req);
                                for (i, p) in callee.params.iter().enumerate() {
                                    if i < args.len() {
                                        let arg_expr = crate::ivl::IvlLowerer::operand_to_expr(&args[i]);
                                        req_ivl = crate::ivl::IvlLowerer::subst_expr(&req_ivl, &p.name, &arg_expr);
                                    }
                                }
                                stmts.push(crate::ivl::IvlStmt::Assert {
                                    cond: req_ivl,
                                    goal_name: format!("Function '{}' - Line {}: Verify REQUIRE contract of '{}'", func.name, s_inst.loc.line, func_name),
                                    category: PropertyCategory::Safety,
                                    loc: s_inst.loc.clone(),
                                });
                            }
                        }
                        if let Some(d) = dest {
                            stmts.push(crate::ivl::IvlStmt::Havoc {
                                vars: vec![d.clone()],
                                is_memory: false,
                            });
                            let callee_ret = Self::find_canonical_ret_var(callee).unwrap_or_else(|| "ret".to_string());
                            for c_si in &callee.instructions {
                                if let Instruction::Ensure(ens) = &c_si.inst {
                                    let mut ens_ivl = crate::ivl::IvlExpr::from(ens);
                                    for (i, p) in callee.params.iter().enumerate() {
                                        if i < args.len() {
                                            let arg_expr = crate::ivl::IvlLowerer::operand_to_expr(&args[i]);
                                            ens_ivl = crate::ivl::IvlLowerer::subst_expr(&ens_ivl, &p.name, &arg_expr);
                                        }
                                    }
                                    let d_expr = crate::ivl::IvlExpr::Var(d.trim_start_matches('%').to_string());
                                    ens_ivl = crate::ivl::IvlLowerer::subst_expr(&ens_ivl, &callee_ret, &d_expr);
                                    stmts.push(crate::ivl::IvlStmt::Assume { cond: ens_ivl });
                                }
                            }
                        }
                    } else {
                        stmts.push(crate::ivl::IvlStmt::Assert {
                            cond: crate::ivl::IvlExpr::BoolConst(false),
                            goal_name: format!("Function '{}' - Line {}: Call to undefined function '{}'", func.name, s_inst.loc.line, func_name),
                            category: PropertyCategory::Safety,
                            loc: s_inst.loc.clone(),
                        });
                    }
                }
            }
            _ => {
                stmts.extend(crate::ivl::IvlLowerer::lower_inst(s_inst, buffer_sizes, Some(buffer_aliases)));
            }
        }
        stmts
    }

    /// Hạ cấp một lát cắt lệnh sang chuỗi IVL kèm đầy đủ các kiểm chứng an toàn và xử lý rẽ nhánh BR_IF / LABEL
    fn lower_slice(
        func: &Function,
        slice: &[SpannedInstruction],
        buffer_sizes: &std::collections::HashMap<String, usize>,
        buffer_aliases: &std::collections::HashMap<String, String>,
        program: Option<&Program>,
        vc: &mut crate::vcgen::VcGen,
        results: &mut Vec<VerificationResult>,
        ensures: &[Expr],
        canon_ret: &str,
        has_loop: bool,
    ) -> Vec<crate::ivl::IvlStmt> {
        let mut stmts = Vec::new();
        let has_branch = slice.iter().any(|s| matches!(s.inst, Instruction::BrIf { .. } | Instruction::RetIf { .. }));
        let mut idx = 0;
        while idx < slice.len() {
            let s_inst = &slice[idx];
            match &s_inst.inst {
                Instruction::Require(req) => {
                    stmts.push(crate::ivl::IvlStmt::Assume {
                        cond: crate::ivl::IvlExpr::from(req),
                    });
                }
                Instruction::Ensure(_) | Instruction::Invariant(_) | Instruction::Decreases(_) => {}
                Instruction::Label(_) | Instruction::Jump(_) => {}
                Instruction::BrIf { cond, target } => {
                    let cond_clean = cond.trim_start_matches('%').to_string();
                    let cond_expr = crate::ivl::IvlExpr::Var(cond_clean.clone());

                    let tgt_pos = slice[idx + 1..]
                        .iter()
                        .position(|s| match &s.inst {
                            Instruction::Label(l) => l == target,
                            _ => false,
                        })
                        .map(|p| idx + 1 + p);

                    if let Some(tgt_idx) = tgt_pos {
                        let is_diamond = if tgt_idx > idx + 1 {
                            match &slice[tgt_idx - 1].inst {
                                Instruction::Jump(join_target) => {
                                    slice[tgt_idx + 1..]
                                        .iter()
                                        .position(|s| match &s.inst {
                                            Instruction::Label(l) => l == join_target,
                                            _ => false,
                                        })
                                        .map(|p| (tgt_idx + 1 + p, join_target.clone()))
                                }
                                _ => None,
                            }
                        } else {
                            None
                        };

                        if let Some((join_idx, _join_target)) = is_diamond {
                            let else_slice = &slice[idx + 1 .. tgt_idx - 1];
                            let then_slice = &slice[tgt_idx + 1 .. join_idx];

                            let else_mod = crate::ivl::IvlLowerer::collect_modified_vars(else_slice);
                            let then_mod = crate::ivl::IvlLowerer::collect_modified_vars(then_slice);
                            let all_mod: std::collections::HashSet<String> = else_mod.union(&then_mod).cloned().collect();

                            let else_mems = crate::ivl::IvlLowerer::collect_modified_mems(else_slice, Some(buffer_aliases));
                            let then_mems = crate::ivl::IvlLowerer::collect_modified_mems(then_slice, Some(buffer_aliases));
                            let all_mems: std::collections::HashSet<String> = else_mems.union(&then_mems).cloned().collect();

                            let branch_id = idx;

                            // Hạ cấp nhánh Else: các biến bị gán được chuyển hướng sang {m}_belse_{branch_id}
                            let mut else_stmts = Vec::new();
                            let mut else_map: std::collections::HashMap<String, String> = std::collections::HashMap::new();
                            for s in else_slice {
                                let mut lowered = Self::lower_inst_with_checks(func, s, buffer_sizes, buffer_aliases, program);
                                for st in &mut lowered {
                                    match st {
                                        crate::ivl::IvlStmt::Assign { dest, expr, is_memory } => {
                                            for (from, to) in &else_map {
                                                *expr = crate::ivl::IvlLowerer::subst_expr(expr, from, &crate::ivl::IvlExpr::Var(to.clone()));
                                            }
                                            let clean = dest.trim_start_matches('%').to_string();
                                            if *is_memory {
                                                if all_mems.contains(&clean) {
                                                    let target_mem = format!("{}_belse_{}", clean, branch_id);
                                                    else_map.insert(clean, target_mem.clone());
                                                    *dest = target_mem;
                                                }
                                            } else if all_mod.contains(&clean) {
                                                let target_var = format!("{}_belse_{}", clean, branch_id);
                                                else_map.insert(clean, target_var.clone());
                                                *dest = target_var;
                                            }
                                        }
                                        crate::ivl::IvlStmt::Assert { cond, .. } => {
                                            for (from, to) in &else_map {
                                                *cond = crate::ivl::IvlLowerer::subst_expr(cond, from, &crate::ivl::IvlExpr::Var(to.clone()));
                                            }
                                            *cond = crate::ivl::IvlExpr::Binary {
                                                op: BinOp::Or,
                                                lhs: Box::new(cond_expr.clone()),
                                                rhs: Box::new(cond.clone()),
                                            };
                                        }
                                        crate::ivl::IvlStmt::Assume { cond } => {
                                            for (from, to) in &else_map {
                                                *cond = crate::ivl::IvlLowerer::subst_expr(cond, from, &crate::ivl::IvlExpr::Var(to.clone()));
                                            }
                                            // Gác điều kiện rẽ nhánh: !cond_expr => cond <=> cond_expr || cond
                                            *cond = crate::ivl::IvlExpr::Binary {
                                                op: BinOp::Or,
                                                lhs: Box::new(cond_expr.clone()),
                                                rhs: Box::new(cond.clone()),
                                            };
                                        }
                                        crate::ivl::IvlStmt::Havoc { vars, is_memory } => {
                                            for v in vars.iter_mut() {
                                                let clean = v.trim_start_matches('%').to_string();
                                                if !*is_memory && all_mod.contains(&clean) {
                                                    let target_var = format!("{}_belse_{}", clean, branch_id);
                                                    else_map.insert(clean, target_var.clone());
                                                    *v = target_var;
                                                } else if *is_memory && all_mems.contains(&clean) {
                                                    let target_mem = format!("{}_belse_{}", clean, branch_id);
                                                    else_map.insert(clean, target_mem.clone());
                                                    *v = target_mem;
                                                }
                                            }
                                        }
                                        _ => {}
                                    }
                                }
                                else_stmts.extend(lowered);
                            }

                            // Hạ cấp nhánh Then: các biến bị gán được chuyển hướng sang {m}_bthen_{branch_id}
                            let mut then_stmts = Vec::new();
                            let mut then_map: std::collections::HashMap<String, String> = std::collections::HashMap::new();
                            for s in then_slice {
                                let mut lowered = Self::lower_inst_with_checks(func, s, buffer_sizes, buffer_aliases, program);
                                for st in &mut lowered {
                                    match st {
                                        crate::ivl::IvlStmt::Assign { dest, expr, is_memory } => {
                                            for (from, to) in &then_map {
                                                *expr = crate::ivl::IvlLowerer::subst_expr(expr, from, &crate::ivl::IvlExpr::Var(to.clone()));
                                            }
                                            let clean = dest.trim_start_matches('%').to_string();
                                            if *is_memory {
                                                if all_mems.contains(&clean) {
                                                    let target_mem = format!("{}_bthen_{}", clean, branch_id);
                                                    then_map.insert(clean, target_mem.clone());
                                                    *dest = target_mem;
                                                }
                                            } else if all_mod.contains(&clean) {
                                                let target_var = format!("{}_bthen_{}", clean, branch_id);
                                                then_map.insert(clean, target_var.clone());
                                                *dest = target_var;
                                            }
                                        }
                                        crate::ivl::IvlStmt::Assert { cond, .. } => {
                                            for (from, to) in &then_map {
                                                *cond = crate::ivl::IvlLowerer::subst_expr(cond, from, &crate::ivl::IvlExpr::Var(to.clone()));
                                            }
                                            *cond = crate::ivl::IvlExpr::Binary {
                                                op: BinOp::Or,
                                                lhs: Box::new(crate::ivl::IvlExpr::Not(Box::new(cond_expr.clone()))),
                                                rhs: Box::new(cond.clone()),
                                            };
                                        }
                                        crate::ivl::IvlStmt::Assume { cond } => {
                                            for (from, to) in &then_map {
                                                *cond = crate::ivl::IvlLowerer::subst_expr(cond, from, &crate::ivl::IvlExpr::Var(to.clone()));
                                            }
                                            // Gác điều kiện rẽ nhánh: cond_expr => cond <=> !cond_expr || cond
                                            *cond = crate::ivl::IvlExpr::Binary {
                                                op: BinOp::Or,
                                                lhs: Box::new(crate::ivl::IvlExpr::Not(Box::new(cond_expr.clone()))),
                                                rhs: Box::new(cond.clone()),
                                            };
                                        }
                                        crate::ivl::IvlStmt::Havoc { vars, is_memory } => {
                                            for v in vars.iter_mut() {
                                                let clean = v.trim_start_matches('%').to_string();
                                                if !*is_memory && all_mod.contains(&clean) {
                                                    let target_var = format!("{}_bthen_{}", clean, branch_id);
                                                    then_map.insert(clean, target_var.clone());
                                                    *v = target_var;
                                                } else if *is_memory && all_mems.contains(&clean) {
                                                    let target_mem = format!("{}_bthen_{}", clean, branch_id);
                                                    then_map.insert(clean, target_mem.clone());
                                                    *v = target_mem;
                                                }
                                            }
                                        }
                                        _ => {}
                                    }
                                }
                                then_stmts.extend(lowered);
                            }

                            stmts.extend(else_stmts);
                            stmts.extend(then_stmts);

                            // Tại điểm hội tụ .join: gán Phi-node ite(cond, then_val, else_val) cho từng biến
                            for m in &all_mod {
                                let clean_m = m.trim_start_matches('%');
                                let then_target = format!("{}_bthen_{}", clean_m, branch_id);
                                let else_target = format!("{}_belse_{}", clean_m, branch_id);

                                let then_expr = if then_mod.contains(clean_m) {
                                    crate::ivl::IvlExpr::Var(then_target)
                                } else {
                                    crate::ivl::IvlExpr::Var(clean_m.to_string())
                                };

                                let else_expr = if else_mod.contains(clean_m) {
                                    crate::ivl::IvlExpr::Var(else_target)
                                } else {
                                    crate::ivl::IvlExpr::Var(clean_m.to_string())
                                };

                                stmts.push(crate::ivl::IvlStmt::Assign {
                                    dest: clean_m.to_string(),
                                    expr: crate::ivl::IvlExpr::Ite {
                                        cond: Box::new(cond_expr.clone()),
                                        then_val: Box::new(then_expr),
                                        else_val: Box::new(else_expr),
                                    },
                                    is_memory: false,
                                });
                            }

                            // Hợp nhất Phi-node cho cả các vùng nhớ (Memory Arrays)
                            for m in &all_mems {
                                let clean_m = m.trim_start_matches('%');
                                let then_target = format!("{}_bthen_{}", clean_m, branch_id);
                                let else_target = format!("{}_belse_{}", clean_m, branch_id);

                                let then_expr = if then_mems.contains(clean_m) {
                                    crate::ivl::IvlExpr::Var(then_target)
                                } else {
                                    crate::ivl::IvlExpr::Var(clean_m.to_string())
                                };

                                let else_expr = if else_mems.contains(clean_m) {
                                    crate::ivl::IvlExpr::Var(else_target)
                                } else {
                                    crate::ivl::IvlExpr::Var(clean_m.to_string())
                                };

                                stmts.push(crate::ivl::IvlStmt::Assign {
                                    dest: clean_m.to_string(),
                                    expr: crate::ivl::IvlExpr::Ite {
                                        cond: Box::new(cond_expr.clone()),
                                        then_val: Box::new(then_expr),
                                        else_val: Box::new(else_expr),
                                    },
                                    is_memory: true,
                                });
                            }

                            idx = join_idx + 1;
                            continue;
                        }

                        let else_ret = slice[idx + 1 .. tgt_idx]
                            .iter()
                            .enumerate()
                            .find_map(|(pos, s)| match &s.inst {
                                Instruction::Ret(op) => Some((idx + 1 + pos, op.clone())),
                                _ => None,
                            });

                        if let Some((ret_idx, ret_op)) = else_ret {
                            results.extend(vc.verify_sequence(&stmts, &func.name, &func.file));
                            stmts.clear();

                            let else_slice = &slice[idx + 1 .. ret_idx];
                            let mut else_stmts = Vec::new();
                            else_stmts.push(crate::ivl::IvlStmt::Assume {
                                cond: crate::ivl::IvlExpr::Not(Box::new(cond_expr.clone())),
                            });
                            for s in else_slice {
                                else_stmts.extend(Self::lower_inst_with_checks(func, s, buffer_sizes, buffer_aliases, program));
                            }
                            if let Some(op) = &ret_op {
                                let op_expr = crate::ivl::IvlLowerer::operand_to_expr(op);
                                else_stmts.push(crate::ivl::IvlStmt::Assign {
                                    dest: canon_ret.to_string(),
                                    expr: op_expr,
                                    is_memory: false,
                                });
                            }
                            for ens in ensures {
                                let ens_ivl = crate::ivl::IvlExpr::from(ens);
                                else_stmts.push(crate::ivl::IvlStmt::Assert {
                                    cond: ens_ivl,
                                    goal_name: format!("Function '{}' - Line {}: Verify ENSURE on branch return (RET)", func.name, slice[ret_idx].loc.line),
                                    category: PropertyCategory::Functional,
                                    loc: slice[ret_idx].loc.clone(),
                                });
                            }

                            let mut vc_else = vc.clone();
                            results.extend(vc_else.verify_sequence(&else_stmts, &func.name, &func.file));

                            stmts.push(crate::ivl::IvlStmt::Assume {
                                cond: cond_expr,
                            });

                            idx = tgt_idx + 1;
                            continue;
                        }
                    }

                    // Nhảy về phía trước ra ngoài slice hiện tại: để tiếp tục đi thẳng, nhánh không được nhảy (!cond)
                    stmts.push(crate::ivl::IvlStmt::Assume {
                        cond: crate::ivl::IvlExpr::Not(Box::new(cond_expr)),
                    });
                }
                Instruction::RetIf { cond, val } => {
                    let cond_expr = crate::ivl::IvlExpr::Var(cond.trim_start_matches('%').to_string());
                    if let Some(op) = val {
                        let op_expr = crate::ivl::IvlLowerer::operand_to_expr(op);
                        for ens in ensures {
                            let ens_ivl = crate::ivl::IvlExpr::from(ens);
                            let mapped_ens = crate::ivl::IvlLowerer::subst_expr(&ens_ivl, canon_ret, &op_expr);
                            let imp = crate::ivl::IvlExpr::Binary {
                                op: BinOp::Or,
                                lhs: Box::new(crate::ivl::IvlExpr::Not(Box::new(cond_expr.clone()))),
                                rhs: Box::new(mapped_ens),
                            };
                            stmts.push(crate::ivl::IvlStmt::Assert {
                                cond: imp,
                                goal_name: format!("Function '{}' - Line {}: Verify ENSURE on early return (RET_IF)", func.name, s_inst.loc.line),
                                category: PropertyCategory::Functional,
                                loc: s_inst.loc.clone(),
                            });
                        }
                    }
                    stmts.push(crate::ivl::IvlStmt::Assume {
                        cond: crate::ivl::IvlExpr::Not(Box::new(cond_expr)),
                    });
                }
                Instruction::Ret(Some(op)) => {
                    let op_expr = crate::ivl::IvlLowerer::operand_to_expr(op);
                    stmts.push(crate::ivl::IvlStmt::Assign {
                        dest: canon_ret.to_string(),
                        expr: op_expr,
                        is_memory: false,
                    });
                    for ens in ensures {
                        let ens_ivl = crate::ivl::IvlExpr::from(ens);
                        let goal_name = if has_loop {
                            format!("Function '{}' - Step 3: Exit Step (ENSURE postcondition satisfaction)", func.name)
                        } else if has_branch {
                            format!("Function '{}' - Line {}: Verify ENSURE on branch return (RET) - Verify ENSURE postcondition", func.name, s_inst.loc.line)
                        } else {
                            format!("Function '{}' - Verify ENSURE postcondition", func.name)
                        };
                        stmts.push(crate::ivl::IvlStmt::Assert {
                            cond: ens_ivl,
                            goal_name,
                            category: PropertyCategory::Functional,
                            loc: s_inst.loc.clone(),
                        });
                    }
                }
                Instruction::Ret(None) => {
                    for ens in ensures {
                        let ens_ivl = crate::ivl::IvlExpr::from(ens);
                        let goal_name = if has_loop {
                            format!("Function '{}' - Step 3: Exit Step (ENSURE postcondition satisfaction)", func.name)
                        } else if has_branch {
                            format!("Function '{}' - Line {}: Verify ENSURE on branch return (RET) - Verify ENSURE postcondition", func.name, s_inst.loc.line)
                        } else {
                            format!("Function '{}' - Verify ENSURE postcondition", func.name)
                        };
                        stmts.push(crate::ivl::IvlStmt::Assert {
                            cond: ens_ivl,
                            goal_name,
                            category: PropertyCategory::Functional,
                            loc: s_inst.loc.clone(),
                        });
                    }
                }
                Instruction::Loop(_) => {
                    let mut depth = 1;
                    let mut l_end_opt = None;
                    for (p, s) in slice[idx + 1..].iter().enumerate() {
                        match &s.inst {
                            Instruction::Loop(_) => depth += 1,
                            Instruction::EndLoop(_) => {
                                depth -= 1;
                                if depth == 0 {
                                    l_end_opt = Some(idx + 1 + p);
                                    break;
                                }
                            }
                            _ => {}
                        }
                    }

                    let l_end = l_end_opt.unwrap_or(slice.len() - 1);
                    let body_slice = &slice[idx + 1 .. l_end];

                    if body_slice.iter().any(|si| matches!(si.inst, Instruction::Syscall { .. })) {
                        results.push(VerificationResult::Unknown {
                            goal_name: format!("Function '{}' - Symbolic Loop Execution - Step 2: Inductive Step (Invariant preservation)", func.name),
                            category: PropertyCategory::Inductive,
                            reason: "Unsupported instruction inside loop body: SYSCALL".into(),
                            stack_trace: vec![StackFrame {
                                file: func.file.clone(),
                                line: slice[idx].loc.line,
                                function: func.name.clone(),
                                snippet: slice[idx].loc.text.clone(),
                                role: "Unsupported instruction inside loop body: SYSCALL".into(),
                            }],
                        });
                        return stmts;
                    }

                    let mut loop_invs = Vec::new();
                    let mut loop_decs = Vec::new();
                    let mut break_points = Vec::new();
                    let mut inner_depth = 0usize;

                    for (pos, b_si) in body_slice.iter().enumerate() {
                        match &b_si.inst {
                            Instruction::Loop(_) => inner_depth += 1,
                            Instruction::EndLoop(_) => inner_depth = inner_depth.saturating_sub(1),
                            Instruction::Invariant(e) if inner_depth == 0 => loop_invs.push(crate::ivl::IvlExpr::from(e)),
                            Instruction::Decreases(e) if inner_depth == 0 => loop_decs.push(crate::ivl::IvlExpr::from(e)),
                            Instruction::BreakIf(c) if inner_depth == 0 => {
                                break_points.push((idx + 1 + pos, crate::ivl::IvlExpr::Var(c.trim_start_matches('%').to_string())));
                            }
                            _ => {}
                        }
                    }

                    // Step 1: Base Case
                    for inv in &loop_invs {
                        stmts.push(crate::ivl::IvlStmt::Assert {
                            cond: inv.clone(),
                            goal_name: format!("Function '{}' - Step 1: Base Case (Loop initialization)", func.name),
                            category: PropertyCategory::Inductive,
                            loc: slice[idx].loc.clone(),
                        });
                    }

                    results.extend(vc.verify_sequence(&stmts, &func.name, &func.file));
                    stmts.clear();

                    let modified: Vec<String> = crate::ivl::IvlLowerer::collect_modified_vars(body_slice).into_iter().collect();
                    let modified_mems: Vec<String> = crate::ivl::IvlLowerer::collect_modified_mems(body_slice, Some(buffer_aliases)).into_iter().collect();

                    // Step 2 & Step 4: Symbolic Loop Execution & Safety Verification
                    {
                        let mut ind_stmts = Vec::new();
                        ind_stmts.push(crate::ivl::IvlStmt::Havoc {
                            vars: modified.clone(),
                            is_memory: false,
                        });
                        if !modified_mems.is_empty() {
                            ind_stmts.push(crate::ivl::IvlStmt::Havoc {
                                vars: modified_mems.clone(),
                                is_memory: true,
                            });
                        }
                        for inv in &loop_invs {
                            ind_stmts.push(crate::ivl::IvlStmt::Assume { cond: inv.clone() });
                        }
                        for (d_idx, dec) in loop_decs.iter().enumerate() {
                            ind_stmts.push(crate::ivl::IvlStmt::Assign {
                                dest: format!("__rank_init_{}", d_idx),
                                expr: dec.clone(),
                                is_memory: false,
                            });
                        }
                        let mut vc_ind = vc.clone();
                        let mut cur_pos = idx + 1;
                        for (b_pos, b_expr) in &break_points {
                            ind_stmts.extend(Self::lower_slice(func, &slice[cur_pos .. *b_pos], buffer_sizes, buffer_aliases, program, &mut vc_ind, results, ensures, canon_ret, true));
                            ind_stmts.push(crate::ivl::IvlStmt::Assume {
                                cond: crate::ivl::IvlExpr::Not(Box::new(b_expr.clone())),
                            });
                            cur_pos = b_pos + 1;
                        }
                        ind_stmts.extend(Self::lower_slice(func, &slice[cur_pos .. l_end], buffer_sizes, buffer_aliases, program, &mut vc_ind, results, ensures, canon_ret, true));

                        for inv in &loop_invs {
                            ind_stmts.push(crate::ivl::IvlStmt::Assert {
                                cond: inv.clone(),
                                goal_name: format!("Function '{}' - Symbolic Loop Execution - Step 2: Inductive Step (Invariant preservation)", func.name),
                                category: PropertyCategory::Inductive,
                                loc: slice[idx].loc.clone(),
                            });
                        }
                        for (d_idx, dec) in loop_decs.iter().enumerate() {
                            let old_r = crate::ivl::IvlExpr::Var(format!("__rank_init_{}", d_idx));
                            ind_stmts.push(crate::ivl::IvlStmt::Assert {
                                cond: crate::ivl::IvlExpr::Binary {
                                    op: BinOp::Gte,
                                    lhs: Box::new(old_r.clone()),
                                    rhs: Box::new(crate::ivl::IvlExpr::IntConst(0)),
                                },
                                goal_name: format!("Function '{}' - Step 4a: Termination Step (DECREASES bounded below >= 0)", func.name),
                                category: PropertyCategory::Termination,
                                loc: slice[idx].loc.clone(),
                            });
                            ind_stmts.push(crate::ivl::IvlStmt::Assert {
                                cond: crate::ivl::IvlExpr::Binary {
                                    op: BinOp::Lt,
                                    lhs: Box::new(dec.clone()),
                                    rhs: Box::new(old_r),
                                },
                                goal_name: format!("Function '{}' - Step 4b: Termination Step (DECREASES ranking function strictly decreases)", func.name),
                                category: PropertyCategory::Termination,
                                loc: slice[idx].loc.clone(),
                            });
                        }
                        results.extend(vc_ind.verify_sequence(&ind_stmts, &func.name, &func.file));
                    }

                    // Exit path (Step 3)
                    stmts.push(crate::ivl::IvlStmt::Havoc {
                        vars: modified.clone(),
                        is_memory: false,
                    });
                    if !modified_mems.is_empty() {
                        stmts.push(crate::ivl::IvlStmt::Havoc {
                            vars: modified_mems.clone(),
                            is_memory: true,
                        });
                    }
                    for inv in &loop_invs {
                        stmts.push(crate::ivl::IvlStmt::Assume { cond: inv.clone() });
                    }

                    if break_points.len() <= 1 {
                        let (body_before, first_brk_expr) = if let Some((b_idx, brk)) = break_points.first() {
                            (&slice[idx + 1 .. *b_idx], Some(brk.clone()))
                        } else {
                            (body_slice, None)
                        };
                        stmts.extend(Self::lower_slice(func, body_before, buffer_sizes, buffer_aliases, program, vc, results, ensures, canon_ret, true));
                        if let Some(brk) = first_brk_expr {
                            stmts.push(crate::ivl::IvlStmt::Assume { cond: brk });
                        }
                    } else {
                        // Multi-break Ite Merging: Hạ cấp từng đoạn giữa các điểm BREAK_IF và hợp nhất trạng thái bằng Ite
                        let first_b_idx = break_points[0].0;
                        stmts.extend(Self::lower_slice(func, &slice[idx + 1 .. first_b_idx], buffer_sizes, buffer_aliases, program, vc, results, ensures, canon_ret, true));

                        let mut accum_exit_cond = break_points[0].1.clone();
                        let mut prev_b_idx = first_b_idx;

                        for (j, (b_idx, brk_expr)) in break_points.iter().enumerate().skip(1) {
                            let seg_slice = &slice[prev_b_idx + 1 .. *b_idx];
                            let seg_mod = crate::ivl::IvlLowerer::collect_modified_vars(seg_slice);
                            let seg_mems = crate::ivl::IvlLowerer::collect_modified_mems(seg_slice, Some(buffer_aliases));

                            let mut seg_map: std::collections::HashMap<String, String> = std::collections::HashMap::new();
                            let mut lowered = Self::lower_slice(func, seg_slice, buffer_sizes, buffer_aliases, program, vc, results, ensures, canon_ret, true);
                            for st in &mut lowered {
                                match st {
                                    crate::ivl::IvlStmt::Assign { dest, expr, is_memory } => {
                                        for (from, to) in &seg_map {
                                            *expr = crate::ivl::IvlLowerer::subst_expr(expr, from, &crate::ivl::IvlExpr::Var(to.clone()));
                                        }
                                        let clean = dest.trim_start_matches('%').to_string();
                                        if *is_memory {
                                            if seg_mems.contains(&clean) {
                                                let target_mem = format!("{}_mb_{}", clean, j);
                                                seg_map.insert(clean, target_mem.clone());
                                                *dest = target_mem;
                                            }
                                        } else if seg_mod.contains(&clean) {
                                            let target_var = format!("{}_mb_{}", clean, j);
                                            seg_map.insert(clean, target_var.clone());
                                            *dest = target_var;
                                        }
                                    }
                                    crate::ivl::IvlStmt::Assert { cond, .. } => {
                                        for (from, to) in &seg_map {
                                            *cond = crate::ivl::IvlLowerer::subst_expr(cond, from, &crate::ivl::IvlExpr::Var(to.clone()));
                                        }
                                        *cond = crate::ivl::IvlExpr::Binary {
                                            op: BinOp::Or,
                                            lhs: Box::new(accum_exit_cond.clone()),
                                            rhs: Box::new(cond.clone()),
                                        };
                                    }
                                    crate::ivl::IvlStmt::Assume { cond } => {
                                        for (from, to) in &seg_map {
                                            *cond = crate::ivl::IvlLowerer::subst_expr(cond, from, &crate::ivl::IvlExpr::Var(to.clone()));
                                        }
                                        *cond = crate::ivl::IvlExpr::Binary {
                                            op: BinOp::Or,
                                            lhs: Box::new(accum_exit_cond.clone()),
                                            rhs: Box::new(cond.clone()),
                                        };
                                    }
                                    crate::ivl::IvlStmt::Havoc { vars, is_memory } => {
                                        for v in vars.iter_mut() {
                                            let clean = v.trim_start_matches('%').to_string();
                                            if !*is_memory && seg_mod.contains(&clean) {
                                                let target_var = format!("{}_mb_{}", clean, j);
                                                seg_map.insert(clean, target_var.clone());
                                                *v = target_var;
                                            } else if *is_memory && seg_mems.contains(&clean) {
                                                let target_mem = format!("{}_mb_{}", clean, j);
                                                seg_map.insert(clean, target_mem.clone());
                                                *v = target_mem;
                                            }
                                        }
                                    }
                                    _ => {}
                                }
                            }
                            stmts.extend(lowered);

                            for m in &seg_mod {
                                let mb_target = seg_map.get(m).cloned().unwrap_or_else(|| m.clone());
                                stmts.push(crate::ivl::IvlStmt::Assign {
                                    dest: m.clone(),
                                    expr: crate::ivl::IvlExpr::Ite {
                                        cond: Box::new(accum_exit_cond.clone()),
                                        then_val: Box::new(crate::ivl::IvlExpr::Var(m.clone())),
                                        else_val: Box::new(crate::ivl::IvlExpr::Var(mb_target)),
                                    },
                                    is_memory: false,
                                });
                            }
                            for mem in &seg_mems {
                                let mb_target = seg_map.get(mem).cloned().unwrap_or_else(|| mem.clone());
                                stmts.push(crate::ivl::IvlStmt::Assign {
                                    dest: mem.clone(),
                                    expr: crate::ivl::IvlExpr::Ite {
                                        cond: Box::new(accum_exit_cond.clone()),
                                        then_val: Box::new(crate::ivl::IvlExpr::Var(mem.clone())),
                                        else_val: Box::new(crate::ivl::IvlExpr::Var(mb_target)),
                                    },
                                    is_memory: true,
                                });
                            }

                            let mut brk_subst = brk_expr.clone();
                            for (from, to) in &seg_map {
                                brk_subst = crate::ivl::IvlLowerer::subst_expr(&brk_subst, from, &crate::ivl::IvlExpr::Var(to.clone()));
                            }

                            accum_exit_cond = crate::ivl::IvlExpr::Binary {
                                op: BinOp::Or,
                                lhs: Box::new(accum_exit_cond),
                                rhs: Box::new(brk_subst),
                            };
                            prev_b_idx = *b_idx;
                        }
                        stmts.push(crate::ivl::IvlStmt::Assume { cond: accum_exit_cond });
                    }

                    idx = l_end + 1;
                    continue;
                }
                Instruction::EndLoop(_) => {}
                _other => {
                    stmts.extend(Self::lower_inst_with_checks(func, s_inst, buffer_sizes, buffer_aliases, program));
                }
            }
            idx += 1;
        }
        stmts
    }

    /// Kiểm tra tính đúng đắn toán học bằng kiến trúc Boogie IVL Engine (Universal VCGen)
    pub fn verify_function(func: &Function, program: Option<&Program>) -> Vec<VerificationResult> {
        let mut results = Vec::new();

        // 0. Static Well-Formedness: SSA Definite Assignment Check (No Undefined Variables)
        let mut defined_vars = std::collections::HashSet::new();
        for p in &func.params {
            defined_vars.insert(p.name.trim_start_matches('%').to_string());
        }
        for s_inst in &func.instructions {
            let mut used_regs = Vec::new();
            match &s_inst.inst {
                Instruction::Mov { src, .. } => used_regs.push(src),
                Instruction::Not { src, .. } => {
                    if let Operand::Reg(r) = src { used_regs.push(r); }
                }
                Instruction::Binary { src1, src2, .. } => {
                    if let Operand::Reg(r) = src1 { used_regs.push(r); }
                    if let Operand::Reg(r) = src2 { used_regs.push(r); }
                }
                Instruction::Store8 { offset, val, .. } => {
                    if let Operand::Reg(r) = offset { used_regs.push(r); }
                    if let Operand::Reg(r) = val { used_regs.push(r); }
                }
                Instruction::Load8 { offset, .. } => {
                    if let Operand::Reg(r) = offset { used_regs.push(r); }
                }
                Instruction::Store64 { offset, val, .. } => {
                    if let Operand::Reg(r) = offset { used_regs.push(r); }
                    if let Operand::Reg(r) = val { used_regs.push(r); }
                }
                Instruction::Load64 { offset, .. } => {
                    if let Operand::Reg(r) = offset { used_regs.push(r); }
                }
                Instruction::BrIf { cond, .. } | Instruction::BreakIf(cond) | Instruction::ContinueIf(cond) => {
                    used_regs.push(cond);
                }
                Instruction::Ret(Some(Operand::Reg(r))) => used_regs.push(r),
                Instruction::RetIf { cond, val } => {
                    used_regs.push(cond);
                    if let Some(Operand::Reg(r)) = val { used_regs.push(r); }
                }
                Instruction::Call { args, .. } => {
                    for a in args {
                        if let Operand::Reg(r) = a {
                            used_regs.push(r);
                        }
                    }
                }
                Instruction::Syscall { rax, rdi, rsi, rdx, r10, r8, r9, .. } => {
                    if let Operand::Reg(r) = rax { used_regs.push(r); }
                    if let Operand::Reg(r) = rdi { used_regs.push(r); }
                    if let Operand::Reg(r) = rsi { used_regs.push(r); }
                    if let Operand::Reg(r) = rdx { used_regs.push(r); }
                    if let Some(Operand::Reg(r)) = r10 { used_regs.push(r); }
                    if let Some(Operand::Reg(r)) = r8 { used_regs.push(r); }
                    if let Some(Operand::Reg(r)) = r9 { used_regs.push(r); }
                }
                _ => {}
            }
            for u in used_regs {
                let clean = u.trim_start_matches('%');
                if !defined_vars.contains(clean) {
                    results.push(VerificationResult::Failed {
                        goal_name: format!("Function '{}' - Line {}: SSA Definite Assignment", func.name, s_inst.loc.line),
                        category: PropertyCategory::Safety,
                        reason: format!("Variable '%{}' used before definition!", clean),
                        counter_example: None,
                        stack_trace: vec![StackFrame {
                            file: func.file.clone(),
                            line: s_inst.loc.line,
                            function: func.name.clone(),
                            snippet: s_inst.loc.text.clone(),
                            role: format!("Use of undefined variable '%{}'", clean),
                        }],
                    });
                    return results;
                }
            }
            match &s_inst.inst {
                Instruction::AssignConst { dest, .. }
                | Instruction::Mov { dest, .. }
                | Instruction::Binary { dest, .. }
                | Instruction::Not { dest, .. }
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

        let buffer_sizes = crate::ivl::IvlLowerer::extract_buffer_sizes(func);
        let buffer_aliases = crate::ivl::IvlLowerer::extract_buffer_aliases(func);
        let mut stmts = Vec::new();

        // 1. Khởi tạo và khai báo các tham số đầu vào của hàm
        let mut vc = crate::vcgen::VcGen::new();
        let param_names: std::collections::HashSet<String> = func
            .params
            .iter()
            .map(|p| p.name.trim_start_matches('%').to_string())
            .collect();

        for p in &param_names {
            vc.declared_vars.insert(p.clone());
            vc.current_val.insert(p.clone(), p.clone());
            let plen = format!("{}_len", p);
            vc.declared_vars.insert(plen.clone());
            vc.current_val.insert(plen.clone(), plen);
        }

        let ensures: Vec<Expr> = func
            .instructions
            .iter()
            .filter_map(|si| if let Instruction::Ensure(e) = &si.inst { Some(e.clone()) } else { None })
            .collect();
        let canon_ret = Self::find_canonical_ret_var(func).unwrap_or_else(|| "ret".to_string());

        let has_ret = func.instructions.iter().any(|si| matches!(si.inst, Instruction::Ret(_) | Instruction::RetIf { .. }));
        if !ensures.is_empty() && !has_ret {
            results.push(VerificationResult::Failed {
                goal_name: format!("Function '{}' - Verify ENSURE postcondition", func.name),
                category: PropertyCategory::Functional,
                reason: format!("Function '{}' declares ENSURE contract but has no RET or RET_IF instruction!", func.name),
                counter_example: None,
                stack_trace: vec![StackFrame {
                    file: func.file.clone(),
                    line: func.instructions.last().map(|s| s.loc.line).unwrap_or(1),
                    function: func.name.clone(),
                    snippet: "Missing RET statement".to_string(),
                    role: "Missing RET for ENSURE postcondition".to_string(),
                }],
            });
            return results;
        }

        let has_loop = func.instructions.iter().any(|s| matches!(s.inst, Instruction::Loop(_)));
        let all_stmts = Self::lower_slice(func, &func.instructions, &buffer_sizes, &buffer_aliases, program, &mut vc, &mut results, &ensures, &canon_ret, has_loop);
        stmts.extend(all_stmts);
        results.extend(vc.verify_sequence(&stmts, &func.name, &func.file));

        results
    }

    /// Alias cho `verify_function` nhằm tương thích ngược với các test case
    #[allow(dead_code)]
    #[inline]
    pub fn verify_function_ivl(func: &Function, program: Option<&Program>) -> Vec<VerificationResult> {
        Self::verify_function(func, program)
    }

    /// Tìm tên biến đại diện cho giá trị trả về của hàm trong ENSURE
    pub fn find_canonical_ret_var(func: &Function) -> Option<String> {
        let mut ensure_vars = std::collections::HashSet::new();
        for si in &func.instructions {
            if let Instruction::Ensure(e) = &si.inst {
                Self::collect_vars(e, &mut ensure_vars);
            }
        }
        // Ưu tiên 1: Thanh ghi ở lệnh RET nào có xuất hiện trực tiếp trong ENSURE
        for s_inst in func.instructions.iter().rev() {
            if let Instruction::Ret(Some(Operand::Reg(r))) = &s_inst.inst {
                let clean = r.trim_start_matches('%');
                if ensure_vars.contains(clean) {
                    return Some(clean.to_string());
                }
            }
        }
        // Ưu tiên 2: Tìm biến trong ENSURE không phải là param của hàm (ví dụ "ret", "res", "result", v.v.)
        let param_names: std::collections::HashSet<String> = func
            .params
            .iter()
            .map(|p| p.name.trim_start_matches('%').to_string())
            .collect();
        for ev in &ensure_vars {
            if !param_names.contains(ev) && (ev == "ret" || ev == "res" || ev == "result") {
                return Some(ev.clone());
            }
        }
        for ev in &ensure_vars {
            if !param_names.contains(ev) {
                return Some(ev.clone());
            }
        }
        // Ưu tiên 3: Nếu ENSURE không có biến riêng, lấy thanh ghi ở lệnh RET cuối cùng
        for s_inst in func.instructions.iter().rev() {
            if let Instruction::Ret(Some(Operand::Reg(r))) = &s_inst.inst {
                return Some(r.trim_start_matches('%').to_string());
            }
        }
        None
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

    #[allow(dead_code)]
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
            Expr::Binary { op: BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod | BinOp::BitAnd | BinOp::BitOr | BinOp::Xor | BinOp::Shl | BinOp::Shr | BinOp::Sar, .. } => {
                format!("(distinct {} (_ bv0 64))", Self::expr_to_smt(expr))
            }
            _ => Self::expr_to_smt(expr),
        }
    }

    /// Chuyển đổi biểu thức Expr sang chuỗi logic SMT-LIB2 (Bit-Vector 64-bit)
    #[allow(dead_code)]
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
                    BinOp::BitAnd => format!("(bvand {} {})", s1, s2),
                    BinOp::BitOr => format!("(bvor {} {})", s1, s2),
                    BinOp::Xor => format!("(bvxor {} {})", s1, s2),
                    BinOp::Shl => format!("(bvshl {} (bvand {} (_ bv63 64)))", s1, s2),
                    BinOp::Shr => format!("(bvlshr {} (bvand {} (_ bv63 64)))", s1, s2),
                    BinOp::Sar => format!("(bvashr {} (bvand {} (_ bv63 64)))", s1, s2),
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

    #[allow(dead_code)]
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
                let len_key = format!("{}_len", clean);
                if let Some(len_repl) = map.get(&len_key) {
                    Expr::Var(len_repl.clone())
                } else if let Some(repl) = map.get(clean) {
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
        } else if first_token == "unknown" || first_token == "timeout" || stdout.contains("timeout") {
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
