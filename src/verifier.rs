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

#[derive(Clone)]
pub struct LoopContext<'a> {
    pub invariants: &'a [crate::ivl::IvlExpr],
    pub decreases: &'a [crate::ivl::IvlExpr],
    pub verify_inductive: bool,
    pub loop_id: usize,
}

pub struct Verifier;

impl Verifier {
    #[inline]
    fn is_true(e: &crate::ivl::IvlExpr) -> bool {
        matches!(e, crate::ivl::IvlExpr::BoolConst(true))
    }

    #[inline]
    fn is_false(e: &crate::ivl::IvlExpr) -> bool {
        matches!(e, crate::ivl::IvlExpr::BoolConst(false))
    }

    fn mk_not(e: crate::ivl::IvlExpr) -> crate::ivl::IvlExpr {
        match e {
            crate::ivl::IvlExpr::BoolConst(b) => crate::ivl::IvlExpr::BoolConst(!b),
            crate::ivl::IvlExpr::Not(inner) => *inner,
            other => crate::ivl::IvlExpr::Not(Box::new(other)),
        }
    }

    fn mk_and(a: crate::ivl::IvlExpr, b: crate::ivl::IvlExpr) -> crate::ivl::IvlExpr {
        if Self::is_false(&a) || Self::is_false(&b) {
            crate::ivl::IvlExpr::BoolConst(false)
        } else if Self::is_true(&a) {
            b
        } else if Self::is_true(&b) {
            a
        } else {
            crate::ivl::IvlExpr::Binary {
                op: BinOp::And,
                lhs: Box::new(a),
                rhs: Box::new(b),
                is_unsigned: false,
            }
        }
    }

    fn mk_or(a: crate::ivl::IvlExpr, b: crate::ivl::IvlExpr) -> crate::ivl::IvlExpr {
        if Self::is_true(&a) || Self::is_true(&b) {
            crate::ivl::IvlExpr::BoolConst(true)
        } else if Self::is_false(&a) {
            b
        } else if Self::is_false(&b) {
            a
        } else {
            crate::ivl::IvlExpr::Binary {
                op: BinOp::Or,
                lhs: Box::new(a),
                rhs: Box::new(b),
                is_unsigned: false,
            }
        }
    }

    /// Biểu thức kéo theo: `guard => prop` (tương đương `!guard || prop`)
    fn mk_implies(guard: &crate::ivl::IvlExpr, prop: crate::ivl::IvlExpr) -> crate::ivl::IvlExpr {
        if Self::is_true(guard) {
            prop
        } else if Self::is_false(guard) {
            crate::ivl::IvlExpr::BoolConst(true)
        } else {
            Self::mk_or(Self::mk_not(guard.clone()), prop)
        }
    }

    /// Bọc điều kiện luồng chạy `active` vào mọi vi lệnh IVL cơ bản (Assign, Assert, Assume, Havoc)
    fn guard_stmts(
        raw_stmts: Vec<crate::ivl::IvlStmt>,
        active: &crate::ivl::IvlExpr,
        havoc_counter: &mut usize,
    ) -> Vec<crate::ivl::IvlStmt> {
        if Self::is_false(active) {
            return Vec::new();
        }
        if Self::is_true(active) {
            return raw_stmts;
        }

        let mut out = Vec::new();
        for st in raw_stmts {
            match st {
                crate::ivl::IvlStmt::Assign { dest, expr, is_memory } => {
                    let clean = dest.trim_start_matches('%').to_string();
                    out.push(crate::ivl::IvlStmt::Assign {
                        dest: clean.clone(),
                        expr: crate::ivl::IvlExpr::Ite {
                            cond: Box::new(active.clone()),
                            then_val: Box::new(expr),
                            else_val: Box::new(crate::ivl::IvlExpr::Var(clean)),
                        },
                        is_memory,
                    });
                }
                crate::ivl::IvlStmt::Assert { cond, goal_name, category, loc } => {
                    out.push(crate::ivl::IvlStmt::Assert {
                        cond: Self::mk_implies(active, cond),
                        goal_name,
                        category,
                        loc,
                    });
                }
                crate::ivl::IvlStmt::Assume { cond } => {
                    out.push(crate::ivl::IvlStmt::Assume {
                        cond: Self::mk_implies(active, cond),
                    });
                }
                crate::ivl::IvlStmt::Havoc { vars, is_memory } => {
                    for v in vars {
                        *havoc_counter += 1;
                        let clean = v.trim_start_matches('%').to_string();
                        let tmp = format!("__guarded_havoc_{}_{}", clean, *havoc_counter);
                        out.push(crate::ivl::IvlStmt::Havoc {
                            vars: vec![tmp.clone()],
                            is_memory,
                        });
                        out.push(crate::ivl::IvlStmt::Assign {
                            dest: clean.clone(),
                            expr: crate::ivl::IvlExpr::Ite {
                                cond: Box::new(active.clone()),
                                then_val: Box::new(crate::ivl::IvlExpr::Var(tmp)),
                                else_val: Box::new(crate::ivl::IvlExpr::Var(clean)),
                            },
                            is_memory,
                        });
                    }
                }
                other => out.push(other),
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
            Instruction::Binary { op: BinOp::Div | BinOp::Mod, ty, src1, src2, .. } => {
                let s1_expr = crate::ivl::IvlLowerer::operand_to_expr(src1);
                let s2_expr = crate::ivl::IvlLowerer::operand_to_expr(src2);
                let is_unsigned = matches!(ty, Type::U64 | Type::U8);
                if is_unsigned {
                    let div_zero = crate::ivl::IvlExpr::Binary {
                        op: BinOp::Neq,
                        lhs: Box::new(s2_expr),
                        rhs: Box::new(crate::ivl::IvlExpr::IntConst(0)),
                        is_unsigned: true,
                    };
                    stmts.push(crate::ivl::IvlStmt::Assert {
                        cond: div_zero,
                        goal_name: format!("Function '{}' - Line {}: Unsigned Division-by-Zero safety check", func.name, s_inst.loc.line),
                        category: PropertyCategory::Safety,
                        loc: s_inst.loc.clone(),
                    });
                } else {
                    let div_zero = crate::ivl::IvlExpr::Binary {
                        op: BinOp::Neq,
                        lhs: Box::new(s2_expr.clone()),
                        rhs: Box::new(crate::ivl::IvlExpr::IntConst(0)),
                        is_unsigned: false,
                    };
                    let overflow_cond = crate::ivl::IvlExpr::Binary {
                        op: BinOp::And,
                        lhs: Box::new(crate::ivl::IvlExpr::Binary {
                            op: BinOp::Eq,
                            lhs: Box::new(s1_expr),
                            rhs: Box::new(crate::ivl::IvlExpr::IntConst(i64::MIN)),
                            is_unsigned: false,
                        }),
                        rhs: Box::new(crate::ivl::IvlExpr::Binary {
                            op: BinOp::Eq,
                            lhs: Box::new(s2_expr),
                            rhs: Box::new(crate::ivl::IvlExpr::IntConst(-1)),
                            is_unsigned: false,
                        }),
                        is_unsigned: false,
                    };
                    let safe_div = crate::ivl::IvlExpr::Binary {
                        op: BinOp::And,
                        lhs: Box::new(div_zero),
                        rhs: Box::new(crate::ivl::IvlExpr::Not(Box::new(overflow_cond))),
                        is_unsigned: false,
                    };
                    stmts.push(crate::ivl::IvlStmt::Assert {
                        cond: safe_div,
                        goal_name: format!("Function '{}' - Line {}: Division-by-Zero safety and Overflow check", func.name, s_inst.loc.line),
                        category: PropertyCategory::Safety,
                        loc: s_inst.loc.clone(),
                    });
                }
                stmts.extend(crate::ivl::IvlLowerer::lower_inst(s_inst, buffer_sizes, Some(buffer_aliases)));
            }
            Instruction::Load8 { buf, offset, .. } | Instruction::Store8 { buf, offset, .. } => {
                let actual_buf = buffer_aliases.get(buf).unwrap_or(buf);
                let clean_buf = actual_buf.trim_start_matches('%');
                let is_slice_param = func.params.iter().any(|p| {
                    p.name.trim_start_matches('%') == clean_buf
                        && matches!(p.ty, Type::Slice(_) | Type::Array(_, _))
                });

                let bound_expr_opt = if let Some(&sz) = buffer_sizes.get(actual_buf).or_else(|| buffer_sizes.get(buf)) {
                    Some(crate::ivl::IvlExpr::IntConst(sz as i64))
                } else if is_slice_param {
                    Some(crate::ivl::IvlExpr::Len(clean_buf.to_string()))
                } else {
                    None
                };

                if let Some(bound_expr) = bound_expr_opt {
                    let off_expr = crate::ivl::IvlLowerer::operand_to_expr(offset);
                    let in_bounds = crate::ivl::IvlExpr::Binary {
                        op: BinOp::And,
                        lhs: Box::new(crate::ivl::IvlExpr::Binary {
                            op: BinOp::Gte,
                            lhs: Box::new(off_expr.clone()),
                            rhs: Box::new(crate::ivl::IvlExpr::IntConst(0)),
                            is_unsigned: false,
                        }),
                        rhs: Box::new(crate::ivl::IvlExpr::Binary {
                            op: BinOp::Lt,
                            lhs: Box::new(off_expr),
                            rhs: Box::new(bound_expr),
                            is_unsigned: false,
                        }),
                        is_unsigned: false,
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
                let clean_buf = actual_buf.trim_start_matches('%');
                let is_slice_param = func.params.iter().any(|p| {
                    p.name.trim_start_matches('%') == clean_buf
                        && matches!(p.ty, Type::Slice(_) | Type::Array(_, _))
                });

                let off_expr = crate::ivl::IvlLowerer::operand_to_expr(offset);
                // 8-byte alignment check
                let align_check = crate::ivl::IvlExpr::Binary {
                    op: BinOp::Eq,
                    lhs: Box::new(crate::ivl::IvlExpr::Binary {
                        op: BinOp::Mod,
                        lhs: Box::new(off_expr.clone()),
                        rhs: Box::new(crate::ivl::IvlExpr::IntConst(8)),
                        is_unsigned: false,
                    }),
                    rhs: Box::new(crate::ivl::IvlExpr::IntConst(0)),
                    is_unsigned: false,
                };
                stmts.push(crate::ivl::IvlStmt::Assert {
                    cond: align_check,
                    goal_name: format!("Function '{}' - Line {}: Memory 64-bit 8-byte alignment check on '{}'", func.name, s_inst.loc.line, buf),
                    category: PropertyCategory::Safety,
                    loc: s_inst.loc.clone(),
                });

                if let Some(&sz) = buffer_sizes.get(actual_buf).or_else(|| buffer_sizes.get(buf)) {
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
                                is_unsigned: false,
                            }),
                            rhs: Box::new(crate::ivl::IvlExpr::Binary {
                                op: BinOp::Lte,
                                lhs: Box::new(off_expr),
                                rhs: Box::new(crate::ivl::IvlExpr::IntConst(max_off)),
                                is_unsigned: false,
                            }),
                            is_unsigned: false,
                        }
                    };
                    stmts.push(crate::ivl::IvlStmt::Assert {
                        cond: in_bounds,
                        goal_name: format!("Function '{}' - Line {}: Memory 64-bit bounds check on '{}'", func.name, s_inst.loc.line, buf),
                        category: PropertyCategory::Safety,
                        loc: s_inst.loc.clone(),
                    });
                } else if is_slice_param {
                    let max_off = crate::ivl::IvlExpr::Binary {
                        op: BinOp::Sub,
                        lhs: Box::new(crate::ivl::IvlExpr::Len(clean_buf.to_string())),
                        rhs: Box::new(crate::ivl::IvlExpr::IntConst(8)),
                        is_unsigned: false,
                    };
                    let in_bounds = crate::ivl::IvlExpr::Binary {
                        op: BinOp::And,
                        lhs: Box::new(crate::ivl::IvlExpr::Binary {
                            op: BinOp::Gte,
                            lhs: Box::new(off_expr.clone()),
                            rhs: Box::new(crate::ivl::IvlExpr::IntConst(0)),
                            is_unsigned: false,
                        }),
                        rhs: Box::new(crate::ivl::IvlExpr::Binary {
                            op: BinOp::Lte,
                            lhs: Box::new(off_expr),
                            rhs: Box::new(max_off),
                            is_unsigned: false,
                        }),
                        is_unsigned: false,
                    };
                    stmts.push(crate::ivl::IvlStmt::Assert {
                        cond: in_bounds,
                        goal_name: format!("Function '{}' - Line {}: Memory 64-bit bounds check on '{}'", func.name, s_inst.loc.line, buf),
                        category: PropertyCategory::Safety,
                        loc: s_inst.loc.clone(),
                    });
                } else {
                    let non_neg = crate::ivl::IvlExpr::Binary {
                        op: BinOp::Gte,
                        lhs: Box::new(off_expr),
                        rhs: Box::new(crate::ivl::IvlExpr::IntConst(0)),
                        is_unsigned: false,
                    };
                    stmts.push(crate::ivl::IvlStmt::Assert {
                        cond: non_neg,
                        goal_name: format!("Function '{}' - Line {}: Memory 64-bit pointer offset non-negative check on '{}'", func.name, s_inst.loc.line, buf),
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

                        // Xây dựng bảng ánh xạ tham số đồng thời (Simultaneous Substitution Map)
                        let mut param_map = std::collections::HashMap::new();
                        for (i, p) in callee.params.iter().enumerate() {
                            if i < args.len() {
                                let p_clean = p.name.trim_start_matches('%').to_string();
                                let arg_expr = crate::ivl::IvlLowerer::operand_to_expr(&args[i]);
                                if let Operand::Reg(r) = &args[i] {
                                    let r_clean = r.trim_start_matches('%');
                                    if let Some(&sz) = buffer_sizes.get(r).or_else(|| buffer_sizes.get(r_clean)) {
                                        param_map.insert(format!("{}_len", p_clean), crate::ivl::IvlExpr::IntConst(sz as i64));
                                    }
                                }
                                param_map.insert(p_clean, arg_expr);
                            }
                        }

                        for c_si in &callee.instructions {
                            if let Instruction::Require(req) = &c_si.inst {
                                let req_ivl = crate::ivl::IvlExpr::from(req);
                                let subst_req = crate::ivl::IvlLowerer::subst_expr_map(&req_ivl, &param_map);
                                stmts.push(crate::ivl::IvlStmt::Assert {
                                    cond: subst_req,
                                    goal_name: format!("Function '{}' - Line {}: Verify REQUIRE contract of '{}'", func.name, s_inst.loc.line, func_name),
                                    category: PropertyCategory::Safety,
                                    loc: s_inst.loc.clone(),
                                });
                            }
                        }
                        // Havoc all memory buffers passed as slice/pointer arguments to the callee
                        let mut havoc_mems = Vec::new();
                        for a in args {
                            if let Operand::Reg(r) = a {
                                let actual = buffer_aliases.get(r).unwrap_or(r);
                                let clean = actual.trim_start_matches('%').to_string();
                                if buffer_sizes.contains_key(actual) || buffer_sizes.contains_key(r)
                                    || func.params.iter().any(|p| p.name.trim_start_matches('%') == clean && matches!(p.ty, Type::Slice(_) | Type::Array(_, _)))
                                {
                                    havoc_mems.push(clean);
                                }
                            }
                        }
                        if !havoc_mems.is_empty() {
                            stmts.push(crate::ivl::IvlStmt::Havoc {
                                vars: havoc_mems,
                                is_memory: true,
                            });
                        }

                        if let Some(d) = dest {
                            stmts.push(crate::ivl::IvlStmt::Havoc {
                                vars: vec![d.clone()],
                                is_memory: false,
                            });
                            let callee_ret = Self::find_canonical_ret_var(callee).unwrap_or_else(|| "ret".to_string());
                            let mut ens_map = param_map;
                            ens_map.insert(
                                callee_ret.trim_start_matches('%').to_string(),
                                crate::ivl::IvlExpr::Var(d.trim_start_matches('%').to_string()),
                            );
                            for c_si in &callee.instructions {
                                if let Instruction::Ensure(ens) = &c_si.inst {
                                    let ens_ivl = crate::ivl::IvlExpr::from(ens);
                                    let subst_ens = crate::ivl::IvlLowerer::subst_expr_map(&ens_ivl, &ens_map);
                                    stmts.push(crate::ivl::IvlStmt::Assume { cond: subst_ens });
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

    /// Hạ cấp một lát cắt lệnh sang chuỗi IVL bằng thuật toán Guarded Symbolic Execution tổng quát
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
        loop_ctx: Option<&LoopContext>,
        loop_exit_out: Option<&mut crate::ivl::IvlExpr>,
        havoc_counter: &mut usize,
    ) -> Vec<crate::ivl::IvlStmt> {
        let mut stmts = Vec::new();
        let has_branch = slice.iter().any(|s| matches!(s.inst, Instruction::BrIf { .. } | Instruction::RetIf { .. }));

        // Trạng thái luồng chạy hiện tại (Path Condition) và bảng các nhánh nhảy tới từng LABEL
        let mut active = crate::ivl::IvlExpr::BoolConst(true);
        let mut incoming_jumps: std::collections::HashMap<String, crate::ivl::IvlExpr> = std::collections::HashMap::new();
        let mut local_loop_exit = crate::ivl::IvlExpr::BoolConst(false);
        let mut local_loop_break = crate::ivl::IvlExpr::BoolConst(false);

        let mut idx = 0;
        while idx < slice.len() {
            let s_inst = &slice[idx];
            match &s_inst.inst {
                Instruction::Require(req) => {
                    let cond = Self::mk_implies(&active, crate::ivl::IvlExpr::from(req));
                    stmts.push(crate::ivl::IvlStmt::Assume { cond });
                }
                Instruction::Ensure(_) | Instruction::Invariant(_) | Instruction::Decreases(_) => {}

                Instruction::Label(lbl) => {
                    if let Some(inc) = incoming_jumps.remove(lbl) {
                        active = Self::mk_or(active, inc);
                        // Tạo một biến định danh ngắn gọn cho Path Condition tại điểm hội tụ để tránh công thức SMT phình to theo cấp số nhân
                        *havoc_counter += 1;
                        let path_var = format!("__path_{}_{}", lbl.trim_start_matches('.'), *havoc_counter);
                        stmts.push(crate::ivl::IvlStmt::Assign {
                            dest: path_var.clone(),
                            expr: active,
                            is_memory: false,
                        });
                        active = crate::ivl::IvlExpr::Var(path_var);
                    }
                }

                Instruction::Jump(target) => {
                    // Kiểm tra xem target có phải là nhãn nằm phía dưới (Forward Jump) trong slice hiện tại không
                    let is_forward = slice[idx + 1..].iter().any(|s| matches!(&s.inst, Instruction::Label(l) if l == target));
                    if !is_forward {
                        results.push(VerificationResult::Unknown {
                            goal_name: format!("Function '{}' - Line {}: Unsupported backward/external JUMP", func.name, s_inst.loc.line),
                            category: PropertyCategory::Safety,
                            reason: format!("Backward or external JUMP to '{}' is not supported (use LOOP for loops)", target),
                            stack_trace: vec![StackFrame {
                                file: func.file.clone(),
                                line: s_inst.loc.line,
                                function: func.name.clone(),
                                snippet: s_inst.loc.text.clone(),
                                role: "Unsupported backward/external JUMP".into(),
                            }],
                        });
                        return stmts;
                    }
                    let prev = incoming_jumps.remove(target).unwrap_or(crate::ivl::IvlExpr::BoolConst(false));
                    incoming_jumps.insert(target.clone(), Self::mk_or(prev, active));
                    active = crate::ivl::IvlExpr::BoolConst(false);
                }

                Instruction::BrIf { cond, target } => {
                    let is_forward = slice[idx + 1..].iter().any(|s| matches!(&s.inst, Instruction::Label(l) if l == target));
                    if !is_forward {
                        results.push(VerificationResult::Unknown {
                            goal_name: format!("Function '{}' - Line {}: Unsupported backward/external BR_IF", func.name, s_inst.loc.line),
                            category: PropertyCategory::Safety,
                            reason: format!("Backward or external branch to '{}' is not supported (use LOOP for loops)", target),
                            stack_trace: vec![StackFrame {
                                file: func.file.clone(),
                                line: s_inst.loc.line,
                                function: func.name.clone(),
                                snippet: s_inst.loc.text.clone(),
                                role: "Unsupported backward/external BR_IF".into(),
                            }],
                        });
                        return stmts;
                    }
                    let cond_expr = crate::ivl::IvlExpr::Var(cond.trim_start_matches('%').to_string());
                    let take_branch = Self::mk_and(active.clone(), cond_expr);
                    *havoc_counter += 1;
                    let br_var = format!("__br_{}", *havoc_counter);
                    stmts.push(crate::ivl::IvlStmt::Assign {
                        dest: br_var.clone(),
                        expr: take_branch,
                        is_memory: false,
                    });
                    let br_var_expr = crate::ivl::IvlExpr::Var(br_var);
                    let prev = incoming_jumps.remove(target).unwrap_or(crate::ivl::IvlExpr::BoolConst(false));
                    incoming_jumps.insert(target.clone(), Self::mk_or(prev, br_var_expr.clone()));
                    active = Self::mk_and(active, Self::mk_not(br_var_expr));
                }

                Instruction::RetIf { cond, val } => {
                    let cond_expr = crate::ivl::IvlExpr::Var(cond.trim_start_matches('%').to_string());
                    let take_ret = Self::mk_and(active.clone(), cond_expr);
                    *havoc_counter += 1;
                    let ret_var = format!("__retif_{}", *havoc_counter);
                    stmts.push(crate::ivl::IvlStmt::Assign {
                        dest: ret_var.clone(),
                        expr: take_ret.clone(),
                        is_memory: false,
                    });
                    let ret_var_expr = crate::ivl::IvlExpr::Var(ret_var);
                    local_loop_exit = Self::mk_or(local_loop_exit, ret_var_expr.clone());
                    if !Self::is_false(&take_ret) {
                        if let Some(op) = val {
                            let op_expr = crate::ivl::IvlLowerer::operand_to_expr(op);
                            for ens in ensures {
                                let ens_ivl = crate::ivl::IvlExpr::from(ens);
                                let mapped_ens = crate::ivl::IvlLowerer::subst_expr(&ens_ivl, canon_ret, &op_expr);
                                stmts.push(crate::ivl::IvlStmt::Assert {
                                    cond: Self::mk_implies(&take_ret, mapped_ens),
                                    goal_name: format!("Function '{}' - Line {}: Verify ENSURE on early return (RET_IF)", func.name, s_inst.loc.line),
                                    category: PropertyCategory::Functional,
                                    loc: s_inst.loc.clone(),
                                });
                            }
                        } else {
                            for ens in ensures {
                                let ens_ivl = crate::ivl::IvlExpr::from(ens);
                                stmts.push(crate::ivl::IvlStmt::Assert {
                                    cond: Self::mk_implies(&take_ret, ens_ivl),
                                    goal_name: format!("Function '{}' - Line {}: Verify ENSURE on early return (RET_IF)", func.name, s_inst.loc.line),
                                    category: PropertyCategory::Functional,
                                    loc: s_inst.loc.clone(),
                                });
                            }
                        }
                    }
                    active = Self::mk_and(active, Self::mk_not(ret_var_expr));
                }

                Instruction::Ret(val_opt) => {
                    *havoc_counter += 1;
                    let ret_var = format!("__ret_{}", *havoc_counter);
                    stmts.push(crate::ivl::IvlStmt::Assign {
                        dest: ret_var.clone(),
                        expr: active.clone(),
                        is_memory: false,
                    });
                    let ret_var_expr = crate::ivl::IvlExpr::Var(ret_var);
                    local_loop_exit = Self::mk_or(local_loop_exit, ret_var_expr);
                    if !Self::is_false(&active) {
                        if let Some(op) = val_opt {
                            let op_expr = crate::ivl::IvlLowerer::operand_to_expr(op);
                            let assign_ret = crate::ivl::IvlStmt::Assign {
                                dest: canon_ret.to_string(),
                                expr: op_expr,
                                is_memory: false,
                            };
                            stmts.extend(Self::guard_stmts(vec![assign_ret], &active, havoc_counter));
                        }
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
                                cond: Self::mk_implies(&active, ens_ivl),
                                goal_name,
                                category: PropertyCategory::Functional,
                                loc: s_inst.loc.clone(),
                            });
                        }
                    }
                    active = crate::ivl::IvlExpr::BoolConst(false);
                }

                Instruction::BreakIf(cond) => {
                    let cond_expr = crate::ivl::IvlExpr::Var(cond.trim_start_matches('%').to_string());
                    let take_break = Self::mk_and(active.clone(), cond_expr);
                    *havoc_counter += 1;
                    let brk_var = format!("__brk_{}", *havoc_counter);
                    stmts.push(crate::ivl::IvlStmt::Assign {
                        dest: brk_var.clone(),
                        expr: take_break,
                        is_memory: false,
                    });
                    let brk_var_expr = crate::ivl::IvlExpr::Var(brk_var);
                    local_loop_break = Self::mk_or(local_loop_break, brk_var_expr.clone());
                    local_loop_exit = Self::mk_or(local_loop_exit, brk_var_expr.clone());
                    active = Self::mk_and(active, Self::mk_not(brk_var_expr));
                }

                Instruction::ContinueIf(cond) => {
                    let cond_expr = crate::ivl::IvlExpr::Var(cond.trim_start_matches('%').to_string());
                    let take_cont = Self::mk_and(active.clone(), cond_expr);
                    *havoc_counter += 1;
                    let cont_var = format!("__cont_{}", *havoc_counter);
                    stmts.push(crate::ivl::IvlStmt::Assign {
                        dest: cont_var.clone(),
                        expr: take_cont.clone(),
                        is_memory: false,
                    });
                    let cont_var_expr = crate::ivl::IvlExpr::Var(cont_var);
                    local_loop_exit = Self::mk_or(local_loop_exit, cont_var_expr.clone());
                    if let Some(ctx) = loop_ctx {
                        if ctx.verify_inductive && !Self::is_false(&take_cont) {
                            for inv in ctx.invariants {
                                stmts.push(crate::ivl::IvlStmt::Assert {
                                    cond: Self::mk_implies(&take_cont, inv.clone()),
                                    goal_name: format!(
                                        "Function '{}' - Line {}: Loop Step 2: Invariant preservation on CONTINUE_IF",
                                        func.name, s_inst.loc.line
                                    ),
                                    category: PropertyCategory::Inductive,
                                    loc: s_inst.loc.clone(),
                                });
                            }
                            for (d_idx, dec) in ctx.decreases.iter().enumerate() {
                                let old_r = crate::ivl::IvlExpr::Var(format!("__rank_init_{}_{}", ctx.loop_id, d_idx));
                                stmts.push(crate::ivl::IvlStmt::Assert {
                                    cond: Self::mk_implies(
                                        &take_cont,
                                        crate::ivl::IvlExpr::Binary {
                                            op: BinOp::Gte,
                                            lhs: Box::new(old_r.clone()),
                                            rhs: Box::new(crate::ivl::IvlExpr::IntConst(0)),
                                            is_unsigned: false,
                                        },
                                    ),
                                    goal_name: format!(
                                        "Function '{}' - Line {}: Step 4a: Termination Step on CONTINUE_IF (DECREASES bounded below >= 0)",
                                        func.name, s_inst.loc.line
                                    ),
                                    category: PropertyCategory::Termination,
                                    loc: s_inst.loc.clone(),
                                });
                                stmts.push(crate::ivl::IvlStmt::Assert {
                                    cond: Self::mk_implies(
                                        &take_cont,
                                        crate::ivl::IvlExpr::Binary {
                                            op: BinOp::Lt,
                                            lhs: Box::new(dec.clone()),
                                            rhs: Box::new(old_r),
                                            is_unsigned: false,
                                        },
                                    ),
                                    goal_name: format!(
                                        "Function '{}' - Line {}: Step 4b: Termination Step on CONTINUE_IF (DECREASES ranking strictly decreases)",
                                        func.name, s_inst.loc.line
                                    ),
                                    category: PropertyCategory::Termination,
                                    loc: s_inst.loc.clone(),
                                });
                            }
                        }
                    }
                    active = Self::mk_and(active, Self::mk_not(cont_var_expr));
                }

                Instruction::Loop(l_lbl) => {
                    *havoc_counter += 1;
                    let loop_id = *havoc_counter;
                    let mut depth = 1;
                    let mut l_end_opt = None;
                    for (p, s) in slice[idx + 1..].iter().enumerate() {
                        match &s.inst {
                            Instruction::Loop(_) => depth += 1,
                            Instruction::EndLoop(end_lbl) => {
                                depth -= 1;
                                if depth == 0 {
                                    if end_lbl == l_lbl {
                                        l_end_opt = Some(idx + 1 + p);
                                    }
                                    break;
                                }
                            }
                            _ => {}
                        }
                    }

                    let l_end = if let Some(le) = l_end_opt {
                        le
                    } else {
                        results.push(VerificationResult::Failed {
                            goal_name: format!("Function '{}' - Line {}: Loop Structure Error", func.name, slice[idx].loc.line),
                            category: PropertyCategory::Safety,
                            reason: format!("Missing or mismatched END_LOOP for LOOP '{}'", l_lbl),
                            counter_example: None,
                            stack_trace: vec![StackFrame {
                                file: func.file.clone(),
                                line: slice[idx].loc.line,
                                function: func.name.clone(),
                                snippet: slice[idx].loc.text.clone(),
                                role: format!("Missing END_LOOP '{}'", l_lbl),
                            }],
                        });
                        return stmts;
                    };
                    let body_slice = &slice[idx + 1..l_end];

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
                    let mut inner_depth = 0usize;

                    for b_si in body_slice {
                        match &b_si.inst {
                            Instruction::Loop(_) => inner_depth += 1,
                            Instruction::EndLoop(_) => inner_depth = inner_depth.saturating_sub(1),
                            Instruction::Invariant(e) if inner_depth == 0 => loop_invs.push(crate::ivl::IvlExpr::from(e)),
                            Instruction::Decreases(e) if inner_depth == 0 => loop_decs.push(crate::ivl::IvlExpr::from(e)),
                            _ => {}
                        }
                    }

                    let vc_loop = if loop_ctx.is_none() {
                        results.extend(vc.verify_sequence(&stmts, &func.name, &func.file));
                        stmts.clear();
                        vc.clone()
                    } else {
                        let mut vcl = vc.clone();
                        let _ = vcl.verify_sequence(&stmts, &func.name, &func.file);
                        vcl
                    };

                    // Step 1: Base Case (chỉ kiểm tra nếu luồng tới được vòng lặp đang active)
                    let mut vc_step1 = vc_loop.clone();
                    let mut step1_asserts = Vec::new();
                    for inv in &loop_invs {
                        step1_asserts.push(crate::ivl::IvlStmt::Assert {
                            cond: Self::mk_implies(&active, inv.clone()),
                            goal_name: format!("Function '{}' - Step 1: Base Case (Loop initialization)", func.name),
                            category: PropertyCategory::Inductive,
                            loc: slice[idx].loc.clone(),
                        });
                    }
                    results.extend(vc_step1.verify_sequence(&step1_asserts, &func.name, &func.file));

                    let modified: Vec<String> = crate::ivl::IvlLowerer::collect_modified_vars(body_slice, Some(buffer_aliases)).into_iter().collect();
                    let modified_mems: Vec<String> = crate::ivl::IvlLowerer::collect_modified_mems(body_slice, Some(buffer_aliases)).into_iter().collect();

                    // Step 2 & Step 4: Symbolic Loop Execution & Safety Verification (Inductive Step)
                    {
                        let mut ind_stmts = Vec::new();
                        ind_stmts.push(crate::ivl::IvlStmt::Assume { cond: active.clone() });
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
                                dest: format!("__rank_init_{}_{}", loop_id, d_idx),
                                expr: dec.clone(),
                                is_memory: false,
                            });
                        }

                        let mut vc_ind = vc_loop.clone();
                        let ind_ctx = LoopContext {
                            invariants: &loop_invs,
                            decreases: &loop_decs,
                            verify_inductive: true,
                            loop_id,
                        };
                        let mut dummy_exit = crate::ivl::IvlExpr::BoolConst(false);
                        ind_stmts.extend(Self::lower_slice(
                            func,
                            body_slice,
                            buffer_sizes,
                            buffer_aliases,
                            program,
                            &mut vc_ind,
                            results,
                            ensures,
                            canon_ret,
                            true,
                            Some(&ind_ctx),
                            Some(&mut dummy_exit),
                            havoc_counter,
                        ));

                        // Cuối thân vòng lặp: chỉ những nhánh không BREAK, không CONTINUE, không RET mới quay lại đầu vòng lặp.
                        ind_stmts.push(crate::ivl::IvlStmt::Assume {
                            cond: Self::mk_not(dummy_exit),
                        });

                        for inv in &loop_invs {
                            ind_stmts.push(crate::ivl::IvlStmt::Assert {
                                cond: inv.clone(),
                                goal_name: format!("Function '{}' - Symbolic Loop Execution - Step 2: Inductive Step (Invariant preservation)", func.name),
                                category: PropertyCategory::Inductive,
                                loc: slice[idx].loc.clone(),
                            });
                        }
                        for (d_idx, dec) in loop_decs.iter().enumerate() {
                            let old_r = crate::ivl::IvlExpr::Var(format!("__rank_init_{}_{}", loop_id, d_idx));
                            ind_stmts.push(crate::ivl::IvlStmt::Assert {
                                cond: crate::ivl::IvlExpr::Binary {
                                    op: BinOp::Gte,
                                    lhs: Box::new(old_r.clone()),
                                    rhs: Box::new(crate::ivl::IvlExpr::IntConst(0)),
                                    is_unsigned: false,
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
                                    is_unsigned: false,
                                },
                                goal_name: format!("Function '{}' - Step 4b: Termination Step (DECREASES ranking function strictly decreases)", func.name),
                                category: PropertyCategory::Termination,
                                loc: slice[idx].loc.clone(),
                            });
                        }
                        results.extend(vc_ind.verify_sequence(&ind_stmts, &func.name, &func.file));
                    }

                    // Step 3: Exit Step (Hạ cấp thân vòng lặp với Guarded Execution để tự động gom mọi điểm BREAK_IF!)
                    let havoc_scalars = crate::ivl::IvlStmt::Havoc {
                        vars: modified,
                        is_memory: false,
                    };
                    stmts.extend(Self::guard_stmts(vec![havoc_scalars], &active, havoc_counter));
                    if !modified_mems.is_empty() {
                        let havoc_mems = crate::ivl::IvlStmt::Havoc {
                            vars: modified_mems,
                            is_memory: true,
                        };
                        stmts.extend(Self::guard_stmts(vec![havoc_mems], &active, havoc_counter));
                    }
                    for inv in &loop_invs {
                        stmts.push(crate::ivl::IvlStmt::Assume {
                            cond: Self::mk_implies(&active, inv.clone()),
                        });
                    }

                    let exit_ctx = LoopContext {
                        invariants: &loop_invs,
                        decreases: &loop_decs,
                        verify_inductive: false,
                        loop_id,
                    };
                    let mut exit_cond = crate::ivl::IvlExpr::BoolConst(false);
                    let mut vc_exit = vc_loop.clone();
                    let body_exit_stmts = Self::lower_slice(
                        func,
                        body_slice,
                        buffer_sizes,
                        buffer_aliases,
                        program,
                        &mut vc_exit,
                        results,
                        ensures,
                        canon_ret,
                        true,
                        Some(&exit_ctx),
                        Some(&mut exit_cond),
                        havoc_counter,
                    );
                    // Tránh sinh lại Assert trong body ở Step 3 (vì đã được chứng minh ở Step 2)
                    let body_exit_no_asserts: Vec<crate::ivl::IvlStmt> = body_exit_stmts
                        .into_iter()
                        .filter(|st| !matches!(st, crate::ivl::IvlStmt::Assert { .. }))
                        .collect();
                    stmts.extend(Self::guard_stmts(body_exit_no_asserts, &active, havoc_counter));

                    // Để thoát khỏi vòng lặp sang câu lệnh sau END_LOOP, ít nhất một nhánh BREAK_IF phải được kích hoạt
                    stmts.push(crate::ivl::IvlStmt::Assume {
                        cond: Self::mk_implies(&active, exit_cond),
                    });

                    idx = l_end + 1;
                    continue;
                }

                Instruction::EndLoop(_) => {}

                _other => {
                    let raw = Self::lower_inst_with_checks(func, s_inst, buffer_sizes, buffer_aliases, program);
                    stmts.extend(Self::guard_stmts(raw, &active, havoc_counter));
                }
            }
            idx += 1;
        }

        if let Some(out_exit) = loop_exit_out {
            if let Some(ctx) = loop_ctx {
                if ctx.verify_inductive {
                    *out_exit = local_loop_exit;
                } else {
                    *out_exit = local_loop_break;
                }
            } else {
                *out_exit = local_loop_break;
            }
        }
        stmts
    }

    /// Kiểm tra tính đúng đắn toán học bằng kiến trúc Boogie IVL Engine (Universal VCGen)
    pub fn verify_function(func: &Function, program: Option<&Program>) -> Vec<VerificationResult> {
        let mut results = Vec::new();

        // 0a. Static Well-Formedness: Loop Structure Check (Matching LOOP <lbl> ... END_LOOP <lbl>)
        let mut loop_stack: Vec<(&str, &crate::ast::Loc)> = Vec::new();
        for s_inst in &func.instructions {
            match &s_inst.inst {
                Instruction::Loop(lbl) => {
                    loop_stack.push((lbl.as_str(), &s_inst.loc));
                }
                Instruction::BreakIf(_) | Instruction::ContinueIf(_) => {
                    if loop_stack.is_empty() {
                        let op_name = match &s_inst.inst {
                            Instruction::BreakIf(_) => "BREAK_IF",
                            _ => "CONTINUE_IF",
                        };
                        results.push(VerificationResult::Failed {
                            goal_name: format!("Function '{}' - Line {}: Loop Structure Error", func.name, s_inst.loc.line),
                            category: PropertyCategory::Safety,
                            reason: format!("{} must be placed inside a LOOP ... END_LOOP block", op_name),
                            counter_example: None,
                            stack_trace: vec![StackFrame {
                                file: func.file.clone(),
                                line: s_inst.loc.line,
                                function: func.name.clone(),
                                snippet: s_inst.loc.text.clone(),
                                role: format!("{} outside of LOOP", op_name),
                            }],
                        });
                        return results;
                    }
                }
                Instruction::EndLoop(lbl) => {
                    match loop_stack.pop() {
                        Some((open_lbl, _)) if open_lbl == lbl => {}
                        Some((open_lbl, open_loc)) => {
                            results.push(VerificationResult::Failed {
                                goal_name: format!("Function '{}' - Line {}: Loop Structure Error", func.name, s_inst.loc.line),
                                category: PropertyCategory::Safety,
                                reason: format!("Mismatched END_LOOP '{}' (expected '{}' opened at line {})", lbl, open_lbl, open_loc.line),
                                counter_example: None,
                                stack_trace: vec![StackFrame {
                                    file: func.file.clone(),
                                    line: s_inst.loc.line,
                                    function: func.name.clone(),
                                    snippet: s_inst.loc.text.clone(),
                                    role: format!("Mismatched END_LOOP '{}'", lbl),
                                }],
                            });
                            return results;
                        }
                        None => {
                            results.push(VerificationResult::Failed {
                                goal_name: format!("Function '{}' - Line {}: Loop Structure Error", func.name, s_inst.loc.line),
                                category: PropertyCategory::Safety,
                                reason: format!("Unexpected END_LOOP '{}' without matching LOOP", lbl),
                                counter_example: None,
                                stack_trace: vec![StackFrame {
                                    file: func.file.clone(),
                                    line: s_inst.loc.line,
                                    function: func.name.clone(),
                                    snippet: s_inst.loc.text.clone(),
                                    role: format!("Unmatched END_LOOP '{}'", lbl),
                                }],
                            });
                            return results;
                        }
                    }
                }
                _ => {}
            }
        }
        if let Some((unclosed_lbl, unclosed_loc)) = loop_stack.last() {
            results.push(VerificationResult::Failed {
                goal_name: format!("Function '{}' - Line {}: Loop Structure Error", func.name, unclosed_loc.line),
                category: PropertyCategory::Safety,
                reason: format!("Unclosed LOOP '{}' (missing END_LOOP '{}')", unclosed_lbl, unclosed_lbl),
                counter_example: None,
                stack_trace: vec![StackFrame {
                    file: func.file.clone(),
                    line: unclosed_loc.line,
                    function: func.name.clone(),
                    snippet: unclosed_loc.text.clone(),
                    role: format!("Unclosed LOOP '{}'", unclosed_lbl),
                }],
            });
            return results;
        }

        // 0b. Static Well-Formedness: Jump Label Validation (No undefined JUMP/BR_IF targets)
        let defined_labels: std::collections::HashSet<&str> = func
            .instructions
            .iter()
            .filter_map(|s| match &s.inst {
                Instruction::Label(l) => Some(l.as_str()),
                _ => None,
            })
            .collect();
        for s_inst in &func.instructions {
            match &s_inst.inst {
                Instruction::Jump(target) | Instruction::BrIf { target, .. } => {
                    if !defined_labels.contains(target.as_str()) {
                        results.push(VerificationResult::Failed {
                            goal_name: format!("Function '{}' - Line {}: Undefined label '{}'", func.name, s_inst.loc.line, target),
                            category: PropertyCategory::Safety,
                            reason: format!("Jump target '{}' is not defined anywhere in function '{}'", target, func.name),
                            counter_example: None,
                            stack_trace: vec![StackFrame {
                                file: func.file.clone(),
                                line: s_inst.loc.line,
                                function: func.name.clone(),
                                snippet: s_inst.loc.text.clone(),
                                role: format!("Undefined jump label '{}'", target),
                            }],
                        });
                        return results;
                    }
                }
                _ => {}
            }
        }

        // 0c. Static Well-Formedness: SSA Definite Assignment Check via CFG Forward Dataflow Analysis
        if let Some(err) = Self::check_definite_assignment_cfg(func) {
            results.push(err);
            return results;
        }

        // 0d. Memory Sort Consistency Check: Prevent mixing 8-bit and 64-bit accesses on same buffer
        let buffer_sizes = crate::ivl::IvlLowerer::extract_buffer_sizes(func);
        let buffer_aliases = crate::ivl::IvlLowerer::extract_buffer_aliases(func);
        let mut has_mem8 = std::collections::HashSet::new();
        let mut has_mem64 = std::collections::HashSet::new();
        for s in &func.instructions {
            match &s.inst {
                Instruction::Load8 { buf, .. } | Instruction::Store8 { buf, .. } => {
                    let actual = buffer_aliases.get(buf).unwrap_or(buf);
                    has_mem8.insert(actual.trim_start_matches('%').to_string());
                }
                Instruction::Load64 { buf, .. } | Instruction::Store64 { buf, .. } => {
                    let actual = buffer_aliases.get(buf).unwrap_or(buf);
                    has_mem64.insert(actual.trim_start_matches('%').to_string());
                }
                _ => {}
            }
        }
        for buf in &has_mem8 {
            if has_mem64.contains(buf) {
                results.push(VerificationResult::Failed {
                    goal_name: format!("Function '{}': Memory Sort Consistency", func.name),
                    category: PropertyCategory::Safety,
                    reason: format!("Mixed 8-bit (LOAD8/STORE8) and 64-bit (LOAD64/STORE64) accesses on buffer '%{}'. In SMT QF_ABV memory theory, mixing byte-level and 64-bit word-level operations without byte concatenation causes memory model unsoundness.", buf),
                    counter_example: None,
                    stack_trace: vec![StackFrame {
                        file: func.file.clone(),
                        line: 1,
                        function: func.name.clone(),
                        snippet: format!("Buffer '%{}' used with both 8-bit and 64-bit memory instructions", buf),
                        role: "Memory Sort Mismatch".to_string(),
                    }],
                });
                return results;
            }
        }

        // 0e. Floating-Point Rejection Check
        for p in &func.params {
            if matches!(p.ty, Type::F64) {
                results.push(VerificationResult::Failed {
                    goal_name: format!("Function '{}': Type Check", func.name),
                    category: PropertyCategory::Safety,
                    reason: "Floating-point type 'f64' is not yet supported in Light SMT verifier (planned for future QF_FP support)".to_string(),
                    counter_example: None,
                    stack_trace: vec![StackFrame {
                        file: func.file.clone(),
                        line: 1,
                        function: func.name.clone(),
                        snippet: format!("param {}: f64", p.name),
                        role: "Unsupported Float Type".to_string(),
                    }],
                });
                return results;
            }
        }

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
        let mut havoc_counter = 0usize;
        let all_stmts = Self::lower_slice(func, &func.instructions, &buffer_sizes, &buffer_aliases, program, &mut vc, &mut results, &ensures, &canon_ret, has_loop, None, None, &mut havoc_counter);
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

    /// Thu thập các biến được định nghĩa bởi một instruction
    fn collect_defined_vars(inst: &Instruction, out: &mut std::collections::HashSet<String>) {
        match inst {
            Instruction::AssignConst { dest, .. }
            | Instruction::Binary { dest, .. }
            | Instruction::Not { dest, .. }
            | Instruction::SliceLen { dest, .. }
            | Instruction::Load8 { dest, .. }
            | Instruction::Load64 { dest, .. } => {
                out.insert(dest.trim_start_matches('%').to_string());
            }
            Instruction::Mov { dest, src } => {
                let clean_dest = dest.trim_start_matches('%').to_string();
                let clean_src = src.trim_start_matches('%');
                out.insert(clean_dest.clone());
                if out.contains(&format!("{}_len", clean_src)) {
                    out.insert(format!("{}_len", clean_dest));
                }
            }
            Instruction::SlicePtr { dest, slice } => {
                let clean_dest = dest.trim_start_matches('%').to_string();
                let clean_slice = slice.trim_start_matches('%');
                out.insert(clean_dest.clone());
                if out.contains(&format!("{}_len", clean_slice)) {
                    out.insert(format!("{}_len", clean_dest));
                }
            }
            Instruction::AllocSlice { dest, .. }
            | Instruction::Alloc { dest, .. } => {
                let clean = dest.trim_start_matches('%').to_string();
                out.insert(clean.clone());
                out.insert(format!("{}_len", clean));
            }
            Instruction::Call { dest: Some(d), .. }
            | Instruction::Syscall { dest: Some(d), .. } => {
                out.insert(d.trim_start_matches('%').to_string());
            }
            Instruction::Syscall { dest: None, .. } => {
                out.insert("rax".to_string());
            }
            _ => {}
        }
    }

    /// Thu thập các biến được sử dụng bởi một instruction
    fn collect_used_vars(
        inst: &Instruction,
        all_ret_vars: &std::collections::HashSet<String>,
        used_regs: &mut Vec<String>,
    ) {
        match inst {
            Instruction::Require(e)
            | Instruction::Invariant(e)
            | Instruction::Decreases(e)
            | Instruction::Assert(e) => {
                let mut expr_vars = std::collections::HashSet::new();
                Self::collect_vars(e, &mut expr_vars);
                for v in expr_vars {
                    used_regs.push(v);
                }
            }
            Instruction::Ensure(e) => {
                let mut expr_vars = std::collections::HashSet::new();
                Self::collect_vars(e, &mut expr_vars);
                for v in expr_vars {
                    if !all_ret_vars.contains(&v) {
                        used_regs.push(v);
                    }
                }
            }
            Instruction::Mov { src, .. } => used_regs.push(src.trim_start_matches('%').to_string()),
            Instruction::Not { src, .. } => {
                if let Operand::Reg(r) = src { used_regs.push(r.trim_start_matches('%').to_string()); }
            }
            Instruction::Binary { src1, src2, .. } => {
                if let Operand::Reg(r) = src1 { used_regs.push(r.trim_start_matches('%').to_string()); }
                if let Operand::Reg(r) = src2 { used_regs.push(r.trim_start_matches('%').to_string()); }
            }
            Instruction::Store8 { buf, offset, val } => {
                used_regs.push(buf.trim_start_matches('%').to_string());
                if let Operand::Reg(r) = offset { used_regs.push(r.trim_start_matches('%').to_string()); }
                if let Operand::Reg(r) = val { used_regs.push(r.trim_start_matches('%').to_string()); }
            }
            Instruction::Load8 { buf, offset, .. } => {
                used_regs.push(buf.trim_start_matches('%').to_string());
                if let Operand::Reg(r) = offset { used_regs.push(r.trim_start_matches('%').to_string()); }
            }
            Instruction::Store64 { buf, offset, val } => {
                used_regs.push(buf.trim_start_matches('%').to_string());
                if let Operand::Reg(r) = offset { used_regs.push(r.trim_start_matches('%').to_string()); }
                if let Operand::Reg(r) = val { used_regs.push(r.trim_start_matches('%').to_string()); }
            }
            Instruction::Load64 { buf, offset, .. } => {
                used_regs.push(buf.trim_start_matches('%').to_string());
                if let Operand::Reg(r) = offset { used_regs.push(r.trim_start_matches('%').to_string()); }
            }
            Instruction::StoreStr { buf, .. } => {
                used_regs.push(buf.trim_start_matches('%').to_string());
            }
            Instruction::SlicePtr { slice, .. } => {
                used_regs.push(slice.trim_start_matches('%').to_string());
            }
            Instruction::SliceLen { slice, .. } => {
                used_regs.push(slice.trim_start_matches('%').to_string());
            }
            Instruction::BrIf { cond, .. } | Instruction::BreakIf(cond) | Instruction::ContinueIf(cond) => {
                used_regs.push(cond.trim_start_matches('%').to_string());
            }
            Instruction::Ret(Some(Operand::Reg(r))) => used_regs.push(r.trim_start_matches('%').to_string()),
            Instruction::RetIf { cond, val } => {
                used_regs.push(cond.trim_start_matches('%').to_string());
                if let Some(Operand::Reg(r)) = val { used_regs.push(r.trim_start_matches('%').to_string()); }
            }
            Instruction::Call { args, .. } => {
                for a in args {
                    if let Operand::Reg(r) = a {
                        used_regs.push(r.trim_start_matches('%').to_string());
                    }
                }
            }
            Instruction::Syscall { rax, rdi, rsi, rdx, r10, r8, r9, .. } => {
                if let Operand::Reg(r) = rax { used_regs.push(r.trim_start_matches('%').to_string()); }
                if let Operand::Reg(r) = rdi { used_regs.push(r.trim_start_matches('%').to_string()); }
                if let Operand::Reg(r) = rsi { used_regs.push(r.trim_start_matches('%').to_string()); }
                if let Operand::Reg(r) = rdx { used_regs.push(r.trim_start_matches('%').to_string()); }
                if let Some(Operand::Reg(r)) = r10 { used_regs.push(r.trim_start_matches('%').to_string()); }
                if let Some(Operand::Reg(r)) = r8 { used_regs.push(r.trim_start_matches('%').to_string()); }
                if let Some(Operand::Reg(r)) = r9 { used_regs.push(r.trim_start_matches('%').to_string()); }
            }
            _ => {}
        }
    }

    /// Phân tích Definite Assignment chuẩn xác qua duyệt luồng tiến (Forward Jump & Structured Loop)
    fn check_definite_assignment_cfg(func: &Function) -> Option<VerificationResult> {
        let mut defined: std::collections::HashSet<String> = func.params.iter().flat_map(|p| {
            let c = p.name.trim_start_matches('%').to_string();
            if matches!(p.ty, Type::Slice(_) | Type::Array(_, _)) {
                vec![c.clone(), format!("{}_len", c)]
            } else {
                vec![c]
            }
        }).collect();

        let mut all_ret_vars: std::collections::HashSet<String> =
            ["ret", "result", "res"].into_iter().map(String::from).collect();
        if let Some(cr) = Self::find_canonical_ret_var(func) {
            all_ret_vars.insert(cr.trim_start_matches('%').to_string());
        }
        for s in &func.instructions {
            if let Instruction::Ret(Some(Operand::Reg(r))) | Instruction::RetIf { val: Some(Operand::Reg(r)), .. } = &s.inst {
                all_ret_vars.insert(r.trim_start_matches('%').to_string());
            }
        }

        // Lưu trạng thái tập biến tại các nhánh nhảy tiến tới LABEL hoặc thoát LOOP
        let mut incoming_label: std::collections::HashMap<String, std::collections::HashSet<String>> = std::collections::HashMap::new();
        let mut loop_exit_states: Vec<Option<std::collections::HashSet<String>>> = Vec::new();
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
                    return Some(VerificationResult::Failed {
                        goal_name: format!("Function '{}' - Line {}: SSA Definite Assignment", func.name, s_inst.loc.line),
                        category: PropertyCategory::Safety,
                        reason: format!("Variable '%{}' used before definition (not assigned on all execution paths)!", clean),
                        counter_example: None,
                        stack_trace: vec![StackFrame {
                            file: func.file.clone(),
                            line: s_inst.loc.line,
                            function: func.name.clone(),
                            snippet: s_inst.loc.text.clone(),
                            role: format!("Use of undefined variable '%{}'", clean),
                        }],
                    });
                }
            }

            Self::collect_defined_vars(&s_inst.inst, &mut defined);

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

    /// Tìm tên biến đại diện cho giá trị trả về của hàm trong ENSURE
    pub fn find_canonical_ret_var(func: &Function) -> Option<String> {
        let mut ensure_vars = std::collections::HashSet::new();
        for si in &func.instructions {
            if let Instruction::Ensure(e) = &si.inst {
                Self::collect_vars(e, &mut ensure_vars);
            }
        }
        // Thu thập tất cả các thanh ghi trả về (cả RET và RET_IF)
        let mut ret_regs = Vec::new();
        for s_inst in func.instructions.iter().rev() {
            match &s_inst.inst {
                Instruction::Ret(Some(Operand::Reg(r))) => ret_regs.push(r.trim_start_matches('%').to_string()),
                Instruction::RetIf { val: Some(Operand::Reg(r)), .. } => ret_regs.push(r.trim_start_matches('%').to_string()),
                _ => {}
            }
        }
        // Ưu tiên 1: Biến nào trong ret_regs có mặt trực tiếp trong ensure_vars
        for r in &ret_regs {
            if ensure_vars.contains(r) {
                return Some(r.clone());
            }
        }
        // Ưu tiên 2: Tên quy ước chuẩn: "ret", "res", "result" nếu có trong ensure_vars
        for standard in &["ret", "res", "result"] {
            if ensure_vars.contains(*standard) {
                return Some(standard.to_string());
            }
        }
        // Ưu tiên 3: Thanh ghi trả về đầu tiên tìm thấy
        if let Some(first_ret) = ret_regs.first() {
            return Some(first_ret.clone());
        }
        // Ưu tiên 4: Biến trong ENSURE không phải là param của hàm
        let param_names: std::collections::HashSet<String> = func
            .params
            .iter()
            .map(|p| p.name.trim_start_matches('%').to_string())
            .collect();
        for ev in &ensure_vars {
            if !param_names.contains(ev) {
                return Some(ev.clone());
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
                vars.insert(name.trim_start_matches('%').to_string());
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
