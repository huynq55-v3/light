//! Intermediate Verification Language (IVL) & Control Flow Graph (CFG)
//! Lấy cảm hứng từ kiến trúc Boogie (Microsoft Research) & Why3 (INRIA).
//!
//! Toàn bộ chương trình được hạ cấp (Lowering) thành đồ thị CFG với chỉ đúng 4 vi lệnh toán học:
//! 1. `Assign`: Gán biểu thức giá trị toán học thuần túy (hỗ trợ cả biến số BitVec và Memory Array)
//! 2. `Assert`: Khẳng định một thuộc tính phải đúng (nếu sai -> Báo lỗi & counter-example)
//! 3. `Assume`: Giả định tiền đề hoặc điều kiện rẽ nhánh hợp lệ
//! 4. `Havoc`: Giải phóng biến/bộ nhớ thành tự do (phục vụ bất biến quy nạp cho vòng lặp & lời gọi hàm)

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
        is_unsigned: bool,
    },
    /// Biểu thức điều kiện Phi-node: ite(cond, then_expr, else_expr)
    Ite {
        cond: Box<IvlExpr>,
        then_val: Box<IvlExpr>,
        else_val: Box<IvlExpr>,
    },
    Not(Box<IvlExpr>),
    BitNot(Box<IvlExpr>),
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
    /// Cắt lấy 8-bit thấp (0..255) chuẩn SMT BitVec: (bvand val (_ bv255 64))
    Mask8(Box<IvlExpr>),
}

impl From<&Expr> for IvlExpr {
    fn from(e: &Expr) -> Self {
        let empty = HashSet::new();
        IvlLowerer::expr_to_ivl_typed(e, &empty)
    }
}

/// Vi lệnh kiểm chứng toán học nguyên tử (Boogie 4-Instruction Core)
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
}

/// Ngữ cảnh thông tin kiểu và bộ đệm của một hàm sau khi chuẩn hóa
pub struct FunctionBufferContext {
    /// Kích thước tĩnh của các buffer (ALLOC / ALLOC slice<T>)
    pub buffer_sizes: HashMap<String, usize>,
    /// Ánh xạ bí danh con trỏ/slice về tên buffer gốc (root buffer name, không có '%')
    pub buffer_aliases: HashMap<String, String>,
    /// Tập hợp các tham số đầu vào có kiểu slice<T> hoặc arr<T, N> (không có '%')
    pub slice_params: HashSet<String>,
    /// Tập hợp các biến mang kiểu số nguyên không dấu (u64 / u8)
    pub unsigned_vars: HashSet<String>,
}

impl FunctionBufferContext {
    pub fn analyze(func: &Function, program: Option<&Program>) -> Self {
        let slice_params: HashSet<String> = func
            .params
            .iter()
            .filter(|p| matches!(p.ty, Type::Slice(_) | Type::Array(_, _)))
            .map(|p| IvlLowerer::clean_name(&p.name).to_string())
            .collect();
        let (buffer_sizes, buffer_aliases) = IvlLowerer::extract_buffers_and_aliases(func, &slice_params);
        let unsigned_vars = IvlLowerer::collect_unsigned_vars_with_prog(func, program);
        Self {
            buffer_sizes,
            buffer_aliases,
            slice_params,
            unsigned_vars,
        }
    }

    /// Tìm tên buffer gốc (đã bỏ '%') của một thanh ghi
    pub fn resolve_root_buf<'a>(&'a self, reg: &'a str) -> String {
        let clean = IvlLowerer::clean_name(reg);
        self.buffer_aliases
            .get(reg)
            .or_else(|| self.buffer_aliases.get(clean))
            .map(|s| IvlLowerer::clean_name(s).to_string())
            .unwrap_or_else(|| clean.to_string())
    }

    /// Kiểm tra xem một thanh ghi có đại diện cho một buffer/slice được quản lý bộ nhớ hay không
    pub fn is_known_buffer(&self, reg: &str) -> bool {
        let clean = IvlLowerer::clean_name(reg);
        let root = self.resolve_root_buf(reg);
        self.buffer_sizes.contains_key(clean)
            || self.buffer_sizes.contains_key(&root)
            || self.buffer_aliases.contains_key(clean)
            || self.slice_params.contains(&root)
    }

    /// Lấy biểu thức độ dài (theo bytes) của một buffer/slice nếu biết
    pub fn bound_expr(&self, reg: &str) -> Option<IvlExpr> {
        let clean = IvlLowerer::clean_name(reg);
        let root = self.resolve_root_buf(reg);
        if let Some(&sz) = self.buffer_sizes.get(&root).or_else(|| self.buffer_sizes.get(clean)) {
            Some(IvlExpr::IntConst(sz as i64))
        } else if self.slice_params.contains(&root) {
            Some(IvlExpr::Len(root))
        } else if self.buffer_aliases.contains_key(clean) {
            Some(IvlExpr::Var(format!("{}_len", clean)))
        } else {
            None
        }
    }
}

/// Bộ chuyển đổi toán học: hạ cấp Function trong Light sang các chuỗi kiểm chứng IVL
pub struct IvlLowerer;

impl IvlLowerer {
    #[inline]
    pub fn clean_name(name: &str) -> &str {
        name.trim_start_matches('%')
    }

    pub fn operand_to_expr(op: &Operand) -> IvlExpr {
        match op {
            Operand::Reg(r) => IvlExpr::Var(Self::clean_name(r).to_string()),
            Operand::Const(v) => match v {
                Value::I64(n) => IvlExpr::IntConst(*n),
                Value::U64(n) => IvlExpr::IntConst(*n as i64),
                Value::Bool(b) => IvlExpr::BoolConst(*b),
                Value::Ptr(p) => IvlExpr::IntConst(*p as i64),
            },
        }
    }

    pub fn subst_expr(expr: &IvlExpr, from: &str, to: &IvlExpr) -> IvlExpr {
        let mut map = HashMap::new();
        map.insert(Self::clean_name(from).to_string(), to.clone());
        Self::subst_expr_map(expr, &map)
    }

    /// Thay thế đồng thời nhiều biến cùng lúc (tránh lỗi Variable Capture khi gọi hàm)
    pub fn subst_expr_map(expr: &IvlExpr, map: &HashMap<String, IvlExpr>) -> IvlExpr {
        match expr {
            IvlExpr::Var(v) => {
                let clean = Self::clean_name(v);
                if let Some(to) = map.get(clean) {
                    to.clone()
                } else {
                    expr.clone()
                }
            }
            IvlExpr::IntConst(_) | IvlExpr::BoolConst(_) => expr.clone(),
            IvlExpr::Len(v) => {
                let clean = Self::clean_name(v);
                let len_key = format!("{}_len", clean);
                if let Some(to_len) = map.get(&len_key) {
                    to_len.clone()
                } else if let Some(IvlExpr::Var(to_var)) = map.get(clean) {
                    IvlExpr::Len(to_var.clone())
                } else {
                    expr.clone()
                }
            }
            IvlExpr::Binary { op, lhs, rhs, is_unsigned } => IvlExpr::Binary {
                op: op.clone(),
                lhs: Box::new(Self::subst_expr_map(lhs, map)),
                rhs: Box::new(Self::subst_expr_map(rhs, map)),
                is_unsigned: *is_unsigned,
            },
            IvlExpr::Ite { cond, then_val, else_val } => IvlExpr::Ite {
                cond: Box::new(Self::subst_expr_map(cond, map)),
                then_val: Box::new(Self::subst_expr_map(then_val, map)),
                else_val: Box::new(Self::subst_expr_map(else_val, map)),
            },
            IvlExpr::Not(e) => IvlExpr::Not(Box::new(Self::subst_expr_map(e, map))),
            IvlExpr::BitNot(e) => IvlExpr::BitNot(Box::new(Self::subst_expr_map(e, map))),
            IvlExpr::Mask8(e) => IvlExpr::Mask8(Box::new(Self::subst_expr_map(e, map))),
            IvlExpr::Select { mem, offset } => {
                let clean_mem = Self::clean_name(mem);
                let new_mem = if let Some(IvlExpr::Var(to_var)) = map.get(clean_mem) {
                    to_var.clone()
                } else {
                    mem.clone()
                };
                IvlExpr::Select {
                    mem: new_mem,
                    offset: Box::new(Self::subst_expr_map(offset, map)),
                }
            }
            IvlExpr::Store { mem, offset, val } => {
                let clean_mem = Self::clean_name(mem);
                let new_mem = if let Some(IvlExpr::Var(to_var)) = map.get(clean_mem) {
                    to_var.clone()
                } else {
                    mem.clone()
                };
                IvlExpr::Store {
                    mem: new_mem,
                    offset: Box::new(Self::subst_expr_map(offset, map)),
                    val: Box::new(Self::subst_expr_map(val, map)),
                }
            }
        }
    }

    /// Thu thập danh sách các biến/tham số có kiểu số nguyên không dấu (u64 / u8) kèm thông tin toàn chương trình
    pub fn collect_unsigned_vars_with_prog(func: &Function, program: Option<&Program>) -> HashSet<String> {
        let mut unsigned = HashSet::new();
        let insert_both = |set: &mut HashSet<String>, name: &str| {
            let clean = Self::clean_name(name).to_string();
            set.insert(clean.clone());
            set.insert(format!("%{}", clean));
        };

        let ret_is_unsigned = matches!(func.return_ty, Some(Type::U64 | Type::U8));
        if ret_is_unsigned {
            for r in ["ret", "res", "result"] {
                insert_both(&mut unsigned, r);
            }
        }
        for p in &func.params {
            if matches!(p.ty, Type::U64 | Type::U8) {
                insert_both(&mut unsigned, &p.name);
            }
        }
        for si in &func.instructions {
            match &si.inst {
                Instruction::AssignConst { dest, ty, val } => {
                    if matches!(ty, Type::U64 | Type::U8) || matches!(val, Value::U64(_)) {
                        insert_both(&mut unsigned, dest);
                    }
                }
                Instruction::Binary { dest, ty, .. } => {
                    if matches!(ty, Type::U64 | Type::U8) {
                        insert_both(&mut unsigned, dest);
                    }
                }
                Instruction::Load8 { dest, .. } => {
                    insert_both(&mut unsigned, dest);
                }
                Instruction::Alloc { dest, elem_ty, .. } => {
                    if matches!(elem_ty, Type::U64 | Type::U8) {
                        insert_both(&mut unsigned, dest);
                    }
                }
                Instruction::Call { dest: Some(dest), func_name, .. } => {
                    if let Some(prog) = program {
                        if let Some(callee) = prog.functions.iter().find(|f| &f.name == func_name) {
                            if matches!(callee.return_ty, Some(Type::U64 | Type::U8)) {
                                insert_both(&mut unsigned, dest);
                            }
                        }
                    }
                }
                Instruction::Ret(Some(Operand::Reg(r)))
                | Instruction::RetIf { val: Some(Operand::Reg(r)), .. } if ret_is_unsigned => {
                    insert_both(&mut unsigned, r);
                }
                _ => {}
            }
        }

        // Fixed-point propagation across MOV instructions
        let mut changed = true;
        while changed {
            changed = false;
            for si in &func.instructions {
                if let Instruction::Mov { dest, src } = &si.inst {
                    let s_clean = Self::clean_name(src);
                    let d_clean = Self::clean_name(dest);
                    if unsigned.contains(s_clean) && !unsigned.contains(d_clean) {
                        insert_both(&mut unsigned, d_clean);
                        changed = true;
                    }
                }
            }
        }

        unsigned
    }

    /// Kiểm tra biểu thức có chứa biến hoặc hằng số không dấu hay không
    pub fn expr_has_unsigned(e: &Expr, unsigned_vars: &HashSet<String>) -> bool {
        match e {
            Expr::Var(v) => unsigned_vars.contains(Self::clean_name(v)),
            Expr::Binary { lhs, rhs, .. } => {
                Self::expr_has_unsigned(lhs, unsigned_vars) || Self::expr_has_unsigned(rhs, unsigned_vars)
            }
            Expr::Not(inner) => Self::expr_has_unsigned(inner, unsigned_vars),
            Expr::UIntConst(_) => true,
            Expr::IntConst(_) | Expr::Len(_) | Expr::BoolConst(_) => false,
        }
    }

    #[inline]
    pub fn operand_is_unsigned(op: &Operand, unsigned_vars: &HashSet<String>) -> bool {
        match op {
            Operand::Reg(r) => unsigned_vars.contains(Self::clean_name(r)),
            Operand::Const(Value::U64(_)) => true,
            _ => false,
        }
    }

    /// Hạ cấp biểu thức Expr sang IvlExpr có xét kiểu dấu (signed vs unsigned) cho các phép toán
    pub fn expr_to_ivl_typed(e: &Expr, unsigned_vars: &HashSet<String>) -> IvlExpr {
        match e {
            Expr::Var(v) => IvlExpr::Var(Self::clean_name(v).to_string()),
            Expr::IntConst(n) => IvlExpr::IntConst(*n),
            Expr::UIntConst(u) => IvlExpr::IntConst(*u as i64),
            Expr::BoolConst(b) => IvlExpr::BoolConst(*b),
            Expr::Len(v) => IvlExpr::Len(Self::clean_name(v).to_string()),
            Expr::Binary { op, lhs, rhs } => {
                let is_unsigned = match op {
                    BinOp::Lt | BinOp::Lte | BinOp::Gt | BinOp::Gte | BinOp::Div | BinOp::Mod => {
                        Self::expr_has_unsigned(lhs, unsigned_vars) || Self::expr_has_unsigned(rhs, unsigned_vars)
                    }
                    BinOp::Shr => Self::expr_has_unsigned(lhs, unsigned_vars),
                    _ => false,
                };
                let resolved_op = if matches!(op, BinOp::Shr) && !is_unsigned {
                    BinOp::Sar
                } else {
                    op.clone()
                };
                IvlExpr::Binary {
                    op: resolved_op,
                    lhs: Box::new(Self::expr_to_ivl_typed(lhs, unsigned_vars)),
                    rhs: Box::new(Self::expr_to_ivl_typed(rhs, unsigned_vars)),
                    is_unsigned,
                }
            }
            Expr::Not(inner) => IvlExpr::Not(Box::new(Self::expr_to_ivl_typed(inner, unsigned_vars))),
        }
    }

    /// Trích xuất tự động mọi biến vô hướng và bộ nhớ bị sửa đổi trực tiếp từ chuỗi 4 lệnh IVL!
    /// (Chuẩn kiến trúc Boogie: không cần quét thủ công từng Instruction của ngôn ngữ nguồn)
    pub fn extract_modified_targets_from_ivl(stmts: &[IvlStmt]) -> (Vec<String>, Vec<String>) {
        let mut scalar_set = HashSet::new();
        let mut mem_set = HashSet::new();

        for st in stmts {
            match st {
                IvlStmt::Assign { dest, is_memory, .. } => {
                    let clean = Self::clean_name(dest);
                    // Bỏ qua các biến tạm nội bộ của hệ thống đường dẫn/nhánh/vòng lặp
                    if clean.starts_with("__") {
                        continue;
                    }
                    if *is_memory {
                        mem_set.insert(clean.to_string());
                    } else {
                        scalar_set.insert(clean.to_string());
                    }
                }
                IvlStmt::Havoc { vars, is_memory } => {
                    for v in vars {
                        let clean = Self::clean_name(v);
                        if clean.starts_with("__") {
                            continue;
                        }
                        if *is_memory {
                            mem_set.insert(clean.to_string());
                        } else {
                            scalar_set.insert(clean.to_string());
                        }
                    }
                }
                _ => {}
            }
        }

        let mut scalars: Vec<String> = scalar_set.into_iter().collect();
        scalars.sort();
        let mut mems: Vec<String> = mem_set.into_iter().collect();
        mems.sort();
        (scalars, mems)
    }

    /// Thu thập đồng thời kích thước tĩnh của các buffer và chuỗi bí danh (alias) chỉ trong 1 pass fixed-point duy nhất
    pub fn extract_buffers_and_aliases(
        func: &Function,
        slice_params: &HashSet<String>,
    ) -> (HashMap<String, usize>, HashMap<String, String>) {
        let mut buffer_sizes = HashMap::new();
        let mut aliases = HashMap::new();

        for sp in slice_params {
            aliases.insert(sp.clone(), sp.clone());
            aliases.insert(format!("%{}", sp), sp.clone());
        }

        for s_inst in &func.instructions {
            if let Instruction::Alloc { dest, elem_ty, len } = &s_inst.inst {
                let clean = Self::clean_name(dest).to_string();
                let byte_len = len.saturating_mul(elem_ty.byte_size());
                buffer_sizes.insert(dest.clone(), byte_len);
                buffer_sizes.insert(clean, byte_len);
            }
        }

        let mut changed = true;
        while changed {
            changed = false;
            for s_inst in &func.instructions {
                if let Instruction::SlicePtr { dest, slice: src } | Instruction::Mov { dest, src } = &s_inst.inst {
                    let s_clean = Self::clean_name(src).to_string();
                    let d_clean = Self::clean_name(dest).to_string();

                    if let Some(&sz) = buffer_sizes.get(src).or_else(|| buffer_sizes.get(&s_clean)) {
                        if !buffer_sizes.contains_key(&d_clean) {
                            buffer_sizes.insert(dest.clone(), sz);
                            buffer_sizes.insert(d_clean.clone(), sz);
                            changed = true;
                        }
                    }

                    let root_opt = if let Some(r) = aliases.get(src).or_else(|| aliases.get(&s_clean)).cloned() {
                        Some(r)
                    } else if matches!(s_inst.inst, Instruction::SlicePtr { .. })
                        || buffer_sizes.contains_key(src)
                        || buffer_sizes.contains_key(&s_clean)
                        || slice_params.contains(&s_clean)
                    {
                        Some(s_clean)
                    } else {
                        None
                    };

                    if let Some(root) = root_opt {
                        if !aliases.contains_key(&d_clean) {
                            aliases.insert(dest.clone(), root.clone());
                            aliases.insert(d_clean, root);
                            changed = true;
                        }
                    }
                }
            }
        }

        (buffer_sizes, aliases)
    }

    /// Hạ cấp DUY NHẤT (Single Source of Truth) một lệnh đơn lẻ thành chuỗi 4 vi lệnh IVL
    /// Kèm đầy đủ cả Safety Checks (bounds, alignment, div-by-zero, overflow, call contracts) lẫn State Transitions!
    pub fn lower_atomic_instruction(
        func: &Function,
        s_inst: &SpannedInstruction,
        ctx: &FunctionBufferContext,
        program: Option<&Program>,
    ) -> Vec<IvlStmt> {
        let mut stmts = Vec::new();

        match &s_inst.inst {
            Instruction::Assert(e) => {
                stmts.push(IvlStmt::Assert {
                    cond: Self::expr_to_ivl_typed(e, &ctx.unsigned_vars),
                    goal_name: format!("Function '{}' - Line {}: Verify ASSERT directive", func.name, s_inst.loc.line),
                    category: PropertyCategory::Functional,
                    loc: s_inst.loc.clone(),
                });
            }

            Instruction::AssignConst { dest, val, .. } => {
                stmts.push(IvlStmt::Assign {
                    dest: Self::clean_name(dest).to_string(),
                    expr: Self::operand_to_expr(&Operand::Const(val.clone())),
                    is_memory: false,
                });
            }

            Instruction::Mov { dest, src } | Instruction::SlicePtr { dest, slice: src } => {
                let s_clean = Self::clean_name(src);
                let d_clean = Self::clean_name(dest);
                if ctx.is_known_buffer(src) {
                    stmts.push(IvlStmt::Assign {
                        dest: d_clean.to_string(),
                        expr: IvlExpr::IntConst(0),
                        is_memory: false,
                    });
                    let root = ctx.resolve_root_buf(src);
                    let len_expr = if let Some(&sz) = ctx.buffer_sizes.get(&root).or_else(|| ctx.buffer_sizes.get(s_clean)) {
                        IvlExpr::IntConst(sz as i64)
                    } else {
                        IvlExpr::Var(format!("{}_len", root))
                    };
                    stmts.push(IvlStmt::Assign {
                        dest: format!("{}_len", d_clean),
                        expr: len_expr,
                        is_memory: false,
                    });
                } else {
                    stmts.push(IvlStmt::Assign {
                        dest: d_clean.to_string(),
                        expr: IvlExpr::Var(s_clean.to_string()),
                        is_memory: false,
                    });
                }
            }

            Instruction::Binary { op, ty, dest, src1, src2 } => {
                let e1 = Self::operand_to_expr(src1);
                let e2 = Self::operand_to_expr(src2);
                let is_unsigned = matches!(ty, Type::U64 | Type::U8)
                    || (matches!(
                        op,
                        BinOp::Lt | BinOp::Lte | BinOp::Gt | BinOp::Gte | BinOp::Div | BinOp::Mod
                    ) && (Self::operand_is_unsigned(src1, &ctx.unsigned_vars)
                        || Self::operand_is_unsigned(src2, &ctx.unsigned_vars)))
                    || (matches!(op, BinOp::Shr)
                        && Self::operand_is_unsigned(src1, &ctx.unsigned_vars));

                // Safety Check cho phép chia (Div / Mod)
                if matches!(op, BinOp::Div | BinOp::Mod) {
                    if is_unsigned {
                        let div_zero = IvlExpr::Binary {
                            op: BinOp::Neq,
                            lhs: Box::new(e2.clone()),
                            rhs: Box::new(IvlExpr::IntConst(0)),
                            is_unsigned: true,
                        };
                        stmts.push(IvlStmt::Assert {
                            cond: div_zero,
                            goal_name: format!("Function '{}' - Line {}: Unsigned Division-by-Zero safety check", func.name, s_inst.loc.line),
                            category: PropertyCategory::Safety,
                            loc: s_inst.loc.clone(),
                        });
                    } else {
                        let div_zero = IvlExpr::Binary {
                            op: BinOp::Neq,
                            lhs: Box::new(e2.clone()),
                            rhs: Box::new(IvlExpr::IntConst(0)),
                            is_unsigned: false,
                        };
                        let overflow_cond = IvlExpr::Binary {
                            op: BinOp::And,
                            lhs: Box::new(IvlExpr::Binary {
                                op: BinOp::Eq,
                                lhs: Box::new(e1.clone()),
                                rhs: Box::new(IvlExpr::IntConst(i64::MIN)),
                                is_unsigned: false,
                            }),
                            rhs: Box::new(IvlExpr::Binary {
                                op: BinOp::Eq,
                                lhs: Box::new(e2.clone()),
                                rhs: Box::new(IvlExpr::IntConst(-1)),
                                is_unsigned: false,
                            }),
                            is_unsigned: false,
                        };
                        let safe_div = IvlExpr::Binary {
                            op: BinOp::And,
                            lhs: Box::new(div_zero),
                            rhs: Box::new(IvlExpr::Not(Box::new(overflow_cond))),
                            is_unsigned: false,
                        };
                        stmts.push(IvlStmt::Assert {
                            cond: safe_div,
                            goal_name: format!("Function '{}' - Line {}: Division-by-Zero safety and Overflow check", func.name, s_inst.loc.line),
                            category: PropertyCategory::Safety,
                            loc: s_inst.loc.clone(),
                        });
                    }
                }

                stmts.push(IvlStmt::Assign {
                    dest: Self::clean_name(dest).to_string(),
                    expr: IvlExpr::Binary {
                        op: op.clone(),
                        lhs: Box::new(e1),
                        rhs: Box::new(e2),
                        is_unsigned,
                    },
                    is_memory: false,
                });
            }

            Instruction::Not { dest, ty, src } => {
                let e = Self::operand_to_expr(src);
                let expr = if matches!(ty, Type::Bool) {
                    IvlExpr::Not(Box::new(e))
                } else {
                    IvlExpr::BitNot(Box::new(e))
                };
                stmts.push(IvlStmt::Assign {
                    dest: Self::clean_name(dest).to_string(),
                    expr,
                    is_memory: false,
                });
            }

            Instruction::Alloc { dest, elem_ty, len } => {
                let clean = Self::clean_name(dest);
                let byte_len = len.saturating_mul(elem_ty.byte_size());
                stmts.push(IvlStmt::Assign {
                    dest: format!("{}_len", clean),
                    expr: IvlExpr::IntConst(byte_len as i64),
                    is_memory: false,
                });
            }

            Instruction::SliceLen { dest, slice } => {
                let root = ctx.resolve_root_buf(slice);
                let sl_clean = Self::clean_name(slice);
                let len_expr = if let Some(&size) = ctx.buffer_sizes.get(&root).or_else(|| ctx.buffer_sizes.get(sl_clean)) {
                    IvlExpr::IntConst(size as i64)
                } else {
                    IvlExpr::Var(format!("{}_len", sl_clean))
                };
                stmts.push(IvlStmt::Assign {
                    dest: Self::clean_name(dest).to_string(),
                    expr: len_expr,
                    is_memory: false,
                });
            }

            Instruction::Load8 { dest, buf, offset } => {
                Self::emit_mem8_checks(func, s_inst, buf, offset, ctx, &mut stmts);
                let root_buf = ctx.resolve_root_buf(buf);
                let off_expr = Self::operand_to_expr(offset);
                let clean_d = Self::clean_name(dest).to_string();
                stmts.push(IvlStmt::Assign {
                    dest: clean_d.clone(),
                    expr: IvlExpr::Mask8(Box::new(IvlExpr::Select {
                        mem: root_buf,
                        offset: Box::new(off_expr),
                    })),
                    is_memory: false,
                });
                stmts.push(IvlStmt::Assume {
                    cond: IvlExpr::Binary {
                        op: BinOp::And,
                        lhs: Box::new(IvlExpr::Binary {
                            op: BinOp::Gte,
                            lhs: Box::new(IvlExpr::Var(clean_d.clone())),
                            rhs: Box::new(IvlExpr::IntConst(0)),
                            is_unsigned: false,
                        }),
                        rhs: Box::new(IvlExpr::Binary {
                            op: BinOp::Lte,
                            lhs: Box::new(IvlExpr::Var(clean_d)),
                            rhs: Box::new(IvlExpr::IntConst(255)),
                            is_unsigned: false,
                        }),
                        is_unsigned: false,
                    },
                });
            }

            Instruction::Store8 { buf, offset, val } => {
                Self::emit_mem8_checks(func, s_inst, buf, offset, ctx, &mut stmts);
                let root_buf = ctx.resolve_root_buf(buf);
                let off_expr = Self::operand_to_expr(offset);
                let val_expr = Self::operand_to_expr(val);
                stmts.push(IvlStmt::Assign {
                    dest: root_buf.clone(),
                    expr: IvlExpr::Store {
                        mem: root_buf,
                        offset: Box::new(off_expr),
                        val: Box::new(IvlExpr::Mask8(Box::new(val_expr))),
                    },
                    is_memory: true,
                });
            }

            Instruction::Load64 { dest, buf, offset } => {
                Self::emit_mem64_checks(func, s_inst, buf, offset, ctx, &mut stmts);
                let root_buf = ctx.resolve_root_buf(buf);
                let off_expr = Self::operand_to_expr(offset);
                stmts.push(IvlStmt::Assign {
                    dest: Self::clean_name(dest).to_string(),
                    expr: IvlExpr::Select {
                        mem: root_buf,
                        offset: Box::new(off_expr),
                    },
                    is_memory: false,
                });
            }

            Instruction::Store64 { buf, offset, val } => {
                Self::emit_mem64_checks(func, s_inst, buf, offset, ctx, &mut stmts);
                let root_buf = ctx.resolve_root_buf(buf);
                let off_expr = Self::operand_to_expr(offset);
                let val_expr = Self::operand_to_expr(val);
                stmts.push(IvlStmt::Assign {
                    dest: root_buf.clone(),
                    expr: IvlExpr::Store {
                        mem: root_buf,
                        offset: Box::new(off_expr),
                        val: Box::new(val_expr),
                    },
                    is_memory: true,
                });
            }

            Instruction::StoreStr { buf, offset, content } => {
                let root_buf = ctx.resolve_root_buf(buf);
                let buf_size = ctx
                    .buffer_sizes
                    .get(&root_buf)
                    .or_else(|| ctx.buffer_sizes.get(Self::clean_name(buf)))
                    .copied()
                    .unwrap_or(0);
                let bytes = content.as_bytes();
                let req_size = *offset + bytes.len();
                stmts.push(IvlStmt::Assert {
                    cond: IvlExpr::BoolConst(req_size <= buf_size),
                    goal_name: format!("Function '{}' - Line {}: String write within buffer '{}'", func.name, s_inst.loc.line, buf),
                    category: PropertyCategory::Safety,
                    loc: s_inst.loc.clone(),
                });

                for (i, &b) in bytes.iter().enumerate() {
                    let off_expr = IvlExpr::IntConst((*offset + i) as i64);
                    let val_expr = IvlExpr::IntConst(b as i64);
                    stmts.push(IvlStmt::Assign {
                        dest: root_buf.clone(),
                        expr: IvlExpr::Store {
                            mem: root_buf.clone(),
                            offset: Box::new(off_expr),
                            val: Box::new(val_expr),
                        },
                        is_memory: true,
                    });
                }
            }

            Instruction::Call { dest, func_name, args } => {
                if let Some(prog) = program {
                    if let Some(callee) = prog.functions.iter().find(|f| &f.name == func_name) {
                        if args.len() != callee.params.len() {
                            stmts.push(IvlStmt::Assert {
                                cond: IvlExpr::BoolConst(false),
                                goal_name: format!(
                                    "Function '{}' - Line {}: Call argument count mismatch for '{}' (expected {}, got {})",
                                    func.name,
                                    s_inst.loc.line,
                                    func_name,
                                    callee.params.len(),
                                    args.len()
                                ),
                                category: PropertyCategory::Safety,
                                loc: s_inst.loc.clone(),
                            });
                        }

                        // Xây dựng bảng ánh xạ tham số đồng thời (Simultaneous Substitution Map)
                        let mut param_map = HashMap::new();
                        for (i, p) in callee.params.iter().enumerate() {
                            if i < args.len() {
                                let p_clean = Self::clean_name(&p.name).to_string();
                                let arg_expr = Self::operand_to_expr(&args[i]);
                                if let Operand::Reg(r) = &args[i] {
                                    if let Some(b_expr) = ctx.bound_expr(r) {
                                        let len_expr = match b_expr {
                                            IvlExpr::Len(root_name) => IvlExpr::Var(format!("{}_len", root_name)),
                                            other => other,
                                        };
                                        param_map.insert(format!("{}_len", p_clean), len_expr);
                                    }
                                }
                                param_map.insert(p_clean, arg_expr);
                            }
                        }

                        let callee_unsigned = Self::collect_unsigned_vars_with_prog(callee, program);
                        for c_si in &callee.instructions {
                            if let Instruction::Require(req) = &c_si.inst {
                                let req_ivl = Self::expr_to_ivl_typed(req, &callee_unsigned);
                                let subst_req = Self::subst_expr_map(&req_ivl, &param_map);
                                stmts.push(IvlStmt::Assert {
                                    cond: subst_req,
                                    goal_name: format!("Function '{}' - Line {}: Verify REQUIRE contract of '{}'", func.name, s_inst.loc.line, func_name),
                                    category: PropertyCategory::Safety,
                                    loc: s_inst.loc.clone(),
                                });
                            }
                        }

                        // Havoc all memory buffers passed as slice/pointer arguments to the callee
                        Self::emit_havoc_for_buffer_args(args.iter(), ctx, &mut stmts);

                        if let Some(d) = dest {
                            let clean_d = Self::clean_name(d).to_string();
                            stmts.push(IvlStmt::Havoc {
                                vars: vec![clean_d.clone()],
                                is_memory: false,
                            });
                            let callee_ret = crate::verifier::Verifier::find_canonical_ret_var(callee)
                                .unwrap_or_else(|| "ret".to_string());
                            let mut ens_map = param_map;
                            ens_map.insert(
                                Self::clean_name(&callee_ret).to_string(),
                                IvlExpr::Var(clean_d),
                            );
                            for c_si in &callee.instructions {
                                if let Instruction::Ensure(ens) = &c_si.inst {
                                    let ens_ivl = Self::expr_to_ivl_typed(ens, &callee_unsigned);
                                    let subst_ens = Self::subst_expr_map(&ens_ivl, &ens_map);
                                    stmts.push(IvlStmt::Assume { cond: subst_ens });
                                }
                            }
                        }
                    } else {
                        stmts.push(IvlStmt::Assert {
                            cond: IvlExpr::BoolConst(false),
                            goal_name: format!("Function '{}' - Line {}: Call to undefined function '{}'", func.name, s_inst.loc.line, func_name),
                            category: PropertyCategory::Safety,
                            loc: s_inst.loc.clone(),
                        });
                    }
                }
            }

            Instruction::Syscall { dest, rax, rdi, rsi, rdx, r10, r8, r9 } => {
                let target = dest.clone().or_else(|| Some("rax".to_string()));
                if let Some(d) = target {
                    let clean_d = Self::clean_name(&d).to_string();
                    stmts.push(IvlStmt::Havoc {
                        vars: vec![clean_d.clone()],
                        is_memory: false,
                    });
                    // 1. Mọi syscall trên Linux Kernel x86_64 khi lỗi đều trả về trong khoảng -4095..-1 (luôn >= -4096)
                    stmts.push(IvlStmt::Assume {
                        cond: IvlExpr::Binary {
                            op: BinOp::Gte,
                            lhs: Box::new(IvlExpr::Var(clean_d.clone())),
                            rhs: Box::new(IvlExpr::IntConst(-4096)),
                            is_unsigned: false,
                        },
                    });
                    // 2. sys_read (rax=0) và sys_write (rax=1) không bao giờ đọc/ghi vượt quá count (rdx)
                    let rax_expr = Self::operand_to_expr(rax);
                    let rdx_expr = Self::operand_to_expr(rdx);
                    let is_read_or_write = IvlExpr::Binary {
                        op: BinOp::Or,
                        lhs: Box::new(IvlExpr::Binary {
                            op: BinOp::Eq,
                            lhs: Box::new(rax_expr.clone()),
                            rhs: Box::new(IvlExpr::IntConst(0)),
                            is_unsigned: false,
                        }),
                        rhs: Box::new(IvlExpr::Binary {
                            op: BinOp::Eq,
                            lhs: Box::new(rax_expr),
                            rhs: Box::new(IvlExpr::IntConst(1)),
                            is_unsigned: false,
                        }),
                        is_unsigned: false,
                    };
                    let lte_count = IvlExpr::Binary {
                        op: BinOp::Lte,
                        lhs: Box::new(IvlExpr::Var(clean_d)),
                        rhs: Box::new(rdx_expr),
                        is_unsigned: false,
                    };
                    stmts.push(IvlStmt::Assume {
                        cond: IvlExpr::Ite {
                            cond: Box::new(is_read_or_write),
                            then_val: Box::new(lte_count),
                            else_val: Box::new(IvlExpr::BoolConst(true)),
                        },
                    });
                }

                // Havoc buffer memory for any buffer passed in syscall arguments
                let sys_args = [Some(rdi), Some(rsi), Some(rdx), r10.as_ref(), r8.as_ref(), r9.as_ref()];
                Self::emit_havoc_for_buffer_args(sys_args.into_iter().flatten(), ctx, &mut stmts);
            }

            _ => {}
        }

        stmts
    }

    fn emit_havoc_for_buffer_args<'a, I>(
        args: I,
        ctx: &FunctionBufferContext,
        stmts: &mut Vec<IvlStmt>,
    ) where
        I: Iterator<Item = &'a Operand>,
    {
        let mut havoc_mems = Vec::new();
        for a in args {
            if let Operand::Reg(r) = a {
                if ctx.is_known_buffer(r) {
                    let root = ctx.resolve_root_buf(r);
                    if !havoc_mems.contains(&root) {
                        havoc_mems.push(root);
                    }
                }
            }
        }
        if !havoc_mems.is_empty() {
            stmts.push(IvlStmt::Havoc {
                vars: havoc_mems,
                is_memory: true,
            });
        }
    }

    fn emit_mem8_checks(
        func: &Function,
        s_inst: &SpannedInstruction,
        buf: &str,
        offset: &Operand,
        ctx: &FunctionBufferContext,
        stmts: &mut Vec<IvlStmt>,
    ) {
        let off_expr = Self::operand_to_expr(offset);
        if let Some(bound_expr) = ctx.bound_expr(buf) {
            let in_bounds = IvlExpr::Binary {
                op: BinOp::And,
                lhs: Box::new(IvlExpr::Binary {
                    op: BinOp::Gte,
                    lhs: Box::new(off_expr.clone()),
                    rhs: Box::new(IvlExpr::IntConst(0)),
                    is_unsigned: false,
                }),
                rhs: Box::new(IvlExpr::Binary {
                    op: BinOp::Lt,
                    lhs: Box::new(off_expr),
                    rhs: Box::new(bound_expr),
                    is_unsigned: false,
                }),
                is_unsigned: false,
            };
            stmts.push(IvlStmt::Assert {
                cond: in_bounds,
                goal_name: format!("Function '{}' - Line {}: Memory 8-bit bounds check on '{}'", func.name, s_inst.loc.line, buf),
                category: PropertyCategory::Safety,
                loc: s_inst.loc.clone(),
            });
        } else {
            let non_neg = IvlExpr::Binary {
                op: BinOp::Gte,
                lhs: Box::new(off_expr),
                rhs: Box::new(IvlExpr::IntConst(0)),
                is_unsigned: false,
            };
            stmts.push(IvlStmt::Assert {
                cond: non_neg,
                goal_name: format!("Function '{}' - Line {}: Memory 8-bit pointer offset non-negative check on '{}'", func.name, s_inst.loc.line, buf),
                category: PropertyCategory::Safety,
                loc: s_inst.loc.clone(),
            });
        }
    }

    fn emit_mem64_checks(
        func: &Function,
        s_inst: &SpannedInstruction,
        buf: &str,
        offset: &Operand,
        ctx: &FunctionBufferContext,
        stmts: &mut Vec<IvlStmt>,
    ) {
        let off_expr = Self::operand_to_expr(offset);

        // 1. 8-byte alignment check
        let align_check = IvlExpr::Binary {
            op: BinOp::Eq,
            lhs: Box::new(IvlExpr::Binary {
                op: BinOp::Mod,
                lhs: Box::new(off_expr.clone()),
                rhs: Box::new(IvlExpr::IntConst(8)),
                is_unsigned: false,
            }),
            rhs: Box::new(IvlExpr::IntConst(0)),
            is_unsigned: false,
        };
        stmts.push(IvlStmt::Assert {
            cond: align_check,
            goal_name: format!("Function '{}' - Line {}: Memory 64-bit 8-byte alignment check on '{}'", func.name, s_inst.loc.line, buf),
            category: PropertyCategory::Safety,
            loc: s_inst.loc.clone(),
        });

        // 2. Bounds check (chống cả tràn dưới len < 8 trên slice!)
        let root_buf = ctx.resolve_root_buf(buf);
        if let Some(&sz) = ctx.buffer_sizes.get(&root_buf).or_else(|| ctx.buffer_sizes.get(Self::clean_name(buf))) {
            let in_bounds = if sz < 8 {
                IvlExpr::BoolConst(false)
            } else {
                let max_off = (sz as i64) - 8;
                IvlExpr::Binary {
                    op: BinOp::And,
                    lhs: Box::new(IvlExpr::Binary {
                        op: BinOp::Gte,
                        lhs: Box::new(off_expr.clone()),
                        rhs: Box::new(IvlExpr::IntConst(0)),
                        is_unsigned: false,
                    }),
                    rhs: Box::new(IvlExpr::Binary {
                        op: BinOp::Lte,
                        lhs: Box::new(off_expr),
                        rhs: Box::new(IvlExpr::IntConst(max_off)),
                        is_unsigned: false,
                    }),
                    is_unsigned: false,
                }
            };
            stmts.push(IvlStmt::Assert {
                cond: in_bounds,
                goal_name: format!("Function '{}' - Line {}: Memory 64-bit bounds check on '{}'", func.name, s_inst.loc.line, buf),
                category: PropertyCategory::Safety,
                loc: s_inst.loc.clone(),
            });
        } else if let Some(bound_expr) = ctx.bound_expr(buf) {
            // Đảm bảo: offset >= 0 && bound >= 8 && offset <= bound - 8 (tránh underflow khi bound < 8)
            let max_off = IvlExpr::Binary {
                op: BinOp::Sub,
                lhs: Box::new(bound_expr.clone()),
                rhs: Box::new(IvlExpr::IntConst(8)),
                is_unsigned: false,
            };
            let len_at_least_8 = IvlExpr::Binary {
                op: BinOp::Gte,
                lhs: Box::new(bound_expr),
                rhs: Box::new(IvlExpr::IntConst(8)),
                is_unsigned: false,
            };
            let off_in_range = IvlExpr::Binary {
                op: BinOp::And,
                lhs: Box::new(IvlExpr::Binary {
                    op: BinOp::Gte,
                    lhs: Box::new(off_expr.clone()),
                    rhs: Box::new(IvlExpr::IntConst(0)),
                    is_unsigned: false,
                }),
                rhs: Box::new(IvlExpr::Binary {
                    op: BinOp::Lte,
                    lhs: Box::new(off_expr),
                    rhs: Box::new(max_off),
                    is_unsigned: false,
                }),
                is_unsigned: false,
            };
            let in_bounds = IvlExpr::Binary {
                op: BinOp::And,
                lhs: Box::new(len_at_least_8),
                rhs: Box::new(off_in_range),
                is_unsigned: false,
            };
            stmts.push(IvlStmt::Assert {
                cond: in_bounds,
                goal_name: format!("Function '{}' - Line {}: Memory 64-bit bounds check on '{}'", func.name, s_inst.loc.line, buf),
                category: PropertyCategory::Safety,
                loc: s_inst.loc.clone(),
            });
        } else {
            let non_neg = IvlExpr::Binary {
                op: BinOp::Gte,
                lhs: Box::new(off_expr),
                rhs: Box::new(IvlExpr::IntConst(0)),
                is_unsigned: false,
            };
            stmts.push(IvlStmt::Assert {
                cond: non_neg,
                goal_name: format!("Function '{}' - Line {}: Memory 64-bit pointer offset non-negative check on '{}'", func.name, s_inst.loc.line, buf),
                category: PropertyCategory::Safety,
                loc: s_inst.loc.clone(),
            });
        }
    }
}
