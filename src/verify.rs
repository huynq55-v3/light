// File: src/verify.rs (Ngân sách: < 250 dòng - Thực tế: ~175 dòng)
use crate::ir::*;
use std::collections::HashMap;
use z3::ast::{Ast, BV, Bool};
use z3::{Config, Context, SatResult, Solver};

pub struct Verifier<'ctx> {
    ctx: &'ctx Context,
    solver: Solver<'ctx>,
    layouts: &'ctx [Layout],
    regs: HashMap<Reg, BV<'ctx>>,
    reg_tys: HashMap<Reg, Type>,
}

impl<'ctx> Verifier<'ctx> {
    /// Hàm kiểm chứng một câu lệnh bất khả xâm phạm:
    /// Muốn chứng minh `cond` LUÔN ĐÚNG, ta đẩy `!cond` vào Z3.
    /// Nếu Z3 tìm ra nghiệm (SAT) -> Có trường hợp gây lỗi -> Trả về Phản ví dụ (Counter-example)!
    fn check(&self, cond: &Bool<'ctx>, err_msg: &str) -> Result<(), String> {
        self.solver.push();
        self.solver.assert(&cond.not());
        let res = self.solver.check();
        let out = match res {
            SatResult::Unsat => Ok(()), // Tuyệt đối an toàn!
            SatResult::Sat => {
                let model = self.solver.get_model().unwrap();
                Err(format!(
                    "[VERIFY FAILED] {} | Counter-example:\n{:?}",
                    err_msg, model
                ))
            }
            SatResult::Unknown => Err(format!(
                "[VERIFY TIMEOUT] Không thể chứng minh: {}",
                err_msg
            )),
        };
        self.solver.pop(1);
        out
    }

    /// Khai báo một thanh ghi SSA mới vào không gian Z3 (Mọi thanh ghi đều mở rộng lên BV64)
    fn decl_reg(&mut self, r: Reg, ty: Type) -> BV<'ctx> {
        let bv = BV::new_const(self.ctx, format!("r{}", r), 64);
        // Nếu kiểu nhỏ hơn 64-bit (Bv8, Bv16, Bv32), khóa chặt các bit cao bằng 0
        let bits = match ty {
            Type::Bv8 => 8,
            Type::Bv16 => 16,
            Type::Bv32 => 32,
            Type::Bv64 | Type::Ptr { .. } | Type::Io { .. } => 64,
        };
        if bits < 64 {
            let max_val = BV::from_u64(self.ctx, (1u64 << bits) - 1, 64);
            self.solver.assert(&bv.bvule(&max_val));
        }
        self.regs.insert(r, bv.clone());
        self.reg_tys.insert(r, ty);
        bv
    }

    fn get_reg(&self, r: Reg) -> Result<&BV<'ctx>, String> {
        self.regs
            .get(&r)
            .ok_or_else(|| format!("Biến SSA %{} chưa được khởi tạo", r))
    }

    /// Dịch cây biểu thức Z3Expr sang kiểu Bool/BV của Z3
    /// `field_val` chỉ được truyền vào khi đang kiểm tra điều kiện `@inv` lúc Store/Load
    fn eval_z3_bv(&self, expr: &Z3Expr, field_val: Option<&BV<'ctx>>) -> Result<BV<'ctx>, String> {
        match expr {
            Z3Expr::Reg(r) => Ok(self.get_reg(*r)?.clone()),
            Z3Expr::FieldVal => field_val
                .cloned()
                .ok_or_else(|| "Dùng FieldVal ngoài @inv".into()),
            Z3Expr::Const(v) => Ok(BV::from_u64(self.ctx, *v, 64)),
            Z3Expr::Bin(op, l, r) => {
                let lhs = self.eval_z3_bv(l, field_val)?;
                let rhs = self.eval_z3_bv(r, field_val)?;
                Ok(self.eval_binop(*op, &lhs, &rhs))
            }
            Z3Expr::And(l, r) => Ok(self
                .eval_z3_bv(l, field_val)?
                .bvand(&self.eval_z3_bv(r, field_val)?)),
            Z3Expr::Or(l, r) => Ok(self
                .eval_z3_bv(l, field_val)?
                .bvor(&self.eval_z3_bv(r, field_val)?)),
            Z3Expr::Not(e) => Ok(self.eval_z3_bv(e, field_val)?.bvnot()),
            _ => Err("Biểu thức logic (Cmp/And/Or/Not) không thể dùng làm giá trị số BV".into()),
        }
    }

    fn eval_z3_bool(
        &self,
        expr: &Z3Expr,
        field_val: Option<&BV<'ctx>>,
    ) -> Result<Bool<'ctx>, String> {
        match expr {
            Z3Expr::Cmp(op, l, r) => {
                let lhs = self.eval_z3_bv(l, field_val)?;
                let rhs = self.eval_z3_bv(r, field_val)?;
                Ok(self.eval_cmpop(*op, &lhs, &rhs))
            }
            Z3Expr::And(l, r) => Ok(Bool::and(
                self.ctx,
                &[
                    &self.eval_z3_bool(l, field_val)?,
                    &self.eval_z3_bool(r, field_val)?,
                ],
            )),
            Z3Expr::Or(l, r) => Ok(Bool::or(
                self.ctx,
                &[
                    &self.eval_z3_bool(l, field_val)?,
                    &self.eval_z3_bool(r, field_val)?,
                ],
            )),
            Z3Expr::Not(e) => Ok(self.eval_z3_bool(e, field_val)?.not()),
            _ => Err("Biểu thức đòi hỏi kiểu logic Bool (Cmp/And/Or/Not)".into()),
        }
    }

    /// Bảng ánh xạ 1:1 từ BinOp sang phép toán BitVector của Z3
    fn eval_binop(&self, op: BinOp, lhs: &BV<'ctx>, rhs: &BV<'ctx>) -> BV<'ctx> {
        match op {
            BinOp::Add => lhs.bvadd(rhs),
            BinOp::Sub => lhs.bvsub(rhs),
            BinOp::Mul => lhs.bvmul(rhs),
            BinOp::UDiv => lhs.bvudiv(rhs),
            BinOp::SDiv => lhs.bvsdiv(rhs),
            BinOp::URem => lhs.bvurem(rhs),
            BinOp::SRem => lhs.bvsrem(rhs),
            BinOp::And => lhs.bvand(rhs),
            BinOp::Or => lhs.bvor(rhs),
            BinOp::Xor => lhs.bvxor(rhs),
            BinOp::Shl => lhs.bvshl(rhs),
            BinOp::LShr => lhs.bvlshr(rhs),
            BinOp::AShr => lhs.bvashr(rhs),
        }
    }

    /// Bảng ánh xạ 1:1 từ CmpOp sang phép so sánh BitVector của Z3
    fn eval_cmpop(&self, op: CmpOp, lhs: &BV<'ctx>, rhs: &BV<'ctx>) -> Bool<'ctx> {
        match op {
            CmpOp::Eq => lhs._eq(rhs),
            CmpOp::Ne => lhs._eq(rhs).not(),
            CmpOp::Ult => lhs.bvult(rhs),
            CmpOp::Ule => lhs.bvule(rhs),
            CmpOp::Ugt => lhs.bvugt(rhs),
            CmpOp::Uge => lhs.bvuge(rhs),
            CmpOp::Slt => lhs.bvslt(rhs),
            CmpOp::Sle => lhs.bvsle(rhs),
            CmpOp::Sgt => lhs.bvsgt(rhs),
            CmpOp::Sge => lhs.bvsge(rhs),
        }
    }

    /// Kiểm tra hợp lệ con trỏ `Ptr` và tìm `FieldDef` tương ứng với `offset`
    fn check_ptr_access(&self, base: Reg, offset: u32) -> Result<&'ctx FieldDef, String> {
        let ty = self.reg_tys.get(&base).ok_or("Biến base không tồn tại")?;
        let (layout_id, max_elems) = match ty {
            Type::Ptr {
                layout_id,
                max_elems,
            } => (*layout_id as usize, *max_elems),
            _ => return Err(format!("Biến %{} không phải kiểu con trỏ Ptr", base)),
        };
        let layout = self
            .layouts
            .get(layout_id)
            .ok_or("layout_id không tồn tại")?;

        // 1. Kiểm tra con trỏ khác NULL (base != 0)
        let base_bv = self.get_reg(base)?;
        let zero = BV::from_u64(self.ctx, 0, 64);
        self.check(
            &base_bv._eq(&zero).not(),
            &format!("Null pointer dereference tại %{}", base),
        )?;

        // 2. Kiểm tra giới hạn vùng nhớ (offset < max_elems * layout.size)
        let max_bytes = max_elems.saturating_mul(layout.size);
        if offset >= max_bytes {
            return Err(format!(
                "Tràn vùng nhớ Ptr: offset {} >= max_bytes {}",
                offset, max_bytes
            ));
        }

        // 3. Kiểm tra căn lề trường dữ liệu trong Layout (offset % layout.size phải khớp 1 FieldDef)
        let field_offset = offset % layout.size;
        layout
            .fields
            .iter()
            .find(|f| f.offset == field_offset)
            .ok_or_else(|| {
                format!(
                    "Truy cập sai lệch offset {} trong Layout '{}'",
                    field_offset, layout.name
                )
            })
    }
}

/// Kiểm tra tính hợp lệ khi truyền Thẻ quyền năng (Capability Subtyping / Attenuation):
/// Cho phép thu hẹp quyền: io<a,b> -> io<c,d> nếu [c,d] nằm gọn trong [a,b]
/// Cho phép thu hẹp vùng nhớ: ptr<L, M1> -> ptr<L, M2> nếu cùng Layout và M2 <= M1
fn can_delegate(from: Type, to: Type) -> bool {
    match (from, to) {
        (Type::Io { min: a, max: b }, Type::Io { min: c, max: d }) => a <= c && d <= b,
        (
            Type::Ptr {
                layout_id: l1,
                max_elems: m1,
            },
            Type::Ptr {
                layout_id: l2,
                max_elems: m2,
            },
        ) => l1 == l2 && m2 <= m1,
        _ => from == to,
    }
}

/// HÀM CHÍNH: Kiểm chứng một hàm `Func` trong `Module` (Hỗ trợ Quy nạp Vòng lặp)
pub fn verify_func(module: &Module, func: &Func) -> Result<(), String> {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let mut v = Verifier {
        ctx: &ctx,
        solver: Solver::new(&ctx),
        layouts: &module.layouts,
        regs: HashMap::new(),
        reg_tys: HashMap::new(),
    };

    // 1. Khởi tạo tham số hàm & Nạp hợp đồng đầu vào (@req)
    for &(reg, ty) in &func.params {
        v.decl_reg(reg, ty);
    }
    for req in &func.requires {
        let cond = v.eval_z3_bool(req, None)?;
        v.solver.assert(&cond);
    }

    // Lưu điều kiện rẽ nhánh (Branch Condition) truyền xuống từng Block từ lệnh Br
    let mut blk_conds: HashMap<BlockId, Bool> = HashMap::new();

    // 2. Duyệt qua các Basic Block
    for block in &func.blocks {
        // Khai báo tham số khối (Block Params) & Nạp giả thiết quy nạp (@inv của Block)
        for &(reg, ty) in &block.params {
            v.decl_reg(reg, ty);
        }
        for inv in &block.invs {
            let cond = v.eval_z3_bool(inv, None)?;
            v.solver.assert(&cond);
        }

        // Nếu Block này là nhánh Then/Else của lệnh Br trước đó, bật điều kiện nhánh trong phạm vi Block
        let has_branch_cond = if let Some(c) = blk_conds.get(&block.id) {
            v.solver.push();
            v.solver.assert(c);
            true
        } else {
            false
        };

        for inst in &block.insts {
            match inst {
                Inst::Const { dst, ty, val } => {
                    // 1. Cấm tuyệt đối việc tự chế tạo thẻ Io bằng hằng số
                    if matches!(ty, Type::Io { .. }) {
                        return Err(format!(
                            "Bảo mật: Không thể tạo thẻ quyền năng Io bằng const tại %{}",
                            dst
                        ));
                    }
                    // 2. Muốn ánh xạ địa chỉ RAM vật lý thành thẻ Ptr mới bằng const, hàm bắt buộc phải giữ thẻ gốc io<0, 0xffff>
                    if matches!(ty, Type::Ptr { .. }) {
                        let has_root_io = func.params.iter().any(|&(_, t)| {
                            t == Type::Io {
                                min: 0,
                                max: 0xFFFF,
                            }
                        });
                        if !has_root_io || *val < 0x10000 {
                            return Err(format!(
                                "Bảo mật: Hàm '{}' không giữ thẻ gốc io<0,0xffff> để ánh xạ RAM tại %{}",
                                func.name, dst
                            ));
                        }
                    }
                    let bv = v.decl_reg(*dst, *ty);
                    v.solver.assert(&bv._eq(&BV::from_u64(&ctx, *val, 64)));
                }
                Inst::Bin { dst, op, lhs, rhs } => {
                    let l = v.get_reg(*lhs)?.clone();
                    let r = v.get_reg(*rhs)?.clone();
                    let zero = BV::from_u64(&ctx, 0, 64);
                    match op {
                        BinOp::Add => v.check(
                            &l.bvadd_no_overflow(&r, false),
                            &format!("Tràn số cộng %{}", dst),
                        )?,
                        BinOp::Sub => v.check(
                            &l.bvsub_no_underflow(&r, false),
                            &format!("Tràn số trừ %{}", dst),
                        )?,
                        BinOp::Mul => v.check(
                            &l.bvmul_no_overflow(&r, false),
                            &format!("Tràn số nhân %{}", dst),
                        )?,
                        BinOp::UDiv | BinOp::SDiv | BinOp::URem | BinOp::SRem => {
                            v.check(&r._eq(&zero).not(), &format!("Lỗi chia cho 0 tại %{}", dst))?;
                        }
                        BinOp::Shl | BinOp::LShr | BinOp::AShr => {
                            let bit_limit = BV::from_u64(&ctx, 64, 64);
                            v.check(
                                &r.bvult(&bit_limit),
                                &format!("Dịch bit quá 64-bit tại %{}", dst),
                            )?;
                        }
                        _ => {}
                    }
                    let res_bv = v.eval_binop(*op, &l, &r);
                    let dst_bv = v.decl_reg(*dst, Type::Bv64);
                    v.solver.assert(&dst_bv._eq(&res_bv));
                }
                Inst::Cmp { dst, op, lhs, rhs } => {
                    let l = v.get_reg(*lhs)?.clone();
                    let r = v.get_reg(*rhs)?.clone();
                    let cond = v.eval_cmpop(*op, &l, &r);
                    let one = BV::from_u64(&ctx, 1, 64);
                    let zero = BV::from_u64(&ctx, 0, 64);
                    let dst_bv = v.decl_reg(*dst, Type::Bv8);
                    v.solver.assert(&dst_bv._eq(&cond.ite(&one, &zero)));
                }
                Inst::Slice { dst, base, idx, ty } => {
                    // 1. Kiểm tra %base là Ptr và kiểu đích `ty` cũng là Ptr cùng Layout
                    let base_ty = *v
                        .reg_tys
                        .get(base)
                        .ok_or("Biến base của slice chưa khai báo")?;
                    let (l1, max_old) = match base_ty {
                        Type::Ptr {
                            layout_id,
                            max_elems,
                        } => (layout_id, max_elems),
                        _ => return Err(format!("Biến %{} trong slice không phải kiểu Ptr", base)),
                    };
                    let (l2, max_new) = match *ty {
                        Type::Ptr {
                            layout_id,
                            max_elems,
                        } if layout_id == l1 && max_elems > 0 => (layout_id, max_elems),
                        _ => {
                            return Err(format!(
                                "Kiểu đích của slice tại %{} phải cùng Layout với base",
                                dst
                            ));
                        }
                    };

                    // 2. Z3 chứng minh: base != NULL và (idx + max_new <= max_old) (Không bao giờ tràn mảng!)
                    let base_bv = v.get_reg(*base)?.clone();
                    let idx_bv = v.get_reg(*idx)?.clone();
                    let zero = BV::from_u64(&ctx, 0, 64);
                    let m_old_bv = BV::from_u64(&ctx, max_old as u64, 64);
                    let m_new_bv = BV::from_u64(&ctx, max_new as u64, 64);

                    v.check(
                        &base_bv._eq(&zero).not(),
                        &format!("Slice trên con trỏ NULL %{}", base),
                    )?;
                    v.check(
                        &idx_bv.bvadd_no_overflow(&m_new_bv, false),
                        &format!("Tràn số cộng index khi slice tại %{}", dst),
                    )?;
                    v.check(
                        &idx_bv.bvadd(&m_new_bv).bvule(&m_old_bv),
                        &format!(
                            "Tràn biên mảng khi slice tại %{}: idx + {} vượt quá {}",
                            dst, max_new, max_old
                        ),
                    )?;

                    // 3. Khai báo %dst = %base + (%idx * layout.size)
                    let elem_size = BV::from_u64(&ctx, v.layouts[l2 as usize].size as u64, 64);
                    let dst_bv = v.decl_reg(*dst, *ty);
                    v.solver
                        .assert(&dst_bv._eq(&base_bv.bvadd(&idx_bv.bvmul(&elem_size))));
                }
                Inst::Load {
                    dst,
                    ty,
                    base,
                    offset,
                } => {
                    let field = v.check_ptr_access(*base, *offset)?;
                    if field.ty != *ty {
                        return Err(format!("Load lệch kiểu tại %{}", dst));
                    }
                    let dst_bv = v.decl_reg(*dst, *ty);
                    if let Some(inv) = &field.inv {
                        let inv_cond = v.eval_z3_bool(inv, Some(&dst_bv))?;
                        v.solver.assert(&inv_cond);
                    }
                }
                Inst::Store { base, offset, val } => {
                    let field = v.check_ptr_access(*base, *offset)?;
                    let val_bv = v.get_reg(*val)?;
                    if let Some(inv) = &field.inv {
                        let inv_cond = v.eval_z3_bool(inv, Some(val_bv))?;
                        v.check(
                            &inv_cond,
                            &format!(
                                "Vi phạm bất biến Layout (@inv) khi Store tại offset {}",
                                offset
                            ),
                        )?;
                    }
                }
                Inst::HwIo {
                    dst,
                    cap,
                    port_or_reg,
                    ..
                } => {
                    // Kiểm tra biến `cap` có phải là thẻ Type::Io hợp lệ và cổng `port_or_reg` có nằm trong [min, max] không
                    match v.reg_tys.get(cap) {
                        Some(Type::Io { min, max })
                            if *port_or_reg >= *min && *port_or_reg <= *max => {}
                        Some(Type::Io { min, max }) => {
                            return Err(format!(
                                "Bảo mật I/O: Cổng 0x{:x} nằm ngoài phạm vi thẻ io<0x{:x}, 0x{:x}> của hàm '{}'",
                                port_or_reg, min, max, func.name
                            ));
                        }
                        _ => {
                            return Err(format!(
                                "Bảo mật I/O: Biến %{} không phải thẻ quyền năng Type::Io",
                                cap
                            ));
                        }
                    }
                    if let Some(d) = dst {
                        v.decl_reg(*d, Type::Bv64);
                    }
                }
                Inst::Call { dst, func_id, args } => {
                    let callee = module
                        .funcs
                        .get(*func_id as usize)
                        .ok_or("Call sai func_id")?;
                    if args.len() != callee.params.len() {
                        return Err(format!("Gọi hàm '{}' sai số lượng tham số", callee.name));
                    }
                    let saved_regs = v.regs.clone();
                    for (&arg_r, &(param_r, param_ty)) in args.iter().zip(&callee.params) {
                        let arg_ty = *v.reg_tys.get(&arg_r).ok_or("Biến Call arg chưa có kiểu")?;
                        // Dùng `can_delegate` để cho phép thu hẹp thẻ quyền năng (Capability Attenuation) khi gọi Driver/App!
                        if !can_delegate(arg_ty, param_ty) {
                            return Err(format!(
                                "Bảo mật: Không thể truyền kiểu {:?} vào {:?} khi gọi '{}'",
                                arg_ty, param_ty, callee.name
                            ));
                        }
                        v.regs
                            .insert(param_r, saved_regs.get(&arg_r).unwrap().clone());
                    }
                    for (i, req) in callee.requires.iter().enumerate() {
                        let cond = v.eval_z3_bool(req, None)?;
                        v.check(
                            &cond,
                            &format!("Vi phạm @req #{} khi gọi hàm '{}'", i, callee.name),
                        )?;
                    }
                    v.regs = saved_regs.clone();

                    if let (Some(d), Some(ret_ty)) = (dst, callee.ret_ty) {
                        let dst_bv = v.decl_reg(*d, ret_ty);
                        let callee_ret_reg =
                            callee.blocks.iter().flat_map(|b| &b.insts).find_map(|i| {
                                if let Inst::Ret { val: Some(r) } = i {
                                    Some(*r)
                                } else {
                                    None
                                }
                            });
                        let mut ens_regs = v.regs.clone();
                        for (&arg_r, &(param_r, _)) in args.iter().zip(&callee.params) {
                            ens_regs.insert(param_r, saved_regs.get(&arg_r).unwrap().clone());
                        }
                        if let Some(ret_r) = callee_ret_reg {
                            ens_regs.insert(ret_r, dst_bv.clone());
                        }
                        v.regs = ens_regs;
                        for ens in &callee.ensures {
                            let cond = v.eval_z3_bool(ens, None)?;
                            v.solver.assert(&cond);
                        }
                        v.regs = saved_regs;
                        v.regs.insert(*d, dst_bv);
                    }
                }
                Inst::Br {
                    cond,
                    then_bb,
                    else_bb,
                } => {
                    let c_bv = v.get_reg(*cond)?;
                    let zero = BV::from_u64(&ctx, 0, 64);
                    let is_true = c_bv._eq(&zero).not();
                    // Nếu Block hiện tại đang nằm trong một nhánh trước đó, gộp (AND) cả 2 điều kiện lại!
                    let (t_cond, e_cond) = if let Some(parent_c) = blk_conds.get(&block.id) {
                        (
                            Bool::and(&ctx, &[parent_c, &is_true]),
                            Bool::and(&ctx, &[parent_c, &is_true.not()]),
                        )
                    } else {
                        (is_true.clone(), is_true.not())
                    };
                    blk_conds.insert(*then_bb, t_cond);
                    blk_conds.insert(*else_bb, e_cond);
                }
                Inst::Jmp { target_bb, args } => {
                    // KIỂM CHỨNG QUY NẠP VÒNG LẶP: Thay thế tham số của Block đích bằng `args` và kiểm tra `@inv`!
                    let target_blk = func
                        .blocks
                        .iter()
                        .find(|b| b.id == *target_bb)
                        .ok_or("Jmp sai BlockId")?;
                    if args.len() != target_blk.params.len() {
                        return Err(format!(
                            "Jmp tới @b{} truyền sai số lượng tham số",
                            target_bb
                        ));
                    }
                    let saved_regs = v.regs.clone();
                    for (&arg_r, &(param_r, _)) in args.iter().zip(&target_blk.params) {
                        let arg_bv = saved_regs
                            .get(&arg_r)
                            .ok_or("Biến Jmp arg chưa khởi tạo")?
                            .clone();
                        v.regs.insert(param_r, arg_bv);
                    }
                    for (i, inv) in target_blk.invs.iter().enumerate() {
                        let cond = v.eval_z3_bool(inv, None)?;
                        v.check(
                            &cond,
                            &format!(
                                "Vi phạm bất biến vòng lặp (@inv #{}) khi nhảy vào @b{}",
                                i, target_bb
                            ),
                        )?;
                    }
                    v.regs = saved_regs;
                }
                Inst::Assume(expr) => {
                    let cond = v.eval_z3_bool(expr, None)?;
                    v.solver.assert(&cond);
                }
                Inst::Assert(expr) => {
                    let cond = v.eval_z3_bool(expr, None)?;
                    v.check(&cond, "Vi phạm lệnh Assert")?;
                }
                Inst::Ret { val } => {
                    if val.is_some() != func.ret_ty.is_some() {
                        return Err(format!("Hàm '{}' trả về sai kiểu ret_ty", func.name));
                    }
                    for (i, ens) in func.ensures.iter().enumerate() {
                        let cond = v.eval_z3_bool(ens, None)?;
                        v.check(
                            &cond,
                            &format!(
                                "Vi phạm điều kiện đầu ra (@ens #{}) của hàm '{}'",
                                i, func.name
                            ),
                        )?;
                    }
                }
                _ => {}
            }
        }
        if has_branch_cond {
            v.solver.pop(1);
        }
    }
    Ok(())
}
