// File: src/verify.rs — Light Verifier v2 (TCB duy nhất của Light OS)
use crate::ir::*;
use std::collections::{HashMap, HashSet};
use z3::ast::{Ast, BV, Bool};
use z3::{Config, Context, Params, SatResult, Solver};

pub const RAM_MIN: u64 = 0x1_0000;
pub const RAM_TOP: u64 = 0x100_0000_0000;
pub const STACK_BUDGET: u64 = 0x6_0000;
const TIMEOUT_MS: u32 = 10_000;
const ROOT_IO: Type = Type::Io {
    min: 0,
    max: 0xFFFF,
};

type Env<'ctx> = HashMap<Reg, BV<'ctx>>;

fn int_bits(ty: Type) -> Option<u32> {
    match ty {
        Type::Bv8 => Some(8),
        Type::Bv16 => Some(16),
        Type::Bv32 => Some(32),
        Type::Bv64 => Some(64),
        _ => None,
    }
}

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
        _ => int_bits(from).is_some() && int_bits(to).is_some(),
    }
}

fn is_term(i: &Inst) -> bool {
    matches!(i, Inst::Br { .. } | Inst::Jmp { .. } | Inst::Ret { .. })
}

fn dst_of(i: &Inst) -> Option<Reg> {
    match i {
        Inst::Const { dst, .. }
        | Inst::Bin { dst, .. }
        | Inst::Cmp { dst, .. }
        | Inst::Slice { dst, .. }
        | Inst::Load { dst, .. } => Some(*dst),
        Inst::HwIo { dst, .. } | Inst::Call { dst, .. } | Inst::CallPtr { dst, .. } => *dst,
        _ => None,
    }
}

fn expr_regs(e: &Z3Expr, out: &mut Vec<Reg>) {
    match e {
        Z3Expr::Reg(r) => out.push(*r),
        Z3Expr::FieldVal | Z3Expr::Const(_) => {}
        Z3Expr::Bin(_, l, r) | Z3Expr::Cmp(_, l, r) | Z3Expr::And(l, r) | Z3Expr::Or(l, r) => {
            expr_regs(l, out);
            expr_regs(r, out);
        }
        Z3Expr::Not(x) => expr_regs(x, out),
    }
}

fn uses_of(i: &Inst) -> Vec<Reg> {
    match i {
        Inst::Const { .. } => vec![],
        Inst::Bin { lhs, rhs, .. } | Inst::Cmp { lhs, rhs, .. } => vec![*lhs, *rhs],
        Inst::Slice { base, idx, .. } => vec![*base, *idx],
        Inst::Load { base, .. } => vec![*base],
        Inst::Store { base, val, .. } => vec![*base, *val],
        Inst::HwIo { cap, val, .. } => std::iter::once(*cap).chain(val.iter().copied()).collect(),
        Inst::Br { cond, .. } => vec![*cond],
        Inst::Jmp { args, .. } | Inst::Call { args, .. } => args.clone(),
        Inst::CallPtr { target, args, .. } => std::iter::once(*target)
            .chain(args.iter().copied())
            .collect(),
        Inst::Ret { val } => val.iter().copied().collect(),
        Inst::Assume(e) | Inst::Assert(e) => {
            let mut v = vec![];
            expr_regs(e, &mut v);
            v
        }
    }
}

struct Cfg {
    idx: HashMap<BlockId, usize>,
    rpo: Vec<usize>,
    pos: Vec<usize>,
    dom: Vec<Vec<bool>>,
}

fn build_cfg(func: &Func) -> Result<Cfg, String> {
    let n = func.blocks.len();
    if n == 0 {
        return Err("hàm không có block nào".into());
    }
    let mut idx = HashMap::new();
    for (i, b) in func.blocks.iter().enumerate() {
        if idx.insert(b.id, i).is_some() {
            return Err(format!("Block @b{} bị khai báo hai lần", b.id));
        }
    }
    if !func.blocks[0].params.is_empty() {
        return Err("block đầu tiên (entry) không được có tham số".into());
    }
    let mut succ = vec![Vec::new(); n];
    for (i, b) in func.blocks.iter().enumerate() {
        let last = b
            .insts
            .last()
            .ok_or_else(|| format!("Block @b{} rỗng", b.id))?;
        if !is_term(last) {
            return Err(format!("Block @b{} không kết thúc bằng br/jmp/ret", b.id));
        }
        if b.insts[..b.insts.len() - 1].iter().any(is_term) {
            return Err(format!(
                "Block @b{} có lệnh br/jmp/ret nằm giữa block",
                b.id
            ));
        }
        let targets = match last {
            Inst::Br {
                then_bb, else_bb, ..
            } => vec![*then_bb, *else_bb],
            Inst::Jmp { target_bb, .. } => vec![*target_bb],
            _ => vec![],
        };
        for t in targets {
            let &ti = idx
                .get(&t)
                .ok_or_else(|| format!("Block @b{} nhảy tới @b{} không tồn tại", b.id, t))?;
            succ[i].push(ti);
        }
    }

    let (mut state, mut post, mut stack) = (vec![0u8; n], Vec::new(), vec![(0usize, 0usize)]);
    state[0] = 1;
    while let Some(&(u, k)) = stack.last() {
        if k < succ[u].len() {
            stack.last_mut().unwrap().1 += 1;
            let v = succ[u][k];
            if state[v] == 0 {
                state[v] = 1;
                stack.push((v, 0));
            }
        } else {
            state[u] = 2;
            post.push(u);
            stack.pop();
        }
    }
    let rpo: Vec<usize> = post.into_iter().rev().collect();
    let mut pos = vec![usize::MAX; n];
    for (p, &b) in rpo.iter().enumerate() {
        pos[b] = p;
    }
    if let Some(i) = (0..n).find(|&i| pos[i] == usize::MAX) {
        return Err(format!(
            "Block @b{} không thể tới được từ entry",
            func.blocks[i].id
        ));
    }

    let mut preds = vec![Vec::new(); n];
    for (u, ss) in succ.iter().enumerate() {
        for &v in ss {
            preds[v].push(u);
        }
    }
    let mut dom = vec![vec![true; n]; n];
    dom[0] = (0..n).map(|i| i == 0).collect();
    let mut changed = true;
    while changed {
        changed = false;
        for &b in rpo.iter().skip(1) {
            let nd: Vec<bool> = (0..n)
                .map(|d| d == b || preds[b].iter().all(|&p| dom[p][d]))
                .collect();
            if nd != dom[b] {
                dom[b] = nd;
                changed = true;
            }
        }
    }
    for (u, ss) in succ.iter().enumerate() {
        for &v in ss {
            if pos[v] <= pos[u] && !dom[u][v] {
                return Err(format!(
                    "Luồng điều khiển không khả quy: cạnh @b{} -> @b{}",
                    func.blocks[u].id, func.blocks[v].id
                ));
            }
        }
    }
    Ok(Cfg { idx, rpo, pos, dom })
}

fn check_ssa(func: &Func, cfg: &Cfg) -> Result<(), String> {
    let mut def = HashMap::new();
    let mut add = |r: Reg, b: usize, p: usize| {
        if def.insert(r, (b, p)).is_some() {
            Err(format!("Biến SSA %{} bị định nghĩa nhiều hơn một lần", r))
        } else {
            Ok(())
        }
    };
    for &(r, _) in &func.params {
        add(r, 0, 0)?;
    }
    for (bi, b) in func.blocks.iter().enumerate() {
        for &(r, _) in &b.params {
            add(r, bi, 0)?;
        }
        for (k, inst) in b.insts.iter().enumerate() {
            if let Some(d) = dst_of(inst) {
                add(d, bi, k + 1)?;
            }
        }
    }
    let ok_use = |r: Reg, b: usize, p: usize, what: &str| -> Result<(), String> {
        let &(db, dp) = def
            .get(&r)
            .ok_or_else(|| format!("Biến %{} được dùng trong {} nhưng chưa định nghĩa", r, what))?;
        if (db == b && dp < p) || (db != b && cfg.dom[b][db]) {
            Ok(())
        } else {
            Err(format!(
                "Biến %{} dùng trong {} tại @b{} nhưng không bị chi phối bởi điểm định nghĩa",
                r, what, func.blocks[b].id
            ))
        }
    };
    for (bi, b) in func.blocks.iter().enumerate() {
        for inv in &b.invs {
            let mut v = vec![];
            expr_regs(inv, &mut v);
            for r in v {
                ok_use(r, bi, 1, "@inv")?;
            }
        }
        for (k, inst) in b.insts.iter().enumerate() {
            for r in uses_of(inst) {
                ok_use(r, bi, k + 1, "lệnh")?;
            }
        }
    }
    Ok(())
}

fn check_contract(func: &Func) -> Result<(), String> {
    let params: HashSet<Reg> = func.params.iter().map(|p| p.0).collect();
    let rets: HashSet<Reg> = func
        .blocks
        .iter()
        .flat_map(|b| &b.insts)
        .filter_map(|i| {
            if let Inst::Ret { val: Some(r) } = i {
                Some(*r)
            } else {
                None
            }
        })
        .collect();
    for (i, req) in func.requires.iter().enumerate() {
        let mut v = vec![];
        expr_regs(req, &mut v);
        if let Some(r) = v.iter().find(|r| !params.contains(r)) {
            return Err(format!(
                "@req #{} dùng %{} không phải tham số của hàm",
                i, r
            ));
        }
    }
    if func.ret_ty.is_some() && !func.ensures.is_empty() && rets.len() > 1 {
        return Err("hàm có @ens nhưng các lệnh ret trả về nhiều thanh ghi khác nhau".into());
    }
    for (i, ens) in func.ensures.iter().enumerate() {
        let mut v = vec![];
        expr_regs(ens, &mut v);
        if let Some(r) = v
            .iter()
            .find(|r| !params.contains(r) && !(func.ret_ty.is_some() && rets.contains(r)))
        {
            return Err(format!(
                "@ens #{} dùng %{} không phải tham số hay thanh ghi trả về",
                i, r
            ));
        }
    }
    Ok(())
}

pub fn check_module(module: &Module) -> Result<(), String> {
    for l in &module.layouts {
        if l.size == 0 {
            return Err(format!("Layout '{}' có kích thước 0", l.name));
        }
        let mut spans: Vec<(u64, u64)> = Vec::new();
        for f in &l.fields {
            let w = int_bits(f.ty).map(|b| (b / 8) as u64).ok_or_else(|| {
                format!(
                    "Layout '{}': trường offset {} mang kiểu capability (ptr/io)",
                    l.name, f.offset
                )
            })?;
            let (s, e) = (f.offset as u64, f.offset as u64 + w);
            if e > l.size as u64 {
                return Err(format!(
                    "Layout '{}': trường offset {} vượt kích thước layout {}",
                    l.name, f.offset, l.size
                ));
            }
            if spans.iter().any(|&(a, b)| s < b && a < e) {
                return Err(format!(
                    "Layout '{}': trường offset {} chồng lên trường khác",
                    l.name, f.offset
                ));
            }
            spans.push((s, e));
            if let Some(inv) = &f.inv {
                let mut v = vec![];
                expr_regs(inv, &mut v);
                if !v.is_empty() {
                    return Err(format!(
                        "Layout '{}': @inv của trường {} không được tham chiếu thanh ghi",
                        l.name, f.offset
                    ));
                }
            }
        }
    }
    let n = module.funcs.len();
    let (mut state, mut memo) = (vec![0u8; n], vec![0u64; n]);
    fn depth(m: &Module, f: usize, st: &mut [u8], memo: &mut [u64]) -> Result<u64, String> {
        if st[f] == 2 {
            return Ok(memo[f]);
        }
        if st[f] == 1 {
            return Err(format!(
                "Đệ quy: hàm '{}' tự gọi lại chính nó",
                m.funcs[f].name
            ));
        }
        st[f] = 1;
        let mut deepest = 0;
        for i in m.funcs[f].blocks.iter().flat_map(|b| &b.insts) {
            if let Inst::Call { func_id, .. } = i {
                let id = *func_id as usize;
                if id >= m.funcs.len() {
                    return Err(format!(
                        "Hàm '{}' gọi func_id {} không tồn tại",
                        m.funcs[f].name, id
                    ));
                }
                deepest = deepest.max(depth(m, id, st, memo)?);
            }
        }
        let max_reg = m.funcs[f]
            .params
            .iter()
            .map(|p| p.0)
            .chain(m.funcs[f].blocks.iter().flat_map(|b| {
                b.params
                    .iter()
                    .map(|p| p.0)
                    .chain(b.insts.iter().filter_map(dst_of))
            }))
            .max()
            .unwrap_or(0);
        st[f] = 2;
        memo[f] = (((max_reg as u64 + 8) * 8 + 15) & !15).max(0x800) + 128 + deepest;
        Ok(memo[f])
    }
    for f in 0..n {
        let d = depth(module, f, &mut state, &mut memo)?;
        if d > STACK_BUDGET {
            return Err(format!(
                "Hàm '{}' cần tới {} byte stack > ngân sách {}",
                module.funcs[f].name, d, STACK_BUDGET
            ));
        }
    }
    Ok(())
}

struct Verifier<'ctx> {
    ctx: &'ctx Context,
    solver: Solver<'ctx>,
    layouts: &'ctx [Layout],
    regs: Env<'ctx>,
    reg_tys: HashMap<Reg, Type>,
    cur_cond: Option<Bool<'ctx>>,
    conds: HashMap<usize, Option<Bool<'ctx>>>,
    pos: Vec<usize>,
    n_assume: usize,
}

impl<'ctx> Verifier<'ctx> {
    fn bv(&self, v: u64) -> BV<'ctx> {
        BV::from_u64(self.ctx, v, 64)
    }

    fn check_with(
        &self,
        extra: Option<&Bool<'ctx>>,
        cond: &Bool<'ctx>,
        msg: &str,
    ) -> Result<(), String> {
        self.solver.push();
        if let Some(c) = &self.cur_cond {
            self.solver.assert(c);
        }
        if let Some(e) = extra {
            self.solver.assert(e);
        }
        self.solver.assert(&cond.not());
        let out = match self.solver.check() {
            SatResult::Unsat => Ok(()),
            SatResult::Sat => {
                let ce = self
                    .solver
                    .get_model()
                    .map(|m| {
                        let mut ids: Vec<&Reg> = self.regs.keys().collect();
                        ids.sort();
                        ids.into_iter()
                            .take(64)
                            .filter_map(|r| {
                                m.eval(&self.regs[r], true)
                                    .and_then(|b| b.as_u64())
                                    .map(|v| format!("%{}={:#x}", r, v))
                            })
                            .collect::<Vec<_>>()
                            .join(" ")
                    })
                    .unwrap_or_default();
                Err(format!("[VERIFY FAILED] {} | Counter-example: {}", msg, ce))
            }
            SatResult::Unknown => Err(format!("[VERIFY TIMEOUT] Không thể chứng minh: {}", msg)),
        };
        self.solver.pop(1);
        out
    }

    fn check(&self, cond: &Bool<'ctx>, msg: &str) -> Result<(), String> {
        self.check_with(None, cond, msg)
    }

    fn feasible(&self) -> bool {
        self.solver.push();
        if let Some(c) = &self.cur_cond {
            self.solver.assert(c);
        }
        let r = self.solver.check();
        self.solver.pop(1);
        !matches!(r, SatResult::Unsat)
    }

    fn assume(&self, b: &Bool<'ctx>) {
        match &self.cur_cond {
            Some(c) => self.solver.assert(&Bool::or(self.ctx, &[&c.not(), b])),
            None => self.solver.assert(b),
        }
    }

    fn ptr_bytes(&self, layout_id: u16, max_elems: u64) -> Result<u64, String> {
        let l = self
            .layouts
            .get(layout_id as usize)
            .ok_or("layout_id không tồn tại")?;
        let bytes = max_elems.saturating_mul(l.size as u64);
        if bytes == 0 || bytes > RAM_TOP - RAM_MIN {
            return Err(format!(
                "Kiểu ptr<{},{}> chiếm {} byte — không hợp lệ",
                l.name, max_elems, bytes
            ));
        }
        Ok(bytes)
    }

    fn ptr_valid(
        &self,
        bv: &BV<'ctx>,
        layout_id: u16,
        max_elems: u64,
    ) -> Result<Bool<'ctx>, String> {
        let bytes = self.ptr_bytes(layout_id, max_elems)?;
        Ok(Bool::and(
            self.ctx,
            &[
                &bv.bvuge(&self.bv(RAM_MIN)),
                &bv.bvule(&self.bv(RAM_TOP - bytes)),
            ],
        ))
    }

    fn decl_raw(&mut self, r: Reg, ty: Type) -> Result<BV<'ctx>, String> {
        if self.regs.contains_key(&r) {
            return Err(format!("Biến SSA %{} bị định nghĩa lại", r));
        }
        let bv = BV::new_const(self.ctx, format!("r{}", r), 64);
        if let Some(bits) = int_bits(ty).filter(|&b| b < 64) {
            self.solver.assert(&bv.bvule(&self.bv((1u64 << bits) - 1)));
        }
        self.regs.insert(r, bv.clone());
        self.reg_tys.insert(r, ty);
        Ok(bv)
    }

    fn decl_reg(&mut self, r: Reg, ty: Type) -> Result<BV<'ctx>, String> {
        let bv = self.decl_raw(r, ty)?;
        if let Type::Ptr {
            layout_id,
            max_elems,
        } = ty
        {
            self.solver
                .assert(&self.ptr_valid(&bv, layout_id, max_elems)?);
        }
        Ok(bv)
    }

    fn get_reg(&self, r: Reg) -> Result<&BV<'ctx>, String> {
        self.regs
            .get(&r)
            .ok_or_else(|| format!("Biến SSA %{} chưa được khởi tạo", r))
    }

    fn reg_ty(&self, r: Reg) -> Result<Type, String> {
        self.reg_tys
            .get(&r)
            .copied()
            .ok_or_else(|| format!("Biến SSA %{} chưa có kiểu", r))
    }

    fn assign_check(&self, val: &BV<'ctx>, from: Type, to: Type, what: &str) -> Result<(), String> {
        if !can_delegate(from, to) {
            return Err(format!(
                "Lỗi kiểu/bảo mật: không thể dùng {:?} làm {:?} ({})",
                from, to, what
            ));
        }
        if let Some(bits) = int_bits(to).filter(|&b| b < 64) {
            self.check(
                &val.bvule(&self.bv((1u64 << bits) - 1)),
                &format!("giá trị không vừa kiểu {:?} ({})", to, what),
            )?;
        }
        Ok(())
    }

    fn eval_binop(&self, op: BinOp, l: &BV<'ctx>, r: &BV<'ctx>) -> BV<'ctx> {
        match op {
            BinOp::Add => l.bvadd(r),
            BinOp::Sub => l.bvsub(r),
            BinOp::Mul => l.bvmul(r),
            BinOp::UDiv => l.bvudiv(r),
            BinOp::SDiv => l.bvsdiv(r),
            BinOp::URem => l.bvurem(r),
            BinOp::SRem => l.bvsrem(r),
            BinOp::And => l.bvand(r),
            BinOp::Or => l.bvor(r),
            BinOp::Xor => l.bvxor(r),
            BinOp::Shl => l.bvshl(r),
            BinOp::LShr => l.bvlshr(r),
            BinOp::AShr => l.bvashr(r),
        }
    }

    fn eval_cmpop(&self, op: CmpOp, l: &BV<'ctx>, r: &BV<'ctx>) -> Bool<'ctx> {
        match op {
            CmpOp::Eq => l._eq(r),
            CmpOp::Ne => l._eq(r).not(),
            CmpOp::Ult => l.bvult(r),
            CmpOp::Ule => l.bvule(r),
            CmpOp::Ugt => l.bvugt(r),
            CmpOp::Uge => l.bvuge(r),
            CmpOp::Slt => l.bvslt(r),
            CmpOp::Sle => l.bvsle(r),
            CmpOp::Sgt => l.bvsgt(r),
            CmpOp::Sge => l.bvsge(r),
        }
    }

    fn eval_bv(
        &self,
        e: &Z3Expr,
        env: &Env<'ctx>,
        fv: Option<&BV<'ctx>>,
    ) -> Result<BV<'ctx>, String> {
        match e {
            Z3Expr::Reg(r) => env
                .get(r)
                .cloned()
                .ok_or_else(|| format!("Biến SSA %{} chưa được khởi tạo", r)),
            Z3Expr::FieldVal => fv
                .cloned()
                .ok_or_else(|| "Dùng 'val' ngoài @inv của Layout".into()),
            Z3Expr::Const(v) => Ok(self.bv(*v)),
            Z3Expr::Bin(op, l, r) => {
                Ok(self.eval_binop(*op, &self.eval_bv(l, env, fv)?, &self.eval_bv(r, env, fv)?))
            }
            Z3Expr::And(l, r) => Ok(self.eval_bv(l, env, fv)?.bvand(&self.eval_bv(r, env, fv)?)),
            Z3Expr::Or(l, r) => Ok(self.eval_bv(l, env, fv)?.bvor(&self.eval_bv(r, env, fv)?)),
            Z3Expr::Not(x) => Ok(self.eval_bv(x, env, fv)?.bvnot()),
            Z3Expr::Cmp(..) => Err("Biểu thức so sánh không thể dùng làm giá trị số".into()),
        }
    }

    fn eval_bool(
        &self,
        e: &Z3Expr,
        env: &Env<'ctx>,
        fv: Option<&BV<'ctx>>,
    ) -> Result<Bool<'ctx>, String> {
        match e {
            Z3Expr::Cmp(op, l, r) => {
                Ok(self.eval_cmpop(*op, &self.eval_bv(l, env, fv)?, &self.eval_bv(r, env, fv)?))
            }
            Z3Expr::And(l, r) => Ok(Bool::and(
                self.ctx,
                &[&self.eval_bool(l, env, fv)?, &self.eval_bool(r, env, fv)?],
            )),
            Z3Expr::Or(l, r) => Ok(Bool::or(
                self.ctx,
                &[&self.eval_bool(l, env, fv)?, &self.eval_bool(r, env, fv)?],
            )),
            Z3Expr::Not(x) => Ok(self.eval_bool(x, env, fv)?.not()),
            _ => Err("Biểu thức đòi hỏi kiểu logic (Cmp/And/Or/Not)".into()),
        }
    }

    fn ev(&self, e: &Z3Expr) -> Result<Bool<'ctx>, String> {
        self.eval_bool(e, &self.regs, None)
    }

    fn check_ptr_access(&self, base: Reg, offset: u32) -> Result<&'ctx FieldDef, String> {
        let Type::Ptr {
            layout_id,
            max_elems,
        } = self.reg_ty(base)?
        else {
            return Err(format!("Biến %{} không phải kiểu con trỏ Ptr", base));
        };
        let layout = self
            .layouts
            .get(layout_id as usize)
            .ok_or("layout_id không tồn tại")?;
        let max_bytes = max_elems.saturating_mul(layout.size as u64);
        if (offset as u64) >= max_bytes {
            return Err(format!(
                "Tràn vùng nhớ Ptr: offset {} >= max_bytes {}",
                offset, max_bytes
            ));
        }
        layout
            .fields
            .iter()
            .find(|f| f.offset == offset % layout.size)
            .ok_or_else(|| {
                format!(
                    "Truy cập sai lệch offset {} trong Layout '{}'",
                    offset % layout.size,
                    layout.name
                )
            })
    }

    fn add_pred(&mut self, from: usize, to: usize, cond: Option<Bool<'ctx>>) {
        if self.pos[to] <= self.pos[from] {
            return;
        }
        let merged = match (self.conds.get(&to), cond) {
            (None, c) => c,
            (Some(None), _) | (Some(_), None) => None,
            (Some(Some(prev)), Some(c)) => Some(Bool::or(self.ctx, &[prev, &c])),
        };
        self.conds.insert(to, merged);
    }

    fn check_target_invs(
        &self,
        func: &Func,
        ti: usize,
        env: &Env<'ctx>,
        extra: Option<&Bool<'ctx>>,
    ) -> Result<(), String> {
        for (i, inv) in func.blocks[ti].invs.iter().enumerate() {
            self.check_with(
                extra,
                &self.eval_bool(inv, env, None)?,
                &format!(
                    "Vi phạm bất biến (@inv #{}) khi nhảy vào @b{}",
                    i, func.blocks[ti].id
                ),
            )?;
        }
        Ok(())
    }

    fn step(
        &mut self,
        module: &Module,
        func: &Func,
        cfg: &Cfg,
        bi: usize,
        inst: &Inst,
    ) -> Result<(), String> {
        match inst {
            Inst::Const { dst, ty, val } => {
                match ty {
                    Type::Io { .. } => {
                        return Err(format!(
                            "Bảo mật: Không thể tạo thẻ quyền năng Io bằng const tại %{}",
                            dst
                        ));
                    }
                    Type::Ptr {
                        layout_id,
                        max_elems,
                    } => {
                        if !func.params.iter().any(|&(_, t)| t == ROOT_IO) {
                            return Err(format!(
                                "Bảo mật: Hàm '{}' không giữ thẻ gốc io<0,0xffff> để ánh xạ RAM tại %{}",
                                func.name, dst
                            ));
                        }
                        let bytes = self.ptr_bytes(*layout_id, *max_elems)?;
                        if *val < RAM_MIN || val.checked_add(bytes).map_or(true, |e| e > RAM_TOP) {
                            return Err(format!(
                                "Bảo mật: const ptr tại %{} = {:#x} nằm ngoài RAM",
                                dst, val
                            ));
                        }
                    }
                    _ if int_bits(*ty).map_or(false, |b| b < 64 && *val >> b != 0) => {
                        return Err(format!(
                            "Hằng số {:#x} không vừa kiểu {:?} tại %{}",
                            val, ty, dst
                        ));
                    }
                    _ => {}
                }
                let bv = self.decl_reg(*dst, *ty)?;
                self.solver.assert(&bv._eq(&self.bv(*val)));
            }
            Inst::Bin { dst, op, lhs, rhs } => {
                let (l, r, zero) = (
                    self.get_reg(*lhs)?.clone(),
                    self.get_reg(*rhs)?.clone(),
                    self.bv(0),
                );
                match op {
                    BinOp::Add => self.check(
                        &l.bvadd_no_overflow(&r, false),
                        &format!("Tràn số cộng %{}", dst),
                    )?,
                    BinOp::Sub => self.check(
                        &l.bvsub_no_underflow(&r, false),
                        &format!("Tràn số trừ %{}", dst),
                    )?,
                    BinOp::Mul => self.check(
                        &l.bvmul_no_overflow(&r, false),
                        &format!("Tràn số nhân %{}", dst),
                    )?,
                    BinOp::UDiv | BinOp::URem => {
                        self.check(&r._eq(&zero).not(), &format!("Lỗi chia cho 0 tại %{}", dst))?
                    }
                    BinOp::SDiv | BinOp::SRem => {
                        self.check(&r._eq(&zero).not(), &format!("Lỗi chia cho 0 tại %{}", dst))?;
                        let ovf = Bool::and(
                            self.ctx,
                            &[&l._eq(&self.bv(1u64 << 63)), &r._eq(&self.bv(u64::MAX))],
                        );
                        self.check(
                            &ovf.not(),
                            &format!("sdiv/srem INT_MIN / -1 gây #DE tại %{}", dst),
                        )?;
                    }
                    BinOp::Shl | BinOp::LShr | BinOp::AShr => self.check(
                        &r.bvult(&self.bv(64)),
                        &format!("Dịch bit quá 64-bit tại %{}", dst),
                    )?,
                    _ => {}
                }
                let res = self.eval_binop(*op, &l, &r);
                let d = self.decl_reg(*dst, Type::Bv64)?;
                self.solver.assert(&d._eq(&res));
            }
            Inst::Cmp { dst, op, lhs, rhs } => {
                let cond = self.eval_cmpop(*op, self.get_reg(*lhs)?, self.get_reg(*rhs)?);
                let d = self.decl_reg(*dst, Type::Bv8)?;
                self.solver
                    .assert(&d._eq(&cond.ite(&self.bv(1), &self.bv(0))));
            }
            Inst::Slice { dst, base, idx, ty } => {
                let Type::Ptr {
                    layout_id: l1,
                    max_elems: max_old,
                } = self.reg_ty(*base)?
                else {
                    return Err(format!("Biến %{} trong slice không phải kiểu Ptr", base));
                };
                let Type::Ptr {
                    layout_id: l2,
                    max_elems: max_new,
                } = *ty
                else {
                    return Err(format!("Kiểu đích của slice tại %{} phải là ptr", dst));
                };
                if l1 != l2 || max_new == 0 {
                    return Err(format!(
                        "Kiểu đích của slice tại %{} phải cùng Layout với base và max_elems > 0",
                        dst
                    ));
                }
                let (base_bv, idx_bv, m_new) = (
                    self.get_reg(*base)?.clone(),
                    self.get_reg(*idx)?.clone(),
                    self.bv(max_new),
                );
                self.check(
                    &idx_bv.bvadd_no_overflow(&m_new, false),
                    &format!("Tràn số cộng index khi slice tại %{}", dst),
                )?;
                self.check(
                    &idx_bv.bvadd(&m_new).bvule(&self.bv(max_old)),
                    &format!("Tràn biên mảng khi slice tại %{}", dst),
                )?;
                let elem = self.bv(self.layouts[l2 as usize].size as u64);
                let d = self.decl_raw(*dst, *ty)?;
                self.solver
                    .assert(&d._eq(&base_bv.bvadd(&idx_bv.bvmul(&elem))));
                let valid = self.ptr_valid(&d, l2, max_new)?;
                self.check(&valid, &format!("Con trỏ slice tại %{} ra ngoài RAM", dst))?;
                self.assume(&valid);
            }
            Inst::Load {
                dst,
                ty,
                base,
                offset,
            } => {
                let field = self.check_ptr_access(*base, *offset)?;
                if field.ty != *ty {
                    return Err(format!(
                        "Load lệch kiểu tại %{}: trường là {:?}, lệnh khai báo {:?}",
                        dst, field.ty, ty
                    ));
                }
                let d = self.decl_reg(*dst, *ty)?;
                if let Some(inv) = &field.inv {
                    self.assume(&self.eval_bool(inv, &HashMap::new(), Some(&d))?);
                }
            }
            Inst::Store { base, offset, val } => {
                let field = self.check_ptr_access(*base, *offset)?;
                if self.reg_ty(*val)? != field.ty {
                    return Err(format!(
                        "Store lệch kiểu: %{} khác kiểu trường offset {} ({:?})",
                        val, offset, field.ty
                    ));
                }
                if let Some(inv) = &field.inv {
                    let c = self.eval_bool(inv, &HashMap::new(), Some(self.get_reg(*val)?))?;
                    self.check(
                        &c,
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
                port_or_reg: port,
                val,
                is_write,
            } => {
                let Type::Io { min, max } = self.reg_ty(*cap)? else {
                    return Err(format!(
                        "Bảo mật I/O: Biến %{} không phải thẻ quyền năng Type::Io",
                        cap
                    ));
                };
                if *port < min || *port > max {
                    return Err(format!(
                        "Bảo mật I/O: Cổng 0x{:x} nằm ngoài phạm vi thẻ io<0x{:x}, 0x{:x}>",
                        port, min, max
                    ));
                }
                if *port == 3 && (min, max) != (0, 0xFFFF) {
                    return Err(
                        "Bảo mật: 'cổng' 3 là thanh ghi CR3 — chỉ thẻ gốc io<0,0xffff> được dùng"
                            .into(),
                    );
                }
                if *is_write {
                    let v = val.ok_or("hwio_w thiếu giá trị")?;
                    let vty = self.reg_ty(v)?;
                    if int_bits(vty).is_none() {
                        return Err(format!("hwio_w: %{} phải là số nguyên", v));
                    }
                    if *port != 3 {
                        let limit = if *port == 0x1F0 || vty == Type::Bv16 {
                            0xFFFF
                        } else {
                            0xFF
                        };
                        self.check(
                            &self.get_reg(v)?.bvule(&self.bv(limit)),
                            &format!("hwio_w cổng 0x{:x}: giá trị quá độ rộng", port),
                        )?;
                    }
                } else if let Some(d) = dst {
                    let bv = self.decl_reg(*d, Type::Bv64)?;
                    if *port != 3 {
                        self.assume(&bv.bvule(&self.bv(if *port == 0x1F0 {
                            0xFFFF
                        } else {
                            0xFF
                        })));
                    }
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
                let mut env = HashMap::new();
                for (&a, &(p, pty)) in args.iter().zip(&callee.params) {
                    let abv = self.get_reg(a)?.clone();
                    self.assign_check(
                        &abv,
                        self.reg_ty(a)?,
                        pty,
                        &format!("đối số %{} của '{}'", a, callee.name),
                    )?;
                    env.insert(p, abv);
                }
                for (i, req) in callee.requires.iter().enumerate() {
                    self.check(
                        &self.eval_bool(req, &env, None)?,
                        &format!("Vi phạm @req #{} khi gọi hàm '{}'", i, callee.name),
                    )?;
                }
                if let Some(d) = dst {
                    let rty = callee.ret_ty.ok_or_else(|| {
                        format!("'{}' là hàm void nhưng gán vào %{}", callee.name, d)
                    })?;
                    let dbv = self.decl_reg(*d, rty)?;
                    if !callee.ensures.is_empty() {
                        if let Some(r) = callee.blocks.iter().flat_map(|b| &b.insts).find_map(|i| {
                            if let Inst::Ret { val: Some(r) } = i {
                                Some(*r)
                            } else {
                                None
                            }
                        }) {
                            env.insert(r, dbv);
                        }
                        for ens in &callee.ensures {
                            self.assume(&self.eval_bool(ens, &env, None)?);
                        }
                    }
                }
            }
            Inst::CallPtr { dst, target, args } => {
                if !func.params.iter().any(|&(_, t)| t == ROOT_IO) {
                    return Err(format!(
                        "Bảo mật: CallPtr chỉ dành cho hàm giữ thẻ gốc io<0,0xffff>; '{}' không có",
                        func.name
                    ));
                }
                if !matches!(self.reg_ty(*target)?, Type::Ptr { .. }) {
                    return Err(format!("CallPtr: đích %{} phải là ptr", target));
                }
                for a in args {
                    self.get_reg(*a)?;
                }
                if let Some(d) = dst {
                    self.decl_reg(*d, Type::Bv64)?;
                }
            }
            Inst::Br {
                cond,
                then_bb,
                else_bb,
            } => {
                let is_true = self.get_reg(*cond)?._eq(&self.bv(0)).not();
                for (t, extra) in [(*then_bb, is_true.clone()), (*else_bb, is_true.not())] {
                    let ti = cfg.idx[&t];
                    if !func.blocks[ti].params.is_empty() {
                        return Err(format!(
                            "br không được nhảy tới @b{} vì block đó có tham số",
                            t
                        ));
                    }
                    self.check_target_invs(func, ti, &self.regs, Some(&extra))?;
                    let pc = self
                        .cur_cond
                        .as_ref()
                        .map_or_else(|| extra.clone(), |c| Bool::and(self.ctx, &[c, &extra]));
                    self.add_pred(bi, ti, Some(pc));
                }
            }
            Inst::Jmp { target_bb, args } => {
                let ti = cfg.idx[target_bb];
                let tb = &func.blocks[ti];
                if args.len() != tb.params.len() {
                    return Err(format!("Jmp tới @b{} truyền sai số lượng tham số", tb.id));
                }
                for j in 0..args.len() {
                    if tb.params[..j].iter().any(|&(p, _)| p == args[j]) {
                        return Err(format!(
                            "Jmp tới @b{}: đối số %{} bị ghi đè (parallel-copy hazard)",
                            tb.id, args[j]
                        ));
                    }
                }
                let mut env = self.regs.clone();
                for (&a, &(p, pty)) in args.iter().zip(&tb.params) {
                    let abv = self.get_reg(a)?.clone();
                    self.assign_check(
                        &abv,
                        self.reg_ty(a)?,
                        pty,
                        &format!("tham số %{} của jmp @b{}", p, tb.id),
                    )?;
                    env.insert(p, abv);
                }
                self.check_target_invs(func, ti, &env, None)?;
                self.add_pred(bi, ti, self.cur_cond.clone());
            }
            Inst::Assume(e) => {
                self.assume(&self.ev(e)?);
                self.n_assume += 1;
            }
            Inst::Assert(e) => self.check(&self.ev(e)?, "Vi phạm lệnh Assert")?,
            Inst::Ret { val } => {
                if val.is_some() != func.ret_ty.is_some() {
                    return Err(format!("Hàm '{}' trả về sai kiểu ret_ty", func.name));
                }
                if let (Some(r), Some(rty)) = (val, func.ret_ty) {
                    self.assign_check(
                        self.get_reg(*r)?,
                        self.reg_ty(*r)?,
                        rty,
                        &format!("giá trị trả về %{}", r),
                    )?;
                }
                for (i, ens) in func.ensures.iter().enumerate() {
                    self.check(
                        &self.ev(ens)?,
                        &format!(
                            "Vi phạm điều kiện đầu ra (@ens #{}) của hàm '{}'",
                            i, func.name
                        ),
                    )?;
                }
            }
        }
        Ok(())
    }
}

pub fn verify_func(module: &Module, func: &Func) -> Result<(), String> {
    verify_inner(module, func).map_err(|e| format!("[func '{}'] {}", func.name, e))
}

fn verify_inner(module: &Module, func: &Func) -> Result<(), String> {
    let cfg = build_cfg(func)?;
    check_ssa(func, &cfg)?;
    check_contract(func)?;

    let ctx = Context::new(&Config::new());
    let solver = Solver::new(&ctx);
    let mut params = Params::new(&ctx);
    params.set_u32("timeout", TIMEOUT_MS);
    solver.set_params(&params);

    let mut v = Verifier {
        ctx: &ctx,
        solver,
        layouts: &module.layouts,
        regs: HashMap::new(),
        reg_tys: HashMap::new(),
        cur_cond: None,
        conds: HashMap::from([(0, None)]),
        pos: cfg.pos.clone(),
        n_assume: 0,
    };

    for &(r, ty) in &func.params {
        v.decl_reg(r, ty)?;
    }
    for req in &func.requires {
        v.solver.assert(&v.ev(req)?);
    }

    for &bi in &cfg.rpo {
        let Some(c) = v.conds.get(&bi).cloned() else {
            continue;
        };
        v.cur_cond = c;
        if !v.feasible() {
            if bi == 0 {
                return Err("các @req của hàm mâu thuẫn nhau".into());
            }
            v.conds.remove(&bi);
            continue;
        }
        let block = &func.blocks[bi];
        for &(r, ty) in &block.params {
            v.decl_reg(r, ty)?;
        }
        for inv in &block.invs {
            v.assume(&v.ev(inv)?);
        }
        if (!block.params.is_empty() || !block.invs.is_empty()) && !v.feasible() {
            return Err(format!(
                "@inv của @b{} mâu thuẫn nhau/với đường đi tới nó",
                block.id
            ));
        }
        for inst in &block.insts {
            v.step(module, func, &cfg, bi, inst)?;
        }
    }
    if v.n_assume > 0 {
        eprintln!(
            "  ⚠ func '{}': {} lệnh `assume` (tiên đề — KHÔNG được Z3 chứng minh)",
            func.name, v.n_assume
        );
    }
    Ok(())
}
