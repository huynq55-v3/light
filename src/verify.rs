// File: src/verify.rs — Light Verifier v2 (TCB duy nhất của Light OS)
use crate::ir::*;
use std::collections::{HashMap, HashSet};
use z3::ast::{Ast, BV, Bool};
use z3::{Config, Context, Params, SatResult, Solver};

pub const RAM_MIN: u64 = 0x1_0000;
pub const RAM_TOP: u64 = 0x100_0000_0000;
pub const STACK_BUDGET: u64 = 0x6_0000;
/// Stack mỗi nhân AP = 32KB (0x150000 + apic_id * 32KB, xem elf64.rs). Hàm worker của `parallel` phải vừa.
pub const AP_STACK_BUDGET: u64 = 0x7000;
/// Địa chỉ cố định duy nhất của bảng SMP
pub const SMP_TABLE: u64 = 0x7e000;
const TIMEOUT_MS: u32 = 10_000;
const ROOT_IO: Type = Type::Io {
    min: 0,
    max: 0xFFFF,
};

type Env<'ctx> = HashMap<Reg, BV<'ctx>>;

/// Độ rộng lệnh `in` theo cổng: 0xCFC (dữ liệu PCI config) 32-bit, 0x1F0 (dữ liệu ATA) 16-bit, còn lại 8-bit.
/// Phải khớp với elf64.rs và oracle.
pub fn hwio_read_limit(port: u16) -> u64 {
    match port {
        0xCFC => 0xFFFF_FFFF,
        0x1F0 => 0xFFFF,
        _ => 0xFF,
    }
}

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
        (Type::Smp, Type::Smp) => true,
        (Type::Ptr { .. } | Type::DPtr { .. }, Type::Ptr { .. } | Type::DPtr { .. }) => {
            from.ptr_layout() == to.ptr_layout()
        }
        _ => int_bits(from).is_some() && int_bits(to).is_some(),
    }
}

/// Quy tắc phạm vi của độ dài trong ptr<L,%n> (xem ir.rs). Chạy trước Z3, cùng check_ssa.
fn check_dyn_scopes(func: &Func) -> Result<(), String> {
    let is_int_param = |ps: &[(Reg, Type)], r: Reg| ps.iter().any(|&(p, t)| p == r && int_bits(t).is_some());
    let not_int = |ps: &[(Reg, Type)], r: Reg| ps.iter().any(|&(p, t)| p == r && int_bits(t).is_none());
    for (i, &(p, t)) in func.params.iter().enumerate() {
        if let Type::DPtr { len, .. } = t {
            if not_int(&func.params[..i], len) {
                return Err(format!("độ dài %{} của ptr động %{} phải là số nguyên", len, p));
            }
            if !is_int_param(&func.params[..i], len) {
                return Err(format!(
                    "độ dài %{} của ptr động %{} phải là tham số đứng trước của hàm",
                    len, p
                ));
            }
        }
    }
    if let Some(Type::DPtr { len, .. }) = func.ret_ty {
        if !is_int_param(&func.params, len) {
            return Err(format!(
                "kiểu trả về ptr<_,%{}>: độ dài phải là tham số số nguyên của hàm",
                len
            ));
        }
    }
    for b in &func.blocks {
        for (i, &(p, t)) in b.params.iter().enumerate() {
            if let Type::DPtr { len, .. } = t {
                if not_int(&b.params[..i], len) || not_int(&func.params, len) {
                    return Err(format!("độ dài %{} của ptr động %{} phải là số nguyên", len, p));
                }
                if !is_int_param(&b.params[..i], len) && !is_int_param(&func.params, len) {
                    return Err(format!(
                        "@b{}: độ dài %{} của ptr động %{} phải là tham số block đứng trước (cùng block) hoặc tham số hàm",
                        b.id, len, p
                    ));
                }
            }
        }
    }
    Ok(())
}

fn is_term(i: &Inst) -> bool {
    matches!(i, Inst::Br { .. } | Inst::Jmp { .. } | Inst::Ret { .. })
}

fn dst_of(i: &Inst) -> Option<Reg> {
    i.dst()
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
        Z3Expr::Math(_, l, r) => {
            expr_regs(l, out);
            expr_regs(r, out);
        }
        Z3Expr::Mem(p, i, _) => {
            out.push(*p);
            expr_regs(i, out);
        }
        Z3Expr::Old(x) => expr_regs(x, out),
        // biến lượng từ là biến buộc: không phải thanh ghi
        Z3Expr::Quant(_, v, lo, hi, body) => {
            let mut inner = vec![];
            for x in [lo, hi, body] {
                expr_regs(x, &mut inner);
            }
            out.extend(inner.into_iter().filter(|r| r != v));
        }
    }
}

fn uses_of(i: &Inst) -> Vec<Reg> {
    match i {
        Inst::Const { .. } => vec![],
        Inst::Bin { lhs, rhs, .. } | Inst::Cmp { lhs, rhs, .. } => vec![*lhs, *rhs],
        Inst::Slice { base, idx, ty, .. } => match ty {
            Type::DPtr { len, .. } => vec![*base, *idx, *len],
            _ => vec![*base, *idx],
        },
        Inst::Load { base, .. } => vec![*base],
        Inst::Narrow { src, .. } => vec![*src],
        Inst::Addr { .. } => vec![],
        Inst::View { src, ty, .. } => match ty {
            Type::DPtr { len, .. } => vec![*src, *len],
            _ => vec![*src],
        },
        Inst::Store { base, val, .. } => vec![*base, *val],
        Inst::Simd256 { op, dst, lhs, rhs } => {
            if *op == SimdOp::Dot {
                vec![*lhs, *rhs]
            } else {
                vec![*dst, *lhs, *rhs]
            }
        }
        Inst::Parallel { smp, n, base, arg, .. } => vec![*smp, *n, *base, *arg],
        Inst::SmpWorkers { smp, .. } => vec![*smp],
        Inst::AtaRead { cap, ptr, idx, nsec } => vec![*cap, *ptr, *idx, *nsec],
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

pub(crate) struct Cfg {
    pub(crate) idx: HashMap<BlockId, usize>,
    pub(crate) rpo: Vec<usize>,
    pub(crate) pos: Vec<usize>,
    dom: Vec<Vec<bool>>,
}

pub(crate) fn build_cfg(func: &Func) -> Result<Cfg, String> {
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

/// Tên giá trị trả về trong @ens: thanh ghi duy nhất không phải tham số (None nếu @ens chỉ nhắc tham số).
fn result_reg(func: &Func) -> Option<Reg> {
    let params: HashSet<Reg> = func.params.iter().map(|p| p.0).collect();
    let mut v = vec![];
    for e in &func.ensures {
        expr_regs(e, &mut v);
    }
    v.into_iter().find(|r| !params.contains(r))
}

fn check_contract(func: &Func) -> Result<(), String> {
    let params: HashSet<Reg> = func.params.iter().map(|p| p.0).collect();
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
    // @ens chỉ được nhắc tới tham số và (nhiều nhất) MỘT tên cho giá trị trả về; tên đó được gán lại ở từng `ret`.
    let mut res: Vec<Reg> = vec![];
    for (i, ens) in func.ensures.iter().enumerate() {
        let mut v = vec![];
        expr_regs(ens, &mut v);
        for r in v.into_iter().filter(|r| !params.contains(r)) {
            if func.ret_ty.is_none() {
                return Err(format!("@ens #{} dùng %{} không phải tham số (hàm không trả giá trị)", i, r));
            }
            if !res.contains(&r) {
                res.push(r);
            }
        }
    }
    if res.len() > 1 {
        return Err(format!(
            "@ens dùng nhiều thanh ghi ngoài tham số ({}); chỉ được một tên cho giá trị trả về",
            res.iter().map(|r| format!("%{}", r)).collect::<Vec<_>>().join(", ")
        ));
    }
    Ok(())
}

/// Cận trên khung stack của RIÊNG hàm `f` (không tính các hàm nó gọi). Khung thật (x86.rs) = 8 byte cho MỖI biến phải tràn
/// (<= số thanh ghi SSA phân biệt) + tối đa 11 thanh ghi callee-saved + rbp + địa chỉ trả về, + 128 byte đệm cho đối số đẩy lên stack,
/// `push rdi` của ata_read và khung lt_parallel. Chỉ phụ thuộc SỐ LƯỢNG biến, không phụ thuộc số định danh.
pub fn local_stack_bound(f: &Func) -> u64 {
    let mut regs: std::collections::HashSet<Reg> = f.params.iter().map(|p| p.0).collect();
    for b in &f.blocks {
        regs.extend(b.params.iter().map(|p| p.0));
        regs.extend(b.insts.iter().filter_map(dst_of));
    }
    (regs.len() as u64 * 8 + 8 * 11 + 16 + 8 + 15 & !15) + 128
}

/// Khung stack thật do bộ sinh mã báo (x86::take_frames) phải <= cận của verifier cho từng hàm; trả về (số hàm, khoảng trống nhỏ nhất)
pub fn check_frames(module: &Module, frames: &[(String, u64)]) -> Result<(usize, i64), String> {
    let mut min_slack = i64::MAX;
    for (name, real) in frames {
        let Some(f) = module.funcs.iter().find(|f| &f.name == name) else { continue };
        let bound = local_stack_bound(f);
        if *real > bound {
            return Err(format!("Hàm '{}': khung stack thật {} byte > cận verifier {} byte", name, real, bound));
        }
        min_slack = min_slack.min(bound as i64 - *real as i64);
    }
    Ok((frames.len(), min_slack))
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
            if let Inst::Call { func_id, .. } | Inst::Parallel { func_id, .. } = i {
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
        st[f] = 2;
        memo[f] = local_stack_bound(&m.funcs[f]) + deepest;
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
    // Hàm worker của `parallel`: chạy trên stack 32KB của nhân AP, và không được (bắc cầu) gọi `parallel`
    // (một AP chờ chính slot của nó -> deadlock).
    fn has_parallel(m: &Module, f: usize, seen: &mut Vec<bool>) -> bool {
        if std::mem::replace(&mut seen[f], true) {
            return false;
        }
        m.funcs[f].blocks.iter().flat_map(|b| &b.insts).any(|i| match i {
            Inst::Parallel { .. } => true,
            Inst::Call { func_id, .. } => has_parallel(m, *func_id as usize, seen),
            _ => false,
        })
    }
    for f in &module.funcs {
        for i in f.blocks.iter().flat_map(|b| &b.insts) {
            if let Inst::Parallel { func_id, .. } = i {
                let w = *func_id as usize;
                if memo[w] > AP_STACK_BUDGET {
                    return Err(format!(
                        "parallel trong '{}': worker '{}' cần {} byte stack > stack nhân AP {}",
                        f.name, module.funcs[w].name, memo[w], AP_STACK_BUDGET
                    ));
                }
                if has_parallel(module, w, &mut vec![false; n]) {
                    return Err(format!(
                        "parallel trong '{}': worker '{}' (bắc cầu) dùng parallel lồng nhau — không cho phép",
                        f.name, module.funcs[w].name
                    ));
                }
            }
        }
    }
    Ok(())
}

struct Verifier<'ctx> {
    ctx: &'ctx Context,
    solver: Solver<'ctx>,
    layouts: &'ctx [Layout],
    func_name: &'ctx str,
    cur_bb: BlockId,
    cur_inst: String,
    cur_at: String, // "file:dòng" của lệnh đang kiểm
    cur_regs: Vec<Reg>,
    regs: Env<'ctx>,
    reg_tys: HashMap<Reg, Type>,
    cur_cond: Option<Bool<'ctx>>,
    conds: HashMap<usize, Option<Bool<'ctx>>>,
    pos: Vec<usize>,
    n_assume: usize,
    /// Cạnh jmp TIẾN vào block có tham số: (điều kiện đường đi của block nguồn, đối số). Block không phải đầu vòng lặp
    /// (không có cạnh lùi vào) dùng chúng để biết giá trị tham số — xem chỗ vào block trong verify_inner.
    edge_args: HashMap<usize, Vec<(Option<Bool<'ctx>>, Vec<BV<'ctx>>)>>,
    /// Vòng lặp phải dừng (hàm không giữ thẻ io: không có lý do chờ phần cứng vô hạn)
    need_term: bool,
    /// Biến giảm còn hợp lệ của từng đầu vòng (block index) sau các cạnh lùi đã kiểm
    term: HashMap<usize, Vec<Z3Expr>>,
}

/// Biểu thức chỉ gồm hằng và thanh ghi bất biến trong vòng lặp đầu `h` (tham số hàm hoặc định nghĩa ở block chi phối
/// NGẶT `h`); thanh ghi `const` được thay bằng giá trị. None nếu không thỏa.
/// Tham số của chính `h` cũng được nhận: biến giảm là hàm của trạng thái đầu vòng nên mọi biểu thức trên tham số `h` đều hợp lệ.
fn loop_invariant(e: &Z3Expr, h: usize, hp: &[Reg], defs: &HashMap<Reg, usize>, consts: &HashMap<Reg, u64>, cfg: &Cfg) -> Option<Z3Expr> {
    Some(match e {
        Z3Expr::Reg(r) => {
            if let Some(&v) = consts.get(r) {
                Z3Expr::Const(v)
            } else if hp.contains(r) {
                Z3Expr::Reg(*r)
            } else {
                match defs.get(r) {
                    None => Z3Expr::Reg(*r), // tham số hàm
                    Some(&b) if b != h && cfg.dom[h][b] => Z3Expr::Reg(*r),
                    _ => return None,
                }
            }
        }
        Z3Expr::Const(v) => Z3Expr::Const(*v),
        Z3Expr::Bin(op, l, r) => Z3Expr::Bin(
            *op,
            Box::new(loop_invariant(l, h, hp, defs, consts, cfg)?),
            Box::new(loop_invariant(r, h, hp, defs, consts, cfg)?),
        ),
        _ => return None,
    })
}

/// Ứng viên biến giảm cho đầu vòng `h`: với mỗi tham số số nguyên p: p, X - p, p - X với X là cận bất biến vòng lấy từ
/// @inv của `h` và mọi lệnh cmp trong hàm.
fn dec_candidates(func: &Func, cfg: &Cfg, h: usize) -> Vec<Z3Expr> {
    let mut defs: HashMap<Reg, usize> = HashMap::new();
    let mut consts: HashMap<Reg, u64> = HashMap::new();
    for (bi, b) in func.blocks.iter().enumerate() {
        for &(r, _) in &b.params {
            defs.insert(r, bi);
        }
        for i in &b.insts {
            if let Some(d) = i.dst() {
                defs.insert(d, bi);
            }
            if let Inst::Const { dst, val, ty } = i {
                if int_bits(*ty).is_some() {
                    consts.insert(*dst, *val);
                }
            }
        }
    }
    let ps: Vec<Reg> = func.blocks[h].params.iter().filter(|(_, t)| int_bits(*t).is_some()).map(|p| p.0).collect();
    let hp: Vec<Reg> = func.blocks[h].params.iter().map(|p| p.0).collect();
    let mut bounds: Vec<Z3Expr> = Vec::new();
    let mut add = |e: &Z3Expr| {
        if let Some(x) = loop_invariant(e, h, &hp, &defs, &consts, cfg) {
            let k = format!("{:?}", x);
            if !bounds.iter().any(|b| format!("{:?}", b) == k) {
                bounds.push(x);
            }
        }
    };
    fn walk(e: &Z3Expr, add: &mut dyn FnMut(&Z3Expr)) {
        match e {
            Z3Expr::Cmp(_, l, r) => {
                add(l);
                add(r);
            }
            Z3Expr::And(l, r) | Z3Expr::Or(l, r) => {
                walk(l, add);
                walk(r, add);
            }
            Z3Expr::Not(x) => walk(x, add),
            _ => {}
        }
    }
    for inv in &func.blocks[h].invs {
        walk(inv, &mut add);
    }
    for b in &func.blocks {
        for i in &b.insts {
            if let Inst::Cmp { lhs, rhs, .. } = i {
                add(&Z3Expr::Reg(*lhs));
                add(&Z3Expr::Reg(*rhs));
            }
        }
    }
    let mut out = Vec::new();
    for &p in &ps {
        out.push(Z3Expr::Reg(p));
        for x in bounds.iter().filter(|x| !matches!(x, Z3Expr::Reg(r) if *r == p)) {
            out.push(Z3Expr::Bin(BinOp::Sub, Box::new(x.clone()), Box::new(Z3Expr::Reg(p))));
            out.push(Z3Expr::Bin(BinOp::Sub, Box::new(Z3Expr::Reg(p)), Box::new(x.clone())));
        }
    }
    out
}

fn fmt_inst(module: &Module, inst: &Inst) -> String {
    match inst {
        Inst::Const { dst, val, ty } => format!("%{} = const {:#x} {:?}", dst, val, ty),
        Inst::Bin { dst, op, lhs, rhs } => {
            format!("%{} = {} %{} %{}", dst, format!("{:?}", op).to_lowercase(), lhs, rhs)
        }
        Inst::Cmp { dst, op, lhs, rhs } => {
            format!("%{} = cmp {} %{} %{}", dst, format!("{:?}", op).to_lowercase(), lhs, rhs)
        }
        Inst::Slice { dst, base, idx, .. } => format!("%{} = slice %{} %{}", dst, base, idx),
        Inst::Load { dst, base, offset, .. } => format!("%{} = load %{} {}", dst, base, offset),
        Inst::Narrow { dst, src, ty } => format!("%{} = narrow %{} {:?}", dst, src, ty),
        Inst::View { dst, src, .. } => format!("%{} = view %{}", dst, src),
        Inst::Addr { dst, data_id, .. } => format!("%{} = addr #{}", dst, data_id),
        Inst::Store { base, offset, val } => format!("store %{} {} %{}", base, offset, val),
        Inst::Simd256 { op, dst, lhs, rhs } => {
            format!("{:?} %{} %{} %{}", op, dst, lhs, rhs)
        }
        Inst::Parallel { smp, n, func_id, base, arg } => {
            let fname = module.funcs.get(*func_id as usize).map(|f| f.name.as_str()).unwrap_or("?");
            format!("parallel %{} %{} {} %{} %{}", smp, n, fname, base, arg)
        }
        Inst::SmpWorkers { dst, smp } => format!("%{} = smp_workers %{}", dst, smp),
        Inst::AtaRead { cap, ptr, idx, nsec } => format!("ata_read %{} %{} %{} %{}", cap, ptr, idx, nsec),
        Inst::HwIo { dst, cap, port_or_reg, val, is_write } => {
            if *is_write {
                format!("hwio_w %{} {:#x} %{:?}", cap, port_or_reg, val)
            } else {
                format!("%{:?} = hwio_r %{} {:#x}", dst, cap, port_or_reg)
            }
        }
        Inst::Call { dst, func_id, args } => {
            let fname = module
                .funcs
                .get(*func_id as usize)
                .map(|f| f.name.as_str())
                .unwrap_or("?");
            let a_str = args.iter().map(|r| format!("%{}", r)).collect::<Vec<_>>().join(" ");
            match dst {
                Some(d) => format!("%{} = call {} {}", d, fname, a_str),
                None => format!("call {} {}", fname, a_str),
            }
        }
        Inst::CallPtr { dst, target, .. } => match dst {
            Some(d) => format!("%{} = call %{}", d, target),
            None => format!("call %{}", target),
        },
        Inst::Br { cond, then_bb, else_bb } => {
            format!("br %{} @b{} @b{}", cond, then_bb, else_bb)
        }
        Inst::Jmp { target_bb, args } => {
            let a_str = args.iter().map(|r| format!("%{}", r)).collect::<Vec<_>>().join(" ");
            format!("jmp @b{} {}", target_bb, a_str)
        }
        Inst::Assume(_) => "assume ...".into(),
        Inst::Assert(_) => "assert ...".into(),
        Inst::Ret { val } => match val {
            Some(r) => format!("ret %{}", r),
            None => "ret".into(),
        },
    }
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
                        let mut primary = Vec::new();
                        let mut seen = HashSet::new();
                        for &r in &self.cur_regs {
                            if seen.insert(r) {
                                if let Some(bv) = self.regs.get(&r) {
                                    if let Some(v) = m.eval(bv, true).and_then(|b| b.as_u64()) {
                                        primary.push(format!("%{} = {:#x}", r, v));
                                    }
                                }
                            }
                        }
                        let mut ids: Vec<&Reg> = self.regs.keys().collect();
                        ids.sort();
                        let others: Vec<String> = ids
                            .into_iter()
                            .filter(|&&r| !seen.contains(&r))
                            .take(16)
                            .filter_map(|r| {
                                m.eval(&self.regs[r], true)
                                    .and_then(|b| b.as_u64())
                                    .map(|v| format!("%{}={:#x}", r, v))
                            })
                            .collect();
                        if primary.is_empty() {
                            others.join(", ")
                        } else if others.is_empty() {
                            primary.join(", ")
                        } else {
                            format!("{} [ctx: {}]", primary.join(", "), others.join(" "))
                        }
                    })
                    .unwrap_or_default();
                Err(format!(
                    "[Z3 FAIL] func {} @b{}: '{}' -> {} when {}{}",
                    self.func_name, self.cur_bb, self.cur_inst, msg, ce, self.at_line()
                ))
            }
            SatResult::Unknown => Err(format!(
                "[Z3 TIMEOUT] func {} @b{}: '{}' -> Không thể chứng minh: {}{}",
                self.func_name, self.cur_bb, self.cur_inst, msg, self.at_line()
            )),
        };
        self.solver.pop(1);
        out
    }

    /// Dòng phụ "\n    tại file:dòng" (parse_err đọc lại; dòng đầu giữ nguyên định dạng cũ)
    fn at_line(&self) -> String {
        if self.cur_at.is_empty() { String::new() } else { format!("\n    tại {}", self.cur_at) }
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

    /// (layout, độ dài BV) của một kiểu ptr; độ dài động tra trong `env`
    fn ptr_len(&self, ty: Type, env: &Env<'ctx>) -> Result<Option<(u16, BV<'ctx>)>, String> {
        match ty {
            Type::Ptr { layout_id, max_elems } => Ok(Some((layout_id, self.bv(max_elems)))),
            Type::DPtr { layout_id, len } => {
                let l = env
                    .get(&len)
                    .cloned()
                    .ok_or_else(|| format!("độ dài %{} của ptr động chưa được định nghĩa", len))?;
                Ok(Some((layout_id, l)))
            }
            _ => Ok(None),
        }
    }

    fn elem_size(&self, layout_id: u16) -> Result<u64, String> {
        Ok(self.layouts.get(layout_id as usize).ok_or("layout_id không tồn tại")?.size as u64)
    }

    /// Bất biến của ptr động: len * size <= RAM (nên mọi phép tính địa chỉ không tràn) và vùng nằm trong RAM
    fn dptr_valid(&self, bv: &BV<'ctx>, layout_id: u16, len: &BV<'ctx>) -> Result<Bool<'ctx>, String> {
        let sz = self.elem_size(layout_id)?;
        let lim = (RAM_TOP - RAM_MIN) / sz;
        Ok(Bool::and(
            self.ctx,
            &[
                &len.bvule(&self.bv(lim)),
                &bv.bvuge(&self.bv(RAM_MIN)),
                &bv.bvule(&self.bv(RAM_TOP).bvsub(&len.bvmul(&self.bv(sz)))),
            ],
        ))
    }

    /// Bất biến kiểu của con trỏ (tĩnh hoặc động) có giá trị `bv`
    fn any_ptr_valid(&self, bv: &BV<'ctx>, ty: Type) -> Result<Bool<'ctx>, String> {
        match ty {
            Type::Ptr { layout_id, max_elems } => self.ptr_valid(bv, layout_id, max_elems),
            Type::DPtr { layout_id, len } => {
                if int_bits(self.reg_ty(len)?).is_none() {
                    return Err(format!("độ dài %{} của ptr động phải là số nguyên", len));
                }
                self.dptr_valid(bv, layout_id, self.get_reg(len)?)
            }
            _ => Ok(Bool::from_bool(self.ctx, true)),
        }
    }

    /// Vùng của con trỏ %r phải dài ít nhất `n` byte (SIMD)
    fn ptr_min_bytes(&self, r: Reg, n: u64, what: &str) -> Result<(), String> {
        match self.reg_ty(r)? {
            Type::Ptr { layout_id, max_elems } => {
                let bytes = self.ptr_bytes(layout_id, max_elems)?;
                if bytes < n {
                    return Err(format!("{}: %{} chỉ có {} bytes (< {} bytes)", what, r, bytes, n));
                }
                Ok(())
            }
            Type::DPtr { layout_id, len } => {
                let sz = self.elem_size(layout_id)?;
                self.check(
                    &self.get_reg(len)?.bvuge(&self.bv(n.div_ceil(sz))),
                    &format!("{}: ptr động %{} có thể ngắn hơn {} bytes", what, r, n),
                )
            }
            _ => Err(format!("{}: Toán hạng %{} không phải kiểu con trỏ Ptr", what, r)),
        }
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
        if matches!(ty, Type::Ptr { .. } | Type::DPtr { .. }) {
            self.solver.assert(&self.any_ptr_valid(&bv, ty)?);
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

    /// Gán giá trị kiểu `from` (độ dài động tra trong self.regs) vào vị trí kiểu `to` (độ dài động tra trong `to_env`)
    fn assign_check(
        &self,
        val: &BV<'ctx>,
        from: Type,
        to: Type,
        to_env: &Env<'ctx>,
        what: &str,
    ) -> Result<(), String> {
        if !can_delegate(from, to) {
            return Err(format!(
                "Lỗi kiểu/bảo mật: không thể dùng {:?} làm {:?} ({})",
                from, to, what
            ));
        }
        if matches!(from, Type::DPtr { .. }) || matches!(to, Type::DPtr { .. }) {
            let (_, lf) = self.ptr_len(from, &self.regs)?.ok_or("assign: không phải ptr")?;
            let (_, lt) = self.ptr_len(to, to_env)?.ok_or("assign: không phải ptr")?;
            self.check(
                &lt.bvule(&lf),
                &format!("độ dài ptr đích có thể vượt độ dài thật ({})", what),
            )?;
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
            BinOp::Add | BinOp::AddWrap | BinOp::AddSat | BinOp::AddOvf => l.bvadd(r),
            BinOp::Sub | BinOp::SubWrap | BinOp::SubSat | BinOp::SubOvf => l.bvsub(r),
            BinOp::Mul | BinOp::MulWrap | BinOp::MulSat | BinOp::MulOvf => l.bvmul(r),
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
            BinOp::FxMul => l.bvmul(r).bvlshr(&self.bv(16)),
            BinOp::FxDiv => l.bvshl(&self.bv(16)).bvudiv(r),
            BinOp::MulHi => l.zero_ext(64).bvmul(&r.zero_ext(64)).extract(127, 64),
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
            Z3Expr::Math(..) => Err("số học toán học (iadd/isub/...) chỉ dùng dưới phép so sánh".into()),
            Z3Expr::Mem(..) | Z3Expr::Old(..) | Z3Expr::Quant(..) => {
                Err("đặc tả bộ nhớ / lượng từ chỉ checker số nguyên xử lý".into())
            }
        }
    }

    /// Biểu thức toán học tính ĐÚNG bằng bit-vector có dấu `w` bit (đủ rộng theo Z3Expr::wide_bits)
    fn eval_wide(&self, e: &Z3Expr, w: u32, env: &Env<'ctx>, fv: Option<&BV<'ctx>>) -> Result<BV<'ctx>, String> {
        match e {
            Z3Expr::Math(op, l, r) => {
                let (a, b) = (self.eval_wide(l, w, env, fv)?, self.eval_wide(r, w, env, fv)?);
                Ok(match op {
                    MathOp::Add => a.bvadd(&b),
                    MathOp::Sub => a.bvsub(&b),
                    MathOp::Mul => a.bvmul(&b),
                    _ => return Err("idiv / imod chỉ có ở checker số nguyên".into()),
                })
            }
            _ => Ok(self.eval_bv(e, env, fv)?.zero_ext(w - 64)),
        }
    }

    fn eval_bool(
        &self,
        e: &Z3Expr,
        env: &Env<'ctx>,
        fv: Option<&BV<'ctx>>,
    ) -> Result<Bool<'ctx>, String> {
        match e {
            Z3Expr::Cmp(op, l, r) if l.has_math() || r.has_math() => {
                let w = match (l.wide_bits(), r.wide_bits()) {
                    (Some(a), Some(b)) => a.max(b),
                    _ => return Err("mệnh đề toán học này chỉ có ở checker số nguyên".into()),
                };
                let (a, b) = (self.eval_wide(l, w, env, fv)?, self.eval_wide(r, w, env, fv)?);
                Ok(match op {
                    CmpOp::Eq => a._eq(&b),
                    CmpOp::Ne => a._eq(&b).not(),
                    CmpOp::Ult => a.bvslt(&b),
                    CmpOp::Ule => a.bvsle(&b),
                    CmpOp::Ugt => a.bvsgt(&b),
                    CmpOp::Uge => a.bvsge(&b),
                    _ => return Err("so sánh có dấu trên số toán học chỉ có ở checker số nguyên".into()),
                })
            }
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
        let bty = self.reg_ty(base)?;
        let Some(layout_id) = bty.ptr_layout() else {
            return Err(format!("Biến %{} không phải kiểu con trỏ Ptr", base));
        };
        let layout = self
            .layouts
            .get(layout_id as usize)
            .ok_or("layout_id không tồn tại")?;
        match bty {
            Type::Ptr { max_elems, .. } => {
                let max_bytes = max_elems.saturating_mul(layout.size as u64);
                if (offset as u64) >= max_bytes {
                    return Err(format!(
                        "Tràn vùng nhớ Ptr: offset {} >= max_bytes {}",
                        offset, max_bytes
                    ));
                }
            }
            _ => {
                // offset / size < len  <=>  offset < len * size (len * size không tràn nhờ dptr_valid)
                let (_, len) = self.ptr_len(bty, &self.regs)?.ok_or("không phải ptr")?;
                self.check(
                    &self.bv(offset as u64 / layout.size as u64).bvult(&len),
                    &format!("Truy cập offset {} vượt độ dài động của %{}", offset, base),
                )?;
            }
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
            if inv.class() != SpecClass::Bv {
                continue; // checker số nguyên (verify_int.rs) chứng minh
            }
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

    /// Cạnh lùi bi -> ti (ti là đầu vòng): chứng minh biến giảm của ti giảm ngặt. `env_new` = giá trị tham số mới.
    fn check_back_edge(
        &mut self,
        func: &Func,
        cfg: &Cfg,
        bi: usize,
        ti: usize,
        env_new: &Env<'ctx>,
        extra: Option<&Bool<'ctx>>,
    ) -> Result<(), String> {
        if !self.need_term || cfg.pos[ti] > cfg.pos[bi] {
            return Ok(());
        }
        let h = &func.blocks[ti];
        // Bất biến của đích (đã được chứng minh ở cạnh này) làm giả thiết
        let mut hyp = Vec::new();
        for inv in h.invs.iter().filter(|e| e.class() != SpecClass::Rich) {
            hyp.push(self.eval_bool(inv, env_new, None)?);
        }
        let hyp_refs: Vec<&Bool> = hyp.iter().collect();
        let hyp_all = Bool::and(self.ctx, &hyp_refs);
        let goal = |s: &Self, v: &Z3Expr| -> Result<Bool<'ctx>, String> {
            let (old, new) = (s.eval_bv(v, &s.regs, None)?, s.eval_bv(v, env_new, None)?);
            Ok(hyp_all.implies(&new.bvult(&old)))
        };
        if let Some(d) = &h.dec {
            let mut used = vec![];
            expr_regs(d, &mut used);
            let defs: HashMap<Reg, usize> = func
                .blocks
                .iter()
                .enumerate()
                .flat_map(|(k, b)| b.insts.iter().filter_map(|i| i.dst()).chain(b.params.iter().map(|p| p.0)).map(move |r| (r, k)))
                .collect();
            for r in used {
                let ok = h.params.iter().any(|p| p.0 == r)
                    || defs.get(&r).is_none_or(|&b| b != ti && cfg.dom[ti][b]);
                if !ok {
                    return Err(format!(
                        "@dec của @b{}: %{} không phải tham số của block hay biến định nghĩa trước vòng lặp",
                        h.id, r
                    ));
                }
            }
            let g = goal(self, d)?;
            return self.check_with(
                extra,
                &g,
                &format!("Vòng lặp @b{} không chắc dừng: @dec không giảm ngặt (không dấu) trên cạnh này", h.id),
            );
        }
        if !self.term.contains_key(&ti) {
            self.term.insert(ti, dec_candidates(func, cfg, ti));
        }
        let cands = self.term[&ti].clone();
        let mut keep = Vec::new();
        for c in cands {
            let g = goal(self, &c)?;
            if self.check_with(extra, &g, "").is_ok() {
                keep.push(c);
            }
        }
        if keep.is_empty() {
            return Err(format!(
                "[Z3 FAIL] func {} @b{}: '{}' -> Không chứng minh được vòng lặp @b{} dừng: thêm `@dec <biểu_thức>` vào @b{} \
                 (giá trị không dấu giảm ngặt ở mỗi vòng, vd `@dec sub %n %i`), hoặc giới hạn vòng bằng @inv/cmp với cận cố định{}",
                self.func_name, self.cur_bb, self.cur_inst, h.id, h.id, self.at_line()
            ));
        }
        self.term.insert(ti, keep);
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
                    Type::Smp => {
                        if *val != SMP_TABLE || !func.params.iter().any(|&(_, t)| t == ROOT_IO) {
                            return Err(format!(
                                "Bảo mật: chỉ hàm giữ thẻ gốc io<0,0xffff> được tạo thẻ smp, và chỉ tại {:#x} (%{})",
                                SMP_TABLE, dst
                            ));
                        }
                    }
                    Type::DPtr { .. } => {
                        return Err(format!(
                            "Bảo mật: không thể tạo ptr động bằng const tại %{} (chỉ qua slice từ ptr có sẵn)",
                            dst
                        ));
                    }
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
                        // Không còn ngoại lệ cho bảng SMP 0x7e000: trước đây mọi hàm (kể cả App) đều rèn được
                        // ptr<Bất_kỳ, 512 byte> vào đây và ghi đè fn_addr của nhân AP -> thực thi mã tùy ý.
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
                    BinOp::FxMul => self.check(
                        &l.bvmul_no_overflow(&r, false),
                        &format!("Tràn số nhân điểm cố định Q16.16 (fxmul) tại %{}", dst),
                    )?,
                    BinOp::FxDiv => {
                        self.check(
                            &r._eq(&zero).not(),
                            &format!("Lỗi chia cho 0 trong fxdiv tại %{}", dst),
                        )?;
                        self.check(
                            &l.bvult(&self.bv(1u64 << 48)),
                            &format!("Tràn số bị chia Q16.16 (fxdiv lhs >= 2^48) tại %{}", dst),
                        )?;
                    }
                    _ => {}
                }
                let res = self.eval_binop(*op, &l, &r);
                let d = self.decl_reg(*dst, Type::Bv64)?;
                if *op != BinOp::MulHi {
                    self.solver.assert(&d._eq(&res));
                    // Bổ đề thừa nhưng đúng (suy ra được từ d == res): Z3 bit-blast phép chia 64-bit rất chậm nên
                    // không tự tìm ra, vd không chứng minh nổi `x urem y < y` để vòng Euclid dừng (Light-Bench 14).
                    // Có điều kiện r != 0: assert là toàn cục (không kèm điều kiện đường đi), nên bổ đề phải đúng cả khi
                    // lệnh không chạy tới — với r = 0 thì bvudiv = 0xff..ff, `d <= l` sẽ ép sai giá trị l.
                    let nz = r._eq(&zero).not();
                    match op {
                        BinOp::URem => {
                            self.solver.assert(&nz.implies(&d.bvule(&l)));
                            self.solver.assert(&nz.implies(&d.bvult(&r)));
                        }
                        BinOp::UDiv => self.solver.assert(&nz.implies(&d.bvule(&l))),
                        _ => {}
                    }
                } else {
                    // mờ, chỉ giữ cận rẻ và đúng: (a*b) >> 64 <= min(a, b) vì cả hai < 2^64
                    self.solver.assert(&d.bvule(&l));
                    self.solver.assert(&d.bvule(&r));
                }
            }
            Inst::Cmp { dst, op, lhs, rhs } => {
                let cond = self.eval_cmpop(*op, self.get_reg(*lhs)?, self.get_reg(*rhs)?);
                let d = self.decl_reg(*dst, Type::Bv8)?;
                self.solver
                    .assert(&d._eq(&cond.ite(&self.bv(1), &self.bv(0))));
            }
            Inst::Slice { dst, base, idx, ty } => {
                let Some((l1, m_old)) = self.ptr_len(self.reg_ty(*base)?, &self.regs)? else {
                    return Err(format!("Biến %{} trong slice không phải kiểu Ptr", base));
                };
                if let Type::DPtr { len, .. } = *ty {
                    if int_bits(self.reg_ty(len)?).is_none() {
                        return Err(format!("độ dài %{} của ptr động phải là số nguyên", len));
                    }
                }
                let Some((l2, m_new)) = self.ptr_len(*ty, &self.regs)? else {
                    return Err(format!("Kiểu đích của slice tại %{} phải là ptr", dst));
                };
                if l1 != l2 || matches!(ty, Type::Ptr { max_elems: 0, .. }) {
                    return Err(format!(
                        "Kiểu đích của slice tại %{} phải cùng Layout với base và max_elems > 0",
                        dst
                    ));
                }
                let (base_bv, idx_bv) = (self.get_reg(*base)?.clone(), self.get_reg(*idx)?.clone());
                self.check(
                    &idx_bv.bvadd_no_overflow(&m_new, false),
                    &format!("Tràn số cộng index khi slice tại %{}", dst),
                )?;
                self.check(
                    &idx_bv.bvadd(&m_new).bvule(&m_old),
                    &format!("Tràn biên mảng khi slice tại %{}", dst),
                )?;
                let elem = self.bv(self.layouts[l2 as usize].size as u64);
                let d = self.decl_raw(*dst, *ty)?;
                self.solver
                    .assert(&d._eq(&base_bv.bvadd(&idx_bv.bvmul(&elem))));
                let valid = self.any_ptr_valid(&d, *ty)?;
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
            Inst::Addr { dst, data_id, ty } => {
                let d = module.datas.get(*data_id as usize).ok_or("addr: data không tồn tại")?;
                if *ty != (Type::Ptr { layout_id: d.layout_id, max_elems: d.count }) {
                    return Err(format!("addr %{}: kiểu không khớp data '{}'", dst, d.name));
                }
                self.decl_reg(*dst, *ty)?;
            }
            Inst::View { dst, src, ty } => {
                let Some((l1, m_old)) = self.ptr_len(self.reg_ty(*src)?, &self.regs)? else {
                    return Err(format!("view: %{} không phải ptr", src));
                };
                if let Type::DPtr { len, .. } = *ty {
                    if int_bits(self.reg_ty(len)?).is_none() {
                        return Err(format!("độ dài %{} của ptr động phải là số nguyên", len));
                    }
                }
                let Some((l2, m_new)) = self.ptr_len(*ty, &self.regs)? else {
                    return Err(format!("view: kiểu đích của %{} phải là ptr", dst));
                };
                for l in [l1, l2] {
                    let lay = &self.layouts[l as usize];
                    if lay.fields.iter().any(|f| f.inv.is_some()) {
                        return Err(format!(
                            "Bảo mật: view không dùng được với Layout '{}' có @inv (ghi qua kiểu khác sẽ phá bất biến)",
                            lay.name
                        ));
                    }
                }
                // heap theo kiểu của checker số nguyên (verify_int.rs) cần: hai phần tử cùng Layout không chồng một phần.
                // slice giữ điều đó; view giữ nếu kích thước đích chia hết kích thước nguồn (vd qword -> byte).
                let (z1, z2) = (self.elem_size(l1)?, self.elem_size(l2)?);
                if z2 == 0 || z1 % z2 != 0 {
                    return Err(format!(
                        "view %{}: kích thước phần tử đích ({} byte) phải chia hết kích thước nguồn ({} byte)",
                        dst, z2, z1
                    ));
                }
                let (s1, s2) = (self.bv(z1), self.bv(z2));
                self.check(
                    &m_new.bvmul_no_overflow(&s2, false),
                    &format!("view %{}: tràn số khi tính số byte đích", dst),
                )?;
                self.check(
                    &m_old.bvmul_no_overflow(&s1, false),
                    &format!("view %{}: tràn số khi tính số byte nguồn", dst),
                )?;
                self.check(
                    &m_new.bvmul(&s2).bvule(&m_old.bvmul(&s1)),
                    &format!("view %{}: vùng đích lớn hơn vùng nguồn", dst),
                )?;
                let s = self.get_reg(*src)?.clone();
                let d = self.decl_raw(*dst, *ty)?;
                self.solver.assert(&d._eq(&s));
                let valid = self.any_ptr_valid(&d, *ty)?;
                self.check(&valid, &format!("Con trỏ view tại %{} ra ngoài RAM", dst))?;
                self.assume(&valid);
            }
            Inst::Narrow { dst, src, ty } => {
                if int_bits(self.reg_ty(*src)?).is_none() {
                    return Err(format!("narrow: %{} phải là số nguyên", src));
                }
                let Some(bits) = int_bits(*ty).filter(|&b| b < 64) else {
                    return Err(format!("narrow %{}: kiểu đích phải là bv8/bv16/bv32", dst));
                };
                let v = self.get_reg(*src)?.clone();
                self.check(
                    &v.bvule(&self.bv((1u64 << bits) - 1)),
                    &format!("narrow %{}: giá trị %{} không vừa {} bit", dst, src, bits),
                )?;
                let d = self.decl_reg(*dst, *ty)?;
                self.solver.assert(&d._eq(&v));
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
            Inst::Simd256 { op, dst, lhs, rhs } => {
                for &ptr_reg in &[*lhs, *rhs] {
                    self.ptr_min_bytes(ptr_reg, 32, "Tràn vùng nhớ SIMD 256-bit")?;
                }
                if *op == SimdOp::Dot {
                    self.decl_reg(*dst, Type::Bv64)?;
                } else {
                    self.ptr_min_bytes(*dst, 32, "Tràn vùng nhớ SIMD 256-bit (đích)")?;
                    let layout_id = self.reg_ty(*dst)?.ptr_layout().ok_or("SIMD: đích không phải ptr")?;
                    let layout = &self.layouts[layout_id as usize];
                    if layout.fields.iter().any(|f| f.inv.is_some()) {
                        return Err(format!(
                            "Bảo mật SIMD 256-bit: Không ghi đè 32-byte trực tiếp lên Layout '{}' có @inv",
                            layout.name
                        ));
                    }
                }
            }
            Inst::Parallel { smp, n, func_id, base, arg } => {
                if self.reg_ty(*smp)? != Type::Smp {
                    return Err(format!("parallel: %{} phải là thẻ smp", smp));
                }
                let worker = module.funcs.get(*func_id as usize).ok_or("parallel: hàm không tồn tại")?;
                let Some((lb, mb)) = self.ptr_len(self.reg_ty(*base)?, &self.regs)? else {
                    return Err(format!("parallel: %{} phải là ptr", base));
                };
                let (wp, wt) = match worker.params.as_slice() {
                    [(p0, Type::Ptr { layout_id, max_elems }), (p1, Type::Bv64), (p2, Type::Bv64)]
                        if *layout_id == lb =>
                    {
                        ([*p0, *p1, *p2], *max_elems)
                    }
                    _ => {
                        return Err(format!(
                            "parallel: worker '{}' phải có chữ ký (ptr<{},K>, bv64 arg, bv64 chỉ_số)",
                            worker.name, self.layouts[lb as usize].name
                        ));
                    }
                };
                if int_bits(self.reg_ty(*n)?).is_none() || int_bits(self.reg_ty(*arg)?).is_none() {
                    return Err("parallel: %n và %arg phải là số nguyên".into());
                }
                let n_bv = self.get_reg(*n)?.clone();
                self.check(
                    &Bool::and(self.ctx, &[&n_bv.bvuge(&self.bv(1)), &n_bv.bvule(&self.bv(16))]),
                    &format!("parallel: số phần %{} phải thuộc [1..16]", n),
                )?;
                // n phần, mỗi phần K phần tử, phải nằm trọn trong %base (M phần tử). n <= 16 nên n*K không tràn.
                self.check(
                    &n_bv.bvmul(&self.bv(wt)).bvule(&mb),
                    &format!("parallel: %{} phần x {} phần tử vượt kích thước %{}", n, wt, base),
                )?;
                // @req của worker phải đúng với MỌI chỉ số i < n
                let i = BV::fresh_const(self.ctx, "par_i", 64);
                let in_range = i.bvult(&n_bv);
                let elem = self.layouts[lb as usize].size as u64;
                let mut env = HashMap::new();
                env.insert(wp[0], self.get_reg(*base)?.bvadd(&i.bvmul(&self.bv(wt * elem))));
                env.insert(wp[1], self.get_reg(*arg)?.clone());
                env.insert(wp[2], i.clone());
                for (k, req) in worker.requires.iter().enumerate() {
                    if req.class() != SpecClass::Bv {
                        return Err(format!("parallel: @req #{} của worker '{}' dùng số học toán học (chưa hỗ trợ)", k, worker.name));
                    }
                    self.check_with(
                        Some(&in_range),
                        &self.eval_bool(req, &env, None)?,
                        &format!("parallel: vi phạm @req #{} của worker '{}' với một chỉ số phần", k, worker.name),
                    )?;
                }
            }
            Inst::SmpWorkers { dst, smp } => {
                if self.reg_ty(*smp)? != Type::Smp {
                    return Err(format!("smp_workers: %{} phải là thẻ smp", smp));
                }
                let d = self.decl_reg(*dst, Type::Bv64)?;
                self.solver.assert(&d.bvule(&self.bv(15)));
            }
            Inst::AtaRead { cap, ptr, idx, nsec } => {
                let Type::Io { min, max } = self.reg_ty(*cap)? else {
                    return Err(format!("Bảo mật I/O: %{} không phải thẻ Type::Io", cap));
                };
                if 0x1F0 < min || 0x1F0 > max {
                    return Err("ata_read: cổng 0x1F0 nằm ngoài thẻ io".into());
                }
                let Some((layout_id, plen)) = self.ptr_len(self.reg_ty(*ptr)?, &self.regs)? else {
                    return Err(format!("ata_read: %{} phải là con trỏ", ptr));
                };
                let lay = &self.layouts[layout_id as usize];
                if lay.fields.iter().any(|f| f.inv.is_some()) {
                    return Err(format!(
                        "ata_read: không được ghi byte thô từ đĩa vào Layout '{}' có @inv (load sau đó sẽ tin @inv sai)",
                        lay.name
                    ));
                }
                let esz = lay.size as u64;
                let (i_bv, n_bv) = (self.get_reg(*idx)?.clone(), self.get_reg(*nsec)?.clone());
                self.check(&n_bv.bvuge(&self.bv(1)), "ata_read: nsec phải >= 1")?;
                self.check(&n_bv.bvule(&self.bv(256)), "ata_read: nsec phải <= 256")?;
                self.check(&i_bv.bvule(&self.bv(1 << 20)), "ata_read: idx quá lớn")?;
                self.check(
                    &i_bv.bvadd(&n_bv).bvmul(&self.bv(512)).bvule(&plen.bvmul(&self.bv(esz))),
                    "ata_read: ghi vượt biên vùng nhớ đích",
                )?;
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
                        let limit = if vty == Type::Bv32 {
                            0xFFFF_FFFF
                        } else if *port == 0x1F0 || vty == Type::Bv16 {
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
                        self.assume(&bv.bvule(&self.bv(hwio_read_limit(*port))));
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
                for (&a, &(p, _)) in args.iter().zip(&callee.params) {
                    env.insert(p, self.get_reg(a)?.clone());
                }
                for (&a, &(p, pty)) in args.iter().zip(&callee.params) {
                    self.assign_check(
                        &env[&p],
                        self.reg_ty(a)?,
                        pty,
                        &env,
                        &format!("đối số %{} của '{}'", a, callee.name),
                    )?;
                }
                for (i, req) in callee.requires.iter().enumerate() {
                    if req.class() != SpecClass::Bv {
                        continue; // checker số nguyên chứng minh
                    }
                    self.check(
                        &self.eval_bool(req, &env, None)?,
                        &format!("Vi phạm @req #{} khi gọi hàm '{}'", i, callee.name),
                    )?;
                }
                if let Some(d) = dst {
                    let mut rty = callee.ret_ty.ok_or_else(|| {
                        format!("'{}' là hàm void nhưng gán vào %{}", callee.name, d)
                    })?;
                    // ptr<L,%tham_số> của callee -> ptr<L,%đối_số> của người gọi
                    if let Type::DPtr { layout_id, len } = rty {
                        let j = callee
                            .params
                            .iter()
                            .position(|&(p, _)| p == len)
                            .ok_or("kiểu trả về ptr động tham chiếu biến không phải tham số")?;
                        rty = Type::DPtr { layout_id, len: args[j] };
                    }
                    let dbv = self.decl_reg(*d, rty)?;
                    if !callee.ensures.is_empty() {
                        if let Some(r) = result_reg(callee) {
                            env.insert(r, dbv);
                        }
                        for ens in callee.ensures.iter().filter(|e| e.class() != SpecClass::Rich) {
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
                    let env = self.regs.clone();
                    self.check_back_edge(func, cfg, bi, ti, &env, Some(&extra))?;
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
                for (&a, &(p, _)) in args.iter().zip(&tb.params) {
                    env.insert(p, self.get_reg(a)?.clone());
                }
                for (&a, &(p, pty)) in args.iter().zip(&tb.params) {
                    self.assign_check(
                        &env[&p],
                        self.reg_ty(a)?,
                        pty,
                        &env,
                        &format!("tham số %{} của jmp @b{}", p, tb.id),
                    )?;
                }
                self.check_target_invs(func, ti, &env, None)?;
                self.check_back_edge(func, cfg, bi, ti, &env, None)?;
                if cfg.pos[ti] > cfg.pos[bi] && !tb.params.is_empty() {
                    let vals = tb.params.iter().map(|(p, _)| env[p].clone()).collect();
                    self.edge_args.entry(ti).or_default().push((self.cur_cond.clone(), vals));
                }
                self.add_pred(bi, ti, self.cur_cond.clone());
            }
            Inst::Assume(e) => {
                if !func.params.iter().any(|&(_, t)| t == ROOT_IO) {
                    return Err(format!(
                        "Bảo mật: `assume` là tiên đề không được chứng minh — chỉ hàm giữ thẻ gốc io<0,0xffff> được dùng ('{}' không có)",
                        func.name
                    ));
                }
                if e.class() != SpecClass::Rich {
                    self.assume(&self.ev(e)?);
                }
                self.n_assume += 1;
            }
            Inst::Assert(e) if e.class() != SpecClass::Bv => {}
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
                        &self.regs,
                        &format!("giá trị trả về %{}", r),
                    )?;
                }
                // @ens kiểm tại TỪNG ret: tên giá trị trả về trong @ens được gán bằng thanh ghi ret này
                let mut env = self.regs.clone();
                if let (Some(rr), Some(r)) = (result_reg(func), val) {
                    env.insert(rr, self.get_reg(*r)?.clone());
                }
                for (i, ens) in func.ensures.iter().enumerate() {
                    if ens.class() != SpecClass::Bv {
                        continue;
                    }
                    self.check(
                        &self.eval_bool(ens, &env, None)?,
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

/// Trả số lệnh `assume` (tiên đề không được chứng minh)
pub fn verify_func(module: &Module, func: &Func) -> Result<u32, String> {
    if std::env::var_os("LIGHT_INT_ONLY").is_some() {
        // chỉ để kiểm thử checker số nguyên (chống chứng minh rỗng): KHÔNG kiểm an toàn
        return crate::verify_int::verify(module, func, true).map(|_| 0);
    }
    verify_inner(module, func)
        .and_then(|n| {
            // An toàn (tràn, biên, dừng) do checker BV ở trên chứng minh; mệnh đề toán học / giàu do checker số nguyên
            let all = std::env::var_os("LIGHT_INT_ALL").is_some();
            if all || crate::verify_int::needed(module, func) {
                crate::verify_int::verify(module, func, all)?;
            }
            Ok(n)
        })
        .map_err(|e| {
        if e.starts_with("[Z3 ") {
            e
        } else {
            format!("[func '{}'] {}", func.name, e)
        }
    })
}

fn verify_inner(module: &Module, func: &Func) -> Result<u32, String> {
    let cfg = build_cfg(func)?;
    check_ssa(func, &cfg)?;
    check_dyn_scopes(func)?;
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
        func_name: &func.name,
        cur_bb: 0,
        cur_inst: String::new(),
        cur_at: String::new(),
        cur_regs: Vec::new(),
        regs: HashMap::new(),
        reg_tys: HashMap::new(),
        cur_cond: None,
        conds: HashMap::from([(0, None)]),
        pos: cfg.pos.clone(),
        n_assume: 0,
        edge_args: HashMap::new(),
        need_term: !func.params.iter().any(|&(_, t)| matches!(t, Type::Io { .. })),
        term: HashMap::new(),
    };

    for &(r, ty) in &func.params {
        v.decl_reg(r, ty)?;
    }
    for req in func.requires.iter().filter(|e| e.class() != SpecClass::Rich) {
        v.solver.assert(&v.ev(req)?);
    }

    // block là đích của cạnh lùi (đầu vòng lặp)
    let mut back_target = vec![false; func.blocks.len()];
    for (bi, b) in func.blocks.iter().enumerate() {
        for t in b.insts.iter().flat_map(|i| match i {
            Inst::Br { then_bb, else_bb, .. } => vec![*then_bb, *else_bb],
            Inst::Jmp { target_bb, .. } => vec![*target_bb],
            _ => vec![],
        }) {
            if let Some(&ti) = cfg.idx.get(&t) {
                if cfg.pos[ti] <= cfg.pos[bi] {
                    back_target[ti] = true;
                }
            }
        }
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
        v.cur_bb = block.id;
        v.cur_inst = format!("@b{} entry", block.id);
        v.cur_at = block.label_at.clone();
        v.cur_regs = block.params.iter().map(|&(r, _)| r).collect();
        for &(r, ty) in &block.params {
            v.decl_reg(r, ty)?;
        }
        // Block nối (có tham số, KHÔNG có cạnh lùi vào — không phải đầu vòng lặp): mỗi cạnh jmp tiến e cho
        // `điều_kiện(e) => tham_số == đối_số(e)`. Đúng đắn: nguồn của jmp chỉ có một đích nên trong một lần chạy chỉ một
        // cạnh tiến vào được đi qua; điều kiện đường đi chính xác trên phần không vòng của CFG. Đầu vòng lặp thì giá trị
        // khác nhau mỗi vòng nên vẫn chỉ biết @inv như cũ.
        if !block.params.is_empty() && !back_target[bi] {
            for (c, vals) in v.edge_args.get(&bi).cloned().unwrap_or_default() {
                let eqs: Vec<Bool> = block.params.iter().zip(&vals).map(|((p, _), a)| v.regs[p]._eq(a)).collect();
                let all = Bool::and(&ctx, &eqs.iter().collect::<Vec<_>>());
                match c {
                    Some(c) => v.solver.assert(&c.implies(&all)),
                    None => v.solver.assert(&all),
                }
            }
        }
        for inv in block.invs.iter().filter(|e| e.class() != SpecClass::Rich) {
            v.assume(&v.ev(inv)?);
        }
        if (!block.params.is_empty() || !block.invs.is_empty()) && !v.feasible() {
            return Err(format!(
                "@inv của @b{} mâu thuẫn nhau/với đường đi tới nó",
                block.id
            ));
        }
        for (k, inst) in block.insts.iter().enumerate() {
            v.cur_inst = fmt_inst(module, inst);
            v.cur_at = block.at.get(k).cloned().unwrap_or_default();
            v.cur_regs = uses_of(inst);
            if let Some(d) = dst_of(inst) {
                v.cur_regs.push(d);
            }
            v.step(module, func, &cfg, bi, inst)?;
        }
    }
    if v.n_assume > 0 {
        eprintln!(
            "  ⚠ func '{}': {} lệnh `assume` (tiên đề — KHÔNG được Z3 chứng minh)",
            func.name, v.n_assume
        );
    }
    Ok(v.n_assume as u32)
}
