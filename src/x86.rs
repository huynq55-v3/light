// File: src/x86.rs — Sinh mã x86-64 cho một hàm Light (gọi từ elf64.rs)
//
// 1. Liveness theo block (tham số block = định nghĩa ở đầu block, đối số jmp = dùng ở cuối block nguồn).
// 2. Cấp phát thanh ghi linear scan trên một khoảng sống bảo thủ [đầu, cuối] mỗi biến SSA:
//    rbx r12..r15 (callee-saved, cho biến sống qua lời gọi) + rsi rdi r8..r11 (caller-saved, biến còn lại).
//    Thiếu thanh ghi -> tràn ra stack [rbp - ...]. rax/rcx/rdx luôn là thanh ghi tạm, không bao giờ được cấp.
// 3. Hằng số không chiếm thanh ghi: mỗi lần dùng được nhúng thẳng làm toán hạng tức thời (imm).
// 4. `cmp` chỉ dùng bởi `br` ngay sau nó -> cmp + jcc (không setcc). Block kế tiếp -> bỏ lệnh jmp.
// 5. Đối số jmp/call được chép SONG SONG (xử lý chu trình hoán vị qua rax) — đúng ngữ nghĩa SSA.
// Giữ nguyên ngữ nghĩa từng lệnh của bộ sinh mã cũ (cùng phép x86 cho chia/fx/hwio/simd), chỉ khác vị trí toán hạng.
use crate::ir::*;
use std::collections::{HashMap, HashSet};

const RAX: u8 = 0;
const RCX: u8 = 1;
const RDX: u8 = 2;
const RBP: u8 = 5;
const RSI: u8 = 6;
const RDI: u8 = 7;
const R8: u8 = 8;
const R9: u8 = 9;
const R11: u8 = 11;
const CALLEE: [u8; 5] = [3, 12, 13, 14, 15];
const CALLER: [u8; 6] = [RSI, RDI, R8, R9, 10, R11];
const ABI: [u8; 6] = [RDI, RSI, RDX, RCX, R8, R9];

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Loc {
    R(u8),
    S(i32), // [rbp + disp]
}
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Opd {
    L(Loc),
    I(u64),
}
#[derive(Clone, Copy)]
enum Rm {
    R(u8),
    M(u8, i32),
    X(u8, u8, u8, i32), // [base + idx << scale + disp]
}

fn rm_of(l: Loc) -> Rm {
    match l {
        Loc::R(r) => Rm::R(r),
        Loc::S(d) => Rm::M(RBP, d),
    }
}
fn fits32(v: u64) -> bool {
    (v as i64) >= i32::MIN as i64 && (v as i64) <= i32::MAX as i64
}
fn fits8(v: i64) -> bool {
    (-128..=127).contains(&v)
}

// ---------------------------------------------------------------------------- bộ mã hóa lệnh
fn op_rm(c: &mut Vec<u8>, p66: bool, w: bool, force_rex: bool, op: &[u8], reg: u8, rm: Rm) {
    if p66 {
        c.push(0x66);
    }
    let (base, idx) = match rm {
        Rm::R(r) => (r, 0),
        Rm::M(b, _) => (b, 0),
        Rm::X(b, i, _, _) => (b, i),
    };
    let rex = 0x40 | (w as u8) << 3 | ((reg >> 3) & 1) << 2 | ((idx >> 3) & 1) << 1 | ((base >> 3) & 1);
    if rex != 0x40 || force_rex {
        c.push(rex);
    }
    c.extend_from_slice(op);
    match rm {
        Rm::R(r) => c.push(0xC0 | (reg & 7) << 3 | (r & 7)),
        Rm::M(b, d) => {
            let md = if d == 0 && b & 7 != 5 { 0x00 } else if fits8(d as i64) { 0x40 } else { 0x80 };
            c.push(md | (reg & 7) << 3 | (b & 7));
            if b & 7 == 4 {
                c.push(0x24);
            }
            match md {
                0x40 => c.push(d as u8),
                0x80 => c.extend_from_slice(&d.to_le_bytes()),
                _ => {}
            }
        }
        Rm::X(b, i, sc, d) => {
            let md = if d == 0 && b & 7 != 5 { 0x00 } else if fits8(d as i64) { 0x40 } else { 0x80 };
            c.push(md | (reg & 7) << 3 | 4);
            c.push(sc << 6 | (i & 7) << 3 | (b & 7));
            match md {
                0x40 => c.push(d as u8),
                0x80 => c.extend_from_slice(&d.to_le_bytes()),
                _ => {}
            }
        }
    }
}
fn mov_rr(c: &mut Vec<u8>, d: u8, s: u8) {
    if d != s {
        op_rm(c, false, true, false, &[0x89], s, Rm::R(d));
    }
}
fn mov_ri(c: &mut Vec<u8>, d: u8, v: u64) {
    if v == 0 {
        op_rm(c, false, false, false, &[0x31], d, Rm::R(d)); // xor r32, r32
    } else if v <= u32::MAX as u64 {
        if d >= 8 {
            c.push(0x41);
        }
        c.push(0xB8 + (d & 7));
        c.extend_from_slice(&(v as u32).to_le_bytes());
    } else if fits32(v) {
        op_rm(c, false, true, false, &[0xC7], 0, Rm::R(d));
        c.extend_from_slice(&(v as u32).to_le_bytes());
    } else {
        c.push(0x48 | (d >> 3));
        c.push(0xB8 + (d & 7));
        c.extend_from_slice(&v.to_le_bytes());
    }
}
/// Nạp toán hạng vào thanh ghi vật lý `d`
fn load(c: &mut Vec<u8>, d: u8, o: Opd) {
    match o {
        Opd::I(v) => mov_ri(c, d, v),
        Opd::L(Loc::R(r)) => mov_rr(c, d, r),
        Opd::L(Loc::S(x)) => op_rm(c, false, true, false, &[0x8B], d, Rm::M(RBP, x)),
    }
}
/// Ghi thanh ghi vật lý `s` vào vị trí `l`
fn save(c: &mut Vec<u8>, l: Loc, s: u8) {
    match l {
        Loc::R(r) => mov_rr(c, r, s),
        Loc::S(x) => op_rm(c, false, true, false, &[0x89], s, Rm::M(RBP, x)),
    }
}
/// Chép một giá trị tới vị trí bất kỳ (mem->mem và imm64->mem đi qua rcx)
fn mov_any(c: &mut Vec<u8>, d: Loc, s: Opd) {
    match (d, s) {
        (Loc::R(r), _) => load(c, r, s),
        (Loc::S(_), Opd::L(Loc::R(r))) => save(c, d, r),
        (Loc::S(x), Opd::I(v)) if fits32(v) => {
            op_rm(c, false, true, false, &[0xC7], 0, Rm::M(RBP, x));
            c.extend_from_slice(&(v as u32).to_le_bytes());
        }
        (Loc::S(_), _) => {
            load(c, RCX, s);
            save(c, d, RCX);
        }
    }
}
/// Phép ALU hai ngôi `w op= o`: (opcode dạng reg,r/m ; mã mở rộng nhóm 0x81)
fn alu(c: &mut Vec<u8>, regop: u8, ext: u8, w: u8, o: Opd) {
    match o {
        Opd::I(v) if fits32(v) => {
            if fits8(v as i64) {
                op_rm(c, false, true, false, &[0x83], ext, Rm::R(w));
                c.push(v as u8);
            } else {
                op_rm(c, false, true, false, &[0x81], ext, Rm::R(w));
                c.extend_from_slice(&(v as u32).to_le_bytes());
            }
        }
        Opd::I(v) => {
            mov_ri(c, RCX, v);
            op_rm(c, false, true, false, &[regop], w, Rm::R(RCX));
        }
        Opd::L(l) => op_rm(c, false, true, false, &[regop], w, rm_of(l)),
    }
}
fn imul(c: &mut Vec<u8>, w: u8, o: Opd) {
    match o {
        Opd::I(v) if fits32(v) => {
            if fits8(v as i64) {
                op_rm(c, false, true, false, &[0x6B], w, Rm::R(w));
                c.push(v as u8);
            } else {
                op_rm(c, false, true, false, &[0x69], w, Rm::R(w));
                c.extend_from_slice(&(v as u32).to_le_bytes());
            }
        }
        Opd::I(v) => {
            mov_ri(c, RCX, v);
            op_rm(c, false, true, false, &[0x0F, 0xAF], w, Rm::R(RCX));
        }
        Opd::L(l) => op_rm(c, false, true, false, &[0x0F, 0xAF], w, rm_of(l)),
    }
}
fn push_r(c: &mut Vec<u8>, r: u8) {
    if r >= 8 {
        c.push(0x41);
    }
    c.push(0x50 + (r & 7));
}
fn pop_r(c: &mut Vec<u8>, r: u8) {
    if r >= 8 {
        c.push(0x41);
    }
    c.push(0x58 + (r & 7));
}
fn rsp_add(c: &mut Vec<u8>, n: i32, sub: bool) {
    let ext = if sub { 5 } else { 0 };
    if fits8(n as i64) {
        op_rm(c, false, true, false, &[0x83], ext, Rm::R(4));
        c.push(n as u8);
    } else {
        op_rm(c, false, true, false, &[0x81], ext, Rm::R(4));
        c.extend_from_slice(&n.to_le_bytes());
    }
}

/// Chép song song: mọi nguồn được đọc trước khi bất kỳ đích nào bị ghi. Chu trình được phá bằng rax.
/// Đích không bao giờ là rax; nguồn mem->mem (chỉ có ở jmp) đi qua rcx.
fn par_move(c: &mut Vec<u8>, moves: Vec<(Loc, Opd)>) {
    let mut pend: Vec<(Loc, Opd)> = moves.into_iter().filter(|(d, s)| *s != Opd::L(*d)).collect();
    while !pend.is_empty() {
        let free = (0..pend.len()).find(|&i| !pend.iter().enumerate().any(|(j, m)| j != i && m.1 == Opd::L(pend[i].0)));
        if let Some(i) = free {
            let (d, s) = pend.remove(i);
            mov_any(c, d, s);
        } else {
            let d0 = pend[0].0;
            load(c, RAX, Opd::L(d0));
            for m in pend.iter_mut() {
                if m.1 == Opd::L(d0) {
                    m.1 = Opd::L(Loc::R(RAX));
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------- phân tích
/// Toán hạng mà mã máy thực sự đọc (bỏ thẻ quyền io và lệnh ghost)
fn uses(i: &Inst) -> Vec<Reg> {
    match i {
        Inst::Bin { lhs, rhs, .. } | Inst::Cmp { lhs, rhs, .. } => vec![*lhs, *rhs],
        Inst::Slice { base, idx, .. } => vec![*base, *idx],
        Inst::Load { base, .. } => vec![*base],
        Inst::Store { base, val, .. } => vec![*base, *val],
        Inst::Narrow { src, .. } => vec![*src],
        Inst::Simd256 { op: SimdOp::Dot, lhs, rhs, .. } => vec![*lhs, *rhs],
        Inst::Simd256 { dst, lhs, rhs, .. } => vec![*lhs, *rhs, *dst],
        Inst::Parallel { smp, n, base, arg, .. } => vec![*smp, *n, *base, *arg],
        Inst::SmpWorkers { smp, .. } => vec![*smp],
        Inst::HwIo { val, is_write: true, .. } => val.iter().copied().collect(),
        Inst::AtaRead { ptr, idx, nsec, .. } => vec![*ptr, *idx, *nsec],
        Inst::Br { cond, .. } => vec![*cond],
        Inst::Jmp { args, .. } | Inst::Call { args, .. } => args.clone(),
        Inst::CallPtr { target, args, .. } => args.iter().copied().chain([*target]).collect(),
        Inst::Ret { val } => val.iter().copied().collect(),
        _ => vec![],
    }
}
fn def(i: &Inst) -> Option<Reg> {
    match i {
        Inst::Bin { dst, .. }
        | Inst::Cmp { dst, .. }
        | Inst::Slice { dst, .. }
        | Inst::Load { dst, .. }
        | Inst::Narrow { dst, .. }
        | Inst::SmpWorkers { dst, .. }
        | Inst::Simd256 { op: SimdOp::Dot, dst, .. } => Some(*dst),
        Inst::HwIo { dst, is_write: false, .. } | Inst::Call { dst, .. } | Inst::CallPtr { dst, .. } => *dst,
        _ => None,
    }
}
fn is_call(i: &Inst) -> bool {
    matches!(i, Inst::Call { .. } | Inst::CallPtr { .. } | Inst::Parallel { .. })
}
fn cc_of(op: CmpOp) -> u8 {
    match op {
        CmpOp::Eq => 0x4,
        CmpOp::Ne => 0x5,
        CmpOp::Ult => 0x2,
        CmpOp::Ule => 0x6,
        CmpOp::Ugt => 0x7,
        CmpOp::Uge => 0x3,
        CmpOp::Slt => 0xC,
        CmpOp::Sle => 0xE,
        CmpOp::Sgt => 0xF,
        CmpOp::Sge => 0xD,
    }
}
/// Điều kiện khi đổi chỗ hai vế (a op b  <=>  b op' a)
fn cc_swap(cc: u8) -> u8 {
    match cc {
        0x2 => 0x7,
        0x7 => 0x2,
        0x6 => 0x3,
        0x3 => 0x6,
        0xC => 0xF,
        0xF => 0xC,
        0xE => 0xD,
        0xD => 0xE,
        x => x,
    }
}

pub fn reg_types(module: &Module, func: &Func) -> HashMap<Reg, Type> {
    let mut t: HashMap<Reg, Type> = func.params.iter().cloned().collect();
    for b in &func.blocks {
        t.extend(b.params.iter().cloned());
        for i in &b.insts {
            match i {
                Inst::Const { dst, ty, .. } | Inst::Load { dst, ty, .. } | Inst::Narrow { dst, ty, .. } | Inst::Slice { dst, ty, .. } => {
                    t.insert(*dst, *ty);
                }
                Inst::Cmp { dst, .. } => {
                    t.insert(*dst, Type::Bv8);
                }
                Inst::Call { dst: Some(dst), func_id, .. } => {
                    if let Some(ty) = module.funcs[*func_id as usize].ret_ty {
                        t.insert(*dst, ty);
                    }
                }
                _ => {
                    if let Some(d) = def(i) {
                        t.insert(d, Type::Bv64);
                    }
                }
            }
        }
    }
    t
}

// ---------------------------------------------------------------------------- sinh mã
/// Sinh mã cho `func` vào cuối `code`. `call_patches`: (vị trí rel32, func_id); `rt_patches`: vị trí rel32 gọi lt_parallel.
pub fn emit_func(
    module: &Module,
    func: &Func,
    code: &mut Vec<u8>,
    call_patches: &mut Vec<(usize, u32)>,
    rt_patches: &mut Vec<usize>,
) -> Result<(), String> {
    let reg_tys = reg_types(module, func);
    let consts: HashMap<Reg, u64> = func
        .blocks
        .iter()
        .flat_map(|b| &b.insts)
        .filter_map(|i| if let Inst::Const { dst, val, .. } = i { Some((*dst, *val)) } else { None })
        .collect();
    let bidx: HashMap<BlockId, usize> = func.blocks.iter().enumerate().map(|(i, b)| (b.id, i)).collect();
    let blk = |id: BlockId| bidx.get(&id).copied().ok_or_else(|| format!("{}: không tìm thấy @b{}", func.name, id));

    // Số lần dùng lúc chạy (không tính hằng) + cmp gộp được vào br ngay sau
    let mut nuse: HashMap<Reg, u32> = HashMap::new();
    for i in func.blocks.iter().flat_map(|b| &b.insts) {
        for r in uses(i) {
            *nuse.entry(r).or_insert(0) += 1;
        }
    }
    let mut fused: HashSet<Reg> = HashSet::new();
    for b in &func.blocks {
        for w in b.insts.windows(2) {
            if let (Inst::Cmp { dst, .. }, Inst::Br { cond, .. }) = (&w[0], &w[1]) {
                if dst == cond && nuse.get(dst) == Some(&1) {
                    fused.insert(*dst);
                }
            }
        }
    }
    // slice chỉ dùng bởi load/store ngay sau, phần tử 1/2/4/8 byte -> gộp vào địa chỉ [base + idx*sz + off]
    let mut folded: HashMap<Reg, (Reg, Reg, u8)> = HashMap::new();
    for b in &func.blocks {
        for w in b.insts.windows(2) {
            let Inst::Slice { dst, base, idx, ty } = &w[0] else { continue };
            let sz = module.layouts[ty.ptr_layout().ok_or("Lỗi kiểu Slice")? as usize].size as u64;
            let off = match &w[1] {
                Inst::Load { base: lb, offset, .. } if lb == dst => *offset,
                Inst::Store { base: sb, val, offset } if sb == dst && val != dst => *offset,
                _ => continue,
            };
            let disp_ok = match consts.get(idx) {
                Some(&k) => (k as i128) * (sz as i128) + (off as i32 as i128) <= i32::MAX as i128,
                None => true,
            };
            if nuse.get(dst) == Some(&1) && matches!(sz, 1 | 2 | 4 | 8) && !consts.contains_key(base) && disp_ok {
                folded.insert(*dst, (*base, *idx, sz.trailing_zeros() as u8));
            }
        }
    }
    let vreg = |r: &Reg| !consts.contains_key(r) && !fused.contains(r) && !folded.contains_key(r);
    // Toán hạng thực sự đọc tại một lệnh, kể cả base/idx của slice đã gộp vào load/store
    let eff_uses = |i: &Inst| -> Vec<Reg> {
        let mut u = uses(i);
        if let Inst::Load { base, .. } | Inst::Store { base, .. } = i {
            if let Some(&(b, x, _)) = folded.get(base) {
                u.extend([b, x]);
            }
        }
        u
    };

    // Vị trí tuyến tính: tham số hàm định nghĩa ở 0; block b bắt đầu ở bs[b] (tham số block định nghĩa tại đó);
    // lệnh thứ k: dùng ở p, định nghĩa ở p+1
    let nb = func.blocks.len();
    let mut bs = vec![0usize; nb];
    let mut be = vec![0usize; nb];
    let mut ipos: Vec<Vec<usize>> = vec![];
    let mut pos = 2;
    for (bi, b) in func.blocks.iter().enumerate() {
        bs[bi] = pos;
        pos += 2;
        ipos.push(b.insts.iter().map(|_| { pos += 2; pos - 2 }).collect());
        be[bi] = pos - 1;
    }

    // Liveness theo block
    let mut succ: Vec<Vec<usize>> = vec![vec![]; nb];
    let mut ubs: Vec<HashSet<Reg>> = vec![HashSet::new(); nb];
    let mut dbs: Vec<HashSet<Reg>> = vec![HashSet::new(); nb];
    for (bi, b) in func.blocks.iter().enumerate() {
        dbs[bi].extend(b.params.iter().map(|p| p.0));
        for i in &b.insts {
            for r in uses(i).into_iter().filter(|r| vreg(r)) {
                if !dbs[bi].contains(&r) {
                    ubs[bi].insert(r);
                }
            }
            if let Some(d) = def(i) {
                dbs[bi].insert(d);
            }
            match i {
                Inst::Br { then_bb, else_bb, .. } => succ[bi].extend([blk(*then_bb)?, blk(*else_bb)?]),
                Inst::Jmp { target_bb, .. } => succ[bi].push(blk(*target_bb)?),
                _ => {}
            }
        }
    }
    let mut live_in: Vec<HashSet<Reg>> = vec![HashSet::new(); nb];
    let mut live_out: Vec<HashSet<Reg>> = vec![HashSet::new(); nb];
    loop {
        let mut changed = false;
        for bi in (0..nb).rev() {
            let out: HashSet<Reg> = succ[bi].iter().flat_map(|&s| live_in[s].iter().copied()).collect();
            let inn: HashSet<Reg> = ubs[bi].iter().copied().chain(out.iter().copied().filter(|r| !dbs[bi].contains(r))).collect();
            if inn != live_in[bi] || out != live_out[bi] {
                changed = true;
                live_in[bi] = inn;
                live_out[bi] = out;
            }
        }
        if !changed {
            break;
        }
    }

    // Khoảng sống bảo thủ [lo, hi] của mỗi biến được dùng lúc chạy
    let used: HashSet<Reg> = nuse.keys().copied().filter(|r| vreg(r)).collect();
    let mut iv: HashMap<Reg, (usize, usize)> = HashMap::new();
    let touch = |iv: &mut HashMap<Reg, (usize, usize)>, r: Reg, p: usize| {
        if used.contains(&r) {
            let e = iv.entry(r).or_insert((p, p));
            e.0 = e.0.min(p);
            e.1 = e.1.max(p);
        }
    };
    for &(r, _) in &func.params {
        touch(&mut iv, r, 0);
    }
    let mut calls: Vec<usize> = vec![];
    for (bi, b) in func.blocks.iter().enumerate() {
        for &(r, _) in &b.params {
            touch(&mut iv, r, bs[bi]);
        }
        for &r in &live_in[bi] {
            touch(&mut iv, r, bs[bi]);
        }
        for &r in &live_out[bi] {
            touch(&mut iv, r, be[bi]);
        }
        for (k, i) in b.insts.iter().enumerate() {
            let p = ipos[bi][k];
            for r in eff_uses(i) {
                touch(&mut iv, r, p);
            }
            if let Some(d) = def(i) {
                touch(&mut iv, d, p + 1);
            }
            if is_call(i) {
                calls.push(p);
            }
            // Tham số block đích bị GHI tại lệnh jmp
            if let Inst::Jmp { target_bb, .. } = i {
                for &(r, _) in &func.blocks[blk(*target_bb)?].params {
                    touch(&mut iv, r, p + 1);
                }
            }
        }
    }

    // Gợi ý ghép đối số jmp với tham số block (cùng thanh ghi -> bỏ lệnh mov). `share[a] = p`: a được định nghĩa
    // trong block nguồn, chết ở lệnh jmp, và p không còn được đọc sau khi a ra đời -> a dùng chung thanh ghi của p
    // ngay cả khi p vẫn đang "sống" theo khoảng bảo thủ (vòng lặp: p bị ghi lại tại jmp).
    let mut hint: HashMap<Reg, Vec<Reg>> = HashMap::new();
    let mut share: HashMap<Reg, Reg> = HashMap::new();
    for (bi, b) in func.blocks.iter().enumerate() {
        let Some(Inst::Jmp { target_bb, args }) = b.insts.last() else { continue };
        for (&a, &(p, _)) in args.iter().zip(&func.blocks[blk(*target_bb)?].params) {
            if !iv.contains_key(&a) || !iv.contains_key(&p) || a == p {
                continue;
            }
            hint.entry(a).or_default().push(p);
            hint.entry(p).or_default().push(a);
            let Some(k) = b.insts.iter().position(|i| def(i) == Some(a)) else { continue };
            let la = ipos[bi][k] + 1;
            let p_read_after = b.insts.iter().enumerate().any(|(j, i)| ipos[bi][j] > la && eff_uses(i).contains(&p));
            if !share.contains_key(&a) && !live_out[bi].contains(&a) && !live_out[bi].contains(&p) && !p_read_after {
                share.insert(a, p);
            }
        }
    }

    // Linear scan
    let mut order: Vec<(Reg, usize, usize, bool)> = iv
        .iter()
        .map(|(&r, &(lo, hi))| (r, lo, hi, calls.iter().any(|&p| lo < p && hi > p + 1)))
        .collect();
    order.sort_by_key(|x| (x.1, x.0));
    let mut loc: HashMap<Reg, Loc> = HashMap::new();
    let mut spilled: Vec<Reg> = vec![];
    let mut active: Vec<(usize, Reg, u8)> = vec![];
    let mut free: Vec<u8> = CALLER.iter().chain(CALLEE.iter()).copied().collect();
    let mut guests: HashMap<Reg, usize> = HashMap::new(); // p -> điểm cuối muộn nhất của biến ở nhờ thanh ghi của p
    for &(r, lo, hi, cross) in &order {
        active.retain(|&(end, _, preg)| {
            if end < lo {
                free.push(preg);
                false
            } else {
                true
            }
        });
        let ok = |p: u8| !cross || CALLEE.contains(&p);
        if let Some(&p) = share.get(&r) {
            if let Some(&(pend, _, preg)) = active.iter().find(|a| a.1 == p) {
                if ok(preg) && pend > hi {
                    loc.insert(r, Loc::R(preg));
                    let g = guests.entry(p).or_insert(hi);
                    *g = (*g).max(hi);
                    continue;
                }
            }
        }
        let hinted = hint.get(&r).into_iter().flatten().filter_map(|h| match loc.get(h) {
            Some(Loc::R(x)) if free.contains(x) && ok(*x) => Some(*x),
            _ => None,
        });
        let pick = hinted.chain(CALLER.iter().chain(CALLEE.iter()).copied().filter(|p| ok(*p) && free.contains(p) && (cross || !CALLEE.contains(p) || !CALLER.iter().any(|q| free.contains(q)))))
            .next();
        if let Some(p) = pick {
            free.retain(|&x| x != p);
            active.push((hi, r, p));
            loc.insert(r, Loc::R(p));
            continue;
        }
        // Tràn: nhường thanh ghi của biến đang sống kết thúc muộn nhất (nếu muộn hơn biến hiện tại)
        let victim = active
            .iter()
            .enumerate()
            .filter(|(_, a)| ok(a.2) && guests.get(&a.1).is_none_or(|&g| g < lo))
            .max_by_key(|(_, a)| a.0).map(|(i, a)| (i, *a));
        match victim {
            Some((i, (end, vr, p))) if end > hi => {
                active.remove(i);
                spilled.push(vr);
                active.push((hi, r, p));
                loc.insert(r, Loc::R(p));
            }
            _ => spilled.push(r),
        }
    }
    let saved: Vec<u8> = CALLEE.iter().copied().filter(|p| loc.values().any(|l| *l == Loc::R(*p))).collect();
    let npush = saved.len() as i32;
    for (k, r) in spilled.iter().enumerate() {
        loc.insert(*r, Loc::S(-8 * npush - 8 * (k as i32 + 1)));
    }
    let mut frame = spilled.len() as i32 * 8;
    if (frame + npush * 8) % 16 != 0 {
        frame += 8;
    }
    let opd = |r: Reg| -> Opd {
        match consts.get(&r) {
            Some(&v) => Opd::I(v),
            None => Opd::L(*loc.get(&r).unwrap_or(&Loc::R(RAX))),
        }
    };

    // Prologue
    let c = code;
    c.extend_from_slice(&[0x55, 0x48, 0x89, 0xE5]);
    for &p in &saved {
        push_r(c, p);
    }
    if frame > 0 {
        rsp_add(c, frame, true);
    }
    let pm: Vec<(Loc, Opd)> = func
        .params
        .iter()
        .take(6)
        .enumerate()
        .filter_map(|(i, &(r, _))| loc.get(&r).map(|&l| (l, Opd::L(Loc::R(ABI[i])))))
        .collect();
    par_move(c, pm);
    for (i, &(r, _)) in func.params.iter().enumerate().skip(6) {
        if let Some(&l) = loc.get(&r) {
            mov_any(c, l, Opd::L(Loc::S(16 + (i as i32 - 6) * 8)));
        }
    }

    let mut blk_addrs: HashMap<BlockId, usize> = HashMap::new();
    let mut patches: Vec<(usize, BlockId)> = vec![];
    // jcc (cc = Some) hoặc jmp tới block; nhảy lùi gần dùng rel8
    let jump = |c: &mut Vec<u8>, cc: Option<u8>, t: BlockId, blk_addrs: &HashMap<BlockId, usize>, patches: &mut Vec<(usize, BlockId)>| {
        if let Some(&a) = blk_addrs.get(&t) {
            let rel = a as i64 - (c.len() as i64 + 2);
            if fits8(rel) {
                c.push(match cc {
                    Some(x) => 0x70 | x,
                    None => 0xEB,
                });
                c.push(rel as u8);
                return;
            }
        }
        match cc {
            Some(x) => c.extend_from_slice(&[0x0F, 0x80 | x]),
            None => c.push(0xE9),
        }
        c.extend_from_slice(&[0, 0, 0, 0]);
        patches.push((c.len() - 4, t));
    };
    let epilogue = |c: &mut Vec<u8>| {
        if frame > 0 {
            rsp_add(c, frame, false);
        }
        for &p in saved.iter().rev() {
            pop_r(c, p);
        }
        c.extend_from_slice(&[0x5D, 0xC3]);
    };
    let dst_loc = |r: &Reg| loc.get(r).copied();
    // Toán hạng bộ nhớ cho load/store: base (+ idx của slice đã gộp) ở thanh ghi, không thì nạp vào rcx/rdx
    let in_reg = |c: &mut Vec<u8>, o: Opd, tmp: u8| match o {
        Opd::L(Loc::R(x)) => x,
        _ => {
            load(c, tmp, o);
            tmp
        }
    };
    let addr = |c: &mut Vec<u8>, base: Reg, off: u32| -> Rm {
        match folded.get(&base) {
            Some(&(b, x, sc)) => {
                let br = in_reg(c, opd(b), RCX);
                match opd(x) {
                    Opd::I(k) => Rm::M(br, ((k << sc) as i64 + off as i32 as i64) as i32),
                    o => Rm::X(br, in_reg(c, o, RDX), sc, off as i32),
                }
            }
            None => Rm::M(in_reg(c, opd(base), RCX), off as i32),
        }
    };

    for (bi, block) in func.blocks.iter().enumerate() {
        blk_addrs.insert(block.id, c.len());
        let next_id = func.blocks.get(bi + 1).map(|b| b.id);
        let mut fused_cc: Option<(Reg, u8)> = None;
        for inst in &block.insts {
            match inst {
                Inst::Const { .. } | Inst::Assume(_) | Inst::Assert(_) => {}
                Inst::Bin { dst, op, lhs, rhs } => {
                    let Some(d) = dst_loc(dst) else { continue };
                    let (mut l, mut r) = (opd(*lhs), opd(*rhs));
                    match op {
                        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::And | BinOp::Or | BinOp::Xor
                        | BinOp::AddWrap | BinOp::SubWrap | BinOp::MulWrap => {
                            let comm = !matches!(op, BinOp::Sub | BinOp::SubWrap);
                            if comm && (r == Opd::L(d) || matches!(l, Opd::I(_))) && l != Opd::L(d) {
                                std::mem::swap(&mut l, &mut r);
                            }
                            let w = match d {
                                Loc::R(x) if r != Opd::L(d) => x,
                                _ => RAX,
                            };
                            load(c, w, l);
                            match op {
                                BinOp::Add | BinOp::AddWrap => alu(c, 0x03, 0, w, r),
                                BinOp::Sub | BinOp::SubWrap => alu(c, 0x2B, 5, w, r),
                                BinOp::And => alu(c, 0x23, 4, w, r),
                                BinOp::Or => alu(c, 0x0B, 1, w, r),
                                BinOp::Xor => alu(c, 0x33, 6, w, r),
                                _ => imul(c, w, r),
                            }
                            save(c, d, w);
                        }
                        BinOp::Shl | BinOp::LShr | BinOp::AShr => {
                            let ext = match op {
                                BinOp::Shl => 4,
                                BinOp::LShr => 5,
                                _ => 7,
                            };
                            let w = match d {
                                Loc::R(x) if r != Opd::L(d) => x,
                                _ => RAX,
                            };
                            if let Opd::I(n) = r {
                                load(c, w, l);
                                op_rm(c, false, true, false, &[0xC1], ext, Rm::R(w));
                                c.push((n & 63) as u8);
                            } else {
                                load(c, RCX, r);
                                load(c, w, l);
                                op_rm(c, false, true, false, &[0xD3], ext, Rm::R(w));
                            }
                            save(c, d, w);
                        }
                        _ => {
                            load(c, RCX, r);
                            load(c, RAX, l);
                            c.extend_from_slice(match op {
                                BinOp::UDiv => &[0x31, 0xD2, 0x48, 0xF7, 0xF1],
                                BinOp::SDiv => &[0x48, 0x99, 0x48, 0xF7, 0xF9],
                                BinOp::URem => &[0x31, 0xD2, 0x48, 0xF7, 0xF1, 0x48, 0x89, 0xD0],
                                BinOp::SRem => &[0x48, 0x99, 0x48, 0xF7, 0xF9, 0x48, 0x89, 0xD0],
                                BinOp::FxMul => &[0x48, 0x0F, 0xAF, 0xC1, 0x48, 0xC1, 0xE8, 0x10],
                                _ => &[0x48, 0xC1, 0xE0, 0x10, 0x31, 0xD2, 0x48, 0xF7, 0xF1], // FxDiv
                            });
                            save(c, d, RAX);
                        }
                    }
                }
                Inst::Cmp { dst, op, lhs, rhs } => {
                    let is_fused = fused.contains(dst);
                    let d = dst_loc(dst);
                    if !is_fused && d.is_none() {
                        continue;
                    }
                    let (mut l, mut r, mut cc) = (opd(*lhs), opd(*rhs), cc_of(*op));
                    if matches!(l, Opd::I(_)) && !matches!(r, Opd::I(_)) {
                        std::mem::swap(&mut l, &mut r);
                        cc = cc_swap(cc);
                    }
                    let lr = match l {
                        Opd::L(Loc::R(x)) => x,
                        _ => {
                            load(c, RAX, l);
                            RAX
                        }
                    };
                    alu(c, 0x3B, 7, lr, r);
                    if is_fused {
                        fused_cc = Some((*dst, cc));
                    } else {
                        c.extend_from_slice(&[0x0F, 0x90 | cc, 0xC0, 0x0F, 0xB6, 0xC0]); // setcc al; movzx eax, al
                        save(c, d.unwrap(), RAX);
                    }
                }
                Inst::Slice { dst, base, idx, ty } => {
                    let Some(d) = dst_loc(dst) else { continue }; // không dùng hoặc đã gộp vào load/store
                    let lid = ty.ptr_layout().ok_or("Lỗi kiểu Slice")? as usize;
                    let sz = module.layouts[lid].size as u64;
                    let (b, ix) = (opd(*base), opd(*idx));
                    if let Opd::I(k) = ix {
                        let w = match d {
                            Loc::R(x) => x,
                            _ => RAX,
                        };
                        load(c, w, b);
                        let off = k.wrapping_mul(sz);
                        if off != 0 {
                            alu(c, 0x03, 0, w, Opd::I(off));
                        }
                        save(c, d, w);
                    } else {
                        let w = match d {
                            Loc::R(x) if b != Opd::L(d) => x,
                            _ => RAX,
                        };
                        load(c, w, ix);
                        if sz.is_power_of_two() {
                            if sz > 1 {
                                op_rm(c, false, true, false, &[0xC1], 4, Rm::R(w));
                                c.push(sz.trailing_zeros() as u8);
                            }
                        } else {
                            imul(c, w, Opd::I(sz as u32 as i32 as i64 as u64));
                        }
                        alu(c, 0x03, 0, w, b);
                        save(c, d, w);
                    }
                }
                Inst::Narrow { dst, src, .. } => {
                    if let Some(d) = dst_loc(dst) {
                        par_move(c, vec![(d, opd(*src))]);
                    }
                }
                Inst::Load { dst, ty, base, offset } => {
                    let m = addr(c, *base, *offset);
                    let d = dst_loc(dst);
                    let t = match d {
                        Some(Loc::R(x)) => x,
                        _ => RAX,
                    };
                    match ty {
                        Type::Bv8 => op_rm(c, false, true, false, &[0x0F, 0xB6], t, m),
                        Type::Bv16 => op_rm(c, false, true, false, &[0x0F, 0xB7], t, m),
                        Type::Bv32 => op_rm(c, false, false, false, &[0x8B], t, m),
                        _ => op_rm(c, false, true, false, &[0x8B], t, m),
                    }
                    if let Some(d) = d {
                        save(c, d, t);
                    }
                }
                Inst::Store { base, offset, val } => {
                    let m = addr(c, *base, *offset);
                    let wty = *reg_tys.get(val).unwrap_or(&Type::Bv64);
                    match opd(*val) {
                        Opd::I(v) if !matches!(wty, Type::Bv64 | Type::Ptr { .. } | Type::DPtr { .. }) || fits32(v) => match wty {
                            Type::Bv8 => {
                                op_rm(c, false, false, false, &[0xC6], 0, m);
                                c.push(v as u8);
                            }
                            Type::Bv16 => {
                                op_rm(c, true, false, false, &[0xC7], 0, m);
                                c.extend_from_slice(&(v as u16).to_le_bytes());
                            }
                            Type::Bv32 => {
                                op_rm(c, false, false, false, &[0xC7], 0, m);
                                c.extend_from_slice(&(v as u32).to_le_bytes());
                            }
                            _ => {
                                op_rm(c, false, true, false, &[0xC7], 0, m);
                                c.extend_from_slice(&(v as u32).to_le_bytes());
                            }
                        },
                        o => {
                            let v = match o {
                                Opd::L(Loc::R(x)) => x,
                                _ => {
                                    load(c, RAX, o);
                                    RAX
                                }
                            };
                            match wty {
                                Type::Bv8 => op_rm(c, false, false, true, &[0x88], v, m),
                                Type::Bv16 => op_rm(c, true, false, false, &[0x89], v, m),
                                Type::Bv32 => op_rm(c, false, false, false, &[0x89], v, m),
                                _ => op_rm(c, false, true, false, &[0x89], v, m),
                            }
                        }
                    }
                }
                Inst::Simd256 { op, dst, lhs, rhs } => {
                    // Blob dùng rsi = lhs, rdx = rhs, rcx = dst: nạp hết toán hạng trước khi đè rsi (rsi được cấp phát)
                    load(c, RAX, opd(*lhs));
                    load(c, RDX, opd(*rhs));
                    if *op != SimdOp::Dot {
                        load(c, RCX, opd(*dst));
                    }
                    c.push(0x56); // push rsi
                    c.extend_from_slice(&[0x48, 0x89, 0xC6]); // mov rsi, rax
                    if *op == SimdOp::Dot {
                        c.extend_from_slice(&[
                            0x80, 0x3C, 0x25, 0x08, 0xE0, 0x07, 0x00, 0x00, 0x74, 0x25, 0xC5, 0xFE, 0x6F, 0x06, 0xC5, 0xFD, 0xF4,
                            0x02, 0xC4, 0xE3, 0x7D, 0x39, 0xC1, 0x01, 0xC5, 0xF9, 0xD4, 0xC1, 0xC5, 0xF9, 0x70, 0xC8, 0x4E, 0xC5,
                            0xF9, 0xD4, 0xC1, 0xC4, 0xE1, 0xF9, 0x7E, 0xC0, 0xC5, 0xF8, 0x77, 0xEB, 0x2C, 0xF3, 0x0F, 0x6F, 0x06,
                            0xF3, 0x0F, 0x6F, 0x0A, 0x66, 0x0F, 0xF4, 0xC1, 0xF3, 0x0F, 0x6F, 0x56, 0x10, 0xF3, 0x0F, 0x6F, 0x4A,
                            0x10, 0x66, 0x0F, 0xF4, 0xD1, 0x66, 0x0F, 0xD4, 0xC2, 0x66, 0x0F, 0x70, 0xC8, 0x4E, 0x66, 0x0F, 0xD4,
                            0xC1, 0x66, 0x48, 0x0F, 0x7E, 0xC0,
                        ]);
                        c.push(0x5E); // pop rsi
                        if let Some(d) = dst_loc(dst) {
                            save(c, d, RAX);
                        }
                    } else {
                        let op_b = match op {
                            SimdOp::Add => 0xD4,
                            SimdOp::Sub => 0xFB,
                            SimdOp::Mul => 0xF4,
                            _ => 0xEF,
                        };
                        c.extend_from_slice(&[
                            0x80, 0x3C, 0x25, 0x08, 0xE0, 0x07, 0x00, 0x00, 0x74, 0x11, 0xC5, 0xFE, 0x6F, 0x06, 0xC5, 0xFD, op_b,
                            0x02, 0xC5, 0xFE, 0x7F, 0x01, 0xC5, 0xF8, 0x77, 0xEB, 0x23, 0xF3, 0x0F, 0x6F, 0x06, 0xF3, 0x0F, 0x6F,
                            0x0A, 0x66, 0x0F, op_b, 0xC1, 0xF3, 0x0F, 0x7F, 0x01, 0xF3, 0x0F, 0x6F, 0x46, 0x10, 0xF3, 0x0F, 0x6F,
                            0x4A, 0x10, 0x66, 0x0F, op_b, 0xC1, 0xF3, 0x0F, 0x7F, 0x41, 0x10,
                        ]);
                        c.push(0x5E); // pop rsi
                    }
                }
                Inst::Parallel { smp, n, func_id, base, arg } => {
                    // lt_parallel(rdi=smp, rsi=n, rdx=&worker, rcx=base, r8=stride, r9=arg)
                    let Some(layout_id) = reg_tys.get(base).and_then(|t| t.ptr_layout()) else {
                        return Err("parallel: base không phải ptr".into());
                    };
                    let Some(&(_, Type::Ptr { max_elems: k, .. })) = module.funcs[*func_id as usize].params.first() else {
                        return Err("parallel: worker sai chữ ký".into());
                    };
                    let stride = k * module.layouts[layout_id as usize].size as u64;
                    par_move(
                        c,
                        vec![
                            (Loc::R(RDI), opd(*smp)),
                            (Loc::R(RSI), opd(*n)),
                            (Loc::R(RCX), opd(*base)),
                            (Loc::R(R9), opd(*arg)),
                        ],
                    );
                    mov_ri(c, R8, stride);
                    c.extend_from_slice(&[0x48, 0x8D, 0x15, 0, 0, 0, 0]); // lea rdx, [rip + worker]
                    call_patches.push((c.len() - 4, *func_id));
                    c.extend_from_slice(&[0xE8, 0, 0, 0, 0]);
                    rt_patches.push(c.len() - 4);
                }
                Inst::SmpWorkers { dst, smp } => {
                    load(c, RCX, opd(*smp));
                    c.extend_from_slice(&[
                        0x48, 0x8B, 0x51, 0x10, 0x81, 0xE2, 0xFE, 0xFF, 0x00, 0x00, 0x31, 0xC0, 0x48, 0x85, 0xD2, 0x74, 0x0B,
                        0x48, 0x8D, 0x4A, 0xFF, 0x48, 0x21, 0xCA, 0xFF, 0xC0, 0xEB, 0xF0,
                    ]);
                    if let Some(d) = dst_loc(dst) {
                        save(c, d, RAX);
                    }
                }
                Inst::AtaRead { ptr, idx, nsec, .. } => {
                    // rep insd: nsec*128 dword từ 0x1F0 vào [ptr + idx*512]; rdi được cấp phát -> push/pop
                    load(c, RAX, opd(*ptr));
                    load(c, RCX, opd(*idx));
                    c.extend_from_slice(&[0x48, 0xC1, 0xE1, 0x09, 0x48, 0x01, 0xC8]); // shl rcx, 9; add rax, rcx
                    load(c, RDX, opd(*nsec));
                    c.extend_from_slice(&[
                        0x57, // push rdi
                        0x48, 0x89, 0xC7, // mov rdi, rax
                        0x48, 0x89, 0xD1, // mov rcx, rdx
                        0x48, 0xC1, 0xE1, 0x07, // shl rcx, 7
                        0x66, 0xBA, 0xF0, 0x01, // mov dx, 0x1F0
                        0xFC, 0xF3, 0x6D, // cld; rep insd
                        0x5F, // pop rdi
                    ]);
                }
                Inst::HwIo { dst, port_or_reg, val, is_write, .. } => {
                    if *is_write {
                        let v_reg = val.ok_or("hwio_w thiếu giá trị")?;
                        load(c, RAX, opd(v_reg));
                        if *port_or_reg == 3 {
                            c.extend_from_slice(&[0x0F, 0x22, 0xD8]);
                        } else {
                            c.extend_from_slice(&[0x66, 0xBA]);
                            c.extend_from_slice(&port_or_reg.to_le_bytes());
                            if reg_tys.get(&v_reg) == Some(&Type::Bv32) {
                                c.push(0xEF);
                            } else if *port_or_reg == 0x1F0 || reg_tys.get(&v_reg) == Some(&Type::Bv16) {
                                c.extend_from_slice(&[0x66, 0xEF]);
                            } else {
                                c.push(0xEE);
                            }
                        }
                    } else if let Some(d) = dst {
                        if *port_or_reg == 3 {
                            c.extend_from_slice(&[0x0F, 0x20, 0xD8]);
                        } else if *port_or_reg == 0x10 {
                            c.extend_from_slice(&[
                                0x0F, 0x31, 0x48, 0xC1, 0xE2, 0x20, 0x48, 0x09, 0xD0, 0x48, 0xC1, 0xE8, 0x14, 0x25, 0xFF, 0x00, 0x00,
                                0x00,
                            ]);
                        } else {
                            c.extend_from_slice(&[0x31, 0xC0, 0x66, 0xBA]);
                            c.extend_from_slice(&port_or_reg.to_le_bytes());
                            if *port_or_reg == 0xCFC {
                                c.push(0xED);
                            } else if *port_or_reg == 0x1F0 {
                                c.extend_from_slice(&[0x66, 0xED]);
                            } else {
                                c.push(0xEC);
                            }
                        }
                        if let Some(dl) = dst_loc(d) {
                            save(c, dl, RAX);
                        }
                    }
                }
                Inst::Br { cond, then_bb, else_bb } => {
                    let cc = match fused_cc {
                        Some((r, cc)) if r == *cond => cc,
                        _ => match opd(*cond) {
                            Opd::I(v) => {
                                let t = if v != 0 { *then_bb } else { *else_bb };
                                if Some(t) != next_id {
                                    jump(c, None, t, &blk_addrs, &mut patches);
                                }
                                continue;
                            }
                            Opd::L(Loc::R(x)) => {
                                op_rm(c, false, true, false, &[0x85], x, Rm::R(x));
                                0x5
                            }
                            Opd::L(Loc::S(x)) => {
                                op_rm(c, false, true, false, &[0x83], 7, Rm::M(RBP, x));
                                c.push(0);
                                0x5
                            }
                        },
                    };
                    if Some(*then_bb) == next_id {
                        jump(c, Some(cc ^ 1), *else_bb, &blk_addrs, &mut patches);
                    } else {
                        jump(c, Some(cc), *then_bb, &blk_addrs, &mut patches);
                        if Some(*else_bb) != next_id {
                            jump(c, None, *else_bb, &blk_addrs, &mut patches);
                        }
                    }
                }
                Inst::Jmp { target_bb, args } => {
                    let tb = &func.blocks[blk(*target_bb)?];
                    let mv = args
                        .iter()
                        .zip(&tb.params)
                        .filter_map(|(&a, &(p, _))| dst_loc(&p).map(|l| (l, opd(a))))
                        .collect();
                    par_move(c, mv);
                    if Some(*target_bb) != next_id {
                        jump(c, None, *target_bb, &blk_addrs, &mut patches);
                    }
                }
                Inst::Call { dst, args, .. } | Inst::CallPtr { dst, args, .. } => {
                    let extra = args.len().saturating_sub(6);
                    let pad = if extra % 2 != 0 { 8 } else { 0 };
                    if pad > 0 {
                        rsp_add(c, 8, true);
                    }
                    for &r in args.iter().skip(6).rev() {
                        match opd(r) {
                            Opd::L(Loc::R(x)) => push_r(c, x),
                            Opd::L(Loc::S(x)) => op_rm(c, false, false, false, &[0xFF], 6, Rm::M(RBP, x)),
                            Opd::I(v) if fits32(v) => {
                                c.push(0x68);
                                c.extend_from_slice(&(v as u32).to_le_bytes());
                            }
                            o => {
                                load(c, RAX, o);
                                c.push(0x50);
                            }
                        }
                    }
                    let mut mv: Vec<(Loc, Opd)> = args.iter().take(6).enumerate().map(|(i, &r)| (Loc::R(ABI[i]), opd(r))).collect();
                    if let Inst::CallPtr { target, .. } = inst {
                        mv.push((Loc::R(R11), opd(*target)));
                    }
                    par_move(c, mv);
                    if let Inst::Call { func_id, .. } = inst {
                        c.extend_from_slice(&[0xE8, 0, 0, 0, 0]);
                        call_patches.push((c.len() - 4, *func_id));
                    } else {
                        c.extend_from_slice(&[0x41, 0xFF, 0xD3]); // call r11
                    }
                    let total = (extra * 8 + pad) as i32;
                    if total > 0 {
                        rsp_add(c, total, false);
                    }
                    if let Some(d) = dst.and_then(|d| dst_loc(&d)) {
                        save(c, d, RAX);
                    }
                }
                Inst::Ret { val } => {
                    if let Some(r) = val {
                        load(c, RAX, opd(*r));
                    }
                    epilogue(c);
                }
            }
        }
    }
    for (p, t) in patches {
        let a = *blk_addrs.get(&t).ok_or("Không tìm thấy BlockId")?;
        let rel = a as i32 - (p as i32 + 4);
        c[p..p + 4].copy_from_slice(&rel.to_le_bytes());
    }
    Ok(())
}
