// File: src/verify_int.rs — checker SỐ NGUYÊN (P3) cho mệnh đề đặc tả giàu: số học toán học (iadd/isub/imul/idiv/imod).
//
// Vì sao một checker riêng (đo ở P3, xem bench/p3.md): Z3 trên bit-vector 64 bit hết giờ với chia / lượng từ, còn trên
// số nguyên (LIA) chỉ mất vài phần trăm giây — nhưng chỉ khi CẢ mã lẫn đặc tả đều là số nguyên (trộn bv2nat cũng hết giờ).
//
// Phân công: checker BV (verify.rs) vẫn là nơi DUY NHẤT chứng minh an toàn (tràn số, biên, chia 0, dừng). Checker này
// chạy SAU khi BV qua và được giả định các sự thật đó: phép `add/sub/mul` có kiểm của mã được mã hoá CHÍNH XÁC là cộng /
// trừ / nhân số nguyên (BV đã chứng minh không tràn). Nó chứng minh mọi mệnh đề mà BV không chứng minh (lớp Wide / Rich
// của SpecClass), và với LIGHT_INT_ALL=1 thì chứng minh MỌI mệnh đề (đối chiếu chéo hai backend).
//
// Mã hoá: mỗi thanh ghi là một hằng Int riêng trong [0, 2^w) (không nhúng biểu thức: đo được nhúng làm lượng từ hết giờ);
// chia / dịch cho hằng = thương mới q với c*q <= x < c*q + c (tuyến tính; `div` của Z3 làm hết giờ); phép bit tổng quát,
// dịch biến, ... = hàm không diễn giải + miền giá trị (đúng đắn: chứng minh cho MỌI cách diễn giải, kể cả cách thật).
//
// Bộ nhớ (P3 giai đoạn 2): HEAP THEO KIỂU — mỗi (Layout, offset trường) là một mảng Int -> Int, chỉ số = địa chỉ PHẦN TỬ.
// Đo được: bộ nhớ theo byte (qword = tổng 8 byte) hết giờ, heap theo kiểu 0,01 s. Đúng đắn dựa trên:
//   * hai phần tử CÙNG Layout không bao giờ chồng một phần: slice dịch bội số kích thước, view chỉ sang Layout có kích
//     thước chia hết (verify.rs kiểm), con trỏ hằng (`const ... ptr`) coi là MỜ (đọc = giá trị mới, ghi = xoá mọi heap);
//   * các trường của một Layout không chồng nhau (parser kiểm);
//   * KHÁC Layout có thể cùng vùng nhớ (view): ghi qua Layout L thì heap của MỌI Layout khác bị thay bằng mảng mới
//     (không có khẳng định khung nào giữa hai Layout). Không ghi thì đọc các mảng độc lập vẫn đúng (chỉ mất thông tin).
//   * lệnh gọi hàm, SIMD, ata_read, parallel, hwio, gọi gián tiếp: xoá mọi heap (giai đoạn 3 sẽ có khung gọi hàm).
// Heap đi theo luồng điều khiển như tham số block ngầm: block nối = mảng mới với `điều_kiện_cạnh => H == H_cạnh`;
// đầu vòng lặp = mảng mới cho các heap hàm có thể ghi (bất biến phải nói về chúng), heap không bị ghi = heap lúc vào.
use crate::ir::*;
use std::collections::{HashMap, HashSet};
use z3::ast::{Array, Ast, Bool, Int};
use z3::{Config, Context, FuncDecl, Params, SatResult, Solver, Sort};

const TIMEOUT_MS: u32 = 10_000;
const FEASIBLE_MS: u32 = 500;

type IEnv<'ctx> = HashMap<Reg, Int<'ctx>>;
/// (layout_id, offset trường trong phần tử)
type HKey = (u16, u32);
type Heap<'ctx> = HashMap<HKey, Array<'ctx>>;

/// Hàm cần checker số nguyên: có mệnh đề BV không tự chứng minh, hoặc gọi hàm có @req như vậy
pub fn needed(module: &Module, func: &Func) -> bool {
    let rich = |e: &Z3Expr| e.class() != SpecClass::Bv;
    func.requires.iter().any(rich)
        || func.ensures.iter().any(rich)
        || func.blocks.iter().any(|b| b.invs.iter().any(rich))
        || func.blocks.iter().flat_map(|b| &b.insts).any(|i| match i {
            Inst::Call { func_id, .. } => module.funcs.get(*func_id as usize).is_some_and(|c| c.requires.iter().any(rich)),
            Inst::Assert(e) => rich(e),
            _ => false,
        })
}

fn int_bits(ty: Type) -> u32 {
    match ty {
        Type::Bv8 => 8,
        Type::Bv16 => 16,
        Type::Bv32 => 32,
        _ => 64,
    }
}

struct IV<'ctx> {
    ctx: &'ctx Context,
    solver: Solver<'ctx>,
    module: &'ctx Module,
    func: &'ctx Func,
    /// true: chứng minh MỌI mệnh đề (đối chiếu chéo); false: chỉ mệnh đề BV không chứng minh
    all: bool,
    regs: IEnv<'ctx>,
    tys: HashMap<Reg, Type>,
    consts: HashMap<Reg, u64>,
    /// thanh ghi chắc chắn là 0/1 (kết quả cmp, and/or/xor của chúng)
    boolish: HashSet<Reg>,
    cur_cond: Option<Bool<'ctx>>,
    conds: HashMap<usize, Option<Bool<'ctx>>>,
    pos: Vec<usize>,
    edge_args: HashMap<usize, Vec<(Option<Bool<'ctx>>, Vec<Int<'ctx>>)>>,
    cur_bb: BlockId,
    cur_inst: String,
    cur_at: String,
    fresh: u32,
    ufs: HashMap<String, FuncDecl<'ctx>>,
    /// thanh ghi là bội của 2^k (kết quả `shl x k` với k hằng)
    low_zero: HashMap<Reg, u32>,
    lowered: HashMap<Reg, (BinOp, Reg, Reg)>,
    /// bộ nhớ lúc vào hàm / hiện tại / "old" của mệnh đề đang tính (lúc vào hàm, hoặc trước lệnh gọi với @ens hàm được gọi)
    heap0: Heap<'ctx>,
    heap: Heap<'ctx>,
    old_heap: Heap<'ctx>,
    /// heap hàm có thể thay đổi (đầu vòng lặp: mảng mới); còn lại luôn là heap0
    written: HashSet<HKey>,
    edge_heaps: HashMap<usize, Vec<(Option<Bool<'ctx>>, Heap<'ctx>)>>,
    /// con trỏ từ hằng (và slice / view của chúng): không theo luật không-chồng-một-phần
    opaque: HashSet<Reg>,
    /// kiểu thanh ghi dùng khi tính `mem %p` (mệnh đề của hàm được gọi: kiểu tham số của nó)
    spec_tys: Option<HashMap<Reg, Type>>,
    in_old: bool,
    /// độ sâu lượng từ: > 0 thì sự thật phụ không khẳng định toàn cục được (có biến buộc) mà gom vào `side`
    depth: u32,
    side: Vec<Bool<'ctx>>,
    /// hàm spec đã khai báo trong Z3: hàm không diễn giải + các heap nó đọc (đối số đầu)
    /// tầng (fuel) [f0, f1, f2]: f2 = thân[f1], f1 = thân[f0], f0 không mở -> không có vòng lặp khớp mẫu vô hạn
    spec_decls: HashMap<u32, (Vec<FuncDecl<'ctx>>, Vec<HKey>)>,
    /// khi tính thân tầng L của hàm spec: lời gọi đệ quy dùng tầng L-1
    spec_layer: HashMap<u32, usize>,
    /// đang tính thân hàm spec: KHÔNG thêm miền giá trị ô nhớ (lượng từ chạy trên MỌI mảng, kể cả mảng có ô ngoài miền;
    /// và miền của ô ở nhánh không đi, vd a[k-1] khi k == 0, sẽ chặn tiên đề)
    in_spec_body: bool,
    /// ứng viên pattern cho lượng từ đang tính (mỗi tầng lượng từ một khung): các hạng đọc heap / gọi hàm spec
    pat_frames: Vec<Vec<z3::ast::Dynamic<'ctx>>>,
    /// con trỏ từ slice cùng Layout: (gốc, chỉ số) -> địa chỉ chuẩn khi load / store qua nó
    slice_of: HashMap<Reg, (Int<'ctx>, Int<'ctx>)>,
    /// cực tính của biểu thức đang tính: true = mục tiêu cần chứng minh, false = giả định (Not lật)
    pol: bool,
    /// lượng từ trong cùng có thêm miền ô nhớ: forall ở mục tiêu (giả thiết dễ hơn) / exists ở giả định (thêm thông tin)
    want_range: bool,
}

const SPEC_FUEL: usize = 2;

/// Giá trị của biểu thức hằng toán học (Const / iadd isub imul của hằng), nếu có
fn const_math(e: &Z3Expr) -> Option<i128> {
    match e {
        Z3Expr::Const(v) => Some(*v as i128),
        Z3Expr::Math(op, l, r) => {
            let (a, b) = (const_math(l)?, const_math(r)?);
            match op {
                MathOp::Add => a.checked_add(b),
                MathOp::Sub => a.checked_sub(b),
                MathOp::Mul => a.checked_mul(b),
                MathOp::Div if b > 0 && a >= 0 => Some(a / b),
                MathOp::Mod if b > 0 && a >= 0 => Some(a % b),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Heap mà hàm spec đọc (trực tiếp hoặc qua hàm spec nó gọi)
fn spec_reads(module: &Module, id: u32, stack: &mut Vec<u32>, out: &mut HashSet<HKey>) -> Result<(), String> {
    if stack.contains(&id) {
        return Ok(());
    }
    stack.push(id);
    let sp = module.specs.get(id as usize).ok_or("hàm spec không tồn tại")?;
    let tys: HashMap<Reg, Type> = sp.params.iter().copied().collect();
    fn walk(m: &Module, e: &Z3Expr, tys: &HashMap<Reg, Type>, st: &mut Vec<u32>, out: &mut HashSet<HKey>) -> Result<(), String> {
        match e {
            Z3Expr::Mem(p, i, off) => {
                let l = tys.get(p).and_then(|t| t.ptr_layout()).ok_or_else(|| format!("mem: %{} không phải con trỏ (tham số hàm spec)", p))?;
                let size = m.layouts[l as usize].size.max(1);
                out.insert((l, off % size));
                walk(m, i, tys, st, out)
            }
            Z3Expr::App(f, args) => {
                spec_reads(m, *f, st, out)?;
                args.iter().try_for_each(|a| walk(m, a, tys, st, out))
            }
            Z3Expr::Bin(_, l, r) | Z3Expr::Cmp(_, l, r) | Z3Expr::And(l, r) | Z3Expr::Or(l, r) | Z3Expr::Math(_, l, r) => {
                walk(m, l, tys, st, out)?;
                walk(m, r, tys, st, out)
            }
            Z3Expr::Not(x) | Z3Expr::Old(x) => walk(m, x, tys, st, out),
            Z3Expr::Ite(c, a, b) => [c, a, b].iter().try_for_each(|x| walk(m, x, tys, st, out)),
            Z3Expr::Quant(_, _, lo, hi, b) => [lo, hi, b].iter().try_for_each(|x| walk(m, x, tys, st, out)),
            Z3Expr::Reg(_) | Z3Expr::Const(_) | Z3Expr::FieldVal => Ok(()),
        }
    }
    if let Some(b) = &sp.body {
        walk(module, b, &tys, stack, out)?;
    }
    stack.pop();
    Ok(())
}

fn collect_apps(e: &Z3Expr, out: &mut Vec<u32>) {
    match e {
        Z3Expr::App(f, args) => {
            out.push(*f);
            args.iter().for_each(|a| collect_apps(a, out));
        }
        Z3Expr::Bin(_, l, r) | Z3Expr::Cmp(_, l, r) | Z3Expr::And(l, r) | Z3Expr::Or(l, r) | Z3Expr::Math(_, l, r) => {
            collect_apps(l, out);
            collect_apps(r, out);
        }
        Z3Expr::Not(x) | Z3Expr::Old(x) => collect_apps(x, out),
        Z3Expr::Mem(_, i, _) => collect_apps(i, out),
        Z3Expr::Ite(c, a, b) => [c, a, b].iter().for_each(|x| collect_apps(x, out)),
        Z3Expr::Quant(_, _, lo, hi, b) => [lo, hi, b].iter().for_each(|x| collect_apps(x, out)),
        Z3Expr::Reg(_) | Z3Expr::Const(_) | Z3Expr::FieldVal => {}
    }
}

/// Các lời gọi hàm spec `id` trong `e`, kèm điều kiện ite trên đường tới nó (cho chứng minh dừng)
fn rec_calls(e: &Z3Expr, id: u32, pc: &mut Vec<(Z3Expr, bool)>, out: &mut Vec<(Vec<(Z3Expr, bool)>, Vec<Z3Expr>)>, in_q: bool) -> Result<(), String> {
    match e {
        Z3Expr::App(f, args) => {
            if *f == id {
                if in_q {
                    return Err("hàm spec: lời gọi đệ quy nằm trong forall / exists chưa được hỗ trợ".into());
                }
                out.push((pc.clone(), args.clone()));
            }
            args.iter().try_for_each(|a| rec_calls(a, id, pc, out, in_q))
        }
        Z3Expr::Ite(c, a, b) => {
            rec_calls(c, id, pc, out, in_q)?;
            pc.push(((**c).clone(), true));
            rec_calls(a, id, pc, out, in_q)?;
            pc.pop();
            pc.push(((**c).clone(), false));
            rec_calls(b, id, pc, out, in_q)?;
            pc.pop();
            Ok(())
        }
        Z3Expr::Bin(_, l, r) | Z3Expr::Cmp(_, l, r) | Z3Expr::And(l, r) | Z3Expr::Or(l, r) | Z3Expr::Math(_, l, r) => {
            rec_calls(l, id, pc, out, in_q)?;
            rec_calls(r, id, pc, out, in_q)
        }
        Z3Expr::Not(x) | Z3Expr::Old(x) => rec_calls(x, id, pc, out, in_q),
        Z3Expr::Mem(_, i, _) => rec_calls(i, id, pc, out, in_q),
        Z3Expr::Quant(_, _, lo, hi, b) => [lo, hi, b].iter().try_for_each(|x| rec_calls(x, id, pc, out, true)),
        Z3Expr::Reg(_) | Z3Expr::Const(_) | Z3Expr::FieldVal => Ok(()),
    }
}

/// Mọi khoá heap của module: (Layout, offset trường) -> số bit của trường
fn heap_keys(module: &Module) -> Vec<(HKey, u32)> {
    let mut v = Vec::new();
    for (l, lay) in module.layouts.iter().enumerate() {
        for f in &lay.fields {
            v.push(((l as u16, f.offset), int_bits(f.ty)));
        }
    }
    v
}

/// Kiểu tĩnh của mọi thanh ghi trong hàm (để biết trước vòng lặp ghi heap nào)
fn reg_types(module: &Module, func: &Func) -> HashMap<Reg, Type> {
    let mut t: HashMap<Reg, Type> = func.params.iter().copied().collect();
    for b in &func.blocks {
        t.extend(b.params.iter().copied());
        for i in &b.insts {
            match i {
                Inst::Const { dst, ty, .. }
                | Inst::Slice { dst, ty, .. }
                | Inst::Load { dst, ty, .. }
                | Inst::View { dst, ty, .. }
                | Inst::Addr { dst, ty, .. }
                | Inst::Narrow { dst, ty, .. } => {
                    t.insert(*dst, *ty);
                }
                Inst::Call { dst: Some(d), func_id, .. } => {
                    if let Some(rt) = module.funcs.get(*func_id as usize).and_then(|c| c.ret_ty) {
                        t.insert(*d, rt);
                    }
                }
                _ => {}
            }
        }
    }
    t
}

/// Heap hàm có thể ghi (kể cả qua hàm nó gọi, đệ quy). `None` = mọi heap (SIMD, phần cứng, ghi qua con trỏ hằng,
/// gọi gián tiếp, đệ quy). Khoá heap là (Layout, trường) TOÀN CỤC nên tập của hàm được gọi dùng thẳng cho hàm gọi.
fn written_keys(module: &Module, func: &Func, tys: &HashMap<Reg, Type>) -> Option<HashSet<HKey>> {
    written_rec(module, func, tys, &mut Vec::new())
}

/// Tóm tắt ghi của hàm dưới dạng chuỗi (khoá cache của HÀM GỌI phải phụ thuộc nó: nó suy từ THÂN hàm được gọi)
pub fn write_summary(module: &Module, func: &Func) -> String {
    let all: Vec<usize> = (0..func.blocks.len()).collect();
    let roots = write_roots(module, func, &all, &mut vec![func.name.clone()]).map(|r| {
        let mut v: Vec<Reg> = r.into_iter().collect();
        v.sort();
        v
    });
    match written_keys(module, func, &reg_types(module, func)) {
        Some(w) => {
            let mut v: Vec<HKey> = w.into_iter().collect();
            v.sort();
            format!("{:?}|{:?}", v, roots)
        }
        None => "ALL".into(),
    }
}

fn written_rec(module: &Module, func: &Func, tys: &HashMap<Reg, Type>, stack: &mut Vec<String>) -> Option<HashSet<HKey>> {
    if stack.contains(&func.name) || stack.len() > 32 {
        return None;
    }
    stack.push(func.name.clone());
    let r = written_body(module, func, tys, stack);
    stack.pop();
    r
}

fn written_body(module: &Module, func: &Func, tys: &HashMap<Reg, Type>, stack: &mut Vec<String>) -> Option<HashSet<HKey>> {
    let all: Vec<usize> = (0..func.blocks.len()).collect();
    written_blocks(module, func, tys, stack, &all)
}

/// Heap mà các block `blocks` của hàm có thể ghi
fn written_blocks(
    module: &Module,
    func: &Func,
    tys: &HashMap<Reg, Type>,
    stack: &mut Vec<String>,
    blocks: &[usize],
) -> Option<HashSet<HKey>> {
    let mut w = HashSet::new();
    let has_const_ptr = func.blocks.iter().flat_map(|b| &b.insts).any(|i| matches!(i, Inst::Const { ty, .. } if ty.ptr_layout().is_some()));
    for i in blocks.iter().flat_map(|&b| &func.blocks[b].insts) {
        match i {
            Inst::Store { base, offset, .. } => {
                let l = tys.get(base).and_then(|t| t.ptr_layout())?;
                if has_const_ptr {
                    return None;
                }
                let size = module.layouts[l as usize].size.max(1);
                w.insert((l, offset % size));
                for (k, _) in heap_keys(module) {
                    if k.0 != l {
                        w.insert(k);
                    }
                }
            }
            Inst::Call { func_id, .. } => {
                let c = module.funcs.get(*func_id as usize)?;
                w.extend(written_rec(module, c, &reg_types(module, c), stack)?);
            }
            Inst::CallPtr { .. } | Inst::Simd256 { .. } | Inst::AtaRead { .. } | Inst::Parallel { .. } | Inst::HwIo { .. } => {
                return None
            }
            // không ghi bộ nhớ (thêm lệnh mới vào Inst thì phải xếp nó vào đây hoặc nhánh trên: match đầy đủ, không `_`)
            Inst::Const { .. }
            | Inst::Bin { .. }
            | Inst::Cmp { .. }
            | Inst::Slice { .. }
            | Inst::Load { .. }
            | Inst::SmpWorkers { .. }
            | Inst::Narrow { .. }
            | Inst::View { .. }
            | Inst::Addr { .. }
            | Inst::Br { .. }
            | Inst::Jmp { .. }
            | Inst::Ret { .. }
            | Inst::Assume(_)
            | Inst::Assert(_) => {}
        }
    }
    Some(w)
}

/// Tham số con trỏ (thanh ghi tham số của `func`) mà các block `blocks` có thể ghi vào VÙNG của nó. `None` = có lệnh ghi
/// không xuất phát từ tham số (addr, con trỏ đọc từ bộ nhớ / trả về / hằng / tham số block, SIMD, phần cứng, gọi gián
/// tiếp, đệ quy) -> coi như ghi mọi nơi. Gốc đi qua slice / view; BV đã chứng minh mọi truy cập nằm trong vùng của gốc
/// ([p, p + len * size)), nên ghi qua gốc p chỉ đổi byte trong vùng của p.
fn write_roots(module: &Module, func: &Func, blocks: &[usize], stack: &mut Vec<String>) -> Option<HashSet<Reg>> {
    if stack.len() > 32 {
        return None;
    }
    let mut root: HashMap<Reg, Reg> = func.params.iter().filter(|(_, t)| t.ptr_layout().is_some()).map(|(r, _)| (*r, *r)).collect();
    // lan truyền qua slice / view (lặp tới điểm bất động: thứ tự block không nhất thiết là thứ tự định nghĩa)
    loop {
        let n0 = root.len();
        for i in func.blocks.iter().flat_map(|b| &b.insts) {
            if let Inst::Slice { dst, base: src, .. } | Inst::View { dst, src, .. } = i {
                if let Some(&r) = root.get(src) {
                    root.insert(*dst, r);
                }
            }
        }
        if root.len() == n0 {
            break;
        }
    }
    let mut out = HashSet::new();
    for i in blocks.iter().flat_map(|&b| &func.blocks[b].insts) {
        match i {
            Inst::Store { base, .. } => {
                out.insert(*root.get(base)?);
            }
            Inst::AtaRead { ptr, .. } => {
                out.insert(*root.get(ptr)?);
            }
            Inst::Call { func_id, args, .. } => {
                let c = module.funcs.get(*func_id as usize)?;
                if stack.contains(&c.name) {
                    return None;
                }
                stack.push(c.name.clone());
                let all: Vec<usize> = (0..c.blocks.len()).collect();
                let cr = write_roots(module, c, &all, stack);
                stack.pop();
                for r in cr? {
                    let j = c.params.iter().position(|(p, _)| *p == r)?;
                    out.insert(*root.get(args.get(j)?)?);
                }
            }
            Inst::CallPtr { .. } | Inst::Simd256 { .. } | Inst::Parallel { .. } | Inst::HwIo { .. } => return None,
            Inst::Const { .. }
            | Inst::Bin { .. }
            | Inst::Cmp { .. }
            | Inst::Slice { .. }
            | Inst::Load { .. }
            | Inst::SmpWorkers { .. }
            | Inst::Narrow { .. }
            | Inst::View { .. }
            | Inst::Addr { .. }
            | Inst::Br { .. }
            | Inst::Jmp { .. }
            | Inst::Ret { .. }
            | Inst::Assume(_)
            | Inst::Assert(_) => {}
        }
    }
    Some(out)
}

impl<'ctx> IV<'ctx> {
    fn n(&self, v: u64) -> Int<'ctx> {
        Int::from_u64(self.ctx, v)
    }
    /// 2^k (k <= 64)
    fn pow2(&self, k: u32) -> Int<'ctx> {
        if k < 64 {
            self.n(1u64 << k)
        } else {
            Int::add(self.ctx, &[&self.n(u64::MAX), &self.n(1)])
        }
    }
    fn m64(&self) -> Int<'ctx> {
        self.pow2(64)
    }
    fn range(&self, x: &Int<'ctx>, bits: u32) -> Bool<'ctx> {
        Bool::and(self.ctx, &[&x.ge(&self.n(0)), &x.lt(&self.pow2(bits))])
    }
    fn new_int(&mut self, hint: &str) -> Int<'ctx> {
        self.fresh += 1;
        Int::new_const(self.ctx, format!("{}!{}", hint, self.fresh))
    }
    fn decl(&mut self, r: Reg, ty: Type) -> Int<'ctx> {
        let x = Int::new_const(self.ctx, format!("r{}", r));
        self.solver.assert(&self.range(&x, int_bits(ty)));
        self.regs.insert(r, x.clone());
        self.tys.insert(r, ty);
        x
    }
    fn get(&self, r: Reg) -> Result<Int<'ctx>, String> {
        self.regs.get(&r).cloned().ok_or_else(|| format!("checker số nguyên: %{} chưa khởi tạo", r))
    }
    /// floor(x / c), c > 0, bằng thương mới (định nghĩa toàn phần nên khẳng định toàn cục được)
    fn divc(&mut self, x: &Int<'ctx>, c: &Int<'ctx>) -> Int<'ctx> {
        if self.depth > 0 {
            // trong lượng từ: thương mới sẽ là MỘT giá trị cho mọi biến buộc -> sai; dùng `div` của Z3 (x >= 0, c > 0)
            return x.div(c);
        }
        let q = self.new_int("q");
        let cq = Int::mul(self.ctx, &[c, &q]);
        self.solver.assert(&cq.le(x));
        self.solver.assert(&x.lt(&Int::add(self.ctx, &[&cq, c])));
        q
    }
    /// sự thật luôn đúng về các hạng: khẳng định toàn cục, hoặc (trong lượng từ) gom làm giả thiết của thân
    fn fact(&mut self, b: Bool<'ctx>) {
        if self.depth > 0 {
            self.side.push(b);
        } else {
            self.solver.assert(&b);
        }
    }
    fn modc(&mut self, x: &Int<'ctx>, c: &Int<'ctx>) -> Int<'ctx> {
        let q = self.divc(x, c);
        Int::sub(self.ctx, &[x, &Int::mul(self.ctx, &[c, &q])])
    }
    /// Hàm không diễn giải `name`(a, b) với kết quả trong [0, 2^64)
    fn uf(&mut self, name: &str, a: &Int<'ctx>, b: &Int<'ctx>) -> Int<'ctx> {
        let ctx = self.ctx;
        let f = self
            .ufs
            .entry(name.to_string())
            .or_insert_with(|| FuncDecl::new(ctx, format!("light_{}", name), &[&Sort::int(ctx), &Sort::int(ctx)], &Sort::int(ctx)));
        let v = f.apply(&[a, b]).as_int().unwrap();
        let r = self.range(&v, 64);
        self.fact(r);
        v
    }
    fn bool01(&self, b: &Bool<'ctx>) -> Int<'ctx> {
        b.ite(&self.n(1), &self.n(0))
    }
    /// giá trị có dấu (bù hai) của x trong [0, 2^64)
    fn signed(&self, x: &Int<'ctx>) -> Int<'ctx> {
        x.ge(&self.pow2(63)).ite(&Int::sub(self.ctx, &[x, &self.m64()]), x)
    }

    /// Phép bit-vector 64 bit trên số nguyên trong [0, 2^64). `kl` / `kr`: giá trị nếu toán hạng là hằng; `bl` / `br`: toán
    /// hạng chắc chắn 0/1. Ngữ nghĩa trùng BV (chia cho 0: udiv = 2^64-1, urem = x; dịch >= 64 = 0).
    #[allow(clippy::too_many_arguments)]
    fn binop(
        &mut self,
        op: BinOp,
        a: &Int<'ctx>,
        b: &Int<'ctx>,
        kl: Option<u64>,
        kr: Option<u64>,
        bl: bool,
        br: bool,
        checked: bool,
    ) -> Int<'ctx> {
        let ctx = self.ctx;
        let m = self.m64();
        let sum = Int::add(ctx, &[a, b]);
        let diff = Int::sub(ctx, &[a, b]);
        let prod = Int::mul(ctx, &[a, b]);
        let is_mask = |k: u64| k != 0 && k & k.wrapping_add(1) == 0;
        // sự thật về phép bit / chia chỉ đúng khi toán hạng là số 64 bit; trong ĐẶC TẢ toán hạng có thể là số toán học
        // (âm / rất lớn, vd `(a - b) & c`), khẳng định không điều kiện sẽ ép a >= b ở mọi nhánh -> phải có điều kiện
        let inr = Bool::and(ctx, &[&self.range(a, 64), &self.range(b, 64)]);
        match op {
            // mã: BV đã chứng minh không tràn -> chính xác; đặc tả: ngữ nghĩa BV quay vòng
            BinOp::Add if checked => sum,
            BinOp::Sub if checked => diff,
            BinOp::Mul if checked => prod,
            BinOp::Add | BinOp::AddWrap => sum.ge(&m).ite(&Int::sub(ctx, &[&sum, &m]), &sum),
            BinOp::Sub | BinOp::SubWrap => a.ge(b).ite(&diff, &Int::add(ctx, &[&diff, &m])),
            BinOp::Mul | BinOp::MulWrap => self.modc(&prod, &m),
            BinOp::MulHi => self.divc(&prod, &m),
            BinOp::UDiv | BinOp::URem => {
                let (q, r) = match kr {
                    Some(c) if c > 0 => {
                        let c = self.n(c);
                        let q = self.divc(a, &c);
                        let r = Int::sub(ctx, &[a, &Int::mul(ctx, &[&c, &q])]);
                        (q, r)
                    }
                    _ => {
                        // b > 0: b*q <= a < b*q + b (phi tuyến nhưng đúng); b == 0 theo ngữ nghĩa BV
                        let q = self.uf("udiv", a, b);
                        let bq = Int::mul(ctx, &[b, &q]);
                        let pos = b.gt(&self.n(0));
                        self.fact(Bool::and(ctx, &[&inr, &pos]).implies(&Bool::and(ctx, &[&bq.le(a), &a.lt(&Int::add(ctx, &[&bq, b]))])));
                        let r = Int::sub(ctx, &[a, &bq]);
                        let zero = b._eq(&self.n(0));
                        (zero.ite(&Int::sub(ctx, &[&m, &self.n(1)]), &q), zero.ite(a, &r))
                    }
                };
                if op == BinOp::UDiv { q } else { r }
            }
            BinOp::And if bl && br => a._eq(&self.n(0)).ite(&self.n(0), b),
            BinOp::Or if bl && br => a._eq(&self.n(0)).ite(b, &self.n(1)),
            BinOp::Xor if bl && br => a._eq(b).ite(&self.n(0), &self.n(1)),
            BinOp::And if kr.is_some_and(is_mask) => {
                let k = kr.unwrap();
                let c = if k == u64::MAX { m } else { self.n(k + 1) };
                self.modc(a, &c)
            }
            BinOp::And if kl.is_some_and(is_mask) => self.binop(op, b, a, kr, kl, br, bl, checked),
            BinOp::And if kr == Some(0) || kl == Some(0) => self.n(0),
            BinOp::Or | BinOp::Xor if kr == Some(0) => a.clone(),
            BinOp::Or | BinOp::Xor if kl == Some(0) => b.clone(),
            BinOp::Xor if kr == Some(u64::MAX) => Int::sub(ctx, &[&m, &self.n(1), a]),
            BinOp::Shl if kr.is_some() => {
                let k = kr.unwrap();
                if k >= 64 {
                    self.n(0)
                } else {
                    let x = Int::mul(ctx, &[a, &self.pow2(k as u32)]);
                    self.modc(&x, &m)
                }
            }
            BinOp::LShr if kr.is_some() => {
                let k = kr.unwrap();
                if k >= 64 { self.n(0) } else { self.divc(a, &self.pow2(k as u32)) }
            }
            // dịch theo biến: chuỗi ite 64 nhánh (chính xác; số dịch >= 64 cho 0 như BV)
            BinOp::Shl | BinOp::LShr => {
                let mut v = self.n(0);
                for k in (0..64u32).rev() {
                    let x = if op == BinOp::Shl {
                        let t = Int::mul(ctx, &[a, &self.pow2(k)]);
                        self.modc(&t, &m)
                    } else {
                        self.divc(a, &self.pow2(k))
                    };
                    v = b._eq(&self.n(k as u64)).ite(&x, &v);
                }
                v
            }
            BinOp::And => {
                let v = self.uf("and", a, b);
                self.fact(inr.implies(&Bool::and(ctx, &[&v.le(a), &v.le(b)])));
                v
            }
            BinOp::Or | BinOp::Xor => {
                let v = self.uf(if op == BinOp::Or { "or" } else { "xor" }, a, b);
                self.fact(inr.implies(&v.le(&sum))); // a | b <= a + b, a ^ b <= a + b
                if op == BinOp::Or {
                    self.fact(inr.implies(&Bool::and(ctx, &[&v.ge(a), &v.ge(b)])));
                }
                v
            }
            _ => self.uf(&format!("{:?}", op).to_lowercase(), a, b),
        }
    }

    fn cmpop(&self, op: CmpOp, a: &Int<'ctx>, b: &Int<'ctx>) -> Bool<'ctx> {
        match op {
            CmpOp::Eq => a._eq(b),
            CmpOp::Ne => a._eq(b).not(),
            CmpOp::Ult => a.lt(b),
            CmpOp::Ule => a.le(b),
            CmpOp::Ugt => a.gt(b),
            CmpOp::Uge => a.ge(b),
            CmpOp::Slt => self.signed(a).lt(&self.signed(b)),
            CmpOp::Sle => self.signed(a).le(&self.signed(b)),
            CmpOp::Sgt => self.signed(a).gt(&self.signed(b)),
            CmpOp::Sge => self.signed(a).ge(&self.signed(b)),
        }
    }

    // ---- đặc tả ----
    fn ev_int(&mut self, e: &Z3Expr, env: &IEnv<'ctx>) -> Result<Int<'ctx>, String> {
        let k = |e: &Z3Expr| if let Z3Expr::Const(v) = e { Some(*v) } else { None };
        Ok(match e {
            Z3Expr::Reg(r) => env.get(r).cloned().ok_or_else(|| format!("checker số nguyên: %{} chưa khởi tạo", r))?,
            Z3Expr::Const(v) => self.n(*v),
            Z3Expr::FieldVal => return Err("checker số nguyên: 'val' (bất biến Layout) chưa hỗ trợ".into()),
            Z3Expr::Bin(op, l, r) => {
                let (a, b) = (self.ev_int(l, env)?, self.ev_int(r, env)?);
                self.binop(*op, &a, &b, k(l), k(r), false, false, false)
            }
            // and / or / not dùng làm GIÁ TRỊ = phép bit (như eval_bv của BV)
            Z3Expr::And(l, r) | Z3Expr::Or(l, r) => {
                let (a, b) = (self.ev_int(l, env)?, self.ev_int(r, env)?);
                let op = if matches!(e, Z3Expr::And(..)) { BinOp::And } else { BinOp::Or };
                self.binop(op, &a, &b, k(l), k(r), false, false, false)
            }
            Z3Expr::Not(x) => {
                let a = self.ev_int(x, env)?;
                Int::sub(self.ctx, &[&self.m64(), &self.n(1), &a])
            }
            Z3Expr::Cmp(..) | Z3Expr::Quant(..) => return Err("biểu thức logic không thể dùng làm giá trị số".into()),
            Z3Expr::Mem(p, i, off) => {
                let ty = match &self.spec_tys {
                    Some(t) => t.get(p).copied(),
                    None => self.tys.get(p).copied(),
                };
                let l = ty.and_then(|t| t.ptr_layout()).ok_or_else(|| format!("mem: %{} không phải con trỏ", p))?;
                let pv = env.get(p).cloned().ok_or_else(|| format!("checker số nguyên: %{} chưa khởi tạo", p))?;
                let iv = self.ev_int(i, env)?;
                let (addr, key, bits) = self.elem(l, &pv, Some(&iv), *off)?;
                let h = if self.in_old { &self.old_heap } else { &self.heap };
                let sel = h[&key].select(&addr);
                if let Some(f) = self.pat_frames.last_mut() {
                    f.push(sel.clone());
                }
                // miền giá trị ô nhớ (đúng với bộ nhớ thật). Ngoài lượng từ: sự thật cụ thể. Trong lượng từ: chỉ khi
                // giúp chứng minh (`want_range`), vì ở giả thiết của lượng từ nó chặn việc dùng lượng từ.
                let v = sel.as_int().unwrap();
                if !self.in_spec_body && (self.depth == 0 || self.want_range) {
                    let r = self.range(&v, bits);
                    self.fact(r);
                }
                v
            }
            Z3Expr::Old(x) => {
                let prev = std::mem::replace(&mut self.in_old, true);
                let v = self.ev_int(x, env);
                self.in_old = prev;
                v?
            }
            Z3Expr::Ite(c, a, b) => {
                let c = self.ev_bool(c, env)?;
                let (a, b) = (self.ev_int(a, env)?, self.ev_int(b, env)?);
                c.ite(&a, &b)
            }
            Z3Expr::App(f, args) => {
                self.define_spec(*f)?;
                let mut vals = Vec::new();
                for a in args {
                    vals.push(self.ev_int(a, env)?);
                }
                let (decls, reads) = &self.spec_decls[f];
                let decl = &decls[self.spec_layer.get(f).copied().unwrap_or(SPEC_FUEL)];
                let h = if self.in_old { &self.old_heap } else { &self.heap };
                let hs: Vec<Array> = reads.iter().map(|k| h[k].clone()).collect();
                let mut all: Vec<&dyn Ast> = hs.iter().map(|x| x as &dyn Ast).collect();
                all.extend(vals.iter().map(|x| x as &dyn Ast));
                let t = decl.apply(&all);
                if let Some(f) = self.pat_frames.last_mut() {
                    f.push(t.clone());
                }
                t.as_int().unwrap()
            }
            Z3Expr::Math(op, l, r) => {
                let (a, b) = (self.ev_int(l, env)?, self.ev_int(r, env)?);
                match op {
                    MathOp::Add => Int::add(self.ctx, &[&a, &b]),
                    MathOp::Sub => Int::sub(self.ctx, &[&a, &b]),
                    MathOp::Mul => Int::mul(self.ctx, &[&a, &b]),
                    MathOp::Div | MathOp::Mod => {
                        // chia Euclid; số chia là hằng dương -> thương mới (tuyến tính), còn lại `div`/`mod` của Z3
                        // số chia là hằng (kể cả biểu thức hằng như 2^64 - 1 + 1): thương mới, tuyến tính
                        let q = match const_math(r) {
                            Some(c) if c > 0 => {
                                let c = Int::from_str(self.ctx, &c.to_string()).unwrap();
                                self.divc(&a, &c)
                            }
                            // a >= 0, b > 0: CÙNG hàm thương với `udiv` / `urem` của mã (để Z3 thấy hai bên là một hạng);
                            // còn lại `div` của Z3 (Euclid)
                            _ => {
                                let ok = Bool::and(self.ctx, &[&a.ge(&self.n(0)), &b.gt(&self.n(0)), &a.lt(&self.m64()), &b.lt(&self.m64())]);
                                let q = self.binop(BinOp::UDiv, &a, &b, None, None, false, false, false);
                                ok.ite(&q, &a.div(&b))
                            }
                        };
                        if *op == MathOp::Div {
                            q
                        } else {
                            Int::sub(self.ctx, &[&a, &Int::mul(self.ctx, &[&b, &q])])
                        }
                    }
                }
            }
        })
    }

    fn ev_bool(&mut self, e: &Z3Expr, env: &IEnv<'ctx>) -> Result<Bool<'ctx>, String> {
        Ok(match e {
            Z3Expr::Cmp(op, l, r) => {
                let (a, b) = (self.ev_int(l, env)?, self.ev_int(r, env)?);
                self.cmpop(*op, &a, &b)
            }
            Z3Expr::And(l, r) => {
                let (a, b) = (self.ev_bool(l, env)?, self.ev_bool(r, env)?);
                Bool::and(self.ctx, &[&a, &b])
            }
            Z3Expr::Or(l, r) => {
                let (a, b) = (self.ev_bool(l, env)?, self.ev_bool(r, env)?);
                Bool::or(self.ctx, &[&a, &b])
            }
            Z3Expr::Not(x) => {
                self.pol = !self.pol;
                let v = self.ev_bool(x, env);
                self.pol = !self.pol;
                v?.not()
            }
            Z3Expr::Old(x) => {
                let prev = std::mem::replace(&mut self.in_old, true);
                let v = self.ev_bool(x, env);
                self.in_old = prev;
                v?
            }
            Z3Expr::Quant(all, v, lo, hi, body) => {
                let (lo, hi) = (self.ev_int(lo, env)?, self.ev_int(hi, env)?);
                let j = self.new_int("j");
                let mut env2 = env.clone();
                env2.insert(*v, j.clone());
                let mark = self.side.len();
                self.depth += 1;
                self.pat_frames.push(Vec::new());
                let prev_wr = std::mem::replace(&mut self.want_range, *all == self.pol);
                let b = self.ev_bool(body, &env2);
                self.want_range = prev_wr;
                let cands = self.pat_frames.pop().unwrap();
                self.depth -= 1;
                let b = b?;
                let mut hyp: Vec<Bool> = vec![lo.le(&j), j.lt(&hi)];
                hyp.extend(self.side.drain(mark..));
                let hyp = Bool::and(self.ctx, &hyp.iter().collect::<Vec<_>>());
                // pattern: hạng đọc heap / gọi hàm spec CÓ biến buộc j (mỗi hạng một pattern thay thế); hạng không có j
                // thuộc về lượng từ bên ngoài. Không có ứng viên: để Z3 tự chọn.
                let jn = j.to_string();
                let has_j = |t: &z3::ast::Dynamic| {
                    let st = t.to_string();
                    st.match_indices(&jn).any(|(i, _)| !st[i + jn.len()..].starts_with(|c: char| c.is_ascii_digit()))
                };
                let (mine, rest): (Vec<_>, Vec<_>) = cands.into_iter().partition(|t| has_j(t));
                if let Some(f) = self.pat_frames.last_mut() {
                    f.extend(rest);
                }
                let pats: Vec<z3::Pattern> = mine.iter().map(|t| z3::Pattern::new(self.ctx, &[t as &dyn Ast])).collect();
                let pref: Vec<&z3::Pattern> = pats.iter().collect();
                if *all {
                    z3::ast::forall_const(self.ctx, &[&j], &pref, &hyp.implies(&b))
                } else {
                    z3::ast::exists_const(self.ctx, &[&j], &pref, &Bool::and(self.ctx, &[&hyp, &b]))
                }
            }
            _ => return Err("biểu thức đòi hỏi kiểu logic (Cmp/And/Or/Not/forall/exists)".into()),
        })
    }

    /// Khai báo hàm spec `id` (một lần): hàm không diễn giải f(heap đọc..., đối số...) + tiên đề mở một bước
    /// `miền(đối số) => f(..) == thân` với pattern f(..) (đo: bench/p3/smt/r1_sum_axiom). Đệ quy: chứng minh @dec >= 0 và
    /// giảm ngặt ở mỗi lời gọi đệ quy (đối số trong miền) TRƯỚC khi khẳng định tiên đề -> tiên đề có nghiệm, không mâu thuẫn.
    fn define_spec(&mut self, id: u32) -> Result<(), String> {
        if self.spec_decls.contains_key(&id) {
            return Ok(());
        }
        let ctx = self.ctx;
        let module = self.module;
        let sp = module.specs.get(id as usize).ok_or("hàm spec không tồn tại")?;
        let body = sp.body.as_ref().ok_or_else(|| format!("hàm spec '{}' thiếu thân", sp.name))?;
        let mut reads = HashSet::new();
        spec_reads(module, id, &mut Vec::new(), &mut reads)?;
        let mut reads: Vec<HKey> = reads.into_iter().collect();
        reads.sort();
        let asort = Sort::array(ctx, &Sort::int(ctx), &Sort::int(ctx));
        let mut dom: Vec<Sort> = reads.iter().map(|_| asort.clone()).collect();
        dom.extend(sp.params.iter().map(|_| Sort::int(ctx)));
        let dref: Vec<&Sort> = dom.iter().collect();
        let decls: Vec<FuncDecl> =
            (0..=SPEC_FUEL).map(|l| FuncDecl::new(ctx, format!("spec_{}_{}", sp.name, l), &dref, &Sort::int(ctx))).collect();
        self.spec_decls.insert(id, (decls, reads.clone()));
        let fail = |m: String| format!("[hàm spec '{}'] {}{}", sp.name, m, if sp.origin.is_empty() { String::new() } else { format!("\n    tại {}", sp.origin) });
        // biến buộc: heap + tham số
        let arrs: Vec<Array> = reads
            .iter()
            .map(|k| {
                self.fresh += 1;
                Array::new_const(ctx, format!("SH{}_{}!{}", k.0, k.1, self.fresh), &Sort::int(ctx), &Sort::int(ctx))
            })
            .collect();
        let xs: Vec<Int> = sp.params.iter().map(|(r, _)| self.new_int(&format!("sx{}", r))).collect();
        let env: IEnv = sp.params.iter().map(|p| p.0).zip(xs.iter().cloned()).collect();
        let ranges: Vec<Bool> = sp.params.iter().zip(&xs).map(|((_, t), x)| self.range(x, int_bits(*t))).collect();
        // ngữ cảnh tính thân: heap = mảng buộc, kiểu = tham số hàm spec
        let saved_heap = self.heap.clone();
        let saved_old = self.old_heap.clone();
        let saved_tys = self.spec_tys.replace(sp.params.iter().copied().collect());
        let saved_in_old = std::mem::replace(&mut self.in_old, false);
        // có thể được gọi lần đầu từ TRONG một lượng từ: định nghĩa là toàn cục, độc lập với ngữ cảnh đó
        let saved_depth = std::mem::replace(&mut self.depth, 0);
        let saved_side = std::mem::take(&mut self.side);
        for (k, a) in reads.iter().zip(&arrs) {
            self.heap.insert(*k, a.clone());
        }
        self.old_heap = self.heap.clone();
        let r = (|| -> Result<(), String> {
            // hàm spec khác được gọi: định nghĩa TRƯỚC (ngoài push/pop của chứng minh dừng, để tiên đề của nó không bị pop)
            let mut others = Vec::new();
            collect_apps(body, &mut others);
            if let Some(d) = &sp.dec {
                collect_apps(d, &mut others);
            }
            for o in others {
                if o != id {
                    self.define_spec(o)?;
                }
            }
            // như tiên đề: không giả định miền ô nhớ (tiên đề đúng cho MỌI mảng)
            self.in_spec_body = true;
            // dừng
            let mut calls = Vec::new();
            rec_calls(body, id, &mut Vec::new(), &mut calls, false).map_err(&fail)?;
            if !calls.is_empty() {
                let dec = sp.dec.as_ref().ok_or_else(|| fail("đệ quy cần `decreases`".into()))?;
                self.solver.push();
                for r in &ranges {
                    self.solver.assert(r);
                }
                let d0 = self.ev_int(dec, &env)?;
                let res = (|| -> Result<(), String> {
                    self.solver.push();
                    self.solver.assert(&d0.lt(&self.n(0)));
                    let st = self.solver.check();
                    self.solver.pop(1);
                    if st != SatResult::Unsat {
                        return Err(fail("decreases có thể âm".into()));
                    }
                    for (pc, args) in &calls {
                        self.solver.push();
                        for (c, pol) in pc {
                            let b = self.ev_bool(c, &env)?;
                            self.solver.assert(&if *pol { b } else { b.not() });
                        }
                        let mut env2 = env.clone();
                        for (((r, t), a), _) in sp.params.iter().zip(args).zip(&xs) {
                            let v = self.ev_int(a, &env)?;
                            self.solver.assert(&self.range(&v, int_bits(*t)));
                            env2.insert(*r, v);
                        }
                        let d1 = self.ev_int(dec, &env2)?;
                        self.solver.assert(&d1.ge(&d0));
                        let st = self.solver.check();
                        self.solver.pop(1);
                        if st != SatResult::Unsat {
                            return Err(fail("decreases không giảm ngặt ở một lời gọi đệ quy".into()));
                        }
                    }
                    Ok(())
                })();
                self.solver.pop(1);
                res?;
            }
            self.in_spec_body = false;
            // tiên đề, theo tầng: fL(x) == thân[f_{L-1}] và fL(x) == f_{L-1}(x), pattern fL(x)
            let mut all: Vec<&dyn Ast> = arrs.iter().map(|x| x as &dyn Ast).collect();
            all.extend(xs.iter().map(|x| x as &dyn Ast));
            for l in 1..=SPEC_FUEL {
                self.spec_layer.insert(id, l - 1);
                let mark = self.side.len();
                self.depth += 1;
                let prev_sb = std::mem::replace(&mut self.in_spec_body, true);
                let bv = self.ev_int(body, &env);
                self.in_spec_body = prev_sb;
                self.depth -= 1;
                self.spec_layer.remove(&id);
                let bv = bv?;
                // sự thật phụ (miền / tính chất của hàm không diễn giải) nằm ở VẾ KẾT LUẬN: đúng với mọi đối số nên
                // không làm tiên đề mâu thuẫn, và không chặn tiên đề như khi đặt ở giả thiết
                let facts: Vec<Bool> = self.side.drain(mark..).collect();
                let hyp = ranges.clone();
                let (decls, _) = &self.spec_decls[&id];
                let app = decls[l].apply(&all);
                let low = decls[l - 1].apply(&all);
                let pat = z3::Pattern::new(ctx, &[&app as &dyn Ast]);
                let hyp = Bool::and(ctx, &hyp.iter().collect::<Vec<_>>());
                let ai = app.as_int().unwrap();
                let mut concl = vec![ai._eq(&bv)];
                concl.extend(facts);
                let concl = Bool::and(ctx, &concl.iter().collect::<Vec<_>>());
                let ax = z3::ast::forall_const(ctx, &all, &[&pat], &hyp.implies(&concl));
                let syn = z3::ast::forall_const(ctx, &all, &[&pat], &ai._eq(&low.as_int().unwrap()));
                self.solver.assert(&ax);
                self.solver.assert(&syn);
            }
            Ok(())
        })();
        self.heap = saved_heap;
        self.old_heap = saved_old;
        self.spec_tys = saved_tys;
        self.in_old = saved_in_old;
        self.in_spec_body = false;
        self.depth = saved_depth;
        self.side = saved_side;
        if r.is_err() {
            self.spec_decls.remove(&id);
        }
        r
    }

    /// Địa chỉ phần tử + khoá heap cho trường ở `off` (có thể vượt một phần tử) của phần tử `idx` sau con trỏ `p`
    fn elem(&self, l: u16, p: &Int<'ctx>, idx: Option<&Int<'ctx>>, off: u32) -> Result<(Int<'ctx>, HKey, u32), String> {
        let lay = &self.module.layouts[l as usize];
        let size = lay.size.max(1);
        let f = lay
            .fields
            .iter()
            .find(|f| f.offset == off % size)
            .ok_or_else(|| format!("mem: offset {} không phải đầu trường của Layout '{}'", off, lay.name))?;
        // dạng CHUẨN `gốc + chỉ_số * kích_thước` (bỏ số hạng 0) cho cả mã lẫn đặc tả: e-matching của lượng từ khớp
        // theo cấu trúc hạng, nên `a + j*8` (đặc tả) phải gặp đúng `a + i*8` (mã), không phải `r10 + 0` với r10 = a + i*8
        let mut a = match idx {
            Some(i) => Int::add(self.ctx, &[p, &Int::mul(self.ctx, &[i, &self.n(size as u64)])]),
            None => p.clone(),
        };
        if off >= size {
            a = Int::add(self.ctx, &[&a, &self.n(((off / size) * size) as u64)]);
        }
        Ok((a, (l, off % size), int_bits(f.ty)))
    }
    /// địa chỉ cho load / store qua thanh ghi con trỏ `base` (dạng chuẩn nếu base là slice). Đúng trên đường đi tới
    /// lệnh: slice được giả định theo điều kiện đường đi, và lệnh dùng nó nằm sau nó.
    fn addr_of(&self, l: u16, base: Reg, off: u32) -> Result<(Int<'ctx>, HKey, u32), String> {
        match self.slice_of.get(&base) {
            Some((root, i)) => self.elem(l, root, Some(i), off),
            None => self.elem(l, &self.get(base)?, None, off),
        }
    }
    /// Khung: `forall x: x không chạm vùng nào trong `regions` (byte [P, P + B)) => new[x] == old[x]`, pattern new[x].
    /// x là địa chỉ PHẦN TỬ của heap `k` (kích thước phần tử s): chạm vùng <=> B > 0, x + s > P và x < P + B.
    fn frame(&mut self, k: HKey, new: &Array<'ctx>, old: &Array<'ctx>, regions: &[(Int<'ctx>, Int<'ctx>)]) {
        let ctx = self.ctx;
        self.fresh += 1;
        let x = Int::new_const(ctx, format!("fx!{}", self.fresh));
        let s = self.n(self.module.layouts[k.0 as usize].size.max(1) as u64);
        let xe = Int::add(ctx, &[&x, &s]);
        let outside: Vec<Bool> = regions
            .iter()
            .map(|(p, b)| Bool::and(ctx, &[&b.gt(&self.n(0)), &xe.gt(p), &x.lt(&Int::add(ctx, &[p, b]))]).not())
            .collect();
        let hyp = Bool::and(ctx, &outside.iter().collect::<Vec<_>>());
        let nx = new.select(&x);
        let pat = z3::Pattern::new(ctx, &[&nx as &dyn Ast]);
        let body = hyp.implies(&nx._eq(&old.select(&x)));
        self.solver.assert(&z3::ast::forall_const(ctx, &[&x], &[&pat], &body));
    }

    /// Vùng byte (đầu, số byte) của tham số con trỏ `r` của hàm `f`; `val` cho giá trị của tham số f (độ dài động)
    fn region_of(&self, f: &Func, r: Reg, val: &dyn Fn(Reg) -> Option<Int<'ctx>>) -> Option<(Int<'ctx>, Int<'ctx>)> {
        let ty = f.params.iter().find(|(p, _)| *p == r)?.1;
        let start = val(r)?;
        let (l, len) = match ty {
            Type::Ptr { layout_id, max_elems } => (layout_id, self.n(max_elems)),
            Type::DPtr { layout_id, len } => (layout_id, val(len)?),
            _ => return None,
        };
        let size = self.n(self.module.layouts[l as usize].size as u64);
        Some((start, Int::mul(self.ctx, &[&len, &size])))
    }

    /// Phiên bản heap mới (mảng tuỳ ý). Miền giá trị ô: xem `want_range`.
    fn fresh_heap(&mut self, keys: &[HKey]) {
        let ctx = self.ctx;
        for k in keys {
            self.fresh += 1;
            let a = Array::new_const(ctx, format!("H{}_{}!{}", k.0, k.1, self.fresh), &Sort::int(ctx), &Sort::int(ctx));
            self.heap.insert(*k, a);
        }
    }
    fn havoc_all(&mut self) {
        let ks: Vec<HKey> = self.heap.keys().copied().collect();
        self.fresh_heap(&ks);
    }
    fn ptr_layout_of(&self, r: Reg) -> Option<u16> {
        self.tys.get(&r).and_then(|t| t.ptr_layout())
    }

    /// tính mệnh đề làm MỤC TIÊU (cực tính dương)
    fn ev_goal(&mut self, e: &Z3Expr, env: &IEnv<'ctx>) -> Result<Bool<'ctx>, String> {
        let prev = std::mem::replace(&mut self.pol, true);
        let r = self.ev_bool(e, env);
        self.pol = prev;
        r
    }

    /// mệnh đề checker này phải CHỨNG MINH (BV không chứng minh nó, hoặc chế độ đối chiếu chéo)
    fn mine(&self, e: &Z3Expr) -> bool {
        self.all || e.class() != SpecClass::Bv
    }

    fn assume(&self, b: &Bool<'ctx>) {
        match &self.cur_cond {
            Some(c) => self.solver.assert(&c.implies(b)),
            None => self.solver.assert(b),
        }
    }

    /// Có đường đi tới đây? "unknown" (thường do lượng từ: Z3 khó trả lời sat) = coi như có -> vẫn kiểm (an toàn), nên
    /// chỉ cho thời gian ngắn thay vì chờ hết TIMEOUT_MS mỗi block
    fn feasible(&self) -> bool {
        self.set_timeout(FEASIBLE_MS);
        self.solver.push();
        if let Some(c) = &self.cur_cond {
            self.solver.assert(c);
        }
        let r = self.solver.check();
        self.solver.pop(1);
        self.set_timeout(TIMEOUT_MS);
        !matches!(r, SatResult::Unsat)
    }
    fn set_timeout(&self, ms: u32) {
        let mut p = Params::new(self.ctx);
        p.set_u32("timeout", ms);
        self.solver.set_params(&p);
    }

    fn check(&self, goal: &Bool<'ctx>, msg: &str) -> Result<(), String> {
        self.solver.push();
        if let Some(c) = &self.cur_cond {
            self.solver.assert(c);
        }
        self.solver.assert(&goal.not());
        if std::env::var_os("LIGHT_INT_DUMP").is_some() {
            eprintln!("{}", self.solver);
        }
        let at = if self.cur_at.is_empty() { String::new() } else { format!("\n    tại {}", self.cur_at) };
        let t0 = std::time::Instant::now();
        let res = self.solver.check();
        if std::env::var_os("LIGHT_INT_TIME").is_some() {
            eprintln!("[int] {:>6} ms  {} {}", t0.elapsed().as_millis(), self.func.name, msg);
        }
        let out = match res {
            SatResult::Unsat => Ok(()),
            SatResult::Sat => {
                let ce = self
                    .solver
                    .get_model()
                    .map(|m| {
                        let mut ids: Vec<&Reg> = self.regs.keys().collect();
                        ids.sort();
                        ids.into_iter()
                            .take(24)
                            .filter_map(|r| {
                                let v = m.eval(&self.regs[r], true)?;
                                let s = v.as_u64().map(|x| format!("{:#x}", x)).unwrap_or_else(|| v.to_string());
                                Some(format!("%{} = {}", r, s))
                            })
                            .collect::<Vec<_>>()
                            .join(", ")
                    })
                    .unwrap_or_default();
                Err(format!(
                    "[Z3 FAIL] func {} @b{}: '{}' -> {} when {}{}",
                    self.func.name, self.cur_bb, self.cur_inst, msg, ce, at
                ))
            }
            SatResult::Unknown => Err(format!(
                "[Z3 TIMEOUT] func {} @b{}: '{}' -> Không chứng minh được (checker số nguyên không kết luận ({}) — thường do \
                 nhân / chia phi tuyến, hoặc lượng từ / hàm spec cần mở thêm): {}{}",
                self.func.name,
                self.cur_bb,
                self.cur_inst,
                self.solver.get_reason_unknown().unwrap_or_default(),
                msg,
                at
            )),
        };
        self.solver.pop(1);
        out
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

    fn check_target_invs(&mut self, ti: usize, env: &IEnv<'ctx>, extra: Option<&Bool<'ctx>>) -> Result<(), String> {
        let b = &self.func.blocks[ti];
        for (i, inv) in b.invs.iter().enumerate() {
            if !self.mine(inv) {
                continue;
            }
            let g = self.ev_goal(inv, env)?;
            let g = match extra {
                Some(x) => x.implies(&g),
                None => g,
            };
            self.check(&g, &format!("Vi phạm bất biến (@inv #{}) khi nhảy vào @b{}", i, b.id))?;
        }
        Ok(())
    }

    fn step(&mut self, bi: usize, inst: &Inst, idx: &HashMap<BlockId, usize>) -> Result<(), String> {
        let ctx = self.ctx;
        match inst {
            Inst::Const { dst, ty, val } => {
                let d = self.decl(*dst, *ty);
                self.solver.assert(&d._eq(&self.n(*val)));
                self.consts.insert(*dst, *val);
                if ty.ptr_layout().is_some() {
                    self.opaque.insert(*dst);
                }
            }
            Inst::Bin { dst, op, lhs, rhs } => {
                let (a, b) = (self.get(*lhs)?, self.get(*rhs)?);
                let (kl, kr) = (self.consts.get(lhs).copied(), self.consts.get(rhs).copied());
                let (bl, br) = (self.boolish.contains(lhs), self.boolish.contains(rhs));
                let v = self.binop(*op, &a, &b, kl, kr, bl, br, true);
                let d = self.decl(*dst, Type::Bv64);
                if matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
                    // định nghĩa TỪNG PHẦN (kết quả chính xác chỉ nằm trong [0, 2^64) trên đường đi mà BV đã chứng minh không
                    // tràn): khẳng định toàn cục sẽ ép toán hạng ở MỌI nhánh (vd `a - b` ép a >= b cả ở nhánh a < b)
                    self.assume(&d._eq(&v));
                } else {
                    self.solver.assert(&d._eq(&v));
                }
                let m = self.m64();
                if let Some(&(gop, gl, gr)) = self.lowered.get(dst) {
                    // ngữ nghĩa gốc của *_sat / *_ovf (parser đã hạ thành phép bit)
                    let (x, y) = (self.get(gl)?, self.get(gr)?);
                    let sum = Int::add(ctx, &[&x, &y]);
                    let prod = Int::mul(ctx, &[&x, &y]);
                    let top = Int::sub(ctx, &[&m, &self.n(1)]);
                    let g = match gop {
                        BinOp::AddOvf => self.bool01(&sum.ge(&m)),
                        BinOp::SubOvf => self.bool01(&x.lt(&y)),
                        BinOp::MulOvf => self.bool01(&prod.ge(&m)),
                        BinOp::AddSat => sum.ge(&m).ite(&top, &sum),
                        BinOp::SubSat => x.ge(&y).ite(&Int::sub(ctx, &[&x, &y]), &self.n(0)),
                        _ => prod.ge(&m).ite(&top, &prod),
                    };
                    self.solver.assert(&d._eq(&g));
                    if matches!(gop, BinOp::AddOvf | BinOp::SubOvf | BinOp::MulOvf) {
                        self.boolish.insert(*dst);
                    }
                }
                if let (BinOp::Shl, Some(k)) = (op, kr) {
                    if k < 64 {
                        self.low_zero.insert(*dst, k as u32);
                    }
                }
                // ghép mảng bit rời: x là bội 2^k và y < 2^k -> x | y == x ^ y == x + y
                if matches!(op, BinOp::Or | BinOp::Xor) {
                    for (x, y, rx) in [(&a, &b, lhs), (&b, &a, rhs)] {
                        if let Some(&k) = self.low_zero.get(rx) {
                            let s = Int::add(ctx, &[x, y]);
                            self.solver.assert(&y.lt(&self.pow2(k)).implies(&d._eq(&s)));
                        }
                    }
                }
                if bl && br && matches!(op, BinOp::And | BinOp::Or | BinOp::Xor) {
                    self.boolish.insert(*dst);
                }
            }
            Inst::Cmp { dst, op, lhs, rhs } => {
                let (a, b) = (self.get(*lhs)?, self.get(*rhs)?);
                let c = self.cmpop(*op, &a, &b);
                let d = self.decl(*dst, Type::Bv8);
                self.solver.assert(&d._eq(&self.bool01(&c)));
                self.boolish.insert(*dst);
            }
            Inst::Slice { dst, base, idx: i, ty } => {
                let lay = match self.tys.get(base) {
                    Some(Type::Ptr { layout_id, .. } | Type::DPtr { layout_id, .. }) => *layout_id,
                    _ => return Err(format!("checker số nguyên: slice từ %{} không phải ptr", base)),
                };
                let size = self.module.layouts[lay as usize].size as u64;
                let v = Int::add(ctx, &[&self.get(*base)?, &Int::mul(ctx, &[&self.get(*i)?, &self.n(size)])]);
                let d = self.decl(*dst, *ty);
                self.assume(&d._eq(&v)); // từng phần (như add có kiểm)
                if ty.ptr_layout() == Some(lay) {
                    let iv = self.get(*i)?;
                    let entry = match self.slice_of.get(base) {
                        Some((root, i0)) => (root.clone(), Int::add(ctx, &[i0, &iv])),
                        None => (self.get(*base)?, iv),
                    };
                    self.slice_of.insert(*dst, entry);
                }
                if self.opaque.contains(base) {
                    self.opaque.insert(*dst);
                }
            }
            Inst::View { dst, src, ty } => {
                let s = self.get(*src)?;
                let d = self.decl(*dst, *ty);
                self.solver.assert(&d._eq(&s));
                if self.opaque.contains(src) {
                    self.opaque.insert(*dst);
                }
            }
            Inst::Narrow { dst, src, ty } => {
                let s = self.get(*src)?;
                let d = self.decl(*dst, *ty);
                self.assume(&d._eq(&s)); // từng phần: BV chứng minh giá trị vừa TRÊN đường đi này
            }
            Inst::Load { dst, ty, base, offset } => {
                let d = self.decl(*dst, *ty);
                if let (Some(l), false) = (self.ptr_layout_of(*base), self.opaque.contains(base)) {
                    let (addr, key, _) = self.addr_of(l, *base, *offset)?;
                    let v = self.heap[&key].select(&addr).as_int().unwrap();
                    self.solver.assert(&d._eq(&v));
                }
            }
            Inst::Store { base, offset, val } => match self.ptr_layout_of(*base) {
                Some(l) if !self.opaque.contains(base) => {
                    let (addr, key, _) = self.addr_of(l, *base, *offset)?;
                    let v = self.get(*val)?;
                    let h = self.heap[&key].store(&addr, &v);
                    let others: Vec<HKey> = self.heap.keys().filter(|k| k.0 != l).copied().collect();
                    self.fresh_heap(&others);
                    self.heap.insert(key, h);
                }
                _ => self.havoc_all(),
            },
            Inst::Call { dst, func_id, args } => {
                let callee = &self.module.funcs[*func_id as usize];
                let mut env = IEnv::new();
                for (&a, &(p, _)) in args.iter().zip(&callee.params) {
                    env.insert(p, self.get(a)?);
                }
                let ctys: HashMap<Reg, Type> = callee.params.iter().copied().collect();
                let saved_tys = self.spec_tys.replace(ctys);
                let saved_old = std::mem::replace(&mut self.old_heap, self.heap.clone());
                let r = (|| -> Result<(), String> {
                    for (i, req) in callee.requires.iter().enumerate() {
                        if self.mine(req) {
                            let g = self.ev_goal(req, &env)?;
                            self.check(&g, &format!("Vi phạm @req #{} khi gọi hàm '{}'", i, callee.name))?;
                        }
                    }
                    // hàm được gọi ghi được mọi heap trong tóm tắt của nó (chưa có khung theo vùng): old = trước lệnh gọi
                    let all_b: Vec<usize> = (0..callee.blocks.len()).collect();
                    let roots = write_roots(self.module, callee, &all_b, &mut vec![callee.name.clone()]);
                    match written_keys(self.module, callee, &reg_types(self.module, callee)) {
                        Some(w) => {
                            let w: Vec<HKey> = w.into_iter().collect();
                            let before = self.heap.clone();
                            self.fresh_heap(&w);
                            // khung theo vùng: hàm được gọi chỉ ghi trong vùng các tham số con trỏ gốc của lệnh ghi
                            if let Some(roots) = roots {
                                let mut regions = Vec::new();
                                let mut ok = true;
                                for r in roots {
                                    let val = |q: Reg| {
                                        let j = callee.params.iter().position(|(p, _)| *p == q)?;
                                        self.regs.get(args.get(j)?).cloned()
                                    };
                                    match self.region_of(callee, r, &val) {
                                        Some(g) => regions.push(g),
                                        None => ok = false,
                                    }
                                }
                                if ok {
                                    for k in &w {
                                        let (nh, oh) = (self.heap[k].clone(), before[k].clone());
                                        self.frame(*k, &nh, &oh, &regions);
                                    }
                                }
                            }
                        }
                        None => self.havoc_all(),
                    }
                    if let Some(d) = dst {
                        let rty = callee.ret_ty.unwrap_or(Type::Bv64);
                        let dv = self.decl(*d, rty);
                        if let Some(r) = result_reg(callee) {
                            env.insert(r, dv);
                            if let Some(t) = self.spec_tys.as_mut() {
                                t.insert(r, rty);
                            }
                        }
                    }
                    for ens in &callee.ensures {
                        let b = self.ev_bool(ens, &env)?;
                        self.assume(&b);
                    }
                    Ok(())
                })();
                self.spec_tys = saved_tys;
                self.old_heap = saved_old;
                r?;
            }
            Inst::Br { cond, then_bb, else_bb } => {
                let t = self.get(*cond)?._eq(&self.n(0)).not();
                for (target, extra) in [(*then_bb, t.clone()), (*else_bb, t.not())] {
                    let ti = idx[&target];
                    let env = self.regs.clone();
                    self.check_target_invs(ti, &env, Some(&extra))?;
                    let pc = self.cur_cond.as_ref().map_or_else(|| extra.clone(), |c| Bool::and(ctx, &[c, &extra]));
                    if self.pos[ti] > self.pos[bi] {
                        self.edge_heaps.entry(ti).or_default().push((Some(pc.clone()), self.heap.clone()));
                    }
                    self.add_pred(bi, ti, Some(pc));
                }
            }
            Inst::Jmp { target_bb, args } => {
                let ti = idx[target_bb];
                let tb = &self.func.blocks[ti];
                let mut env = self.regs.clone();
                for (&a, &(p, _)) in args.iter().zip(&tb.params) {
                    env.insert(p, self.get(a)?);
                }
                self.check_target_invs(ti, &env, None)?;
                if self.pos[ti] > self.pos[bi] && !tb.params.is_empty() {
                    let vals = tb.params.iter().map(|(p, _)| env[p].clone()).collect();
                    self.edge_args.entry(ti).or_default().push((self.cur_cond.clone(), vals));
                }
                if self.pos[ti] > self.pos[bi] {
                    self.edge_heaps.entry(ti).or_default().push((self.cur_cond.clone(), self.heap.clone()));
                }
                self.add_pred(bi, ti, self.cur_cond.clone());
            }
            Inst::Assume(e) => {
                let b = self.ev_bool(e, &self.regs.clone())?;
                self.assume(&b);
            }
            Inst::Assert(e) => {
                let b = self.ev_goal(e, &self.regs.clone())?;
                if self.mine(e) {
                    self.check(&b, "Vi phạm lệnh Assert")?;
                }
                self.assume(&b);
            }
            Inst::Ret { val } => {
                let mut env = self.regs.clone();
                if let (Some(rr), Some(r)) = (result_reg(self.func), val) {
                    env.insert(rr, self.get(*r)?);
                }
                for (i, ens) in self.func.ensures.iter().enumerate() {
                    if self.mine(ens) {
                        let g = self.ev_goal(ens, &env)?;
                        self.check(&g, &format!("Vi phạm điều kiện đầu ra (@ens #{}) của hàm '{}'", i, self.func.name))?;
                    }
                }
            }
            Inst::HwIo { dst: Some(d), port_or_reg: port, is_write: false, .. } => {
                self.havoc_all(); // syscall có thể ghi bộ đệm
                let x = self.decl(*d, Type::Bv64);
                if *port != 3 {
                    self.solver.assert(&x.le(&self.n(crate::verify::hwio_read_limit(*port))));
                }
            }
            // lệnh còn lại (phần cứng, SIMD, parallel, gọi gián tiếp, addr): khai báo đích với miền của kiểu; mọi lệnh có
            // thể ghi bộ nhớ xoá mọi heap
            other => {
                if !matches!(other, Inst::Addr { .. } | Inst::SmpWorkers { .. }) {
                    self.havoc_all();
                }
                if let Some(d) = other.dst() {
                    let ty = match other {
                        Inst::Addr { ty, .. } => *ty,
                        _ => Type::Bv64,
                    };
                    self.decl(d, ty);
                }
            }
        }
        Ok(())
    }
}

/// Tên giá trị trả về trong @ens (như verify.rs)
fn result_reg(func: &Func) -> Option<Reg> {
    let params: HashSet<Reg> = func.params.iter().map(|p| p.0).collect();
    let mut v = vec![];
    for e in &func.ensures {
        regs_of(e, &mut v);
    }
    v.into_iter().find(|r| !params.contains(r))
}

fn regs_of(e: &Z3Expr, out: &mut Vec<Reg>) {
    match e {
        Z3Expr::Reg(r) => out.push(*r),
        Z3Expr::Bin(_, l, r) | Z3Expr::Cmp(_, l, r) | Z3Expr::And(l, r) | Z3Expr::Or(l, r) | Z3Expr::Math(_, l, r) => {
            regs_of(l, out);
            regs_of(r, out);
        }
        Z3Expr::Not(x) | Z3Expr::Old(x) => regs_of(x, out),
        Z3Expr::Mem(p, i, _) => {
            out.push(*p);
            regs_of(i, out);
        }
        Z3Expr::Ite(c, a, b) => {
            for x in [c, a, b] {
                regs_of(x, out);
            }
        }
        Z3Expr::App(_, args) => {
            for x in args {
                regs_of(x, out);
            }
        }
        Z3Expr::Quant(_, v, lo, hi, body) => {
            let mut inner = vec![];
            for x in [lo, hi, body] {
                regs_of(x, &mut inner);
            }
            out.extend(inner.into_iter().filter(|r| r != v));
        }
        Z3Expr::Const(_) | Z3Expr::FieldVal => {}
    }
}

pub fn verify(module: &Module, func: &Func, all: bool) -> Result<(), String> {
    let cfg = crate::verify::build_cfg(func)?;
    let (cfg_idx, order, pos) = (cfg.idx, cfg.rpo, cfg.pos);
    let ctx = Context::new(&Config::new());
    let solver = Solver::new(&ctx);
    let mut params = Params::new(&ctx);
    params.set_u32("timeout", TIMEOUT_MS);
    if std::env::var_os("LIGHT_INT_NOMBQI").is_some() {
        params.set_bool("smt.mbqi", false);
    }
    solver.set_params(&params);
    let mut v = IV {
        ctx: &ctx,
        solver,
        module,
        func,
        all,
        regs: HashMap::new(),
        tys: HashMap::new(),
        consts: HashMap::new(),
        boolish: HashSet::new(),
        cur_cond: None,
        conds: HashMap::from([(order[0], None)]),
        pos,
        edge_args: HashMap::new(),
        cur_bb: 0,
        cur_inst: String::new(),
        cur_at: String::new(),
        fresh: 0,
        ufs: HashMap::new(),
        low_zero: HashMap::new(),
        lowered: func.lowered.iter().map(|&(d, op, l, r)| (d, (op, l, r))).collect(),
        heap0: HashMap::new(),
        heap: HashMap::new(),
        old_heap: HashMap::new(),
        written: HashSet::new(),
        edge_heaps: HashMap::new(),
        opaque: HashSet::new(),
        spec_tys: None,
        in_old: false,
        depth: 0,
        side: Vec::new(),
        spec_decls: HashMap::new(),
        spec_layer: HashMap::new(),
        in_spec_body: false,
        pat_frames: Vec::new(),
        slice_of: HashMap::new(),
        pol: false,
        want_range: false,
    };
    let keys: Vec<HKey> = heap_keys(module).into_iter().map(|(k, _)| k).collect();
    v.fresh_heap(&keys);
    v.heap0 = v.heap.clone();
    v.old_heap = v.heap.clone();
    let rtys = reg_types(module, func);
    v.written = match written_keys(module, func, &rtys) {
        Some(w) => w,
        None => keys.iter().copied().collect(),
    };
    for &(r, ty) in &func.params {
        v.decl(r, ty);
    }
    for req in &func.requires {
        let b = v.ev_bool(req, &v.regs.clone())?;
        v.solver.assert(&b);
    }
    if !v.feasible() {
        return Err(format!("[func '{}'] các @req mâu thuẫn nhau (checker số nguyên)", func.name));
    }
    let mut back_target = vec![false; func.blocks.len()];
    let succs: Vec<Vec<usize>> = func
        .blocks
        .iter()
        .map(|b| {
            b.insts
                .iter()
                .flat_map(|i| match i {
                    Inst::Br { then_bb, else_bb, .. } => vec![*then_bb, *else_bb],
                    Inst::Jmp { target_bb, .. } => vec![*target_bb],
                    _ => vec![],
                })
                .filter_map(|t| cfg_idx.get(&t).copied())
                .collect()
        })
        .collect();
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); func.blocks.len()];
    for (bi, ss) in succs.iter().enumerate() {
        for &t in ss {
            preds[t].push(bi);
        }
    }
    // vòng lặp tự nhiên của từng đầu vòng: đầu + mọi block tới được cạnh lùi mà không qua đầu (DFS ngược)
    let mut loop_blocks: HashMap<usize, HashSet<usize>> = HashMap::new();
    for (bi, ss) in succs.iter().enumerate() {
        for &ti in ss {
            if v.pos[ti] <= v.pos[bi] {
                back_target[ti] = true;
                let body = loop_blocks.entry(ti).or_insert_with(|| HashSet::from([ti]));
                let mut stack = vec![bi];
                while let Some(x) = stack.pop() {
                    if body.insert(x) {
                        stack.extend(preds[x].iter().copied());
                    }
                }
            }
        }
    }
    // heap thân vòng có thể ghi (đầu vòng: mảng mới chỉ cho chúng; heap khác giữ giá trị từ cạnh vào)
    #[allow(clippy::type_complexity)]
    let loop_written: HashMap<usize, (Vec<HKey>, Option<Vec<Reg>>)> = loop_blocks
        .iter()
        .map(|(&h, body)| {
            let bl: Vec<usize> = body.iter().copied().collect();
            let w = match written_blocks(module, func, &rtys, &mut vec![func.name.clone()], &bl) {
                Some(w) => w.into_iter().collect(),
                None => keys.clone(),
            };
            let roots = write_roots(module, func, &bl, &mut vec![func.name.clone()]).map(|r| r.into_iter().collect());
            (h, (w, roots))
        })
        .collect();
    for &bi in &order {
        let Some(c) = v.conds.get(&bi).cloned() else { continue };
        v.cur_cond = c;
        if !v.feasible() {
            continue;
        }
        let block = &func.blocks[bi];
        v.cur_bb = block.id;
        v.cur_inst = format!("@b{} entry", block.id);
        v.cur_at = block.label_at.clone();
        for &(r, ty) in &block.params {
            v.decl(r, ty);
        }
        // bộ nhớ ở đầu block
        if back_target[bi] {
            // giá trị heap không bị thân vòng ghi = giá trị trên cạnh vào (các cạnh tiến; nối như block thường)
            if let Some(edges) = v.edge_heaps.get(&bi).cloned() {
                if edges.len() == 1 {
                    v.heap = edges[0].1.clone();
                } else {
                    let w: Vec<HKey> = v.written.iter().copied().collect();
                    for k in w {
                        if edges.iter().all(|(_, h)| h[&k] == edges[0].1[&k]) {
                            v.heap.insert(k, edges[0].1[&k].clone());
                            continue;
                        }
                        v.fresh_heap(&[k]);
                        for (c, h) in &edges {
                            let eq = v.heap[&k]._eq(&h[&k]);
                            match c {
                                Some(c) => v.solver.assert(&c.implies(&eq)),
                                None => v.solver.assert(&eq),
                            }
                        }
                    }
                }
            }
            let (w, roots) = loop_written[&bi].clone();
            let before = v.heap.clone();
            v.fresh_heap(&w);
            // khung đầu vòng (luật Dafny): ngoài vùng các tham số con trỏ thân vòng ghi, heap == heap lúc vào vòng
            if let Some(roots) = roots {
                let val = |q: Reg| v.regs.get(&q).cloned();
                let regions: Option<Vec<_>> = roots.iter().map(|&r| v.region_of(func, r, &val)).collect();
                if let Some(regions) = regions {
                    for k in &w {
                        let (nh, oh) = (v.heap[k].clone(), before[k].clone());
                        v.frame(*k, &nh, &oh, &regions);
                    }
                }
            }
        } else if let Some(edges) = v.edge_heaps.get(&bi).cloned() {
            if edges.len() == 1 {
                v.heap = edges[0].1.clone();
            } else {
                let w: Vec<HKey> = v.written.iter().copied().collect();
                for k in w {
                    if edges.iter().all(|(_, h)| h[&k] == edges[0].1[&k]) {
                        v.heap.insert(k, edges[0].1[&k].clone());
                        continue;
                    }
                    v.fresh_heap(&[k]);
                    for (c, h) in &edges {
                        let eq = v.heap[&k]._eq(&h[&k]);
                        match c {
                            Some(c) => v.solver.assert(&c.implies(&eq)),
                            None => v.solver.assert(&eq),
                        }
                    }
                }
            }
        }
        if !block.params.is_empty() && !back_target[bi] {
            for (c, vals) in v.edge_args.get(&bi).cloned().unwrap_or_default() {
                let eqs: Vec<Bool> = block.params.iter().zip(&vals).map(|((p, _), a)| v.regs[p]._eq(a)).collect();
                let all_eq = Bool::and(&ctx, &eqs.iter().collect::<Vec<_>>());
                match c {
                    Some(c) => v.solver.assert(&c.implies(&all_eq)),
                    None => v.solver.assert(&all_eq),
                }
            }
        }
        for inv in &block.invs {
            let b = v.ev_bool(inv, &v.regs.clone())?;
            v.assume(&b);
        }
        // chống chứng minh rỗng: bất biến (đã giả định) không được mâu thuẫn với đường đi tới đầu vòng
        if !block.invs.is_empty() && !v.feasible() {
            return Err(format!(
                "[func '{}'] @inv của @b{} mâu thuẫn nhau / với đường đi tới nó (checker số nguyên){}",
                func.name,
                block.id,
                if block.label_at.is_empty() { String::new() } else { format!("\n    tại {}", block.label_at) }
            ));
        }
        for (k, inst) in block.insts.iter().enumerate() {
            v.cur_inst = format!("{:?}", inst).chars().take(80).collect();
            v.cur_at = block.at.get(k).cloned().unwrap_or_default();
            v.step(bi, inst, &cfg_idx)?;
        }
    }
    Ok(())
}

