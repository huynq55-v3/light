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
    match written_keys(module, func, &reg_types(module, func)) {
        Some(w) => {
            let mut v: Vec<HKey> = w.into_iter().collect();
            v.sort();
            format!("{:?}", v)
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
    let mut w = HashSet::new();
    let has_const_ptr = func.blocks.iter().flat_map(|b| &b.insts).any(|i| matches!(i, Inst::Const { ty, .. } if ty.ptr_layout().is_some()));
    for i in func.blocks.iter().flat_map(|b| &b.insts) {
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
                        self.fact(pos.implies(&Bool::and(ctx, &[&bq.le(a), &a.lt(&Int::add(ctx, &[&bq, b]))])));
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
                self.fact(Bool::and(ctx, &[&v.le(a), &v.le(b)]));
                v
            }
            BinOp::Or | BinOp::Xor => {
                let v = self.uf(if op == BinOp::Or { "or" } else { "xor" }, a, b);
                self.fact(v.le(&sum)); // a | b <= a + b, a ^ b <= a + b
                if op == BinOp::Or {
                    self.fact(Bool::and(ctx, &[&v.ge(a), &v.ge(b)]));
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
                let v = h[&key].select(&addr).as_int().unwrap();
                let r = self.range(&v, bits);
                self.fact(r);
                v
            }
            Z3Expr::Old(x) => {
                let prev = std::mem::replace(&mut self.in_old, true);
                let v = self.ev_int(x, env);
                self.in_old = prev;
                v?
            }
            Z3Expr::Math(op, l, r) => {
                let (a, b) = (self.ev_int(l, env)?, self.ev_int(r, env)?);
                match op {
                    MathOp::Add => Int::add(self.ctx, &[&a, &b]),
                    MathOp::Sub => Int::sub(self.ctx, &[&a, &b]),
                    MathOp::Mul => Int::mul(self.ctx, &[&a, &b]),
                    MathOp::Div | MathOp::Mod => {
                        // chia Euclid; số chia là hằng dương -> thương mới (tuyến tính), còn lại `div`/`mod` của Z3
                        let q = match k(r) {
                            Some(c) if c > 0 => self.divc(&a, &self.n(c)),
                            _ => a.div(&b),
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
            Z3Expr::Not(x) => self.ev_bool(x, env)?.not(),
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
                let b = self.ev_bool(body, &env2);
                self.depth -= 1;
                let b = b?;
                let mut hyp: Vec<Bool> = vec![lo.le(&j), j.lt(&hi)];
                hyp.extend(self.side.drain(mark..));
                let hyp = Bool::and(self.ctx, &hyp.iter().collect::<Vec<_>>());
                if *all {
                    z3::ast::forall_const(self.ctx, &[&j], &[], &hyp.implies(&b))
                } else {
                    z3::ast::exists_const(self.ctx, &[&j], &[], &Bool::and(self.ctx, &[&hyp, &b]))
                }
            }
            _ => return Err("biểu thức đòi hỏi kiểu logic (Cmp/And/Or/Not/forall/exists)".into()),
        })
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
        let mut a = Int::add(self.ctx, &[p, &self.n(((off / size) * size) as u64)]);
        if let Some(i) = idx {
            a = Int::add(self.ctx, &[&a, &Int::mul(self.ctx, &[i, &self.n(size as u64)])]);
        }
        Ok((a, (l, off % size), int_bits(f.ty)))
    }
    fn fresh_heap(&mut self, keys: &[HKey]) {
        for k in keys {
            self.fresh += 1;
            let a = Array::new_const(self.ctx, format!("H{}_{}!{}", k.0, k.1, self.fresh), &Sort::int(self.ctx), &Sort::int(self.ctx));
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

    fn feasible(&self) -> bool {
        self.solver.push();
        if let Some(c) = &self.cur_cond {
            self.solver.assert(c);
        }
        let r = self.solver.check();
        self.solver.pop(1);
        !matches!(r, SatResult::Unsat)
    }

    fn check(&self, goal: &Bool<'ctx>, msg: &str) -> Result<(), String> {
        self.solver.push();
        if let Some(c) = &self.cur_cond {
            self.solver.assert(c);
        }
        self.solver.assert(&goal.not());
        let at = if self.cur_at.is_empty() { String::new() } else { format!("\n    tại {}", self.cur_at) };
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
                "[Z3 TIMEOUT] func {} @b{}: '{}' -> Không chứng minh được (checker số nguyên không kết luận — thường do nhân / \
                 chia phi tuyến): {}{}",
                self.func.name, self.cur_bb, self.cur_inst, msg, at
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
            let g = self.ev_bool(inv, env)?;
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
                    let (addr, key, _) = self.elem(l, &self.get(*base)?, None, *offset)?;
                    let v = self.heap[&key].select(&addr).as_int().unwrap();
                    self.solver.assert(&d._eq(&v));
                }
            }
            Inst::Store { base, offset, val } => match self.ptr_layout_of(*base) {
                Some(l) if !self.opaque.contains(base) => {
                    let (addr, key, _) = self.elem(l, &self.get(*base)?, None, *offset)?;
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
                            let g = self.ev_bool(req, &env)?;
                            self.check(&g, &format!("Vi phạm @req #{} khi gọi hàm '{}'", i, callee.name))?;
                        }
                    }
                    // hàm được gọi ghi được mọi heap trong tóm tắt của nó (chưa có khung theo vùng): old = trước lệnh gọi
                    match written_keys(self.module, callee, &reg_types(self.module, callee)) {
                        Some(w) => {
                            let w: Vec<HKey> = w.into_iter().collect();
                            self.fresh_heap(&w)
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
                let b = self.ev_bool(e, &self.regs.clone())?;
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
                        let g = self.ev_bool(ens, &env)?;
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
        Z3Expr::Quant(_, v, lo, hi, body) => {
            let mut inner = vec![];
            for x in [lo, hi, body] {
                regs_of(x, &mut inner);
            }
            out.extend(inner.into_iter().filter(|r| r != v));
        }
        Z3Expr::Reg(_) | Z3Expr::Const(_) | Z3Expr::FieldVal => {}
    }
}

pub fn verify(module: &Module, func: &Func, all: bool) -> Result<(), String> {
    let cfg = crate::verify::build_cfg(func)?;
    let (cfg_idx, order, pos) = (cfg.idx, cfg.rpo, cfg.pos);
    let ctx = Context::new(&Config::new());
    let solver = Solver::new(&ctx);
    let mut params = Params::new(&ctx);
    params.set_u32("timeout", TIMEOUT_MS);
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
    for (bi, b) in func.blocks.iter().enumerate() {
        for t in b.insts.iter().flat_map(|i| match i {
            Inst::Br { then_bb, else_bb, .. } => vec![*then_bb, *else_bb],
            Inst::Jmp { target_bb, .. } => vec![*target_bb],
            _ => vec![],
        }) {
            if let Some(&ti) = cfg_idx.get(&t) {
                if v.pos[ti] <= v.pos[bi] {
                    back_target[ti] = true;
                }
            }
        }
    }
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
            let w: Vec<HKey> = v.written.iter().copied().collect();
            v.fresh_heap(&w);
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

