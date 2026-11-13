// File: src/bin/oracle.rs — Oracle Interpreter & Soundness Fuzzer cho Light (.lit)
//
// Ý tưởng: Z3 nói "an toàn" -> ta chạy thật bằng số cụ thể; nếu một NGHĨA VỤ mà Z3 lẽ ra đã chứng minh
// lại bị vi phạm lúc chạy thì verifier có bug. Cách dùng:
//   cargo run --bin oracle -- lit_program/os/kernel.lit [--runs 2000] [--seed 1] [--func NAME]
//                             [--mode inline|contract|mixed] [--steps 100000] [--time 5] [-v]
//
// Phân biệt rất quan trọng (file oracle cũ lẫn lộn hai loại này):
//   * NGHĨA VỤ (obligation)  : Z3 phải chứng minh. Vi phạm trong hàm đã verify = SOUNDNESS BUG.
//        tràn số, chia 0, shift>=64, ra ngoài biên, @inv khi store/jmp/br, @req tại lời gọi, @ens, assert, kiểu...
//   * GIẢ ĐỊNH (assumption)  : Z3 được phép tin. Vi phạm = bỏ lượt chạy, KHÔNG phải bug.
//        @req ở đầu vào hàm đang test, assume, @inv của dữ liệu LOAD từ RAM, độ rộng giá trị hwio_r.
// Môi trường đối nghịch: RAM chưa khởi tạo, hwio_r, kết quả hàm (chế độ contract) là ngẫu nhiên nhưng luôn
// thoả các giả định ở trên — đúng bằng tập hành vi mà verifier phải bao phủ.
#![allow(dead_code)]

#[path = "../ir.rs"]
mod ir;
#[path = "../front.rs"]
mod front;
#[path = "../parser.rs"]
mod parser;
#[path = "../verify.rs"]
mod verify;
#[path = "../verify_int.rs"]
mod verify_int;

use ir::*;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::process;
use std::time::Instant;

// Dùng chung hằng số với verify.rs (trước đây oracle tự khai RAM_TOP = 2GB trong khi verifier là 1TB:
// ptr hợp lệ nằm trên 2GB bị oracle báo nhầm, và gen_args không bao giờ thử con trỏ ở vùng cao)
use verify::{RAM_MIN, RAM_TOP};
const ROOT_IO: Type = Type::Io {
    min: 0,
    max: 0xFFFF,
};

type Val = (u64, Type);
type Regs = HashMap<Reg, Val>;

// =============================================================================
// Kết quả chạy
// =============================================================================

struct Fail {
    func: String, // hàm nơi nghĩa vụ bị vi phạm (có thể là callee)
    block: BlockId,
    what: String,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum DKind {
    Req,    // @req đầu vào không thoả
    Assume, // lệnh assume sai
    Mem,    // dữ liệu RAM có sẵn vi phạm @inv (writer không tin cậy)
}
enum Stop {
    Fail(Fail),
    Discard(DKind, String),
    Fuel,
}
type R<T> = Result<T, Stop>;

// =============================================================================
// Tiện ích số học / kiểu
// =============================================================================

fn bytes_of(ty: Type) -> u64 {
    match ty {
        Type::Bv8 => 1,
        Type::Bv16 => 2,
        Type::Bv32 => 4,
        _ => 8,
    }
}
fn ty_max(ty: Type) -> u64 {
    match ty {
        Type::Bv8 => 0xFF,
        Type::Bv16 => 0xFFFF,
        Type::Bv32 => 0xFFFF_FFFF,
        _ => u64::MAX,
    }
}
fn is_int(ty: Type) -> bool {
    matches!(ty, Type::Bv8 | Type::Bv16 | Type::Bv32 | Type::Bv64)
}
fn can_delegate(from: Type, to: Type) -> bool {
    match (from, to) {
        (Type::Io { min: a, max: b }, Type::Io { min: c, max: d }) => a <= c && d <= b,
        (Type::Smp, Type::Smp) => true,
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
        _ => is_int(from) && is_int(to),
    }
}
/// Lúc chạy, độ dài của ptr<L,%n> là một số cụ thể: đổi thành ptr<L,giá_trị> để mọi kiểm tra tĩnh dùng lại được.
fn conc(ty: Type, regs: &Regs) -> Result<Type, String> {
    match ty {
        Type::DPtr { layout_id, len } => {
            let &(v, lt) = regs
                .get(&len)
                .ok_or_else(|| format!("độ dài %{} của ptr động chưa có giá trị", len))?;
            if !is_int(lt) {
                return Err(format!("độ dài %{} của ptr động không phải số nguyên", len));
            }
            Ok(Type::Ptr { layout_id, max_elems: v })
        }
        t => Ok(t),
    }
}

fn cmp(op: CmpOp, l: u64, r: u64) -> bool {
    match op {
        CmpOp::Eq => l == r,
        CmpOp::Ne => l != r,
        CmpOp::Ult => l < r,
        CmpOp::Ule => l <= r,
        CmpOp::Ugt => l > r,
        CmpOp::Uge => l >= r,
        CmpOp::Slt => (l as i64) < (r as i64),
        CmpOp::Sle => (l as i64) <= (r as i64),
        CmpOp::Sgt => (l as i64) > (r as i64),
        CmpOp::Sge => (l as i64) >= (r as i64),
    }
}

/// Ngữ nghĩa TOÀN PHẦN của bitvector Z3 (dùng trong biểu thức @req/@inv/@ens): không bao giờ lỗi.
fn bv_total(op: BinOp, l: u64, r: u64) -> u64 {
    match op {
        BinOp::Add | BinOp::AddWrap | BinOp::AddSat | BinOp::AddOvf => l.wrapping_add(r),
        BinOp::Sub | BinOp::SubWrap | BinOp::SubSat | BinOp::SubOvf => l.wrapping_sub(r),
        BinOp::Mul | BinOp::MulWrap | BinOp::MulSat | BinOp::MulOvf => l.wrapping_mul(r),
        BinOp::UDiv => {
            if r == 0 {
                u64::MAX
            } else {
                l / r
            }
        }
        BinOp::URem => {
            if r == 0 {
                l
            } else {
                l % r
            }
        }
        BinOp::SDiv => {
            if r == 0 {
                if (l as i64) >= 0 { u64::MAX } else { 1 }
            } else {
                (l as i64).wrapping_div(r as i64) as u64
            }
        }
        BinOp::SRem => {
            if r == 0 {
                l
            } else {
                (l as i64).wrapping_rem(r as i64) as u64
            }
        }
        BinOp::And => l & r,
        BinOp::Or => l | r,
        BinOp::Xor => l ^ r,
        BinOp::Shl => {
            if r >= 64 {
                0
            } else {
                l << r
            }
        }
        BinOp::LShr => {
            if r >= 64 {
                0
            } else {
                l >> r
            }
        }
        BinOp::AShr => {
            if r >= 64 {
                if (l as i64) < 0 { u64::MAX } else { 0 }
            } else {
                ((l as i64) >> r) as u64
            }
        }
        BinOp::FxMul => l.wrapping_mul(r) >> 16,
        BinOp::MulHi => ((l as u128 * r as u128) >> 64) as u64,
        BinOp::FxDiv => {
            if r == 0 {
                u64::MAX
            } else {
                (l << 16) / r
            }
        }
    }
}

/// Ngữ nghĩa của LỆNH SSA: mỗi trường hợp mà Z3 phải loại trừ sẽ trả về Err (nghĩa vụ bị vi phạm).
fn alu(op: BinOp, l: u64, r: u64) -> Result<u64, String> {
    match op {
        BinOp::Add => l
            .checked_add(r)
            .ok_or_else(|| format!("tràn số cộng {:#x} + {:#x}", l, r)),
        BinOp::Sub => l
            .checked_sub(r)
            .ok_or_else(|| format!("tràn số trừ {:#x} - {:#x}", l, r)),
        BinOp::Mul => l
            .checked_mul(r)
            .ok_or_else(|| format!("tràn số nhân {:#x} * {:#x}", l, r)),
        BinOp::FxMul => l
            .checked_mul(r)
            .map(|p| p >> 16)
            .ok_or_else(|| format!("tràn số fxmul {:#x} * {:#x}", l, r)),
        BinOp::FxDiv => {
            if r == 0 {
                Err("chia cho 0 trong fxdiv".into())
            } else if l >= (1u64 << 48) {
                Err(format!("tràn số bị chia fxdiv {:#x} >= 2^48", l))
            } else {
                Ok((l << 16) / r)
            }
        }
        BinOp::UDiv | BinOp::URem if r == 0 => Err("chia cho 0".into()),
        BinOp::SDiv | BinOp::SRem if r == 0 => Err("chia cho 0".into()),
        BinOp::SDiv | BinOp::SRem if l == 1u64 << 63 && r == u64::MAX => {
            Err("sdiv/srem INT_MIN / -1 (#DE)".into())
        }
        BinOp::Shl | BinOp::LShr | BinOp::AShr if r >= 64 => Err(format!("dịch bit {} >= 64", r)),
        _ => Ok(bv_total(op, l, r)),
    }
}

// =============================================================================
// Biểu thức Z3Expr
// =============================================================================

fn ev(e: &Z3Expr, regs: &Regs, fv: Option<u64>) -> Result<u64, String> {
    match e {
        Z3Expr::Reg(r) => regs
            .get(r)
            .map(|x| x.0)
            .ok_or_else(|| format!("%{} chưa khởi tạo", r)),
        Z3Expr::FieldVal => fv.ok_or_else(|| "dùng 'val' ngoài @inv".to_string()),
        Z3Expr::Const(c) => Ok(*c),
        Z3Expr::Bin(op, l, r) => Ok(bv_total(*op, ev(l, regs, fv)?, ev(r, regs, fv)?)),
        Z3Expr::And(l, r) => Ok(ev(l, regs, fv)? & ev(r, regs, fv)?),
        Z3Expr::Or(l, r) => Ok(ev(l, regs, fv)? | ev(r, regs, fv)?),
        Z3Expr::Not(x) => Ok(!ev(x, regs, fv)?),
        Z3Expr::Cmp(..) => Err("biểu thức so sánh dùng làm giá trị số".into()),
        Z3Expr::Math(..) => u64::try_from(evm(e, regs, fv)?).map_err(|_| "số toán học ngoài [0, 2^64)".to_string()),
        Z3Expr::Mem(..) | Z3Expr::Old(..) | Z3Expr::Quant(..) => Err("đặc tả bộ nhớ: oracle chưa hỗ trợ".into()),
    }
}

/// đặc tả nói về bộ nhớ / lượng từ (P3): oracle không tính được -> bỏ qua kiểm (requires ở đỉnh: bỏ đầu vào)
fn mem_spec(e: &Z3Expr) -> bool {
    match e {
        Z3Expr::Mem(..) | Z3Expr::Old(..) | Z3Expr::Quant(..) => true,
        Z3Expr::Bin(_, l, r) | Z3Expr::Cmp(_, l, r) | Z3Expr::And(l, r) | Z3Expr::Or(l, r) | Z3Expr::Math(_, l, r) => {
            mem_spec(l) || mem_spec(r)
        }
        Z3Expr::Not(x) => mem_spec(x),
        _ => false,
    }
}
/// số học toán học (i128 đủ cho đặc tả trên toán hạng 64 bit mức hiện tại)
fn evm(e: &Z3Expr, regs: &Regs, fv: Option<u64>) -> Result<i128, String> {
    match e {
        Z3Expr::Math(op, l, r) => {
            let (a, b) = (evm(l, regs, fv)?, evm(r, regs, fv)?);
            let ov = || "tràn i128 khi tính đặc tả".to_string();
            Ok(match op {
                MathOp::Add => a.checked_add(b).ok_or_else(ov)?,
                MathOp::Sub => a.checked_sub(b).ok_or_else(ov)?,
                MathOp::Mul => a.checked_mul(b).ok_or_else(ov)?,
                MathOp::Div if b != 0 => a.div_euclid(b),
                MathOp::Mod if b != 0 => a.rem_euclid(b),
                _ => return Err("idiv / imod cho 0".into()),
            })
        }
        _ => Ok(ev(e, regs, fv)? as i128),
    }
}
fn evb(e: &Z3Expr, regs: &Regs, fv: Option<u64>) -> Result<bool, String> {
    match e {
        e if mem_spec(e) => Ok(true),
        Z3Expr::Cmp(op, l, r) if l.has_math() || r.has_math() => {
            let (a, b) = (evm(l, regs, fv)?, evm(r, regs, fv)?);
            Ok(match op {
                CmpOp::Eq => a == b,
                CmpOp::Ne => a != b,
                CmpOp::Ult => a < b,
                CmpOp::Ule => a <= b,
                CmpOp::Ugt => a > b,
                CmpOp::Uge => a >= b,
                _ => return Err("so sánh có dấu trên số toán học".into()),
            })
        }
        Z3Expr::Cmp(op, l, r) => Ok(cmp(*op, ev(l, regs, fv)?, ev(r, regs, fv)?)),
        Z3Expr::And(l, r) => Ok(evb(l, regs, fv)? && evb(r, regs, fv)?),
        Z3Expr::Or(l, r) => Ok(evb(l, regs, fv)? || evb(r, regs, fv)?),
        Z3Expr::Not(x) => Ok(!evb(x, regs, fv)?),
        _ => Err("biểu thức đòi hỏi kiểu logic".into()),
    }
}

// =============================================================================
// Sinh số ngẫu nhiên có thiên vị về giá trị biên + rút cận từ @req/@inv
// =============================================================================

#[derive(Clone)]
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed)
    }
    fn next(&mut self) -> u64 {
        // splitmix64
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        if n == 0 { 0 } else { self.next() % n }
    }
    fn range(&mut self, lo: u64, hi: u64) -> u64 {
        if hi <= lo {
            return lo;
        }
        let span = hi - lo;
        if span == u64::MAX {
            self.next()
        } else {
            lo + self.next() % (span + 1)
        }
    }
}

/// Lấy mẫu trong [lo, hi], ưu tiên: biên, sát biên, giữa, 2^k, 2^k±1, đều.
fn sample(rng: &mut Rng, lo: u64, hi: u64) -> u64 {
    if lo >= hi {
        return lo;
    }
    // giá trị "đặc biệt" của số học nhị phân: 0, 1, -1, INT_MIN, INT_MAX, 2^32...
    if rng.below(8) == 0 {
        const SP: [u64; 9] = [
            0,
            1,
            u64::MAX,
            1 << 63,
            (1 << 63) - 1,
            u64::MAX - 1,
            1 << 32,
            0xFF,
            0x7F,
        ];
        let c = SP[rng.below(SP.len() as u64) as usize];
        if c >= lo && c <= hi {
            return c;
        }
    }
    match rng.below(10) {
        0 => lo,
        1 => hi,
        2 => (lo + 1).min(hi),
        3 => (hi - 1).max(lo),
        4 => lo + (hi - lo) / 2,
        5 | 6 => {
            let p = 1u64 << rng.below(64);
            let c = match rng.below(3) {
                0 => p,
                1 => p.wrapping_sub(1),
                _ => p.wrapping_add(1),
            };
            if c >= lo && c <= hi {
                c
            } else {
                rng.range(lo, hi)
            }
        }
        _ => rng.range(lo, hi),
    }
}

fn flip(op: CmpOp) -> Option<CmpOp> {
    Some(match op {
        CmpOp::Ult => CmpOp::Ugt,
        CmpOp::Ule => CmpOp::Uge,
        CmpOp::Ugt => CmpOp::Ult,
        CmpOp::Uge => CmpOp::Ule,
        CmpOp::Eq => CmpOp::Eq,
        _ => return None,
    })
}

/// Rút khoảng [lo, hi] cho `target` từ các mệnh đề đơn giản dạng (target <cmp> const) nối bằng And.
fn collect_bounds(e: &Z3Expr, is_t: &dyn Fn(&Z3Expr) -> bool, lo: &mut u64, hi: &mut u64) {
    match e {
        Z3Expr::And(l, r) => {
            collect_bounds(l, is_t, lo, hi);
            collect_bounds(r, is_t, lo, hi);
        }
        Z3Expr::Cmp(op, l, r) => {
            let (op, c) = match (&**l, &**r) {
                (t, Z3Expr::Const(c)) if is_t(t) => (Some(*op), *c),
                (Z3Expr::Const(c), t) if is_t(t) => (flip(*op), *c),
                _ => return,
            };
            match op {
                Some(CmpOp::Ult) => {
                    if c == 0 {
                        *lo = 1;
                        *hi = 0
                    } else {
                        *hi = (*hi).min(c - 1)
                    }
                }
                Some(CmpOp::Ule) => *hi = (*hi).min(c),
                Some(CmpOp::Ugt) => {
                    if c == u64::MAX {
                        *lo = 1;
                        *hi = 0
                    } else {
                        *lo = (*lo).max(c + 1)
                    }
                }
                Some(CmpOp::Uge) => *lo = (*lo).max(c),
                Some(CmpOp::Eq) => {
                    *lo = (*lo).max(c);
                    *hi = (*hi).min(c)
                }
                _ => {}
            }
        }
        _ => {}
    }
}

fn ret_reg(f: &Func) -> Option<Reg> {
    f.blocks
        .iter()
        .flat_map(|b| b.insts.iter())
        .find_map(|i| match i {
            Inst::Ret { val: Some(r) } => Some(*r),
            _ => None,
        })
}

// =============================================================================
// Máy ảo
// =============================================================================

#[derive(Clone, Copy, PartialEq, Eq)]
enum CallMode {
    Inline,   // chạy thật thân callee
    Contract, // chỉ tin @ens của callee (mô phỏng đúng lý luận mô-đun của verifier)
    Mixed,    // mỗi lời gọi chọn ngẫu nhiên
}

/// Địa chỉ mô phỏng của dữ liệu tĩnh thứ k (vùng riêng gần đỉnh RAM mô hình)
fn data_addr(m: &Module, k: usize) -> u64 {
    let mut a = RAM_TOP / 2;
    for d in &m.datas[..k] {
        a += (d.bytes.len() as u64 + 15) & !15;
    }
    a
}

struct Vm<'a> {
    m: &'a Module,
    ram: BTreeMap<u64, u8>,
    env: Rng, // phi tất định của môi trường
    steps: u64,
    max_steps: u64,
    seq_jmp: bool, // true = mô phỏng mã máy elf64.rs: gán tham số jmp TUẦN TỰ
    mode: CallMode,
    mem_mode: u8, // cách khởi tạo RAM lười: 0 ngẫu nhiên, 1 cận dưới, 2 cận trên, 3 ngẫu nhiên nhỏ
    cov: HashSet<(usize, BlockId)>,
    depth: usize,
    trace: u64, // hash trạng thái mỗi lần vào block (để so sánh cả khi hết fuel)
}

impl<'a> Vm<'a> {
    fn new(
        m: &'a Module,
        env_seed: u64,
        max_steps: u64,
        seq_jmp: bool,
        mode: CallMode,
        mem_mode: u8,
    ) -> Self {
        let mut ram = BTreeMap::new();
        for (k, d) in m.datas.iter().enumerate() {
            for (i, &b) in d.bytes.iter().enumerate() {
                ram.insert(data_addr(m, k) + i as u64, b);
            }
        }
        Vm {
            m,
            ram,
            env: Rng::new(env_seed),
            steps: 0,
            max_steps,
            seq_jmp,
            mode,
            mem_mode,
            cov: HashSet::new(),
            depth: 0,
            trace: 0,
        }
    }

    fn write(&mut self, addr: u64, n: u64, val: u64) {
        let b = val.to_le_bytes();
        for i in 0..n {
            self.ram.insert(addr + i, b[i as usize]);
        }
    }

    /// Bất biến của kiểu: số nguyên hẹp vừa khít, ptr nằm trọn trong RAM.
    fn ty_inv(&self, ty: Type, v: u64) -> Result<(), String> {
        match ty {
            Type::Bv8 | Type::Bv16 | Type::Bv32 => {
                if v > ty_max(ty) {
                    Err(format!("giá trị {:#x} không vừa kiểu {:?}", v, ty))
                } else {
                    Ok(())
                }
            }
            Type::Ptr {
                layout_id,
                max_elems,
            } => {
                let l = &self.m.layouts[layout_id as usize];
                let bytes = max_elems.saturating_mul(l.size as u64);
                if v < RAM_MIN || v.checked_add(bytes).map_or(true, |e| e > RAM_TOP) {
                    Err(format!(
                        "con trỏ {:#x} (+{} byte) ra ngoài RAM [{:#x},{:#x})",
                        v, bytes, RAM_MIN, RAM_TOP
                    ))
                } else {
                    Ok(())
                }
            }
            _ => Ok(()),
        }
    }

    fn set_reg(&self, regs: &mut Regs, r: Reg, v: u64, ty: Type) -> Result<(), String> {
        self.ty_inv(ty, v)?;
        regs.insert(r, (v, ty));
        Ok(())
    }

    fn assign(&self, from: Type, to: Type, v: u64) -> Result<(), String> {
        if !can_delegate(from, to) {
            return Err(format!(
                "không thể dùng {:?} làm {:?} (giả mạo capability / sai kiểu)",
                from, to
            ));
        }
        self.ty_inv(to, v)
    }

    fn ptr_field(&self, regs: &Regs, base: Reg, off: u32) -> Result<(u64, &'a FieldDef), String> {
        let m: &'a Module = self.m;
        let (addr, ty) = regs
            .get(&base)
            .copied()
            .ok_or_else(|| format!("%{} chưa khởi tạo", base))?;
        let (lid, me) = match ty {
            Type::Ptr {
                layout_id,
                max_elems,
            } => (layout_id as usize, max_elems),
            _ => return Err(format!("%{} không phải Ptr", base)),
        };
        let l = &m.layouts[lid];
        let max_bytes = me.saturating_mul(l.size as u64);
        if (off as u64) >= max_bytes {
            return Err(format!("offset {} vượt vùng {} byte", off, max_bytes));
        }
        let fo = off % l.size;
        let f = l
            .fields
            .iter()
            .find(|f| f.offset == fo)
            .ok_or_else(|| format!("truy cập sai lệch offset {} trong '{}'", fo, l.name))?;
        Ok((addr + off as u64, f))
    }

    /// LOAD: byte chưa từng ghi được sinh ngẫu nhiên nhưng THOẢ @inv (giả định mà verifier dùng).
    fn load(&mut self, addr: u64, ty: Type, inv: Option<&Z3Expr>) -> R<u64> {
        let n = bytes_of(ty);
        let mut cur = [0u8; 8];
        let mut present = 0;
        for i in 0..n {
            if let Some(&b) = self.ram.get(&(addr + i)) {
                cur[i as usize] = b;
                present += 1;
            }
        }
        let ok_inv = |v: u64| inv.map_or(true, |e| evb(e, &HashMap::new(), Some(v)) == Ok(true));
        let val = if present == n {
            u64::from_le_bytes(cur)
        } else {
            let (mut lo, mut hi) = (0u64, ty_max(ty));
            if let Some(e) = inv {
                collect_bounds(e, &|x| matches!(x, Z3Expr::FieldVal), &mut lo, &mut hi);
            }
            let mut got = None;
            for t in 0..64 {
                let c = if t == 0 {
                    match self.mem_mode {
                        1 => lo,
                        2 => hi,
                        3 => sample(&mut self.env, lo, hi.min(lo.saturating_add(16))),
                        _ => sample(&mut self.env, lo, hi),
                    }
                } else {
                    sample(&mut self.env, lo, hi)
                };
                let cb = c.to_le_bytes();
                let mut b = cur;
                for i in 0..n as usize {
                    if !self.ram.contains_key(&(addr + i as u64)) {
                        b[i] = cb[i];
                    }
                }
                let v = u64::from_le_bytes(b);
                if ok_inv(v) {
                    got = Some(v);
                    break;
                }
            }
            let v = got.ok_or_else(|| {
                Stop::Discard(DKind::Mem, "không sinh được giá trị thoả @inv".into())
            })?;
            self.write(addr, n, v);
            v
        };
        if !ok_inv(val) {
            return Err(Stop::Discard(
                DKind::Mem,
                format!("RAM chứa {:#x} vi phạm @inv của trường", val),
            ));
        }
        Ok(val)
    }

    fn exec(&mut self, fi: usize, args: &[Val], top: bool) -> R<Option<Val>> {
        if self.depth > 100 {
            return Err(Stop::Fuel);
        }
        self.depth += 1;
        let func: &'a Func = &self.m.funcs[fi];
        let r = self.exec_inner(fi, func, args, top);
        self.depth -= 1;
        r
    }

    fn exec_inner(&mut self, fi: usize, func: &'a Func, args: &[Val], top: bool) -> R<Option<Val>> {
        let m: &'a Module = self.m;
        let bad = |b: BlockId, w: String| {
            Stop::Fail(Fail {
                func: func.name.clone(),
                block: b,
                what: w,
            })
        };
        let get = |regs: &Regs, r: Reg, b: BlockId| -> R<Val> {
            regs.get(&r).copied().ok_or_else(|| {
                bad(
                    b,
                    format!("dùng %{} chưa khởi tạo (verifier lẽ ra phải chặn)", r),
                )
            })
        };

        let entry = func
            .blocks
            .first()
            .map(|b| b.id)
            .ok_or_else(|| bad(0, "hàm không có block".into()))?;
        if args.len() != func.params.len() {
            return Err(bad(entry, "sai số lượng tham số".into()));
        }
        let mut regs: Regs = HashMap::new();
        for (&(p, pty), &(v, _)) in func.params.iter().zip(args) {
            let t = conc(pty, &regs).map_err(|w| bad(entry, w))?;
            self.set_reg(&mut regs, p, v, t)
                .map_err(|w| bad(entry, w))?;
        }
        if top {
            for (i, req) in func.requires.iter().enumerate() {
                if mem_spec(req) {
                    return Err(Stop::Discard(DKind::Req, format!("@req #{} (bộ nhớ: oracle chưa hỗ trợ)", i)));
                }
                match evb(req, &regs, None) {
                    Ok(true) => {}
                    Ok(false) => return Err(Stop::Discard(DKind::Req, format!("@req #{}", i))),
                    Err(e) => return Err(bad(entry, e)),
                }
            }
        }

        let has_root = func.params.iter().any(|&(_, t)| t == ROOT_IO);
        let mut cur = entry;
        loop {
            let blk = func
                .blocks
                .iter()
                .find(|b| b.id == cur)
                .ok_or_else(|| bad(cur, format!("không có @b{}", cur)))?;
            self.cov.insert((fi, cur));
            {
                let mut ks: Vec<_> = regs.iter().collect();
                ks.sort_by_key(|(k, _)| **k);
                let mut h = self.trace ^ (cur as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
                for (k, v) in ks {
                    h = (h ^ (*k as u64) ^ v.0.rotate_left(17)).wrapping_mul(0x100_0000_01B3);
                }
                self.trace = h;
            }
            self.steps += 1;
            if self.steps > self.max_steps {
                return Err(Stop::Fuel);
            }
            for (i, inv) in blk.invs.iter().enumerate() {
                match evb(inv, &regs, None) {
                    Ok(true) => {}
                    Ok(false) => {
                        return Err(bad(cur, format!("vi phạm @inv #{} khi vào @b{}", i, cur)));
                    }
                    Err(e) => return Err(bad(cur, e)),
                }
            }

            let mut next: Option<BlockId> = None;
            for inst in &blk.insts {
                self.steps += 1;
                if self.steps > self.max_steps {
                    return Err(Stop::Fuel);
                }
                match inst {
                    Inst::Const { dst, ty, val } => {
                        match ty {
                            Type::Io { .. } => {
                                return Err(bad(cur, "tạo thẻ Io bằng const".into()));
                            }
                            Type::Smp if !has_root || *val != 0x7e000 => {
                                return Err(bad(cur, "tạo thẻ smp sai (cần thẻ gốc và địa chỉ 0x7e000)".into()));
                            }
                            Type::Ptr { .. } if !has_root => {
                                return Err(bad(
                                    cur,
                                    "const ptr mà hàm không giữ thẻ gốc io<0,0xffff>".into(),
                                ));
                            }
                            _ => {}
                        }
                        self.set_reg(&mut regs, *dst, *val, *ty)
                            .map_err(|w| bad(cur, w))?;
                    }
                    Inst::Bin { dst, op, lhs, rhs } => {
                        let (l, _) = get(&regs, *lhs, cur)?;
                        let (r, _) = get(&regs, *rhs, cur)?;
                        let v = alu(*op, l, r).map_err(|w| bad(cur, format!("%{}: {}", dst, w)))?;
                        self.set_reg(&mut regs, *dst, v, Type::Bv64)
                            .map_err(|w| bad(cur, w))?;
                    }
                    Inst::Narrow { dst, src, ty } => {
                        let (v, sty) = get(&regs, *src, cur)?;
                        if !matches!(sty, Type::Bv8 | Type::Bv16 | Type::Bv32 | Type::Bv64) {
                            return Err(bad(cur, "narrow trên biến không phải số nguyên".into()));
                        }
                        let lim = match ty {
                            Type::Bv8 => 0xFF,
                            Type::Bv16 => 0xFFFF,
                            Type::Bv32 => 0xFFFF_FFFF,
                            _ => return Err(bad(cur, "narrow: kiểu đích sai".into())),
                        };
                        if v > lim {
                            return Err(bad(cur, format!("narrow %{}: {:#x} không vừa", dst, v)));
                        }
                        self.set_reg(&mut regs, *dst, v, *ty).map_err(|w| bad(cur, w))?;
                    }
                    Inst::Cmp { dst, op, lhs, rhs } => {
                        let (l, _) = get(&regs, *lhs, cur)?;
                        let (r, _) = get(&regs, *rhs, cur)?;
                        self.set_reg(&mut regs, *dst, cmp(*op, l, r) as u64, Type::Bv8)
                            .map_err(|w| bad(cur, w))?;
                    }
                    Inst::Slice { dst, base, idx, ty } => {
                        let (ba, bt) = get(&regs, *base, cur)?;
                        let (iv, _) = get(&regs, *idx, cur)?;
                        let (l1, m_old) = match bt {
                            Type::Ptr {
                                layout_id,
                                max_elems,
                            } => (layout_id, max_elems),
                            _ => return Err(bad(cur, "slice trên biến không phải Ptr".into())),
                        };
                        let cty = conc(*ty, &regs).map_err(|w| bad(cur, w))?;
                        let dyn_ok = matches!(ty, Type::DPtr { .. });
                        let (l2, m_new) = match cty {
                            Type::Ptr {
                                layout_id,
                                max_elems,
                            } if layout_id == l1 && (max_elems > 0 || dyn_ok) => (layout_id, max_elems),
                            _ => return Err(bad(cur, "slice sai kiểu đích".into())),
                        };
                        let end = iv
                            .checked_add(m_new)
                            .ok_or_else(|| bad(cur, format!("slice %{}: tràn cộng index", dst)))?;
                        if end > m_old {
                            return Err(bad(
                                cur,
                                format!("slice %{}: idx {} + {} vượt {}", dst, iv, m_new, m_old),
                            ));
                        }
                        let sz = m.layouts[l2 as usize].size as u64;
                        let addr = ba + iv * sz;
                        self.set_reg(&mut regs, *dst, addr, cty)
                            .map_err(|w| bad(cur, format!("slice %{}: {}", dst, w)))?;
                    }
                    Inst::Addr { dst, data_id, ty } => {
                        self.set_reg(&mut regs, *dst, data_addr(m, *data_id as usize), *ty)
                            .map_err(|w| bad(cur, w))?;
                    }
                    Inst::View { dst, src, ty } => {
                        let (ba, bt) = get(&regs, *src, cur)?;
                        let Type::Ptr { layout_id: l1, max_elems: m_old } = bt else {
                            return Err(bad(cur, "view trên biến không phải Ptr".into()));
                        };
                        let cty = conc(*ty, &regs).map_err(|w| bad(cur, w))?;
                        let Type::Ptr { layout_id: l2, max_elems: m_new } = cty else {
                            return Err(bad(cur, "view sai kiểu đích".into()));
                        };
                        if [l1, l2].iter().any(|&l| m.layouts[l as usize].fields.iter().any(|f| f.inv.is_some())) {
                            return Err(bad(cur, "view trên Layout có @inv".into()));
                        }
                        let b_old = m_old.checked_mul(m.layouts[l1 as usize].size as u64);
                        let b_new = m_new.checked_mul(m.layouts[l2 as usize].size as u64);
                        if b_old.zip(b_new).is_none_or(|(o, n)| n > o) {
                            return Err(bad(cur, format!("view %{}: vùng đích lớn hơn nguồn", dst)));
                        }
                        self.set_reg(&mut regs, *dst, ba, cty)
                            .map_err(|w| bad(cur, format!("view %{}: {}", dst, w)))?;
                    }
                    Inst::Load {
                        dst,
                        ty,
                        base,
                        offset,
                    } => {
                        let (addr, field) = self
                            .ptr_field(&regs, *base, *offset)
                            .map_err(|w| bad(cur, w))?;
                        if field.ty != *ty {
                            return Err(bad(
                                cur,
                                format!(
                                    "load %{} lệch kiểu: trường {:?} vs lệnh {:?}",
                                    dst, field.ty, ty
                                ),
                            ));
                        }
                        let v = self.load(addr, *ty, field.inv.as_ref())?;
                        self.set_reg(&mut regs, *dst, v, *ty)
                            .map_err(|w| bad(cur, w))?;
                    }
                    Inst::Store { base, offset, val } => {
                        let (addr, field) = self
                            .ptr_field(&regs, *base, *offset)
                            .map_err(|w| bad(cur, w))?;
                        let (v, vty) = get(&regs, *val, cur)?;
                        if vty != field.ty {
                            return Err(bad(
                                cur,
                                format!(
                                    "store ghi {} byte ({:?}) vào trường {:?} ({} byte): mã máy ghi đè lân cận",
                                    bytes_of(vty),
                                    vty,
                                    field.ty,
                                    bytes_of(field.ty)
                                ),
                            ));
                        }
                        if let Some(inv) = &field.inv {
                            if evb(inv, &HashMap::new(), Some(v)) != Ok(true) {
                                return Err(bad(
                                    cur,
                                    format!("store {:#x} vào offset {} vi phạm @inv", v, offset),
                                ));
                            }
                        }
                        self.write(addr, bytes_of(vty), v);
                    }
                    Inst::Simd256 { op, dst, lhs, rhs } => {
                        let (la, _) = get(&regs, *lhs, cur)?;
                        let (ra, _) = get(&regs, *rhs, cur)?;
                        if *op == SimdOp::Dot {
                            let mut sum = 0u64;
                            for lane in 0..4u64 {
                                let lv = self.load(la + lane * 8, Type::Bv64, None)? & 0xFFFF_FFFF;
                                let rv = self.load(ra + lane * 8, Type::Bv64, None)? & 0xFFFF_FFFF;
                                sum = sum.wrapping_add(lv.wrapping_mul(rv));
                            }
                            self.set_reg(&mut regs, *dst, sum, Type::Bv64)
                                .map_err(|w| bad(cur, w))?;
                        } else {
                            let (da, _) = get(&regs, *dst, cur)?;
                            let mut out = [0u64; 4];
                            for lane in 0..4usize {
                                let lv = self.load(la + (lane as u64) * 8, Type::Bv64, None)?;
                                let rv = self.load(ra + (lane as u64) * 8, Type::Bv64, None)?;
                                out[lane] = match op {
                                    SimdOp::Add => lv.wrapping_add(rv),
                                    SimdOp::Sub => lv.wrapping_sub(rv),
                                    SimdOp::Mul => (lv & 0xFFFF_FFFF).wrapping_mul(rv & 0xFFFF_FFFF),
                                    _ => lv ^ rv,
                                };
                            }
                            for lane in 0..4usize {
                                self.write(da + (lane as u64) * 8, 8, out[lane]);
                            }
                        }
                    }
                    Inst::Parallel { smp, n, func_id, base, arg } => {
                        // Ngữ nghĩa tham chiếu: chạy tuần tự worker(base + i*K*size, arg, i) cho i = 0..n-1.
                        // Nghĩa vụ: thẻ smp, 1 <= n <= 16, n*K <= M, @req của worker với từng i.
                        let (_, sty) = get(&regs, *smp, cur)?;
                        if sty != Type::Smp {
                            return Err(bad(cur, "parallel: không phải thẻ smp".into()));
                        }
                        let (nv, _) = get(&regs, *n, cur)?;
                        let (bv, bty) = get(&regs, *base, cur)?;
                        let (av, _) = get(&regs, *arg, cur)?;
                        let w = &m.funcs[*func_id as usize];
                        let (Type::Ptr { max_elems: mb, .. }, Some(&(p0, pty @ Type::Ptr { layout_id, max_elems: k }))) =
                            (bty, w.params.first())
                        else {
                            return Err(bad(cur, "parallel: sai kiểu".into()));
                        };
                        if !(1..=16).contains(&nv) {
                            return Err(bad(cur, format!("parallel: n = {} ngoài [1..16]", nv)));
                        }
                        if nv * k > mb {
                            return Err(bad(cur, format!("parallel: {} phần x {} > {}", nv, k, mb)));
                        }
                        let sz = m.layouts[layout_id as usize].size as u64;
                        for i in 0..nv {
                            let part = (bv + i * k * sz, pty);
                            let vals = vec![part, (av, Type::Bv64), (i, Type::Bv64)];
                            let mut cregs: Regs = HashMap::new();
                            for (&(p, t), &(v, _)) in w.params.iter().zip(&vals) {
                                cregs.insert(p, (v, t));
                            }
                            let _ = p0;
                            for (q, req) in w.requires.iter().enumerate() {
                                if evb(req, &cregs, None) != Ok(true) {
                                    return Err(bad(cur, format!("parallel: vi phạm @req #{} của '{}' tại phần {}", q, w.name, i)));
                                }
                            }
                            self.exec(*func_id as usize, &vals, false)?;
                        }
                    }
                    Inst::SmpWorkers { dst, smp } => {
                        let (_, sty) = get(&regs, *smp, cur)?;
                        if sty != Type::Smp {
                            return Err(bad(cur, "smp_workers: không phải thẻ smp".into()));
                        }
                        let v = sample(&mut self.env, 0, 15);
                        self.set_reg(&mut regs, *dst, v, Type::Bv64).map_err(|w| bad(cur, w))?;
                    }
                    Inst::AtaRead { cap, .. } => {
                        let _ = get(&regs, *cap, cur)?; // oracle: bỏ qua tác dụng phụ phần cứng
                    }
                    Inst::HwIo {
                        dst,
                        cap,
                        port_or_reg,
                        val,
                        is_write,
                    } => {
                        let port = *port_or_reg;
                        let (_, cty) = get(&regs, *cap, cur)?;
                        match cty {
                            Type::Io { min, max } if port >= min && port <= max => {
                                if port == 3 && (min, max) != (0, 0xFFFF) {
                                    return Err(bad(
                                        cur,
                                        "cổng 3 (CR3) mà không có thẻ gốc".into(),
                                    ));
                                }
                            }
                            _ => {
                                return Err(bad(
                                    cur,
                                    format!("vi phạm thẻ I/O tại cổng {:#x}", port),
                                ));
                            }
                        }
                        if *is_write {
                            let (v, vty) = get(&regs, val.unwrap_or(0), cur)?;
                            if port != 3 {
                                let lim = if vty == Type::Bv32 {
                                    0xFFFF_FFFF
                                } else if port == 0x1F0 || vty == Type::Bv16 {
                                    0xFFFF
                                } else {
                                    0xFF
                                };
                                let wide = lim > 0xFF;
                                if v > lim {
                                    return Err(bad(
                                        cur,
                                        format!(
                                            "hwio_w cổng {:#x}: giá trị {:#x} không vừa {} bit",
                                            port,
                                            v,
                                            if lim > 0xFFFF { 32 } else if wide { 16 } else { 8 }
                                        ),
                                    ));
                                }
                            }
                        } else if let Some(d) = dst {
                            let lim = if port == 3 {
                                u64::MAX
                            } else {
                                verify::hwio_read_limit(port)
                            };
                            let v = sample(&mut self.env, 0, lim);
                            self.set_reg(&mut regs, *d, v, Type::Bv64)
                                .map_err(|w| bad(cur, w))?;
                        }
                    }
                    Inst::Call {
                        dst,
                        func_id,
                        args: ca,
                    } => {
                        let ci = *func_id as usize;
                        let callee = m
                            .funcs
                            .get(ci)
                            .ok_or_else(|| bad(cur, "func_id sai".into()))?;
                        if ca.len() != callee.params.len() {
                            return Err(bad(cur, format!("gọi '{}' sai số tham số", callee.name)));
                        }
                        let mut vals: Vec<Val> = Vec::new();
                        let mut cregs: Regs = HashMap::new();
                        for (&a, &(p, pty)) in ca.iter().zip(&callee.params) {
                            let (v, aty) = get(&regs, a, cur)?;
                            let pty = conc(pty, &cregs).map_err(|w| bad(cur, w))?;
                            self.assign(aty, pty, v).map_err(|w| {
                                bad(cur, format!("đối số %{} của '{}': {}", a, callee.name, w))
                            })?;
                            vals.push((v, pty));
                            cregs.insert(p, (v, pty));
                        }
                        for (i, req) in callee.requires.iter().enumerate() {
                            match evb(req, &cregs, None) {
                                Ok(true) => {}
                                Ok(false) => {
                                    return Err(bad(
                                        cur,
                                        format!("vi phạm @req #{} khi gọi '{}'", i, callee.name),
                                    ));
                                }
                                Err(e) => return Err(bad(cur, e)),
                            }
                        }
                        let use_contract = match self.mode {
                            CallMode::Inline => false,
                            CallMode::Contract => true,
                            CallMode::Mixed => self.env.below(2) == 0,
                        };
                        let mut ret: Option<Val> = None;
                        let mut done = false;
                        if use_contract {
                            match callee.ret_ty {
                                None => done = true, // hàm void: hiệu ứng bộ nhớ bị trừu tượng hoá
                                Some(rty) if is_int(rty) => {
                                    let rr = ret_reg(callee);
                                    let (mut lo, mut hi) = (0u64, ty_max(rty));
                                    if let Some(r) = rr {
                                        for e in &callee.ensures {
                                            collect_bounds(
                                                e,
                                                &|x| matches!(x, Z3Expr::Reg(q) if *q == r),
                                                &mut lo,
                                                &mut hi,
                                            );
                                        }
                                    }
                                    for _ in 0..200 {
                                        let v = sample(&mut self.env, lo, hi);
                                        let mut e2 = cregs.clone();
                                        if let Some(r) = rr {
                                            e2.insert(r, (v, rty));
                                        }
                                        if callee
                                            .ensures
                                            .iter()
                                            .all(|e| evb(e, &e2, None) == Ok(true))
                                        {
                                            ret = Some((v, rty));
                                            done = true;
                                            break;
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                        if !done {
                            ret = self.exec(ci, &vals, false)?;
                        }
                        if let Some(d) = dst {
                            match ret {
                                Some((v, t)) => {
                                    self.set_reg(&mut regs, *d, v, t).map_err(|w| bad(cur, w))?
                                }
                                None => {
                                    return Err(bad(
                                        cur,
                                        format!("gán kết quả của hàm void '{}'", callee.name),
                                    ));
                                }
                            }
                        }
                    }
                    Inst::CallPtr {
                        dst,
                        target,
                        args: ca,
                    } => {
                        if !has_root {
                            return Err(bad(cur, "CallPtr mà hàm không giữ thẻ gốc".into()));
                        }
                        let (_, tty) = get(&regs, *target, cur)?;
                        if !matches!(tty, Type::Ptr { .. }) {
                            return Err(bad(cur, "CallPtr tới giá trị không phải ptr".into()));
                        }
                        for &a in ca {
                            get(&regs, a, cur)?;
                        }
                        if let Some(d) = dst {
                            let v = self.env.next();
                            self.set_reg(&mut regs, *d, v, Type::Bv64)
                                .map_err(|w| bad(cur, w))?;
                        }
                    }
                    Inst::Br {
                        cond,
                        then_bb,
                        else_bb,
                    } => {
                        let (c, _) = get(&regs, *cond, cur)?;
                        let t = if c != 0 { *then_bb } else { *else_bb };
                        let tb = func
                            .blocks
                            .iter()
                            .find(|b| b.id == t)
                            .ok_or_else(|| bad(cur, "br tới block không tồn tại".into()))?;
                        if !tb.params.is_empty() {
                            return Err(bad(cur, "br tới block có tham số".into()));
                        }
                        next = Some(t);
                        break;
                    }
                    Inst::Jmp {
                        target_bb,
                        args: ja,
                    } => {
                        let tb = func
                            .blocks
                            .iter()
                            .find(|b| b.id == *target_bb)
                            .ok_or_else(|| bad(cur, "jmp tới block không tồn tại".into()))?;
                        if ja.len() != tb.params.len() {
                            return Err(bad(cur, "jmp sai số tham số".into()));
                        }
                        if self.seq_jmp {
                            // mã máy elf64.rs: đọc arg rồi ghi param NGAY, lần lượt
                            for (&a, &(p, pty)) in ja.iter().zip(&tb.params) {
                                let (v, aty) = get(&regs, a, cur)?;
                                let pty = conc(pty, &regs).map_err(|w| bad(cur, w))?;
                                self.assign(aty, pty, v)
                                    .map_err(|w| bad(cur, format!("tham số %{}: {}", p, w)))?;
                                self.set_reg(&mut regs, p, v, pty)
                                    .map_err(|w| bad(cur, w))?;
                            }
                        } else {
                            let mut tmp: Vec<(Reg, u64, Type)> = Vec::new();
                            let mut tenv = regs.clone();
                            for (&a, &(p, pty)) in ja.iter().zip(&tb.params) {
                                let (v, aty) = get(&regs, a, cur)?;
                                let pty = conc(pty, &tenv).map_err(|w| bad(cur, w))?;
                                self.assign(aty, pty, v)
                                    .map_err(|w| bad(cur, format!("tham số %{}: {}", p, w)))?;
                                tenv.insert(p, (v, pty));
                                tmp.push((p, v, pty));
                            }
                            for (p, v, pty) in tmp {
                                self.set_reg(&mut regs, p, v, pty)
                                    .map_err(|w| bad(cur, w))?;
                            }
                        }
                        next = Some(*target_bb);
                        break;
                    }
                    Inst::Assume(e) => match evb(e, &regs, None) {
                        Ok(true) => {}
                        Ok(false) => return Err(Stop::Discard(DKind::Assume, "assume sai".into())),
                        Err(w) => return Err(bad(cur, w)),
                    },
                    Inst::Assert(e) => match evb(e, &regs, None) {
                        Ok(true) => {}
                        Ok(false) => return Err(bad(cur, "assert sai".into())),
                        Err(w) => return Err(bad(cur, w)),
                    },
                    Inst::Ret { val } => {
                        if val.is_some() != func.ret_ty.is_some() {
                            return Err(bad(cur, "ret sai kiểu ret_ty".into()));
                        }
                        let out = if let (Some(r), Some(rt)) = (val, func.ret_ty) {
                            let (v, t) = get(&regs, *r, cur)?;
                            let rt = conc(rt, &regs).map_err(|w| bad(cur, w))?;
                            self.assign(t, rt, v)
                                .map_err(|w| bad(cur, format!("giá trị trả về: {}", w)))?;
                            Some((v, rt))
                        } else {
                            None
                        };
                        for (i, ens) in func.ensures.iter().enumerate() {
                            match evb(ens, &regs, None) {
                                Ok(true) => {}
                                Ok(false) => return Err(bad(cur, format!("vi phạm @ens #{}", i))),
                                Err(w) => return Err(bad(cur, w)),
                            }
                        }
                        return Ok(out);
                    }
                }
            }
            match next {
                Some(n) => cur = n,
                None => return Err(bad(cur, "block hết lệnh mà không có br/jmp/ret".into())),
            }
        }
    }
}

// =============================================================================
// Sinh đầu vào cho hàm đang test (theo @req)
// =============================================================================

fn gen_args(m: &Module, f: &Func, rng: &mut Rng, small: bool) -> Option<Vec<Val>> {
    const SP: [u64; 9] = [
        0,
        1,
        u64::MAX,
        1 << 63,
        (1 << 63) - 1,
        u64::MAX - 1,
        1 << 32,
        0xFF,
        0x7F,
    ];
    let special = rng.below(4) == 0; // 1/4 số lượt: MỌI tham số số nguyên cùng lấy giá trị đặc biệt
    for _ in 0..40 {
        let mut next = RAM_MIN + 0x10_0000 + 0x1000 * rng.below(256);
        let mut args: Vec<Val> = Vec::new();
        let mut ok = true;
        for &(p, ty) in &f.params {
            let sofar: Regs = f.params.iter().map(|&(q, _)| q).zip(args.iter().copied()).collect();
            let ty = match conc(ty, &sofar) {
                Ok(t) => t,
                Err(_) => {
                    ok = false;
                    break;
                }
            };
            let v = match ty {
                Type::Ptr {
                    layout_id,
                    max_elems,
                } => {
                    let bytes = max_elems.saturating_mul(m.layouts[layout_id as usize].size as u64);
                    // 1/8 số con trỏ đặt sát đỉnh RAM (nơi phép cộng địa chỉ dễ vượt biên nhất)
                    if bytes < RAM_TOP - RAM_MIN && rng.below(8) == 0 {
                        let hi = (RAM_TOP - bytes - 0x1000 * rng.below(16)) & !0xFFF;
                        if hi >= RAM_MIN {
                            args.push((hi, ty));
                            continue;
                        }
                    }
                    let base = (next + 0xFFF) & !0xFFF;
                    if base
                        .checked_add(bytes)
                        .map_or(true, |e| e + 0x1000 > RAM_TOP)
                    {
                        ok = false;
                        0
                    } else {
                        next = base + bytes + 0x1000 * (1 + rng.below(4));
                        base
                    }
                }
                Type::Io { .. } => 0,
                Type::Smp => 0x7e000,
                _ => {
                    let (mut lo, mut hi) = (0u64, ty_max(ty));
                    for r in &f.requires {
                        collect_bounds(
                            r,
                            &|x| matches!(x, Z3Expr::Reg(q) if *q == p),
                            &mut lo,
                            &mut hi,
                        );
                    }
                    if small {
                        hi = hi.min(lo.saturating_add(64));
                    }
                    let c = SP[rng.below(SP.len() as u64) as usize] & ty_max(ty);
                    if special && c >= lo && c <= hi && !small {
                        c
                    } else {
                        sample(rng, lo, hi)
                    }
                }
            };
            args.push((v, ty));
        }
        if !ok {
            continue;
        }
        let regs: Regs = f
            .params
            .iter()
            .map(|&(p, _)| p)
            .zip(args.iter().copied())
            .collect();
        if f.requires.iter().all(|r| evb(r, &regs, None) == Ok(true)) {
            return Some(args);
        }
    }
    None
}

fn show_args(f: &Func, args: &[Val]) -> String {
    f.params
        .iter()
        .zip(args)
        .map(|(&(p, _), &(v, t))| match t {
            Type::Ptr { .. } => format!("%{}=ptr@{:#x}", p, v),
            Type::Io { .. } => format!("%{}=io", p),
            Type::Smp => format!("%{}=smp", p),
            _ => format!("%{}={:#x}", p, v),
        })
        .collect::<Vec<_>>()
        .join(" ")
}

// =============================================================================
// Chương trình chính
// =============================================================================

#[derive(Default)]
struct Stats {
    ok: u64,
    d_req: u64,
    d_assume: u64,
    d_mem: u64,
    fuel: u64,
    trapped: u64, // hàm CHƯA verify mà trap (đúng như kỳ vọng, chỉ để thông tin)
    unsat_req: u64,
    bugs: u64,
    mismatch: u64,
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let (mut path, mut runs, mut seed, mut only) = (None, 2000u64, 0xC0FFEEu64, None::<String>);
    let (mut steps, mut budget, mut mode, mut verbose) =
        (100_000u64, 5.0f64, CallMode::Mixed, false);
    let mut i = 1;
    while i < a.len() {
        let next = |i: usize| a.get(i + 1).cloned().unwrap_or_default();
        match a[i].as_str() {
            "--runs" => {
                runs = next(i).parse().unwrap_or(runs);
                i += 1
            }
            "--seed" => {
                seed = next(i).parse().unwrap_or(seed);
                i += 1
            }
            "--func" => {
                only = Some(next(i));
                i += 1
            }
            "--steps" => {
                steps = next(i).parse().unwrap_or(steps);
                i += 1
            }
            "--time" => {
                budget = next(i).parse().unwrap_or(budget);
                i += 1
            }
            "--mode" => {
                mode = match next(i).as_str() {
                    "inline" => CallMode::Inline,
                    "contract" => CallMode::Contract,
                    _ => CallMode::Mixed,
                };
                i += 1
            }
            "-v" => verbose = true,
            s => path = Some(s.to_string()),
        }
        i += 1;
    }
    let path = path.unwrap_or_else(|| {
        eprintln!("Cách dùng: oracle <file.lit> [--runs N] [--seed S] [--func NAME] [--mode inline|contract|mixed] [--steps N] [--time SEC] [-v]");
        process::exit(2)
    });
    let m = parser::parse_file(&path).unwrap_or_else(|e| {
        eprintln!("Lỗi parse: {}", e);
        process::exit(2)
    });
    if let Err(e) = verify::check_module(&m) {
        eprintln!("check_module thất bại (oracle cần module hợp lệ): {}", e);
        process::exit(2);
    }
    let verified: Vec<bool> = m
        .funcs
        .iter()
        .map(|f| verify::verify_func(&m, f).is_ok())
        .collect();
    println!(
        "🔍 Oracle trên '{}': {} hàm ({} qua Z3), {} lượt/hàm, seed {}",
        path,
        m.funcs.len(),
        verified.iter().filter(|&&v| v).count(),
        runs,
        seed
    );
    println!(
        "  {:<26} {:<5} {:>6} {:>9} {:>5} {:>7} {:>8}",
        "hàm", "Z3", "ok", "bỏ(r/a/m)", "fuel", "trap*", "cover"
    );

    let mut cov: HashSet<(usize, BlockId)> = HashSet::new();
    let (mut total_bugs, mut total_mismatch) = (0u64, 0u64);

    for (fi, func) in m.funcs.iter().enumerate() {
        if only.as_ref().map_or(false, |n| n != &func.name) {
            continue;
        }
        let mut rng = Rng::new(seed ^ (fi as u64).wrapping_mul(0x9E37_79B9));
        let mut st = Stats::default();
        let t0 = Instant::now();
        let mut shown = 0;

        for run in 0..runs {
            if t0.elapsed().as_secs_f64() > budget {
                break;
            }
            let small = rng.below(2) == 0;
            let Some(args) = gen_args(&m, func, &mut rng, small) else {
                st.unsat_req += 1;
                continue;
            };
            let env_seed = rng.next();
            let mem_mode = rng.below(4) as u8;

            let mut ideal = Vm::new(&m, env_seed, steps, false, mode, mem_mode);
            let r1 = ideal.exec(fi, &args, true);
            cov.extend(ideal.cov.iter().copied());

            match &r1 {
                Err(Stop::Discard(k, _)) => {
                    match k {
                        DKind::Req => st.d_req += 1,
                        DKind::Assume => st.d_assume += 1,
                        DKind::Mem => st.d_mem += 1,
                    }
                    continue;
                }
                Err(Stop::Fuel) => {
                    st.fuel += 1;
                    if verified[fi] {
                        let mut mach = Vm::new(&m, env_seed, steps, true, mode, mem_mode);
                        let r2 = mach.exec(fi, &args, true);
                        if !matches!(r2, Err(Stop::Fuel)) || mach.trace != ideal.trace {
                            st.mismatch += 1;
                            if shown < 3 {
                                shown += 1;
                                eprintln!(
                                    "\n⚠️  [CODEGEN MISMATCH] '{}': vết thực thi SSA ≠ mã máy (gán jmp tuần tự)\n   đầu vào: {}\n   tái hiện: --seed {} --func {} (lượt #{})",
                                    func.name,
                                    show_args(func, &args),
                                    seed,
                                    func.name,
                                    run
                                );
                            }
                        }
                    }
                    continue;
                }
                Err(Stop::Fail(f)) => {
                    let blamed_ok = m
                        .funcs
                        .iter()
                        .position(|g| g.name == f.func)
                        .map_or(false, |gi| verified[gi]);
                    if blamed_ok {
                        st.bugs += 1;
                        if shown < 3 {
                            shown += 1;
                            eprintln!(
                                "\n❌ [SOUNDNESS BUG] '{}' đã qua Z3 nhưng chạy thật vi phạm nghĩa vụ:\n   tại hàm '{}' @b{}: {}\n   đầu vào: {}\n   tái hiện: --seed {} --func {} (lượt #{}, mode={})",
                                func.name,
                                f.func,
                                f.block,
                                f.what,
                                show_args(func, &args),
                                seed,
                                func.name,
                                run,
                                match mode {
                                    CallMode::Inline => "inline",
                                    CallMode::Contract => "contract",
                                    CallMode::Mixed => "mixed",
                                }
                            );
                        }
                    } else {
                        st.trapped += 1;
                        if verbose && shown < 2 {
                            shown += 1;
                            println!("      (hàm '{}' chưa qua Z3, trap: {})", f.func, f.what);
                        }
                    }
                    continue;
                }
                Ok(_) => {}
            }

            // Vi phân với ngữ nghĩa mã máy (gán jmp tuần tự). Với hàm đã verify, hai bên phải y hệt nhau.
            let mut mach = Vm::new(&m, env_seed, steps, true, mode, mem_mode);
            let r2 = mach.exec(fi, &args, true);
            let same = match (&r1, &r2) {
                (Ok(x), Ok(y)) => x == y && ideal.ram == mach.ram && ideal.trace == mach.trace,
                _ => false,
            };
            if same {
                st.ok += 1;
            } else if verified[fi] {
                st.mismatch += 1;
                if shown < 3 {
                    shown += 1;
                    eprintln!(
                        "\n⚠️  [CODEGEN MISMATCH] '{}': ngữ nghĩa SSA ≠ ngữ nghĩa mã máy (gán jmp tuần tự)\n   đầu vào: {}\n   tái hiện: --seed {} --func {} (lượt #{})",
                        func.name,
                        show_args(func, &args),
                        seed,
                        func.name,
                        run
                    );
                }
            } else {
                st.ok += 1;
            }
        }

        let total_blocks = func.blocks.len();
        let covered = func
            .blocks
            .iter()
            .filter(|b| cov.contains(&(fi, b.id)))
            .count();
        println!(
            "  {:<26} {:<5} {:>6} {:>9} {:>5} {:>7} {:>5}/{:<3}{}",
            func.name,
            if verified[fi] { "PASS" } else { "FAIL" },
            st.ok,
            format!("{}/{}/{}", st.d_req + st.unsat_req, st.d_assume, st.d_mem),
            st.fuel,
            st.trapped,
            covered,
            total_blocks,
            if st.bugs > 0 {
                "  ❌ BUG"
            } else if st.mismatch > 0 {
                "  ⚠️ MISMATCH"
            } else {
                ""
            }
        );
        total_bugs += st.bugs;
        total_mismatch += st.mismatch;
    }

    // Báo cáo block chưa được chạm tới (để biết fuzz còn mù ở đâu)
    let mut blind: Vec<String> = Vec::new();
    for (fi, f) in m.funcs.iter().enumerate() {
        if only.as_ref().map_or(false, |n| n != &f.name) {
            continue;
        }
        let un: Vec<String> = f
            .blocks
            .iter()
            .filter(|b| !cov.contains(&(fi, b.id)))
            .map(|b| format!("@b{}", b.id))
            .collect();
        if !un.is_empty() && un.len() < f.blocks.len() {
            blind.push(format!(
                "    {}: {}",
                f.name,
                un.iter().take(10).cloned().collect::<Vec<_>>().join(" ")
            ));
        }
    }
    if verbose && !blind.is_empty() {
        println!("\n  Block chưa chạy tới:\n{}", blind.join("\n"));
    }
    println!(
        "\n  (trap* = hàm CHƯA qua Z3 mà trap thật; bỏ(r/a/m) = bỏ lượt do @req / assume / dữ liệu RAM vi phạm @inv)"
    );
    if total_bugs + total_mismatch > 0 {
        eprintln!(
            "\n❌ Phát hiện {} soundness bug, {} codegen mismatch.",
            total_bugs, total_mismatch
        );
        process::exit(1);
    }
    println!("✅ Không thấy vi phạm nghĩa vụ nào trong các hàm đã qua Z3.");
}
