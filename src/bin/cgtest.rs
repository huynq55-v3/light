// File: src/bin/cgtest.rs — Test vi sai cho bộ sinh mã x86-64 (elf64.rs)
//
// Biên dịch các file .lit trong tests/lit/codegen/, nạp mã máy vào vùng nhớ thực thi được của tiến trình host rồi
// gọi trực tiếp từng hàm `t_*` với đầu vào ngẫu nhiên, đối chiếu kết quả + nội dung bộ nhớ với một trình thông dịch
// tham chiếu nhỏ (chỉ tập lệnh thuần tính toán: const/bin/cmp/slice/load/store/narrow/br/jmp/call/ret).
// Lượt chạy có hành vi mà verifier sẽ cấm (chia 0, shift >= 64, ra ngoài buffer) bị bỏ qua.
//
//   cargo run --release --bin cgtest [-- --runs 3000] [--bench]
#![allow(dead_code)]

#[path = "../elf64.rs"]
mod elf64;
#[path = "../ir.rs"]
mod ir;
#[path = "../parser.rs"]
mod parser;
#[path = "../x86.rs"]
mod x86;

use ir::*;
use std::collections::HashMap;
use std::time::Instant;

unsafe extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut u8;
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    /// Giá trị "thú vị": nhỏ, biên, lũy thừa 2, ngẫu nhiên
    fn val(&mut self) -> u64 {
        match self.next() % 8 {
            0 => self.next() % 8,
            1 => self.next() % 300,
            2 => u64::MAX - self.next() % 4,
            3 => 1u64 << (self.next() % 64),
            4 => (1u64 << 63) + self.next() % 3,
            5 => self.next() & 0xffff_ffff,
            _ => self.next(),
        }
    }
}

/// Vùng nhớ hợp lệ của một lượt chạy: [start, end)
type Bufs = Vec<(u64, u64)>;

enum Stop {
    Skip(String),
    Bad(String),
}

fn width(t: Type) -> u32 {
    match t {
        Type::Bv8 => 1,
        Type::Bv16 => 2,
        Type::Bv32 => 4,
        _ => 8,
    }
}

fn reg_types(m: &Module, f: &Func) -> HashMap<Reg, Type> {
    let mut t: HashMap<Reg, Type> = f.params.iter().cloned().collect();
    for b in &f.blocks {
        t.extend(b.params.iter().cloned());
        for i in &b.insts {
            match i {
                Inst::Const { dst, ty, .. } | Inst::Load { dst, ty, .. } | Inst::Narrow { dst, ty, .. } | Inst::Slice { dst, ty, .. } => {
                    t.insert(*dst, *ty);
                }
                Inst::Cmp { dst, .. } => {
                    t.insert(*dst, Type::Bv8);
                }
                Inst::Bin { dst, .. } => {
                    t.insert(*dst, Type::Bv64);
                }
                Inst::Call { dst: Some(d), func_id, .. } => {
                    t.insert(*d, m.funcs[*func_id as usize].ret_ty.unwrap_or(Type::Bv64));
                }
                _ => {}
            }
        }
    }
    t
}

fn interp(m: &Module, fid: usize, args: &[u64], bufs: &Bufs, fuel: &mut u64, depth: u32) -> Result<u64, Stop> {
    let f = &m.funcs[fid];
    let tys = reg_types(m, f);
    let mut r: HashMap<Reg, u64> = HashMap::new();
    for (i, &(p, _)) in f.params.iter().enumerate() {
        r.insert(p, args[i]);
    }
    let get = |r: &HashMap<Reg, u64>, x: Reg| r.get(&x).copied().ok_or_else(|| Stop::Bad(format!("%{} chưa định nghĩa", x)));
    let chk = |a: u64, n: u64| -> Result<(), Stop> {
        if bufs.iter().any(|&(s, e)| a >= s && a.checked_add(n).is_some_and(|x| x <= e)) {
            Ok(())
        } else {
            Err(Stop::Skip(format!("truy cập ngoài buffer 0x{:x}", a)))
        }
    };
    let mut bi = 0usize;
    loop {
        let b = &f.blocks[bi];
        let mut next: Option<(u32, Vec<u64>)> = None;
        for inst in &b.insts {
            *fuel = fuel.checked_sub(1).ok_or(Stop::Skip("hết fuel".into()))?;
            match inst {
                Inst::Const { dst, val, .. } => {
                    r.insert(*dst, *val);
                }
                Inst::Bin { dst, op, lhs, rhs } => {
                    let (a, c) = (get(&r, *lhs)?, get(&r, *rhs)?);
                    let v = match op {
                        BinOp::Add | BinOp::AddWrap | BinOp::AddSat | BinOp::AddOvf => a.wrapping_add(c),
                        BinOp::Sub | BinOp::SubWrap | BinOp::SubSat | BinOp::SubOvf => a.wrapping_sub(c),
                        BinOp::Mul | BinOp::MulWrap | BinOp::MulSat | BinOp::MulOvf => a.wrapping_mul(c),
                        BinOp::And => a & c,
                        BinOp::Or => a | c,
                        BinOp::Xor => a ^ c,
                        BinOp::Shl | BinOp::LShr | BinOp::AShr if c >= 64 => return Err(Stop::Skip("shift".into())),
                        BinOp::Shl => a << c,
                        BinOp::LShr => a >> c,
                        BinOp::AShr => ((a as i64) >> c) as u64,
                        _ if c == 0 => return Err(Stop::Skip("chia 0".into())),
                        BinOp::UDiv => a / c,
                        BinOp::URem => a % c,
                        BinOp::SDiv | BinOp::SRem if a == 1 << 63 && c == u64::MAX => return Err(Stop::Skip("sdiv tràn".into())),
                        BinOp::SDiv => ((a as i64) / (c as i64)) as u64,
                        BinOp::SRem => ((a as i64) % (c as i64)) as u64,
                        BinOp::FxMul => a.wrapping_mul(c) >> 16,
                        BinOp::FxDiv => {
                            if (a << 16) >> 16 != a {
                                return Err(Stop::Skip("fxdiv tràn".into()));
                            }
                            (a << 16) / c
                        }
                    };
                    r.insert(*dst, v);
                }
                Inst::Cmp { dst, op, lhs, rhs } => {
                    let (a, c) = (get(&r, *lhs)?, get(&r, *rhs)?);
                    let (sa, sc) = (a as i64, c as i64);
                    let v = match op {
                        CmpOp::Eq => a == c,
                        CmpOp::Ne => a != c,
                        CmpOp::Ult => a < c,
                        CmpOp::Ule => a <= c,
                        CmpOp::Ugt => a > c,
                        CmpOp::Uge => a >= c,
                        CmpOp::Slt => sa < sc,
                        CmpOp::Sle => sa <= sc,
                        CmpOp::Sgt => sa > sc,
                        CmpOp::Sge => sa >= sc,
                    };
                    r.insert(*dst, v as u64);
                }
                Inst::Slice { dst, base, idx, ty } => {
                    let sz = m.layouts[ty.ptr_layout().unwrap() as usize].size as u64;
                    let v = get(&r, *base)?.wrapping_add(get(&r, *idx)?.wrapping_mul(sz));
                    r.insert(*dst, v);
                }
                Inst::Narrow { dst, src, .. } => {
                    r.insert(*dst, get(&r, *src)?);
                }
                Inst::Load { dst, ty, base, offset } => {
                    let a = get(&r, *base)?.wrapping_add(*offset as u64);
                    let w = width(*ty);
                    chk(a, w as u64)?;
                    let v = unsafe {
                        match w {
                            1 => *(a as *const u8) as u64,
                            2 => (a as *const u16).read_unaligned() as u64,
                            4 => (a as *const u32).read_unaligned() as u64,
                            _ => (a as *const u64).read_unaligned(),
                        }
                    };
                    r.insert(*dst, v);
                }
                Inst::Store { base, offset, val } => {
                    let a = get(&r, *base)?.wrapping_add(*offset as u64);
                    let v = get(&r, *val)?;
                    let w = width(*tys.get(val).unwrap_or(&Type::Bv64));
                    chk(a, w as u64)?;
                    unsafe {
                        match w {
                            1 => *(a as *mut u8) = v as u8,
                            2 => (a as *mut u16).write_unaligned(v as u16),
                            4 => (a as *mut u32).write_unaligned(v as u32),
                            _ => (a as *mut u64).write_unaligned(v),
                        }
                    }
                }
                Inst::Call { dst, func_id, args } => {
                    if depth > 64 {
                        return Err(Stop::Skip("đệ quy sâu".into()));
                    }
                    let a: Vec<u64> = args.iter().map(|&x| get(&r, x)).collect::<Result<_, _>>()?;
                    let v = interp(m, *func_id as usize, &a, bufs, fuel, depth + 1)?;
                    if let Some(d) = dst {
                        r.insert(*d, v);
                    }
                }
                Inst::Br { cond, then_bb, else_bb } => {
                    next = Some((if get(&r, *cond)? != 0 { *then_bb } else { *else_bb }, vec![]));
                    break;
                }
                Inst::Jmp { target_bb, args } => {
                    let a: Vec<u64> = args.iter().map(|&x| get(&r, x)).collect::<Result<_, _>>()?;
                    next = Some((*target_bb, a));
                    break;
                }
                Inst::Ret { val } => {
                    return match val {
                        Some(v) => get(&r, *v),
                        None => Ok(0),
                    };
                }
                Inst::Assume(_) | Inst::Assert(_) => {}
                other => return Err(Stop::Bad(format!("interp không hỗ trợ {:?}", other))),
            }
        }
        let (tb, a) = next.ok_or_else(|| Stop::Bad("block không kết thúc".into()))?;
        bi = f.blocks.iter().position(|x| x.id == tb).ok_or_else(|| Stop::Bad("thiếu block".into()))?;
        for (i, &(p, _)) in f.blocks[bi].params.iter().enumerate() {
            r.insert(p, a[i]);
        }
    }
}

type NFn = unsafe extern "sysv64" fn(u64, u64, u64, u64, u64, u64, u64, u64, u64, u64) -> u64;

fn native(base: *const u8, off: usize, a: &[u64]) -> u64 {
    let mut x = [0u64; 10];
    x[..a.len()].copy_from_slice(a);
    unsafe {
        let f: NFn = std::mem::transmute(base.add(off));
        f(x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7], x[8], x[9])
    }
}

fn load_code(code: &[u8]) -> *mut u8 {
    let len = (code.len() + 4095) & !4095;
    // PROT_READ|WRITE|EXEC, MAP_PRIVATE|MAP_ANONYMOUS
    let p = unsafe { mmap(std::ptr::null_mut(), len.max(4096), 7, 0x22, -1, 0) };
    assert!(!p.is_null() && p as isize != -1, "mmap thất bại");
    unsafe { std::ptr::copy_nonoverlapping(code.as_ptr(), p, code.len()) };
    p
}

/// Sinh ngẫu nhiên một module Light: hàm phụ g (1..8 tham số) + hàm t_fuzz có vòng lặp với nhiều tham số block bị
/// hoán vị ở hai cạnh lùi, phép tính/so sánh/load/store/gọi hàm ngẫu nhiên -> thử cấp phát thanh ghi, tràn stack,
/// chép song song và giữ giá trị qua lời gọi.
fn gen_prog(r: &mut Rng) -> String {
    const OPS: [&str; 11] = ["add", "sub", "mul", "and", "or", "xor", "shl", "lshr", "ashr", "udiv", "urem"];
    const CMPS: [&str; 10] = ["eq", "ne", "ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge"];
    let mut s = String::from("layout Q 8 {\n    0: bv64\n}\n");
    let mut v: u64;
    let pick = |r: &mut Rng, a: &Vec<u64>| a[(r.next() % a.len() as u64) as usize];
    // Một câu lệnh ngẫu nhiên; trả về biến mới (nếu có)
    let stmt = |r: &mut Rng, s: &mut String, v: &mut u64, a: &Vec<u64>, gparams: Option<u64>| -> Vec<u64> {
        let x = pick(r, a);
        let y = pick(r, a);
        let k = r.next() % 12;
        let mut out = vec![];
        let new = |s: &mut String, v: &mut u64, rhs: String| {
            s.push_str(&format!("        %{} = {}\n", v, rhs));
            *v += 1;
            *v - 1
        };
        match k {
            0..=4 => {
                let op = OPS[(r.next() % 11) as usize];
                let y = match op {
                    "shl" | "lshr" | "ashr" => {
                        let c = new(s, v, "const 63 bv64".into());
                        new(s, v, format!("and %{} %{}", y, c))
                    }
                    "udiv" | "urem" => {
                        let c = new(s, v, "const 1 bv64".into());
                        new(s, v, format!("or %{} %{}", y, c))
                    }
                    _ => y,
                };
                out.push(new(s, v, format!("{} %{} %{}", op, x, y)));
            }
            5 => {
                let c = new(s, v, format!("const {} bv64", r.val()));
                let op = OPS[(r.next() % 6) as usize];
                out.push(new(s, v, format!("{} %{} %{}", op, x, c)));
            }
            6 => out.push(new(s, v, format!("cmp {} %{} %{}", CMPS[(r.next() % 10) as usize], x, y))),
            7 | 8 => {
                let c = new(s, v, "const 63 bv64".into());
                let i = new(s, v, format!("and %{} %{}", x, c));
                let p = new(s, v, format!("slice %0 %{} ptr<Q,1>", i));
                if k == 7 {
                    out.push(new(s, v, format!("load %{} 0 bv64", p)));
                } else {
                    s.push_str(&format!("        store %{} 0 %{}\n", p, y));
                }
            }
            9 if gparams.is_some() => {
                let args: Vec<String> = (0..gparams.unwrap()).map(|_| format!("%{}", pick(r, a))).collect();
                out.push(new(s, v, format!("call g {}", args.join(" "))));
            }
            _ => out.push(new(s, v, format!("xor %{} %{}", x, y))),
        }
        out
    };
    // Hàm g
    let gm = 1 + r.next() % 8;
    let gp: Vec<String> = (0..gm).map(|i| format!("%{}:bv64", i + 1)).collect();
    s.push_str(&format!("func g bv64 %0:ptr<Q,64> {} {{\n    @b0\n", gp.join(" ")));
    let mut a: Vec<u64> = (1..=gm).collect();
    v = gm + 1;
    for _ in 0..1 + r.next() % 8 {
        let o = stmt(r, &mut s, &mut v, &a, None);
        a.extend(o);
    }
    s.push_str(&format!("        ret %{}\n}}\n", a.last().unwrap()));
    let gm = gm + 1; // g nhận thêm %0
    // Hàm t_fuzz
    let n = 1 + r.next() % 7;
    let fp: Vec<String> = (1..=n).map(|i| format!("%{}:bv64", i)).collect();
    s.push_str(&format!("func t_fuzz bv64 %0:ptr<Q,64> {} {{\n    @b0\n", fp.join(" ")));
    v = n + 1;
    let mut a0: Vec<u64> = (1..=n).collect();
    for _ in 0..2 {
        s.push_str(&format!("        %{} = const {} bv64\n", v, r.val()));
        a0.push(v);
        v += 1;
    }
    let np = 2 + r.next() % 8;
    let init: Vec<String> = (0..np).map(|_| format!("%{}", pick(r, &a0))).collect();
    let zero = v;
    s.push_str(&format!("        %{} = const 0 bv64\n        jmp @b1 {} %{}\n", zero, init.join(" "), zero));
    v += 1;
    let hp: Vec<u64> = (0..np).map(|i| v + i).collect();
    let cnt = v + np;
    v = cnt + 1;
    let hps: Vec<String> = hp.iter().map(|h| format!("%{}:bv64", h)).collect();
    let lim = v;
    s.push_str(&format!(
        "    @b1 {} %{}:bv64\n        %{} = const {} bv64\n        %{} = cmp ult %{} %{}\n        br %{} @b2 @b3\n    @b2\n",
        hps.join(" "), cnt, lim, r.next() % 7, lim + 1, cnt, lim, lim + 1
    ));
    v = lim + 2;
    // g nhận %0 (ptr) + gm-1 số; danh sách tham số gọi được dựng bên trong stmt từ biến số -> tạo ptr riêng
    let mut a: Vec<u64> = (1..=n).chain(hp.iter().copied()).collect();
    for _ in 0..3 + r.next() % 24 {
        let o = stmt(r, &mut s, &mut v, &a, Some(gm - 1));
        a.extend(o);
    }
    let one = v;
    s.push_str(&format!("        %{} = const 1 bv64\n        %{} = add %{} %{}\n", one, one + 1, cnt, one));
    let next = one + 1;
    v = one + 2;
    let c = pick(r, &a);
    let c2 = v;
    s.push_str(&format!("        %{} = cmp ugt %{} %{}\n        br %{} @b4 @b5\n", c2, c, pick(r, &a), c2));
    v += 1;
    for b in [4, 5] {
        s.push_str(&format!("    @b{}\n", b));
        let mut ab = a.clone();
        for _ in 0..r.next() % 4 {
            let o = stmt(r, &mut s, &mut v, &ab, Some(gm - 1));
            ab.extend(o);
        }
        let args: Vec<String> = (0..np).map(|_| format!("%{}", pick(r, &ab))).collect();
        s.push_str(&format!("        jmp @b1 {} %{}\n", args.join(" "), next));
    }
    let mut acc = hp[0];
    s.push_str("    @b3\n");
    for &h in &hp[1..] {
        s.push_str(&format!("        %{} = xor %{} %{}\n", v, acc, h));
        acc = v;
        v += 1;
    }
    s.push_str(&format!("        ret %{}\n}}\n", acc));
    // call g trong stmt dùng "call g %a %b..." -> chèn %0 làm đối số đầu
    s.replace("call g ", "call g %0 ")
}

/// Ngữ nghĩa add/sub/mul_{wrap,sat,ovf}: mã máy thật phải khớp số học của Rust trên các giá trị biên
fn check_ovf_semantics() -> usize {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/lit/codegen/ovf.lit");
    let m = parser::parse_file(path).expect("ovf.lit");
    let (code, offs) = elf64::compile_code(&m, false).expect("biên dịch ovf.lit");
    let exe = load_code(&code);
    let edge: [u64; 14] = [0, 1, 2, 3, 7, 0xffff, 1 << 32, (1 << 32) - 1, 1 << 63, (1 << 63) - 1, u64::MAX, u64::MAX - 1, 0x1234_5678_9abc_def0, 0xdead_beef];
    let mut bad = 0;
    for (fi, f) in m.funcs.iter().enumerate() {
        for &a in &edge {
            for &b in &edge {
                let want = match f.name.as_str() {
                    "t_add_wrap" => a.wrapping_add(b),
                    "t_sub_wrap" => a.wrapping_sub(b),
                    "t_mul_wrap" => a.wrapping_mul(b),
                    "t_add_sat" => a.saturating_add(b),
                    "t_sub_sat" => a.saturating_sub(b),
                    "t_mul_sat" => a.saturating_mul(b),
                    "t_add_ovf" => a.overflowing_add(b).1 as u64,
                    "t_sub_ovf" => a.overflowing_sub(b).1 as u64,
                    "t_mul_ovf" => a.overflowing_mul(b).1 as u64,
                    n => panic!("ovf.lit: hàm lạ {}", n),
                };
                let got = native(exe, offs[fi], &[a, b]);
                if got != want {
                    bad += 1;
                    println!("SAI {}({:#x}, {:#x}) = {:#x}, mong {:#x}", f.name, a, b, got, want);
                }
            }
        }
    }
    bad
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let runs: usize = args.iter().position(|a| a == "--runs").and_then(|i| args.get(i + 1)?.parse().ok()).unwrap_or(2000);
    let bench = args.iter().any(|a| a == "--bench");
    let fuzz: u64 = args.iter().position(|a| a == "--fuzz").and_then(|i| args.get(i + 1)?.parse().ok()).unwrap_or(300);
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/lit/codegen");
    let mut files: Vec<_> = std::fs::read_dir(dir).expect("thiếu tests/lit/codegen").map(|e| e.unwrap().path()).collect();
    files.sort();
    let mut mods: Vec<(String, Module, Option<String>)> = vec![];
    for path in files.iter().filter(|p| p.extension().is_some_and(|x| x == "lit")) {
        let m = parser::parse_file(path.to_str().unwrap()).unwrap_or_else(|e| panic!("{}: {}", path.display(), e));
        mods.push((path.file_stem().unwrap().to_string_lossy().into(), m, None));
    }
    let mut grng = Rng(0xD1B54A32D192ED03);
    for k in 0..if bench { 0 } else { fuzz } {
        let src = gen_prog(&mut grng);
        let m = parser::parse_module(&src).unwrap_or_else(|e| panic!("fuzz {}: {}\n{}", k, e, src));
        mods.push((format!("fuzz{}", k), m, Some(src)));
    }
    let mut fails = 0;
    let mut rng = Rng(0x9E3779B97F4A7C15);
    let (mut fz_ok, mut fz_skip) = (0, 0);
    for (name, m, src) in &mods {
        let runs = if src.is_some() { runs / 10 + 1 } else { runs };
        let (code, offs) = elf64::compile_code(m, false).unwrap_or_else(|e| panic!("{}: {}", name, e));
        if let Ok(d) = std::env::var("CGDUMP") {
            std::fs::write(format!("{}/{}.bin", d, name), &code).unwrap();
        }
        let exe = load_code(&code);
        for (fi, f) in m.funcs.iter().enumerate().filter(|(_, f)| f.name.starts_with("t_") || (bench && f.name.starts_with("bench_"))) {
            // Buffer cho tham số con trỏ: 2 bản (thông dịch / chạy thật), cùng nội dung ban đầu
            let ptrs: Vec<(usize, u64)> = f
                .params
                .iter()
                .enumerate()
                .filter_map(|(i, p)| match p.1 {
                    Type::Ptr { layout_id, max_elems } => Some((i, max_elems * m.layouts[layout_id as usize].size as u64)),
                    _ => None,
                })
                .collect();
            if f.name.starts_with("bench_") {
                let mut mem: Vec<Vec<u8>> = ptrs.iter().map(|&(_, n)| vec![1u8; n as usize]).collect();
                let mut a: Vec<u64> = f.params.iter().map(|_| 0).collect();
                for (k, &(i, _)) in ptrs.iter().enumerate() {
                    a[i] = mem[k].as_mut_ptr() as u64;
                }
                let t = Instant::now();
                let mut v = 0;
                for _ in 0..20 {
                    v = native(exe, offs[fi], &a);
                }
                println!("bench {:<24} {:>9.3} ms/lần  (kết quả {})", f.name, t.elapsed().as_secs_f64() * 1000.0 / 20.0, v);
                continue;
            }
            let (mut ok, mut skip) = (0, 0);
            for run in 0..runs {
                let mut mem_i: Vec<Vec<u8>> = vec![];
                let mut a: Vec<u64> = f.params.iter().map(|_| rng.val()).collect();
                for &(_, n) in &ptrs {
                    mem_i.push((0..n).map(|_| rng.next() as u8).collect());
                }
                let mut mem_n = mem_i.clone();
                let mut bufs = vec![];
                for (k, &(i, n)) in ptrs.iter().enumerate() {
                    a[i] = mem_i[k].as_mut_ptr() as u64;
                    bufs.push((a[i], a[i] + n));
                }
                let mut fuel = 2_000_000;
                match interp(m, fi, &a, &bufs, &mut fuel, 0) {
                    Err(Stop::Skip(_)) => {
                        skip += 1;
                        continue;
                    }
                    Err(Stop::Bad(e)) => panic!("{}: {}", f.name, e),
                    Ok(want) => {
                        for (k, &(i, _)) in ptrs.iter().enumerate() {
                            a[i] = mem_n[k].as_mut_ptr() as u64;
                        }
                        let got = native(exe, offs[fi], &a);
                        if got != want || mem_n != mem_i {
                            fails += 1;
                            println!("SAI {} lượt {}: đầu vào {:x?} -> native 0x{:x}, thông dịch 0x{:x}{}", f.name, run, a, got, want,
                                if mem_n != mem_i { " (bộ nhớ khác)" } else { "" });
                            if let Some(src) = src {
                                println!("{}", src);
                            }
                            break;
                        }
                        ok += 1;
                    }
                }
            }
            if src.is_some() {
                fz_ok += ok;
                fz_skip += skip;
            } else if !bench {
                println!("{:<28} {:>5} khớp, {:>5} bỏ qua", f.name, ok, skip);
            }
        }
        if src.is_none() {
            println!("== {}: {} byte mã máy", name, code.len());
        }
    }
    println!("== fuzz: {} chương trình ngẫu nhiên, {} lượt khớp, {} bỏ qua", fuzz, fz_ok, fz_skip);
    if !bench {
        let bad = check_ovf_semantics();
        println!("== ngữ nghĩa add/sub/mul_{{wrap,sat,ovf}}: {} sai", bad);
        fails += bad;
    }
    if fails > 0 {
        println!("THẤT BẠI: {} hàm sai", fails);
        std::process::exit(1);
    }
    println!("OK");
}
