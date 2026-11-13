// File: src/front.rs — front-end cú pháp B (file `.lt`): Rust-like, hạ xuống văn bản SSA `.lit` hiện có.
//
// Thiết kế: SSA phẳng vẫn là IR duy nhất cho Z3 và bộ sinh mã. Front-end chỉ sinh các dòng SSA, mỗi dòng kèm vị trí
// "file:dòng:cột" của nút cú pháp B tạo ra nó, nên lỗi Z3 chỉ đúng chỗ trong file `.lt`. Xem `light lower FILE.lt`.
//
// P1 (xem ROADMAP): biểu thức lồng nhau, `let`, `p[i]`, `p[a..b]`, `p.f`, `p[i].f`, gán bộ nhớ, gọi hàm, `if/else`,
// `return`; đặc tả `requires/ensures` (so sánh, &&, ||, !, ==>, <==>, phép bit, +% -% *%). Chưa có: vòng lặp, `var`
// (P2), số học toán học / lượng từ trong đặc tả (P3). Quy tắc:
//   - `+ - * / % <<` có kiểm (Z3 phải chứng minh không tràn / không chia 0); `+% -% *%` quay vòng; `+| -| *|` bão hòa.
//   - So sánh không dấu. `&&` / `||` ngắn mạch (vế phải có thể đọc bộ nhớ hay chia: chỉ được kiểm khi vế trái cho phép).
//   - Gọi hàm phải đứng riêng (`let x = f(..);`, `f(..);`, `return f(..);`) để thứ tự tác dụng phụ luôn rõ.
//   - `u8(x)` / `u16` / `u32`: thu hẹp CÓ KIỂM (Z3 chứng minh x vừa), không cắt bớt như `as` của Rust. `u64(x)`: mở rộng.
use crate::ir::{Module, Type};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::path::Path;

thread_local! {
    /// hàm spec đã biết (tên -> số tham số): từ include và từ file đang hạ; `spec()` dùng để dịch lời gọi trong đặc tả
    static SPECS: RefCell<HashMap<String, usize>> = RefCell::new(HashMap::new());
}

// ---------------------------------------------------------------------------------------------------------------
// Lexer
// ---------------------------------------------------------------------------------------------------------------
#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Id(String),
    Int(u64),
    Str(String),
    P(&'static str),
    Eof,
}

#[derive(Clone, Debug)]
struct T {
    t: Tok,
    line: u32,
    col: u32,
}

const PUNCTS: &[&str] = &[
    "<==>", "+%=", "-%=", "*%=", "+|=", "-|=", "*|=", "<<=", ">>=", "==>", "+=", "-=", "*=", "/=", "%=", "&=", "|=",
    "^=", "+%", "-%", "*%", "+|", "-|", "*|", "<<", ">>", "<=", ">=", "==", "!=", "&&", "||", "->", "..",
    "(", ")", "{", "}", "[", "]", ",", ";", ":", ".", "=", "<", ">", "+", "-", "*", "/", "%", "&", "|", "^", "!", "~",
];

fn lex(src: &str, file: &str) -> Result<Vec<T>, String> {
    let cs: Vec<char> = src.chars().collect();
    let (mut i, mut line, mut col) = (0usize, 1u32, 1u32);
    let mut out = Vec::new();
    let err = |l: u32, c: u32, m: &str| format!("Dòng {}:{}:{}: {}", file, l, c, m);
    while i < cs.len() {
        let c = cs[i];
        if c == '\n' {
            i += 1;
            line += 1;
            col = 1;
            continue;
        }
        if c.is_whitespace() {
            i += 1;
            col += 1;
            continue;
        }
        if c == '/' && cs.get(i + 1) == Some(&'/') {
            while i < cs.len() && cs[i] != '\n' {
                i += 1;
            }
            continue;
        }
        let (l0, c0) = (line, col);
        let start = i;
        if c.is_ascii_alphabetic() || c == '_' {
            while i < cs.len() && (cs[i].is_ascii_alphanumeric() || cs[i] == '_') {
                i += 1;
            }
            out.push(T { t: Tok::Id(cs[start..i].iter().collect()), line: l0, col: c0 });
        } else if c.is_ascii_digit() {
            while i < cs.len() && (cs[i].is_ascii_alphanumeric() || cs[i] == '_') {
                i += 1;
            }
            let s: String = cs[start..i].iter().filter(|&&c| c != '_').collect();
            let v = match s.strip_prefix("0x") {
                Some(h) => u64::from_str_radix(h, 16),
                None => s.parse::<u64>(),
            }
            .map_err(|_| err(l0, c0, &format!("số không hợp lệ hoặc vượt 2^64-1: {}", s)))?;
            out.push(T { t: Tok::Int(v), line: l0, col: c0 });
        } else if c == '\'' || c == '"' {
            let q = c;
            i += 1;
            let mut s = String::new();
            loop {
                let Some(&d) = cs.get(i) else { return Err(err(l0, c0, "chuỗi / ký tự chưa đóng")) };
                if d == '\n' {
                    return Err(err(l0, c0, "chuỗi / ký tự chưa đóng trên cùng dòng"));
                }
                i += 1;
                if d == q {
                    break;
                }
                if d == '\\' {
                    let e = *cs.get(i).ok_or_else(|| err(l0, c0, "thiếu ký tự sau \\"))?;
                    i += 1;
                    s.push(match e {
                        'n' => '\n',
                        't' => '\t',
                        'r' => '\r',
                        '0' => '\0',
                        '\\' | '\'' | '"' => e,
                        _ => return Err(err(l0, c0, &format!("escape không hỗ trợ: \\{}", e))),
                    });
                } else {
                    s.push(d);
                }
            }
            if q == '\'' {
                let mut it = s.chars();
                match (it.next(), it.next()) {
                    (Some(ch), None) if (ch as u32) < 256 => out.push(T { t: Tok::Int(ch as u64), line: l0, col: c0 }),
                    _ => return Err(err(l0, c0, "ký tự '...' phải là đúng một byte")),
                }
            } else {
                out.push(T { t: Tok::Str(s), line: l0, col: c0 });
            }
        } else {
            let rest: String = cs[i..cs.len().min(i + 4)].iter().collect();
            let Some(p) = PUNCTS.iter().find(|p| rest.starts_with(**p)) else {
                return Err(err(l0, c0, &format!("ký tự không hợp lệ '{}'", c)));
            };
            i += p.chars().count();
            out.push(T { t: Tok::P(p), line: l0, col: c0 });
        }
        col += (i - start) as u32;
    }
    out.push(T { t: Tok::Eof, line, col });
    Ok(out)
}

/// Số token của file `.lt` (để so độ dài với cú pháp SSA trong Light-Bench)
pub fn count_tokens(src: &str) -> Result<usize, String> {
    Ok(lex(src, "?")?.len() - 1)
}

// ---------------------------------------------------------------------------------------------------------------
// AST
// ---------------------------------------------------------------------------------------------------------------
type Pos = (u32, u32);

#[derive(Clone, Debug)]
enum EK {
    Int(u64),
    Name(String),
    Un(&'static str, Box<E>),
    Bin(&'static str, Box<E>, Box<E>),
    Index(Box<E>, Box<E>),
    Range(Box<E>, Box<E>, Box<E>),
    Field(Box<E>, String),
    Call(String, Vec<E>),
    /// `forall j in lo..hi: thân` / `exists ...` (chỉ trong đặc tả)
    Quant(bool, String, Box<E>, Box<E>, Box<E>),
    /// `if c { a } else { b }` dùng làm biểu thức (chỉ trong đặc tả / thân hàm spec)
    IfE(Box<E>, Box<E>, Box<E>),
}

#[derive(Clone, Debug)]
struct E {
    k: EK,
    p: Pos,
}

#[derive(Clone, Debug)]
enum TyB {
    Int(u32),
    Ptr(String, String), // (layout, độ dài: tên tham số / hằng / số)
}

#[derive(Clone, Debug)]
enum S {
    Let(String, Option<TyB>, E, Pos),
    Var(String, Option<TyB>, E, Pos),
    Assign(String, E, Pos), // x = e (x op= e đã được viết lại thành x = x op e)
    While { cond: E, invs: Vec<E>, dec: Option<E>, body: Vec<S>, p: Pos, end: Pos },
    For { var: String, from: E, to: E, invs: Vec<E>, body: Vec<S>, p: Pos, end: Pos },
    Break(Pos),
    /// `assert e;` (đặc tả): chứng minh e ở đây rồi dùng làm giả thiết — gợi ý cho Z3 (vd nhắc tới hạng dec(n, s, i + 1))
    Assert(E, Pos),
    Continue(Pos),
    Store(E, E, Pos),
    Expr(E, Pos),
    If(E, Vec<S>, Option<Vec<S>>, Pos),
    Ret(Option<E>, Pos),
}

#[derive(Clone, Debug)]
struct FnB {
    name: String,
    params: Vec<(String, TyB, Pos)>,
    ret: Option<TyB>,
    req: Vec<E>,
    ens: Vec<E>,
    body: Vec<S>,
    p: Pos,
}

/// `spec fn tên(tham số) -> int [decreases e] { biểu_thức }`
#[derive(Clone, Debug)]
struct SpecB {
    name: String,
    params: Vec<(String, TyB, Pos)>,
    dec: Option<E>,
    body: E,
    p: Pos,
}

enum Item {
    Spec(SpecB),
    Include(String, Pos),
    Const(String, u64, Pos),
    Data(String, String, Vec<u64>, Pos),
    Fn(FnB),
}

// ---------------------------------------------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------------------------------------------
struct Ps<'a> {
    t: Vec<T>,
    i: usize,
    file: &'a str,
}

const CMP: &[&str] = &["==", "!=", "<", "<=", ">", ">="];

fn prec(op: &str) -> Option<u8> {
    Some(match op {
        "<==>" => 1,
        "==>" => 2,
        "||" => 3,
        "&&" => 4,
        "==" | "!=" | "<" | "<=" | ">" | ">=" => 5,
        "|" => 6,
        "^" => 7,
        "&" => 8,
        "<<" | ">>" => 9,
        "+" | "-" | "+%" | "-%" | "+|" | "-|" => 10,
        "*" | "/" | "%" | "*%" | "*|" => 11,
        _ => return None,
    })
}

impl<'a> Ps<'a> {
    fn peek(&self) -> &Tok {
        &self.t[self.i].t
    }
    fn pos(&self) -> Pos {
        (self.t[self.i].line, self.t[self.i].col)
    }
    fn err<X>(&self, m: &str) -> Result<X, String> {
        let (l, c) = self.pos();
        Err(format!("Dòng {}:{}:{}: {}", self.file, l, c, m))
    }
    fn next(&mut self) -> Tok {
        let t = self.t[self.i].t.clone();
        if t != Tok::Eof {
            self.i += 1;
        }
        t
    }
    fn is(&self, p: &str) -> bool {
        matches!(self.peek(), Tok::P(q) if *q == p)
    }
    fn is_kw(&self, k: &str) -> bool {
        matches!(self.peek(), Tok::Id(q) if q == k)
    }
    fn eat(&mut self, p: &str) -> bool {
        if self.is(p) {
            self.i += 1;
            true
        } else {
            false
        }
    }
    fn expect(&mut self, p: &str) -> Result<(), String> {
        if self.eat(p) {
            Ok(())
        } else {
            self.err(&format!("cần '{}', gặp {}", p, show(self.peek())))
        }
    }
    fn ident(&mut self) -> Result<String, String> {
        match self.next() {
            Tok::Id(s) => Ok(s),
            t => {
                self.i -= 1;
                self.err(&format!("cần tên, gặp {}", show(&t)))
            }
        }
    }

    fn items(&mut self) -> Result<Vec<Item>, String> {
        let mut out = Vec::new();
        while *self.peek() != Tok::Eof {
            let p = self.pos();
            let kw = self.ident()?;
            match kw.as_str() {
                "include" => {
                    let Tok::Str(s) = self.next() else { return self.err("cần đường dẫn \"...\" sau include") };
                    self.expect(";")?;
                    out.push(Item::Include(s, p));
                }
                "const" => {
                    let n = self.ident()?;
                    self.expect("=")?;
                    let Tok::Int(v) = self.next() else { return self.err("const chỉ nhận một số nguyên") };
                    self.expect(";")?;
                    out.push(Item::Const(n, v, p));
                }
                "data" => {
                    // data NAME: u8 = "chuỗi";  |  data NAME: u64 = [1, 2, 3];
                    let n = self.ident()?;
                    self.expect(":")?;
                    let lay = self.elem()?;
                    self.expect("=")?;
                    let vals = match self.next() {
                        Tok::Str(s) => s.chars().map(|c| c as u64).collect(),
                        Tok::P("[") => {
                            let mut v = Vec::new();
                            while !self.eat("]") {
                                let Tok::Int(x) = self.next() else { return self.err("data [...] chỉ chứa số") };
                                v.push(x);
                                if !self.is("]") {
                                    self.expect(",")?;
                                }
                            }
                            v
                        }
                        _ => return self.err("data cần \"chuỗi\" hoặc [số, ...]"),
                    };
                    self.expect(";")?;
                    out.push(Item::Data(n, lay, vals, p));
                }
                "fn" => out.push(Item::Fn(self.func(p)?)),
                "spec" => {
                    if !self.is_kw("fn") {
                        return self.err("cần `spec fn tên(...) -> int { ... }`");
                    }
                    self.i += 1;
                    let f = self.func_head()?;
                    let (name, params, ret) = f;
                    if !matches!(ret.as_deref(), Some("int")) {
                        return self.err("hàm spec trả `int` (số nguyên toán học): `-> int`");
                    }
                    let dec = if self.is_kw("decreases") {
                        self.i += 1;
                        Some(self.expr(0)?)
                    } else {
                        None
                    };
                    self.expect("{")?;
                    let body = self.expr(0)?;
                    self.expect("}")?;
                    out.push(Item::Spec(SpecB { name, params, dec, body, p }));
                }
                _ => {
                    self.i -= 1;
                    return self.err(&format!("cần include / const / data / fn / spec fn, gặp '{}'", kw));
                }
            }
        }
        Ok(out)
    }

    /// Kiểu phần tử của ptr: u8 -> Byte, u32 -> VgaCell, u64 -> DiskQword (layout trong std/core.lit), hoặc tên layout
    fn elem(&mut self) -> Result<String, String> {
        let n = self.ident()?;
        Ok(match n.as_str() {
            "u8" => "Byte".into(),
            "u32" => "VgaCell".into(),
            "u64" => "DiskQword".into(),
            "u16" | "bool" => return self.err("chưa có layout cho phần tử u16 / bool"),
            _ => n,
        })
    }

    fn ty(&mut self) -> Result<TyB, String> {
        let n = self.ident()?;
        match n.as_str() {
            "u8" => Ok(TyB::Int(8)),
            "u16" => Ok(TyB::Int(16)),
            "u32" => Ok(TyB::Int(32)),
            "u64" => Ok(TyB::Int(64)),
            "ptr" => {
                self.expect("<")?;
                let e = self.elem()?;
                self.expect(",")?;
                let len = match self.next() {
                    Tok::Id(s) => s,
                    Tok::Int(v) => v.to_string(),
                    _ => return self.err("độ dài ptr là tên tham số, hằng hoặc số"),
                };
                self.expect(">")?;
                Ok(TyB::Ptr(e, len))
            }
            _ => {
                self.i -= 1;
                self.err(&format!("kiểu không hợp lệ '{}' (u8 u16 u32 u64 ptr<T, n>)", n))
            }
        }
    }

    /// `tên(tham số) -> int` của hàm spec (kiểu trả về là tên `int`)
    #[allow(clippy::type_complexity)]
    fn func_head(&mut self) -> Result<(String, Vec<(String, TyB, Pos)>, Option<String>), String> {
        let name = self.ident()?;
        self.expect("(")?;
        let mut params = Vec::new();
        while !self.eat(")") {
            let pp = self.pos();
            let n = self.ident()?;
            self.expect(":")?;
            params.push((n, self.ty()?, pp));
            if !self.is(")") {
                self.expect(",")?;
            }
        }
        let ret = if self.eat("->") { Some(self.ident()?) } else { None };
        Ok((name, params, ret))
    }

    fn func(&mut self, p: Pos) -> Result<FnB, String> {
        let name = self.ident()?;
        self.expect("(")?;
        let mut params = Vec::new();
        while !self.eat(")") {
            let pp = self.pos();
            let n = self.ident()?;
            self.expect(":")?;
            params.push((n, self.ty()?, pp));
            if !self.is(")") {
                self.expect(",")?;
            }
        }
        let ret = if self.eat("->") { Some(self.ty()?) } else { None };
        let (mut req, mut ens) = (Vec::new(), Vec::new());
        loop {
            let which = if self.is_kw("requires") {
                &mut req
            } else if self.is_kw("ensures") {
                &mut ens
            } else {
                break;
            };
            self.i += 1;
            loop {
                which.push(self.expr(0)?);
                if !self.eat(",") {
                    break;
                }
            }
        }
        let body = self.block()?;
        Ok(FnB { name, params, ret, req, ens, body, p })
    }

    fn block(&mut self) -> Result<Vec<S>, String> {
        Ok(self.block_end()?.0)
    }

    /// `{ ... }` kèm vị trí dấu `}` (cạnh lùi của vòng lặp báo lỗi ở đó)
    fn block_end(&mut self) -> Result<(Vec<S>, Pos), String> {
        self.expect("{")?;
        let mut out = Vec::new();
        loop {
            let p = self.pos();
            if self.eat("}") {
                return Ok((out, p));
            }
            if *self.peek() == Tok::Eof {
                return self.err("thiếu '}'");
            }
            out.push(self.stmt()?);
        }
    }

    /// `invariant e, e ... decreases e` (lặp lại được) trước thân vòng lặp
    fn loop_annots(&mut self, allow_dec: bool) -> Result<(Vec<E>, Option<E>), String> {
        let (mut invs, mut dec) = (Vec::new(), None);
        loop {
            if self.is_kw("invariant") {
                self.i += 1;
                loop {
                    invs.push(self.expr(0)?);
                    if !self.eat(",") {
                        break;
                    }
                }
            } else if self.is_kw("decreases") {
                if !allow_dec {
                    return self.err("for tự sinh decreases (to - i): không cần viết");
                }
                if dec.is_some() {
                    return self.err("chỉ một decreases cho mỗi vòng");
                }
                self.i += 1;
                dec = Some(self.expr(0)?);
            } else {
                return Ok((invs, dec));
            }
        }
    }

    fn stmt(&mut self) -> Result<S, String> {
        let p = self.pos();
        if self.is_kw("let") {
            self.i += 1;
            let n = self.ident()?;
            let ty = if self.eat(":") { Some(self.ty()?) } else { None };
            self.expect("=")?;
            let e = self.expr(0)?;
            self.expect(";")?;
            return Ok(S::Let(n, ty, e, p));
        }
        if self.is_kw("if") {
            return self.if_stmt();
        }
        if self.is_kw("assert") {
            self.i += 1;
            let e = self.expr(0)?;
            self.expect(";")?;
            return Ok(S::Assert(e, p));
        }
        if self.is_kw("return") {
            self.i += 1;
            let e = if self.is(";") { None } else { Some(self.expr(0)?) };
            self.expect(";")?;
            return Ok(S::Ret(e, p));
        }
        if self.is_kw("var") {
            self.i += 1;
            let n = self.ident()?;
            let ty = if self.eat(":") { Some(self.ty()?) } else { None };
            self.expect("=")?;
            let e = self.expr(0)?;
            self.expect(";")?;
            return Ok(S::Var(n, ty, e, p));
        }
        if self.is_kw("while") {
            self.i += 1;
            let cond = self.expr(0)?;
            let (invs, dec) = self.loop_annots(true)?;
            let (body, end) = self.block_end()?;
            return Ok(S::While { cond, invs, dec, body, p, end });
        }
        if self.is_kw("for") {
            // for i in a..b invariant ... { }
            self.i += 1;
            let var = self.ident()?;
            if !self.is_kw("in") {
                return self.err("cần `in`: for i in a..b { ... }");
            }
            self.i += 1;
            let from = self.expr(0)?;
            self.expect("..")?;
            let to = self.expr(0)?;
            let (invs, _) = self.loop_annots(false)?;
            let (body, end) = self.block_end()?;
            return Ok(S::For { var, from, to, invs, body, p, end });
        }
        for (kw, mk) in [("break", S::Break as fn(Pos) -> S), ("continue", S::Continue)] {
            if self.is_kw(kw) {
                self.i += 1;
                self.expect(";")?;
                return Ok(mk(p));
            }
        }
        if self.is_kw("loop") {
            return self.err("không có `loop` (vòng vô hạn): dùng while <điều kiện> decreases <biểu thức>");
        }
        let e = self.expr(0)?;
        let compound = match *self.peek() {
            Tok::P(op) if op.len() >= 2 && op.ends_with('=') && !matches!(op, "==" | "!=" | "<=" | ">=") => {
                Some(&op[..op.len() - 1])
            }
            _ => None,
        };
        if compound.is_some() || self.is("=") {
            let op_pos = self.pos();
            self.i += 1;
            let mut v = self.expr(0)?;
            self.expect(";")?;
            if let Some(op) = compound {
                let op: &'static str = PUNCTS.iter().find(|q| **q == op).unwrap();
                v = E { k: EK::Bin(op, Box::new(e.clone()), Box::new(v)), p: op_pos };
            }
            if let EK::Name(n) = &e.k {
                return Ok(S::Assign(n.clone(), v, p));
            }
            return Ok(S::Store(e, v, p));
        }
        self.expect(";")?;
        Ok(S::Expr(e, p))
    }

    fn if_stmt(&mut self) -> Result<S, String> {
        let p = self.pos();
        self.i += 1; // if
        let c = self.expr(0)?;
        let then = self.block()?;
        let els = if self.is_kw("else") {
            self.i += 1;
            if self.is_kw("if") {
                Some(vec![self.if_stmt()?])
            } else {
                Some(self.block()?)
            }
        } else {
            None
        };
        Ok(S::If(c, then, els, p))
    }

    fn expr(&mut self, min: u8) -> Result<E, String> {
        let mut l = self.unary()?;
        loop {
            let Tok::P(op) = *self.peek() else { break };
            let Some(pr) = prec(op) else { break };
            if pr < min {
                break;
            }
            let p = self.pos();
            self.i += 1;
            // ==> kết hợp phải; so sánh không kết hợp; còn lại kết hợp trái
            let r = self.expr(if op == "==>" { pr } else { pr + 1 })?;
            if CMP.contains(&op) {
                if let Tok::P(o2) = *self.peek() {
                    if CMP.contains(&o2) {
                        return self.err("không viết so sánh nối tiếp (a < b < c): dùng a < b && b < c");
                    }
                }
            }
            l = E { k: EK::Bin(op, Box::new(l), Box::new(r)), p };
        }
        Ok(l)
    }

    fn unary(&mut self) -> Result<E, String> {
        let p = self.pos();
        for op in ["!", "~"] {
            if self.eat(op) {
                let x = self.unary()?;
                return Ok(E { k: EK::Un(op, Box::new(x)), p });
            }
        }
        if self.is("-") {
            return self.err("không có số âm / phép đổi dấu: Light dùng số không dấu (0 -% x nếu cần quay vòng)");
        }
        let mut e = self.primary()?;
        loop {
            let p = self.pos();
            if self.eat("[") {
                let a = self.expr(0)?;
                if self.eat("..") {
                    let b = self.expr(0)?;
                    self.expect("]")?;
                    e = E { k: EK::Range(Box::new(e), Box::new(a), Box::new(b)), p };
                } else {
                    self.expect("]")?;
                    e = E { k: EK::Index(Box::new(e), Box::new(a)), p };
                }
            } else if self.eat(".") {
                let f = self.ident()?;
                e = E { k: EK::Field(Box::new(e), f), p };
            } else {
                break;
            }
        }
        Ok(e)
    }

    fn primary(&mut self) -> Result<E, String> {
        let p = self.pos();
        match self.next() {
            Tok::Int(v) => Ok(E { k: EK::Int(v), p }),
            Tok::Id(n) if n == "if" => {
                let c = self.expr(0)?;
                self.expect("{")?;
                let a = self.expr(0)?;
                self.expect("}")?;
                if !self.is_kw("else") {
                    return self.err("biểu thức if cần else: if c { a } else { b }");
                }
                self.i += 1;
                let b = if self.is_kw("if") {
                    self.primary()?
                } else {
                    self.expect("{")?;
                    let b = self.expr(0)?;
                    self.expect("}")?;
                    b
                };
                Ok(E { k: EK::IfE(Box::new(c), Box::new(a), Box::new(b)), p })
            }
            Tok::Id(n) if (n == "forall" || n == "exists") && matches!(self.peek(), Tok::Id(_)) => {
                let v = self.ident()?;
                if !self.is_kw("in") {
                    return self.err("cần `in`: forall j in lo..hi: điều_kiện");
                }
                self.i += 1;
                let lo = self.expr(0)?;
                self.expect("..")?;
                let hi = self.expr(0)?;
                self.expect(":")?;
                let body = self.expr(0)?;
                Ok(E { k: EK::Quant(n == "forall", v, Box::new(lo), Box::new(hi), Box::new(body)), p })
            }
            Tok::Id(n) => {
                if self.eat("(") {
                    let mut args = Vec::new();
                    while !self.eat(")") {
                        args.push(self.expr(0)?);
                        if !self.is(")") {
                            self.expect(",")?;
                        }
                    }
                    Ok(E { k: EK::Call(n, args), p })
                } else {
                    Ok(E { k: EK::Name(n), p })
                }
            }
            Tok::P("(") => {
                let e = self.expr(0)?;
                self.expect(")")?;
                Ok(e)
            }
            t => {
                self.i -= 1;
                self.err(&format!("cần biểu thức, gặp {}", show(&t)))
            }
        }
    }
}

fn show(t: &Tok) -> String {
    match t {
        Tok::Id(s) => format!("'{}'", s),
        Tok::Int(v) => format!("số {}", v),
        Tok::Str(_) => "chuỗi".into(),
        Tok::P(p) => format!("'{}'", p),
        Tok::Eof => "hết file".into(),
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Khai báo đã biết (từ các file include + chính file này)
// ---------------------------------------------------------------------------------------------------------------
#[derive(Clone)]
struct Sig {
    nparams: usize,
    ret: Option<VT>,
}

#[derive(Default)]
struct Decls {
    fields: HashMap<String, Vec<(Option<String>, u32, u32)>>, // layout -> [(tên, offset, bit)]
    funcs: HashMap<String, Sig>,
    datas: HashMap<String, String>, // data -> layout
}

fn bits_of(t: Type) -> Option<u32> {
    match t {
        Type::Bv8 => Some(8),
        Type::Bv16 => Some(16),
        Type::Bv32 => Some(32),
        Type::Bv64 => Some(64),
        _ => None,
    }
}

impl Decls {
    fn add_module(&mut self, m: &Module) {
        for l in &m.layouts {
            let fs = l.fields.iter().filter_map(|f| Some((f.name.clone(), f.offset, bits_of(f.ty)?))).collect();
            self.fields.insert(l.name.clone(), fs);
        }
        for f in &m.funcs {
            let ret = match f.ret_ty {
                None => None,
                // con trỏ độ dài tĩnh (vd mbr_num -> ptr<DiskQword,17>); độ dài động theo tham số: chưa hỗ trợ
                Some(Type::Ptr { layout_id, max_elems }) => {
                    Some(VT::Ptr(m.layouts[layout_id as usize].name.clone(), max_elems.to_string()))
                }
                Some(t) => Some(bits_of(t).map_or(VT::Other, VT::Int)),
            };
            self.funcs.insert(f.name.clone(), Sig { nparams: f.params.len(), ret });
        }
        for d in &m.datas {
            self.datas.insert(d.name.clone(), m.layouts[d.layout_id as usize].name.clone());
        }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Hạ xuống SSA
// ---------------------------------------------------------------------------------------------------------------
#[derive(Clone, Debug, PartialEq)]
enum VT {
    Int(u32),        // số nguyên bvN
    Bool(u32),       // 0/1, nằm trong thanh ghi bv8 (cmp) hoặc bv64 (and/or)
    Ptr(String, String), // (layout, độ dài dạng SSA: "%n" / "5" / "TÊN")
    Lit,             // hằng chưa gán kiểu (số hoặc tên `const`)
    Other,           // giá trị trả về kiểu khác (vd ptr) từ hàm std — chưa hỗ trợ
}

#[derive(Clone, Debug)]
struct V {
    s: String,
    t: VT,
}

/// Tên người viết -> tên SSA. `%r` là kết quả hàm trong @ens của SSA, nên biến tên `r` thành `%_r`
/// (người viết không đặt được tên bắt đầu bằng `_`, nên không trùng; biến tạm của front-end là `%_tN`).
fn mangle(n: &str) -> String {
    if n == "r" { "_r".into() } else { n.to_string() }
}

fn check_ident(n: &str, file: &str, p: Pos) -> Result<(), String> {
    if n.starts_with('_') {
        return Err(format!("Dòng {}:{}:{}: tên '{}' không được bắt đầu bằng '_' (dành cho biến tạm)", file, p.0, p.1, n));
    }
    Ok(())
}

fn ssa_ty(t: &TyB, params: &HashSet<String>) -> String {
    match t {
        TyB::Int(b) => format!("bv{}", b),
        TyB::Ptr(l, n) => {
            let len = if params.contains(n) { format!("%{}", mangle(n)) } else { n.clone() };
            format!("ptr<{},{}>", l, len)
        }
    }
}

fn vt_of(t: &TyB, params: &HashSet<String>) -> VT {
    match t {
        TyB::Int(b) => VT::Int(*b),
        TyB::Ptr(l, n) => VT::Ptr(l.clone(), if params.contains(n) { format!("%{}", mangle(n)) } else { n.clone() }),
    }
}

struct Fx<'a> {
    file: &'a str,
    out: &'a mut Vec<(String, String)>,
    decls: &'a Decls,
    tmp: u32,
    lbl: u32,
    scopes: Vec<HashMap<String, V>>,
    used: HashSet<String>,
    term: bool,
    ret: Option<TyB>,
    params: HashSet<String>,
    /// tên khai báo bằng `var` theo từng tầng scope (song song với `scopes`)
    vars: Vec<Vec<String>>,
    loops: Vec<Lp>,
}

/// Vòng lặp đang hạ: đầu vòng (block có tham số) và các cạnh `break` chờ nối vào block sau vòng
struct Lp {
    head: String,
    /// tham số của đầu vòng: [chỉ số for] + biến bị gán trong thân
    hparams: Vec<String>,
    /// chỉ số `for` (thanh ghi) — cạnh lùi truyền i + 1
    idx: Option<String>,
    /// biến `var` thấy được lúc vào vòng / giá trị lúc vào / tập bị gán trong thân
    vars: Vec<String>,
    env0: Vec<V>,
    modified: Vec<String>,
    breaks: Vec<(usize, Vec<V>)>,
}

/// Mọi tên bị gán (`x = ...`) trong thân, kể cả trong if / vòng lồng nhau (tập lớn hơn hoặc bằng tập thật)
fn assigned(ss: &[S], out: &mut HashSet<String>) {
    for s in ss {
        match s {
            S::Assign(n, ..) => {
                out.insert(n.clone());
            }
            S::If(_, t, e, _) => {
                assigned(t, out);
                if let Some(e) = e {
                    assigned(e, out);
                }
            }
            S::While { body, .. } | S::For { body, .. } => assigned(body, out),
            _ => {}
        }
    }
}

impl Fx<'_> {
    fn org(&self, p: Pos) -> String {
        format!("{}:{}:{}", self.file, p.0, p.1)
    }
    fn err<X>(&self, p: Pos, m: &str) -> Result<X, String> {
        Err(format!("Dòng {}: {}", self.org(p), m))
    }
    fn emit(&mut self, p: Pos, s: String) {
        self.out.push((format!("        {}", s), self.org(p)));
    }
    fn label(&mut self, p: Pos, l: &str) {
        self.out.push((format!("    @{}", l), self.org(p)));
        self.term = false;
    }
    fn new_label(&mut self, kind: &str) -> String {
        self.lbl += 1;
        format!("{}{}", kind, self.lbl)
    }
    /// Đích của lệnh: tên người viết muốn (từ `let`) hoặc biến tạm `%_tN` (không trùng tên người viết vì có `_` đầu)
    fn dst(&mut self, want: Option<String>) -> String {
        want.unwrap_or_else(|| {
            self.tmp += 1;
            format!("%_t{}", self.tmp)
        })
    }
    fn lookup(&self, n: &str) -> Option<V> {
        self.scopes.iter().rev().find_map(|s| s.get(n).cloned())
    }
    fn fresh_name(&mut self, n: &str) -> String {
        let mut cand = n.to_string();
        let mut k = 1;
        while !self.used.insert(cand.clone()) {
            k += 1;
            cand = format!("{}_{}", n, k);
        }
        cand
    }

    // ---- biến `var` ----
    fn is_var(&self, n: &str) -> bool {
        self.vars.iter().any(|v| v.iter().any(|x| x == n))
    }
    /// biến `var` thấy được (theo thứ tự khai báo)
    fn visible_vars(&self) -> Vec<String> {
        self.vars.iter().flatten().cloned().collect()
    }
    fn snapshot(&self, names: &[String]) -> Vec<V> {
        names.iter().map(|n| self.lookup(n).expect("biến var phải thấy được")).collect()
    }
    fn set_var(&mut self, n: &str, v: V) {
        for s in self.scopes.iter_mut().rev() {
            if let Some(x) = s.get_mut(n) {
                *x = v;
                return;
            }
        }
        unreachable!("set_var {}", n)
    }
    fn restore(&mut self, names: &[String], env: &[V]) {
        for (n, v) in names.iter().zip(env) {
            self.set_var(n, v.clone());
        }
    }
    /// Giá trị `v` đưa về số nguyên đúng `bits` bit, nằm trong thanh ghi (biến var luôn là thanh ghi có kiểu cố định)
    fn materialize(&mut self, v: V, bits: u32, want: &str, p: Pos, what: &str) -> Result<V, String> {
        if v.t == VT::Lit {
            let raw = self.fit(v, bits, p, what)?;
            self.emit(p, format!("{} = const {} bv{}", want, raw.split(':').next().unwrap(), bits));
            return Ok(V { s: want.into(), t: VT::Int(bits) });
        }
        let s = self.fit(v, bits, p, what)?;
        Ok(V { s, t: VT::Int(bits) })
    }
    /// `jmp @l` chưa có đối số: vị trí dòng để vá khi biết tham số của block nối
    fn jmp_placeholder(&mut self, p: Pos, l: &str) -> usize {
        self.emit(p, format!("jmp @{}", l));
        self.term = true;
        self.out.len() - 1
    }
    /// Block nối `l` của các cạnh `edges` (dòng jmp, giá trị các biến `names` trên cạnh đó). Biến có giá trị khác nhau
    /// giữa các cạnh thành tham số của block; vá đối số vào từng jmp. Không cạnh nào tới -> không sinh block (term).
    fn join(&mut self, l: &str, p: Pos, names: &[String], edges: Vec<(usize, Vec<V>)>) {
        if edges.is_empty() {
            self.term = true;
            return;
        }
        let differ: Vec<usize> =
            (0..names.len()).filter(|&k| edges.iter().any(|(_, env)| env[k].s != edges[0].1[k].s)).collect();
        let mut head = format!("    @{}", l);
        let mut regs = Vec::new();
        for &k in &differ {
            let VT::Int(b) = edges[0].1[k].t else { unreachable!() };
            let r = format!("%{}", self.fresh_name(&mangle(&names[k])));
            head.push_str(&format!(" {}:bv{}", r, b));
            regs.push(V { s: r, t: VT::Int(b) });
        }
        for (idx, env) in &edges {
            let args: String = differ.iter().map(|&k| format!(" {}", env[k].s)).collect();
            self.out[*idx].0 = format!("        jmp @{}{}", l, args);
        }
        let env0 = edges[0].1.clone();
        self.out.push((head, self.org(p)));
        self.term = false;
        self.restore(names, &env0);
        for (&k, v) in differ.iter().zip(regs) {
            self.set_var(&names[k], v);
        }
    }
    /// Cạnh lùi về đầu vòng `self.loops[li]` (cuối thân hoặc `continue`)
    fn back_jmp(&mut self, li: usize, p: Pos) -> Result<(), String> {
        let lp = &self.loops[li];
        let (head, hparams, idx) = (lp.head.clone(), lp.hparams.clone(), lp.idx.clone());
        let (vars, env0, modified) = (lp.vars.clone(), lp.env0.clone(), lp.modified.clone());
        self.check_unmodified(&vars, &env0, &modified, p)?;
        let mut args = Vec::new();
        if let Some(i) = idx {
            let d = self.dst(None);
            self.emit(p, format!("{} = add {} 1", d, i));
            args.push(V { s: d, t: VT::Int(64) });
        }
        args.extend(self.snapshot(&modified));
        // parallel-copy: đối số trùng tham số đứng TRƯỚC của đầu vòng (vd hoán đổi a, b) -> chép sang biến tạm
        let mut ss = Vec::new();
        for (j, a) in args.iter().enumerate() {
            if hparams[..j].contains(&a.s) {
                let VT::Int(b) = a.t else { unreachable!() };
                let d = self.dst(None);
                if b == 64 {
                    self.emit(p, format!("{} = or {} 0", d, a.s));
                } else {
                    self.emit(p, format!("{} = narrow {} bv{}", d, a.s, b));
                }
                ss.push(d);
            } else {
                ss.push(a.s.clone());
            }
        }
        let tail: String = ss.iter().map(|x| format!(" {}", x)).collect();
        self.emit(p, format!("jmp @{}{}", head, tail));
        self.term = true;
        Ok(())
    }
    /// Kiểm nội bộ: biến không nằm trong tập bị gán thì phải giữ nguyên giá trị lúc vào vòng
    fn check_unmodified(&self, vars: &[String], env0: &[V], modified: &[String], p: Pos) -> Result<(), String> {
        for (n, v0) in vars.iter().zip(env0) {
            if !modified.contains(n) && self.lookup(n).map(|v| v.s) != Some(v0.s.clone()) {
                return self.err(p, &format!("lỗi nội bộ front-end: biến '{}' đổi giá trị nhưng không có trong tập bị gán", n));
            }
        }
        Ok(())
    }
    /// tên -> toán hạng SSA của mọi biến / tham số đang thấy (cho invariant / decreases)
    fn names_map(&self) -> HashMap<String, String> {
        let mut m = HashMap::new();
        for sc in &self.scopes {
            for (n, v) in sc {
                if v.s.starts_with('%') {
                    m.insert(n.clone(), v.s.clone());
                }
            }
        }
        m
    }
    fn new_binding_ok(&self, n: &str, is_var: bool, p: Pos) -> Result<(), String> {
        check_ident(n, self.file, p)?;
        if n == "result" {
            return self.err(p, "'result' là từ khóa của ensures");
        }
        if self.is_var(n) {
            return self.err(p, &format!("'{}' trùng tên biến var đang thấy (không cho che biến var)", n));
        }
        if is_var && self.lookup(n).is_some() {
            return self.err(p, &format!("biến var '{}' trùng tên đang thấy (tham số / let): đặt tên khác", n));
        }
        Ok(())
    }

    // ---- biểu thức (giá trị) ----
    fn int_operand(&self, v: &V, p: Pos) -> Result<(), String> {
        match v.t {
            VT::Int(_) | VT::Bool(_) | VT::Lit => Ok(()),
            VT::Ptr(..) => self.err(p, "con trỏ không dùng được trong phép tính số: dùng p[i] để đọc phần tử"),
            VT::Other => self.err(p, "giá trị kiểu này chưa hỗ trợ trong biểu thức"),
        }
    }

    fn expr(&mut self, e: &E, want: Option<String>, top: bool) -> Result<V, String> {
        let p = e.p;
        match &e.k {
            EK::Quant(..) | EK::IfE(..) => {
                self.err(p, "forall / exists / biểu thức if chỉ dùng trong đặc tả (requires / ensures / invariant / spec fn)")
            }
            EK::Int(v) => Ok(V { s: v.to_string(), t: VT::Lit }),
            EK::Name(n) => {
                if n == "result" {
                    return self.err(p, "`result` chỉ dùng trong ensures");
                }
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                if self.decls.datas.contains_key(n) {
                    return self.err(p, &format!("'{}' là data: dùng addr({})", n, n));
                }
                // tên hằng (`const` / `def` của std): parser SSA tự tra và báo lỗi nếu không có
                if n.chars().next().is_some_and(|c| c.is_ascii_uppercase()) || n.contains('.') {
                    return Ok(V { s: n.clone(), t: VT::Lit });
                }
                self.err(p, &format!("không có biến '{}'", n))
            }
            EK::Un(op, x) => {
                let v = self.expr(x, None, false)?;
                if *op == "!" {
                    if !matches!(v.t, VT::Bool(_)) {
                        return self.err(p, "`!` cần điều kiện (so sánh / && / ||); với số dùng `x == 0`");
                    }
                    let d = self.dst(want);
                    self.emit(p, format!("{} = cmp eq {} 0", d, v.s));
                    Ok(V { s: d, t: VT::Bool(8) })
                } else {
                    self.int_operand(&v, x.p)?;
                    let d = self.dst(want);
                    self.emit(p, format!("{} = xor {} 0xffffffffffffffff", d, v.s));
                    Ok(V { s: d, t: VT::Int(64) })
                }
            }
            EK::Bin(op, a, b) if *op == "&&" || *op == "||" => {
                if is_safe(b) {
                    let l = self.expr(a, None, false)?;
                    let r = self.expr(b, None, false)?;
                    for (v, q) in [(&l, a.p), (&r, b.p)] {
                        if !matches!(v.t, VT::Bool(_)) {
                            return self.err(q, &format!("`{}` cần điều kiện hai vế (so sánh); với số dùng `x != 0`", op));
                        }
                    }
                    let d = self.dst(want);
                    self.emit(p, format!("{} = {} {} {}", d, if *op == "&&" { "and" } else { "or" }, l.s, r.s));
                    return Ok(V { s: d, t: VT::Bool(64) });
                }
                // vế phải có điều kiện chứng minh (đọc bộ nhớ, chia, ...): ngắn mạch bằng rẽ nhánh
                let (lt, lf, lj) = (self.new_label("sc_t"), self.new_label("sc_f"), self.new_label("sc_j"));
                self.cond(e, &lt, &lf)?;
                self.label(p, &lt);
                self.emit(p, format!("jmp @{} 1", lj));
                self.label(p, &lf);
                self.emit(p, format!("jmp @{} 0", lj));
                let d = self.dst(want);
                self.out.push((format!("    @{} {}:bv8", lj, d), self.org(p)));
                self.term = false;
                Ok(V { s: d, t: VT::Bool(8) })
            }
            EK::Bin(op, ..) if *op == "==>" || *op == "<==>" => {
                self.err(p, &format!("`{}` chỉ dùng trong requires / ensures", op))
            }
            EK::Bin(op, a, b) => {
                let l = self.expr(a, None, false)?;
                let r = self.expr(b, None, false)?;
                self.int_operand(&l, a.p)?;
                self.int_operand(&r, b.p)?;
                let d = self.dst(want);
                if let Some(c) = cmp_name(op) {
                    self.emit(p, format!("{} = cmp {} {} {}", d, c, l.s, r.s));
                    return Ok(V { s: d, t: VT::Bool(8) });
                }
                let name = bin_name(op).unwrap();
                self.emit(p, format!("{} = {} {} {}", d, name, l.s, r.s));
                Ok(V { s: d, t: VT::Int(64) })
            }
            EK::Index(pe, ie) => {
                let (c, lay) = self.elem_ptr(pe, ie, p)?;
                let f = self.single_field(&lay, p)?;
                let d = self.dst(want);
                self.emit(p, format!("{} = load {} {} bv{}", d, c, f.1, f.2));
                Ok(V { s: d, t: VT::Int(f.2) })
            }
            EK::Range(pe, ae, be) => {
                let pv = self.expr(pe, None, false)?;
                let VT::Ptr(lay, _) = pv.t.clone() else { return self.err(pe.p, "chỉ cắt được con trỏ: p[a..b]") };
                let a = self.expr(ae, None, false)?;
                // p[x..x + K] với K là số: độ dài tĩnh K (kiểu ptr<L,K>, không cần thanh ghi độ dài)
                let static_k = match (&ae.k, &be.k) {
                    (EK::Name(x), EK::Bin("+", y, k)) => match (&y.k, &k.k) {
                        (EK::Name(y), EK::Int(k)) if x == y => Some(*k),
                        _ => None,
                    },
                    _ => None,
                };
                if let Some(k) = static_k {
                    let d = self.dst(want);
                    self.emit(p, format!("{} = slice {} {} ptr<{},{}>", d, pv.s, a.s, lay, k));
                    return Ok(V { s: d, t: VT::Ptr(lay, k.to_string()) });
                }
                let b = self.expr(be, None, false)?;
                self.int_operand(&a, ae.p)?;
                self.int_operand(&b, be.p)?;
                let len = if a.s == "0" && b.t == VT::Lit {
                    b.s.clone()
                } else if a.s == "0" && b.s.starts_with('%') {
                    b.s.clone()
                } else {
                    let d = self.dst(None);
                    self.emit(p, format!("{} = sub {} {}", d, b.s, a.s));
                    d
                };
                let d = self.dst(want);
                self.emit(p, format!("{} = slice {} {} ptr<{},{}>", d, pv.s, a.s, lay, len));
                Ok(V { s: d, t: VT::Ptr(lay, len) })
            }
            EK::Field(be, f) if matches!(&be.k, EK::Name(n) if is_const_name(n) && self.lookup(n).is_none()) => {
                let EK::Name(n) = &be.k else { unreachable!() };
                Ok(V { s: format!("{}.{}", n, f), t: VT::Lit }) // DATA.len / Layout.trường: hằng
            }
            EK::Field(be, f) => {
                let (c, lay) = self.field_base(be)?;
                let (off, bits) = self.field(&lay, f, p)?;
                let d = self.dst(want);
                self.emit(p, format!("{} = load {} {} bv{}", d, c, off, bits));
                Ok(V { s: d, t: VT::Int(bits) })
            }
            EK::Call(name, args) => self.call(name, args, want, top, p),
        }
    }

    fn call(&mut self, name: &str, args: &[E], want: Option<String>, top: bool, p: Pos) -> Result<V, String> {
        let one = |s: &Self| -> Result<&E, String> {
            if args.len() == 1 { Ok(&args[0]) } else { s.err(p, &format!("{}(...) nhận đúng 1 đối số", name)) }
        };
        match name {
            "u8" | "u16" | "u32" => {
                let bits: u32 = name[1..].parse().unwrap();
                let a = one(self)?;
                let v = self.expr(a, None, false)?;
                self.int_operand(&v, a.p)?;
                if v.t == VT::Lit {
                    if let Ok(x) = v.s.parse::<u64>() {
                        if x >> bits != 0 {
                            return self.err(p, &format!("{} không vừa {}", x, name));
                        }
                    }
                    return Ok(V { s: format!("{}:bv{}", v.s, bits), t: VT::Int(bits) });
                }
                if matches!(v.t, VT::Int(b) | VT::Bool(b) if b == bits) {
                    return Ok(v);
                }
                let d = self.dst(want);
                self.emit(p, format!("{} = narrow {} bv{}", d, v.s, bits));
                Ok(V { s: d, t: VT::Int(bits) })
            }
            "u64" => {
                let a = one(self)?;
                let v = self.expr(a, None, false)?;
                self.int_operand(&v, a.p)?;
                if matches!(v.t, VT::Lit | VT::Int(64)) {
                    return Ok(V { s: v.s, t: if v.t == VT::Lit { VT::Lit } else { VT::Int(64) } });
                }
                let d = self.dst(want);
                self.emit(p, format!("{} = or {} 0", d, v.s));
                Ok(V { s: d, t: VT::Int(64) })
            }
            "lt_s" | "le_s" | "gt_s" | "ge_s" => {
                // so sánh CÓ DẤU (bù hai) — mặc định của <, <=, ... là không dấu
                if args.len() != 2 {
                    return self.err(p, &format!("{}(a, b) nhận 2 đối số", name));
                }
                let a = self.expr(&args[0], None, false)?;
                let b = self.expr(&args[1], None, false)?;
                self.int_operand(&a, args[0].p)?;
                self.int_operand(&b, args[1].p)?;
                let op = &format!("s{}", &name[..2]);
                let d = self.dst(want);
                self.emit(p, format!("{} = cmp {} {} {}", d, op, a.s, b.s));
                Ok(V { s: d, t: VT::Bool(8) })
            }
            "mulhi" => {
                if args.len() != 2 {
                    return self.err(p, "mulhi(a, b) nhận 2 đối số");
                }
                let a = self.expr(&args[0], None, false)?;
                let b = self.expr(&args[1], None, false)?;
                let d = self.dst(want);
                self.emit(p, format!("{} = mulhi {} {}", d, a.s, b.s));
                Ok(V { s: d, t: VT::Int(64) })
            }
            "addr" => {
                let a = one(self)?;
                let EK::Name(n) = &a.k else { return self.err(p, "addr(TÊN_DATA)") };
                let Some(lay) = self.decls.datas.get(n).cloned() else {
                    return self.err(a.p, &format!("không có data '{}'", n));
                };
                let d = self.dst(want);
                self.emit(p, format!("{} = addr {}", d, n));
                Ok(V { s: d, t: VT::Ptr(lay, format!("{}.len", n)) })
            }
            _ => {
                if !top {
                    return self.err(p, &format!("gọi hàm phải đứng riêng: `let t = {}(...);` rồi dùng t", name));
                }
                let Some(sig) = self.decls.funcs.get(name).cloned() else {
                    return self.err(p, &format!("không có hàm '{}' (thiếu include?)", name));
                };
                if sig.nparams != args.len() {
                    return self.err(p, &format!("'{}' nhận {} đối số, gặp {}", name, sig.nparams, args.len()));
                }
                let mut a = Vec::new();
                for x in args {
                    let v = self.expr(x, None, false)?;
                    a.push(v.s);
                }
                let tail = if a.is_empty() { String::new() } else { format!(" {}", a.join(" ")) };
                match sig.ret {
                    None => {
                        if want.is_some() {
                            return self.err(p, &format!("'{}' không trả giá trị", name));
                        }
                        self.emit(p, format!("call {}{}", name, tail));
                        Ok(V { s: String::new(), t: VT::Other })
                    }
                    Some(t) => {
                        if t == VT::Other {
                            return self.err(p, &format!("'{}' trả kiểu chưa hỗ trợ trong cú pháp B", name));
                        }
                        let d = self.dst(want);
                        self.emit(p, format!("{} = call {}{}", d, name, tail));
                        Ok(V { s: d, t })
                    }
                }
            }
        }
    }

    /// `p[i]` -> (thanh ghi con trỏ 1 phần tử, layout)
    fn elem_ptr(&mut self, pe: &E, ie: &E, p: Pos) -> Result<(String, String), String> {
        let pv = self.expr(pe, None, false)?;
        let VT::Ptr(lay, _) = pv.t.clone() else { return self.err(pe.p, "chỉ đánh chỉ số được con trỏ ptr<T, n>") };
        let i = self.expr(ie, None, false)?;
        self.int_operand(&i, ie.p)?;
        let d = self.dst(None);
        self.emit(p, format!("{} = slice {} {} ptr<{},1>", d, pv.s, i.s, lay));
        Ok((d, lay))
    }

    /// Cơ sở của `.f`: `p[i].f` (slice phần tử i) hoặc `p.f` (phần tử 0)
    fn field_base(&mut self, be: &E) -> Result<(String, String), String> {
        if let EK::Index(pe, ie) = &be.k {
            return self.elem_ptr(pe, ie, be.p);
        }
        let v = self.expr(be, None, false)?;
        match v.t {
            VT::Ptr(lay, _) => Ok((v.s, lay)),
            _ => self.err(be.p, "`.trường` cần con trỏ tới layout"),
        }
    }

    fn single_field(&self, lay: &str, p: Pos) -> Result<(Option<String>, u32, u32), String> {
        let fs = self.decls.fields.get(lay).ok_or_else(|| format!("Dòng {}: không có layout '{}'", self.org(p), lay))?;
        match fs.as_slice() {
            [f] if f.1 == 0 => Ok(f.clone()),
            _ => self.err(p, &format!("layout '{}' có nhiều trường: dùng p[i].tên_trường", lay)),
        }
    }

    fn field(&self, lay: &str, f: &str, p: Pos) -> Result<(u32, u32), String> {
        let fs = self.decls.fields.get(lay).ok_or_else(|| format!("Dòng {}: không có layout '{}'", self.org(p), lay))?;
        fs.iter()
            .find(|x| x.0.as_deref() == Some(f))
            .map(|x| (x.1, x.2))
            .ok_or_else(|| format!("Dòng {}: layout '{}' không có trường '{}'", self.org(p), lay, f))
    }

    /// Giá trị `v` để ghi vào ô bvN: hằng -> hằng có kiểu; số cùng bề rộng; còn lại lỗi có gợi ý
    fn fit(&mut self, v: V, bits: u32, p: Pos, what: &str) -> Result<String, String> {
        match v.t {
            VT::Lit => {
                if let Ok(x) = v.s.parse::<u64>() {
                    if bits < 64 && x >> bits != 0 {
                        return self.err(p, &format!("{} không vừa {} bit ({})", x, bits, what));
                    }
                }
                Ok(if bits == 64 { v.s } else { format!("{}:bv{}", v.s, bits) })
            }
            VT::Int(b) | VT::Bool(b) if b == bits => Ok(v.s),
            VT::Int(b) | VT::Bool(b) if b < bits && bits == 64 => {
                let d = self.dst(None);
                self.emit(p, format!("{} = or {} 0", d, v.s));
                Ok(d)
            }
            VT::Int(b) | VT::Bool(b) => {
                self.err(p, &format!("{}: giá trị {} bit, ô {} bit — dùng u{}(x) (thu hẹp có kiểm) hoặc u64(x)", what, b, bits, bits))
            }
            _ => self.err(p, &format!("{}: giá trị không phải số", what)),
        }
    }

    // ---- điều kiện: rẽ nhánh thẳng tới T / F (ngắn mạch && ||) ----
    fn cond(&mut self, e: &E, t: &str, f: &str) -> Result<(), String> {
        match &e.k {
            EK::Bin("&&", a, b) => {
                let m = self.new_label("and");
                self.cond(a, &m, f)?;
                self.label(e.p, &m);
                self.cond(b, t, f)
            }
            EK::Bin("||", a, b) => {
                let m = self.new_label("or");
                self.cond(a, t, &m)?;
                self.label(e.p, &m);
                self.cond(b, t, f)
            }
            EK::Un("!", x) => self.cond(x, f, t),
            _ => {
                let v = self.expr(e, None, false)?;
                if !matches!(v.t, VT::Bool(_)) {
                    return self.err(e.p, "điều kiện phải là so sánh / && / || (với số dùng `x != 0`)");
                }
                self.emit(e.p, format!("br {} @{} @{}", v.s, t, f));
                self.term = true;
                Ok(())
            }
        }
    }

    // ---- câu lệnh ----
    fn stmts(&mut self, ss: &[S]) -> Result<(), String> {
        self.scopes.push(HashMap::new());
        self.vars.push(Vec::new());
        for s in ss {
            let p = match s {
                S::Let(.., p) | S::Var(.., p) | S::Assign(.., p) | S::Store(.., p) | S::Expr(_, p) | S::If(.., p) => *p,
                S::Ret(_, p) | S::Assert(_, p) | S::Break(p) | S::Continue(p) | S::While { p, .. } | S::For { p, .. } => *p,
            };
            if self.term {
                return self.err(p, "câu lệnh không bao giờ chạy tới (sau return / break / continue)");
            }
            self.stmt(s)?;
        }
        self.scopes.pop();
        self.vars.pop();
        Ok(())
    }

    fn stmt(&mut self, s: &S) -> Result<(), String> {
        match s {
            S::Let(n, ty, e, p) => {
                if self.params.contains(n) || n == "result" {
                    return self.err(*p, &format!("'{}' trùng tên tham số / từ khóa", n));
                }
                self.new_binding_ok(n, false, *p)?;
                let name = self.fresh_name(&mangle(n));
                let want = format!("%{}", name);
                let v = self.expr(e, Some(want.clone()), true)?;
                let v = match (ty, &v.t) {
                    (_, VT::Other) => return self.err(*p, "giá trị này không gán được"),
                    (Some(TyB::Int(b)), VT::Lit) => {
                        // `let x: u8 = 61;`: hằng -> khai báo thẳng bằng const (kiểm vừa bề rộng)
                        let raw = self.fit(v, *b, *p, "let")?;
                        self.emit(*p, format!("{} = const {} bv{}", want, raw.split(':').next().unwrap(), b));
                        V { s: want.clone(), t: VT::Int(*b) }
                    }
                    (Some(TyB::Int(b)), VT::Int(x) | VT::Bool(x)) if x == b => v,
                    (Some(TyB::Int(b)), _) => {
                        return self.err(*p, &format!("giá trị không phải u{}: dùng u{}(...) (thu hẹp có kiểm) hoặc u64(...)", b, b))
                    }
                    (Some(TyB::Ptr(..)), _) => {
                        if !matches!(v.t, VT::Ptr(..)) {
                            return self.err(*p, "giá trị không phải con trỏ");
                        }
                        v
                    }
                    (None, VT::Lit) => {
                        self.emit(*p, format!("{} = const {} bv64", want, v.s));
                        V { s: want.clone(), t: VT::Int(64) }
                    }
                    (None, _) => v,
                };
                self.scopes.last_mut().unwrap().insert(n.clone(), v);
                Ok(())
            }
            S::Store(place, e, p) => {
                let (c, off, bits, v) = match &place.k {
                    EK::Index(pe, ie) => {
                        let v = self.expr(e, None, true)?;
                        let (c, lay) = self.elem_ptr(pe, ie, place.p)?;
                        let f = self.single_field(&lay, place.p)?;
                        let s = self.fit(v, f.2, *p, "ghi bộ nhớ")?;
                        self.emit(*p, format!("store {} {} {}", c, f.1, s));
                        return Ok(());
                    }
                    EK::Field(be, f) => {
                        // vế phải TRƯỚC rồi mới tới chỗ ghi (như Rust), giống nhánh p[i] ở trên
                        let v = self.expr(e, None, true)?;
                        let (c, lay) = self.field_base(be)?;
                        let (off, bits) = self.field(&lay, f, place.p)?;
                        (c, off, bits, v)
                    }
                    _ => return self.err(place.p, "chỉ gán được vào bộ nhớ: p[i] = ..., p.f = ..., p[i].f = ... (biến: khai báo `var x = ...;` rồi `x = ...;`)"),
                };
                let s = self.fit(v, bits, *p, "ghi bộ nhớ")?;
                self.emit(*p, format!("store {} {} {}", c, off, s));
                Ok(())
            }
            S::Expr(e, p) => {
                if !matches!(e.k, EK::Call(..)) {
                    return self.err(*p, "câu lệnh chỉ là biểu thức thì vô ích (chỉ gọi hàm mới đứng riêng được)");
                }
                self.expr(e, None, true)?;
                Ok(())
            }
            S::Ret(e, p) => {
                match (e, self.ret.clone()) {
                    (None, None) => self.emit(*p, "ret".into()),
                    (Some(_), None) => return self.err(*p, "hàm không có kiểu trả về: dùng `return;`"),
                    (None, Some(_)) => return self.err(*p, "thiếu giá trị trả về"),
                    (Some(e), Some(t)) => {
                        let v = self.expr(e, None, true)?;
                        let s = match t {
                            TyB::Int(b) => self.fit(v, b, *p, "return")?,
                            TyB::Ptr(..) => v.s,
                        };
                        let s = s.split(':').next().unwrap().to_string(); // ret: parser tự gán kiểu hằng theo kiểu trả về
                        self.emit(*p, format!("ret {}", s));
                    }
                }
                self.term = true;
                Ok(())
            }
            S::If(c, then, els, p) => {
                let (lt, le, lj) = (self.new_label("then"), self.new_label("else"), self.new_label("endif"));
                let names = self.visible_vars();
                let env0 = self.snapshot(&names);
                self.cond(c, &lt, &le)?;
                self.label(*p, &lt);
                self.stmts(then)?;
                let mut edges = Vec::new();
                if !self.term {
                    let i = self.jmp_placeholder(*p, &lj);
                    edges.push((i, self.snapshot(&names)));
                }
                self.restore(&names, &env0);
                self.label(*p, &le); // luôn có block else: br không nhảy thẳng được tới block nối có tham số
                if let Some(es) = els {
                    self.stmts(es)?;
                }
                if !self.term {
                    let i = self.jmp_placeholder(*p, &lj);
                    edges.push((i, self.snapshot(&names)));
                }
                self.join(&lj, *p, &names, edges);
                Ok(())
            }
            S::Var(n, ty, e, p) => {
                self.new_binding_ok(n, true, *p)?;
                let name = format!("%{}", self.fresh_name(&mangle(n)));
                let v = self.expr(e, Some(name.clone()), true)?;
                let bits = match (ty, &v.t) {
                    (Some(TyB::Int(b)), _) => *b,
                    (None, VT::Int(b)) => *b,
                    (None, VT::Lit | VT::Bool(_)) => 64,
                    _ => return self.err(*p, "var chỉ cho số nguyên (con trỏ: dùng let)"),
                };
                let v = self.materialize(v, bits, &name, *p, "var")?;
                self.scopes.last_mut().unwrap().insert(n.clone(), v);
                self.vars.last_mut().unwrap().push(n.clone());
                Ok(())
            }
            S::Assign(n, e, p) => {
                let Some(cur) = self.lookup(n) else { return self.err(*p, &format!("không có biến '{}'", n)) };
                if !self.is_var(n) {
                    let what = if self.scopes[0].contains_key(n) && self.scopes.iter().skip(1).all(|s| !s.contains_key(n)) {
                        "tham số"
                    } else {
                        "let / chỉ số for"
                    };
                    return self.err(*p, &format!("'{}' là {}, không gán lại được: khai báo `var {} = ...;` để thay đổi", n, what, n));
                }
                let VT::Int(bits) = cur.t else { unreachable!() };
                let name = format!("%{}", self.fresh_name(&mangle(n)));
                let v = self.expr(e, Some(name.clone()), true)?;
                if v.t == VT::Other {
                    return self.err(*p, "giá trị này không gán được");
                }
                let v = self.materialize(v, bits, &name, *p, &format!("gán '{}' (u{})", n, bits))?;
                self.set_var(n, v);
                Ok(())
            }
            S::Assert(e, p) => {
                let names = self.names_map();
                let z = spec(e, &names, false, self.file)?;
                self.emit(*p, format!("assert {}", z));
                Ok(())
            }
            S::Break(p) | S::Continue(p) => {
                let Some(li) = self.loops.len().checked_sub(1) else {
                    return self.err(*p, "break / continue ngoài vòng lặp");
                };
                if matches!(s, S::Continue(_)) {
                    return self.back_jmp(li, *p);
                }
                let (vars, env0, modified) =
                    (self.loops[li].vars.clone(), self.loops[li].env0.clone(), self.loops[li].modified.clone());
                self.check_unmodified(&vars, &env0, &modified, *p)?;
                let done = format!("{}_done", self.loops[li].head);
                let i = self.jmp_placeholder(*p, &done);
                let env = self.snapshot(&vars);
                self.loops[li].breaks.push((i, env));
                Ok(())
            }
            S::While { cond, invs, dec, body, p, end } => {
                self.lower_loop(None, Some(cond), invs, dec.as_ref(), body, *p, *end)
            }
            S::For { var, from, to, invs, body, p, end } => {
                self.lower_loop(Some((var, from, to)), None, invs, None, body, *p, *end)
            }
        }
    }

    /// while / for. Đầu vòng = block có tham số cho [chỉ số for] + mọi biến var bị gán trong thân;
    /// `@inv` / `@dec` gắn ở đó. Ra khỏi vòng (điều kiện sai hoặc break) đi qua block nối `<đầu>_done`.
    #[allow(clippy::too_many_arguments)]
    fn lower_loop(
        &mut self,
        for_: Option<(&String, &E, &E)>,
        cond: Option<&E>,
        invs: &[E],
        dec: Option<&E>,
        body: &[S],
        p: Pos,
        end: Pos,
    ) -> Result<(), String> {
        let vars = self.visible_vars();
        let env0 = self.snapshot(&vars);
        let mut asg = HashSet::new();
        assigned(body, &mut asg);
        let modified: Vec<String> = vars.iter().filter(|n| asg.contains(*n)).cloned().collect();
        let head = self.new_label(if for_.is_some() { "for" } else { "while" });
        let (lb, lx, ld) = (format!("{}_body", head), format!("{}_exit", head), format!("{}_done", head));
        // for: cận dưới A, cận trên E = A + (B -| A) (a > b thì 0 vòng), tính MỘT lần trước vòng
        let mut fr = None;
        if let Some((iv, fe, te)) = for_ {
            self.new_binding_ok(iv, false, p)?;
            let a = self.expr(fe, None, false)?;
            let b = self.expr(te, None, false)?;
            self.int_operand(&a, fe.p)?;
            self.int_operand(&b, te.p)?;
            let a = if a.t == VT::Lit && a.s.parse::<u64>().is_err() {
                let d = self.dst(None);
                self.emit(fe.p, format!("{} = or {} 0", d, a.s));
                d
            } else {
                self.fit(a, 64, fe.p, "cận dưới của for")?
            };
            let b = self.fit(b, 64, te.p, "cận trên của for")?;
            let e = if a == "0" {
                b
            } else {
                let t = self.dst(None);
                self.emit(p, format!("{} = sub_sat {} {}", t, b, a));
                let e = self.dst(None);
                self.emit(p, format!("{} = add {} {}", e, a, t));
                e
            };
            let ir = format!("%{}", self.fresh_name(&mangle(iv)));
            fr = Some((iv.clone(), a, e, ir));
        }
        self.scopes.push(HashMap::new());
        self.vars.push(Vec::new());
        // cạnh vào
        let mut hparams = Vec::new();
        let mut entry_args = Vec::new();
        let mut head_line = format!("    @{}", head);
        if let Some((iv, a, _, ir)) = &fr {
            hparams.push(ir.clone());
            entry_args.push(a.clone());
            head_line.push_str(&format!(" {}:bv64", ir));
            self.scopes.last_mut().unwrap().insert(iv.clone(), V { s: ir.clone(), t: VT::Int(64) });
        }
        let mut hvals = Vec::new();
        for n in &modified {
            let v0 = self.lookup(n).unwrap();
            let VT::Int(b) = v0.t else { unreachable!() };
            let r = format!("%{}", self.fresh_name(&mangle(n)));
            entry_args.push(v0.s.clone());
            head_line.push_str(&format!(" {}:bv{}", r, b));
            hparams.push(r.clone());
            hvals.push((n.clone(), V { s: r, t: VT::Int(b) }));
        }
        let tail: String = entry_args.iter().map(|x| format!(" {}", x)).collect();
        self.emit(p, format!("jmp @{}{}", head, tail));
        self.out.push((head_line, self.org(p)));
        self.term = false;
        for (n, v) in hvals {
            self.set_var(&n, v);
        }
        // bất biến / biến giảm
        // của người viết TRƯỚC (số thứ tự @inv #k khớp `invariant` thứ k), rồi mới tới a <= i <= E tự sinh của for
        let names = self.names_map();
        for iv in invs {
            let z = spec(iv, &names, false, self.file)?;
            self.emit(iv.p, format!("@inv {}", z));
        }
        if let Some((_, a, e, ir)) = &fr {
            if a != "0" {
                self.emit(p, format!("@inv ule {} {}", a, ir));
            }
            self.emit(p, format!("@inv ule {} {}", ir, e));
        }
        if let Some((_, _, e, ir)) = &fr {
            self.emit(p, format!("@dec sub {} {}", e, ir));
        }
        if let Some(d) = dec {
            let z = spec_m(d, &names, false, true, self.file)?;
            self.emit(d.p, format!("@dec {}", z));
        }
        // điều kiện
        if let Some((_, _, e, ir)) = &fr {
            let c = self.dst(None);
            self.emit(p, format!("{} = cmp ult {} {}", c, ir, e));
            self.emit(p, format!("br {} @{} @{}", c, lb, lx));
            self.term = true;
        } else {
            self.cond(cond.unwrap(), &lb, &lx)?;
        }
        let hdr_env = self.snapshot(&vars);
        self.label(p, &lb);
        self.loops.push(Lp {
            head: head.clone(),
            hparams,
            idx: fr.as_ref().map(|f| f.3.clone()),
            vars: vars.clone(),
            env0: env0.clone(),
            modified,
            breaks: Vec::new(),
        });
        let r = self.stmts(body);
        let r = r.and_then(|_| if self.term { Ok(()) } else { self.back_jmp(self.loops.len() - 1, end) });
        let lp = self.loops.pop().unwrap();
        r?;
        // ra khỏi vòng
        self.restore(&vars, &hdr_env);
        self.label(p, &lx);
        let i = self.jmp_placeholder(p, &ld);
        let mut edges = vec![(i, hdr_env)];
        edges.extend(lp.breaks);
        self.scopes.pop();
        self.vars.pop();
        self.join(&ld, p, &vars, edges);
        Ok(())
    }
}

/// Vế phải của && / || không có điều kiện chứng minh -> tính thẳng bằng and/or (không cần rẽ nhánh)
fn is_safe(e: &E) -> bool {
    match &e.k {
        EK::Int(_) | EK::Name(_) => true,
        EK::Un(_, x) => is_safe(x),
        EK::Bin(op, a, b) => {
            // `<<` / `>>` có điều kiện (số bit < 64) nên KHÔNG an toàn
            matches!(*op, "==" | "!=" | "<" | "<=" | ">" | ">=" | "&&" | "||" | "&" | "|" | "^" | "+%" | "-%" | "*%" | "+|" | "-|" | "*|")
                && is_safe(a)
                && is_safe(b)
        }
        _ => false,
    }
}

/// Tên hằng / data / layout: bắt đầu bằng chữ HOA (biến và tham số viết thường)
fn is_const_name(n: &str) -> bool {
    n.chars().next().is_some_and(|c| c.is_ascii_uppercase())
}

fn cmp_name(op: &str) -> Option<&'static str> {
    Some(match op {
        "==" => "eq",
        "!=" => "ne",
        "<" => "ult",
        "<=" => "ule",
        ">" => "ugt",
        ">=" => "uge",
        _ => return None,
    })
}

fn bin_name(op: &str) -> Option<&'static str> {
    Some(match op {
        "+" => "add",
        "-" => "sub",
        "*" => "mul",
        "/" => "udiv",
        "%" => "urem",
        "+%" => "add_wrap",
        "-%" => "sub_wrap",
        "*%" => "mul_wrap",
        "+|" => "add_sat",
        "-|" => "sub_sat",
        "*|" => "mul_sat",
        "&" => "and",
        "|" => "or",
        "^" => "xor",
        "<<" => "shl",
        ">>" => "lshr",
        _ => return None,
    })
}

/// requires / ensures -> biểu thức Z3 tiền tố của SSA
/// `names`: tên người viết -> toán hạng SSA (tham số; trong invariant / decreases: mọi biến đang thấy)
/// `+ - * / %` là số học TOÁN HỌC (iadd ... imod: số nguyên không giới hạn, không quay vòng). Riêng `decreases` (`dec`):
/// phép bit-vector quay vòng — biến giảm chỉ cần giảm ngặt theo nghĩa không dấu nên cách hiểu nào cũng đúng cho việc dừng.
fn spec(e: &E, names: &HashMap<String, String>, ens: bool, file: &str) -> Result<String, String> {
    spec_m(e, names, ens, false, file)
}

fn spec_m(e: &E, names: &HashMap<String, String>, ens: bool, dec: bool, file: &str) -> Result<String, String> {
    let err = |p: Pos, m: &str| Err(format!("Dòng {}:{}:{}: {}", file, p.0, p.1, m));
    let r = |x: &E| spec_m(x, names, ens, dec, file);
    Ok(match &e.k {
        EK::Int(v) => v.to_string(),
        EK::Name(n) if n == "result" => {
            if !ens {
                return err(e.p, "`result` chỉ dùng trong ensures");
            }
            "%r".into()
        }
        EK::Name(n) if names.contains_key(n) => names[n].clone(),
        EK::Name(n) if n.chars().next().is_some_and(|c| c.is_ascii_uppercase()) || n.contains('.') => n.clone(),
        EK::Name(n) => return err(e.p, &format!("'{}' không phải tham số (requires / ensures chỉ nói về tham số, result và hằng HOA; invariant: biến đang thấy)", n)),
        EK::Call(n, a) if matches!(n.as_str(), "lt_s" | "le_s" | "gt_s" | "ge_s") && a.len() == 2 => {
            format!("s{} {} {}", &n[..2], r(&a[0])?, r(&a[1])?)
        }
        EK::Un("!", x) => format!("not {}", r(x)?),
        EK::Un(_, x) => format!("xor {} 0xffffffffffffffff", r(x)?),
        EK::Bin("==>", a, b) => format!("or not {} {}", r(a)?, r(b)?),
        EK::Bin("<==>", a, b) => {
            let (x, y) = (r(a)?, r(b)?);
            format!("and or not {} {} or not {} {}", x, y, y, x)
        }
        EK::Bin("&&", a, b) => format!("and {} {}", r(a)?, r(b)?),
        EK::Bin("||", a, b) => format!("or {} {}", r(a)?, r(b)?),
        EK::Bin(op, a, b) if cmp_name(op).is_some() => format!("{} {} {}", cmp_name(op).unwrap(), r(a)?, r(b)?),
        EK::Bin(op @ ("+" | "-" | "*" | "/" | "%"), a, b) => {
            let n = match (*op, dec) {
                ("+", false) => "iadd",
                ("-", false) => "isub",
                ("*", false) => "imul",
                ("/", false) => "idiv",
                ("%", false) => "imod",
                ("+", true) => "add",
                ("-", true) => "sub",
                ("*", true) => "mul",
                ("/", true) => "udiv",
                _ => "urem",
            };
            format!("{} {} {}", n, r(a)?, r(b)?)
        }
        EK::Bin(op, a, b) => {
            let n = match *op {
                "&" => "and",
                "|" => "or",
                "^" => "xor",
                "<<" => "shl",
                ">>" => "lshr",
                "+%" => "add_wrap",
                "-%" => "sub_wrap",
                "*%" => "mul_wrap",
                _ => return err(e.p, &format!("`{}` không dùng được trong đặc tả", op)),
            };
            format!("{} {} {}", n, r(a)?, r(b)?)
        }
        EK::Field(b, f) if matches!(&b.k, EK::Name(n) if is_const_name(n)) => {
            let EK::Name(n) = &b.k else { unreachable!() };
            format!("{}.{}", n, f) // DATA.len / Layout.trường: hằng
        }
        EK::Index(a, i) => {
            let EK::Name(n) = &a.k else { return err(e.p, "đặc tả: chỉ đọc được p[i] với p là tên con trỏ") };
            let Some(pr) = names.get(n) else { return err(a.p, &format!("'{}' không phải con trỏ nhìn thấy được ở đây", n)) };
            format!("mem {} {} 0", pr, r(i)?)
        }
        EK::Range(..) | EK::Field(..) => {
            return err(e.p, "đặc tả: chưa đọc được p.trường / p[a..b] (P3 giai đoạn sau); dùng p[i]")
        }
        EK::Call(n, a) if n == "old" && a.len() == 1 => format!("old {}", r(&a[0])?),
        EK::Call(n, a) if SPECS.with(|s| s.borrow().contains_key(n)) => {
            let k = SPECS.with(|s| s.borrow()[n]);
            if a.len() != k {
                return err(e.p, &format!("hàm spec '{}' nhận {} đối số, gọi với {}", n, k, a.len()));
            }
            let mut out = format!("app {} {}", n, k);
            for x in a {
                out.push(' ');
                out.push_str(&r(x)?);
            }
            out
        }
        EK::IfE(c, a, b) => format!("ite {} {} {}", r(c)?, r(a)?, r(b)?),
        EK::Quant(all, v, lo, hi, body) => {
            if names.contains_key(v) || v == "result" {
                return err(e.p, &format!("biến lượng từ '{}' trùng tên đang dùng: đặt tên khác", v));
            }
            let mut n2 = names.clone();
            let bound = format!("%q_{}_{}_{}", v, e.p.0, e.p.1);
            n2.insert(v.clone(), bound.clone());
            let rb = |x: &E| spec_m(x, &n2, ens, dec, file);
            format!("{} {} {} {} {}", if *all { "forall" } else { "exists" }, bound, r(lo)?, r(hi)?, rb(body)?)
        }
        EK::Call(n, _) => return err(e.p, &format!("gọi '{}' trong đặc tả: chưa có hàm spec (P3)", n)),
    })
}

/// Hạ file `.lt` -> các dòng SSA kèm vị trí gốc "file:dòng:cột"
pub fn lower_file(path: &Path) -> Result<Vec<(String, String)>, String> {
    let src = std::fs::read_to_string(path).map_err(|e| format!("Lỗi đọc '{}': {}", path.display(), e))?;
    let file = path.display().to_string();
    let toks = lex(&src, &file)?;
    let items = Ps { t: toks, i: 0, file: &file }.items()?;
    let dir = path.parent().unwrap_or(Path::new("."));
    let org = |p: Pos| format!("{}:{}:{}", file, p.0, p.1);
    let mut out: Vec<(String, String)> = Vec::new();
    let mut decls = Decls::default();
    let mut defined = HashSet::new();
    SPECS.with(|s| s.borrow_mut().clear());

    for it in &items {
        match it {
            Item::Include(s, p) => {
                let inc = dir.join(s);
                let m = crate::parser::parse_file(&inc.display().to_string())
                    .map_err(|e| format!("Dòng {}: include '{}' lỗi:\n{}", org(*p), s, e))?;
                decls.add_module(&m);
                SPECS.with(|t| {
                    for sp in &m.specs {
                        t.borrow_mut().insert(sp.name.clone(), sp.params.len());
                    }
                });
                out.push((format!("include {}", s), org(*p)));
            }
            Item::Const(n, v, p) => {
                if !n.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
                    return Err(format!("Dòng {}: tên hằng phải bắt đầu bằng chữ HOA (vd {})", org(*p), n.to_uppercase()));
                }
                out.push((format!("def {} {}", n, v), org(*p)))
            }
            Item::Data(n, lay, vals, p) => {
                decls.datas.insert(n.clone(), lay.clone());
                out.push((format!("data {} {} {{", n, lay), org(*p)));
                out.push((format!("    {}", vals.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" ")), org(*p)));
                out.push(("}".into(), org(*p)));
            }
            Item::Fn(f) => {
                if !defined.insert(f.name.clone()) {
                    return Err(format!("Dòng {}: hàm '{}' bị định nghĩa hai lần", org(f.p), f.name));
                }
                let ret = f.ret.as_ref().map(|t| match t {
                    TyB::Int(b) => VT::Int(*b),
                    TyB::Ptr(l, n) if n.parse::<u64>().is_ok() || is_const_name(n) => VT::Ptr(l.clone(), n.clone()),
                    TyB::Ptr(..) => VT::Other,
                });
                decls.funcs.insert(f.name.clone(), Sig { nparams: f.params.len(), ret });
            }
            Item::Spec(_) => {}
        }
    }

    // hàm spec: hạ TRƯỚC mọi hàm (SSA cần khai báo trước khi dùng); một hàm spec chỉ gọi chính nó hoặc hàm spec trước nó
    for it in &items {
        let Item::Spec(sp) = it else { continue };
        if !defined.insert(sp.name.clone()) || SPECS.with(|s| s.borrow().contains_key(&sp.name)) {
            return Err(format!("Dòng {}: '{}' bị định nghĩa hai lần", org(sp.p), sp.name));
        }
        let params: HashSet<String> = sp.params.iter().map(|p| p.0.clone()).collect();
        let mut sig = format!("spec {} int", sp.name);
        for (n, t, pp) in &sp.params {
            check_ident(n, &file, *pp)?;
            sig.push_str(&format!(" %{}:{}", mangle(n), ssa_ty(t, &params)));
        }
        out.push((format!("{} {{", sig), org(sp.p)));
        SPECS.with(|s| s.borrow_mut().insert(sp.name.clone(), sp.params.len()));
        let pmap: HashMap<String, String> = params.iter().map(|n| (n.clone(), format!("%{}", mangle(n)))).collect();
        if let Some(d) = &sp.dec {
            out.push((format!("    @dec {}", spec(d, &pmap, false, &file)?), org(d.p)));
        }
        out.push((format!("    @def {}", spec(&sp.body, &pmap, false, &file)?), org(sp.body.p)));
        out.push(("}".into(), org(sp.p)));
    }

    for it in &items {
        let Item::Fn(f) = it else { continue };
        let params: HashSet<String> = f.params.iter().map(|p| p.0.clone()).collect();
        let mut sig = format!("func {} {}", f.name, f.ret.as_ref().map_or("void".into(), |t| ssa_ty(t, &params)));
        let mut seen = HashSet::new();
        for (n, t, pp) in &f.params {
            if !seen.insert(n.clone()) || n == "result" {
                return Err(format!("Dòng {}: tham số '{}' trùng tên / là từ khóa", org(*pp), n));
            }
            if let TyB::Ptr(_, len) = t {
                let ok_len = seen.contains(len) && len != n
                    || len.parse::<u64>().is_ok()
                    || len.chars().next().is_some_and(|c| c.is_ascii_uppercase());
                if !ok_len {
                    return Err(format!(
                        "Dòng {}: độ dài '{}' của ptr phải là tham số đứng TRƯỚC, hằng HOA hoặc số",
                        org(*pp), len
                    ));
                }
            }
            check_ident(n, &file, *pp)?;
            sig.push_str(&format!(" %{}:{}", mangle(n), ssa_ty(t, &params)));
        }
        out.push((format!("{} {{", sig), org(f.p)));
        let pmap: HashMap<String, String> = params.iter().map(|n| (n.clone(), format!("%{}", mangle(n)))).collect();
        for e in &f.req {
            out.push((format!("    @req {}", spec(e, &pmap, false, &file)?), org(e.p)));
        }
        for e in &f.ens {
            // hàm không trả giá trị: ensures nói về bộ nhớ (vd `a[t] == old(...)`), không có `result`
            out.push((format!("    @ens {}", spec(e, &pmap, f.ret.is_some(), &file)?), org(e.p)));
        }
        out.push(("    @entry".into(), org(f.p)));
        let mut scope = HashMap::new();
        for (n, t, _) in &f.params {
            scope.insert(n.clone(), V { s: format!("%{}", mangle(n)), t: vt_of(t, &params) });
        }
        let mut fx = Fx {
            file: &file,
            out: &mut out,
            decls: &decls,
            tmp: 0,
            lbl: 0,
            scopes: vec![scope],
            used: params.iter().map(|n| mangle(n)).collect(),
            term: false,
            ret: f.ret.clone(),
            params: params.clone(),
            vars: vec![Vec::new()],
            loops: Vec::new(),
        };
        fx.stmts(&f.body)?;
        if !fx.term {
            if f.ret.is_some() {
                return fx.err(f.p, &format!("hàm '{}' có thể chạy hết thân mà không return", f.name));
            }
            fx.out.push(("        ret".into(), org(f.p)));
        }
        out.push(("}".into(), org(f.p)));
    }
    Ok(out)
}
