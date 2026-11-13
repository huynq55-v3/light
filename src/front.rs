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
use std::collections::{HashMap, HashSet};
use std::path::Path;

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
    "<==>", "==>", "+%", "-%", "*%", "+|", "-|", "*|", "<<", ">>", "<=", ">=", "==", "!=", "&&", "||", "->", "..",
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

enum Item {
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
                _ => {
                    self.i -= 1;
                    return self.err(&format!("cần include / const / data / fn, gặp '{}'", kw));
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
        self.expect("{")?;
        let mut out = Vec::new();
        while !self.eat("}") {
            if *self.peek() == Tok::Eof {
                return self.err("thiếu '}'");
            }
            out.push(self.stmt()?);
        }
        Ok(out)
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
        if self.is_kw("return") {
            self.i += 1;
            let e = if self.is(";") { None } else { Some(self.expr(0)?) };
            self.expect(";")?;
            return Ok(S::Ret(e, p));
        }
        for kw in ["while", "for", "loop", "var", "break", "continue"] {
            if self.is_kw(kw) {
                return self.err(&format!("'{}' chưa có (P2: vòng lặp và biến thay đổi được)", kw));
            }
        }
        let e = self.expr(0)?;
        if self.eat("=") {
            let v = self.expr(0)?;
            self.expect(";")?;
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
        for s in ss {
            let p = match s {
                S::Let(.., p) | S::Store(.., p) | S::Expr(_, p) | S::If(.., p) | S::Ret(_, p) => *p,
            };
            if self.term {
                return self.err(p, "câu lệnh không bao giờ chạy tới (sau return)");
            }
            self.stmt(s)?;
        }
        self.scopes.pop();
        Ok(())
    }

    fn stmt(&mut self, s: &S) -> Result<(), String> {
        match s {
            S::Let(n, ty, e, p) => {
                if self.params.contains(n) || n == "result" {
                    return self.err(*p, &format!("'{}' trùng tên tham số / từ khóa", n));
                }
                check_ident(n, self.file, *p)?;
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
                    _ => return self.err(place.p, "chỉ gán được vào bộ nhớ: p[i] = ..., p.f = ..., p[i].f = ... (biến thay đổi được: P2)"),
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
                let f = if els.is_some() { le.clone() } else { lj.clone() };
                self.cond(c, &lt, &f)?;
                self.label(*p, &lt);
                self.stmts(then)?;
                let mut join = !self.term;
                if join {
                    self.emit(*p, format!("jmp @{}", lj));
                    self.term = true;
                }
                if let Some(es) = els {
                    self.label(*p, &le);
                    self.stmts(es)?;
                    if !self.term {
                        self.emit(*p, format!("jmp @{}", lj));
                        self.term = true;
                        join = true;
                    }
                } else {
                    join = true;
                }
                if join {
                    self.label(*p, &lj);
                }
                Ok(())
            }
        }
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
fn spec(e: &E, params: &HashSet<String>, ens: bool, file: &str) -> Result<String, String> {
    let err = |p: Pos, m: &str| Err(format!("Dòng {}:{}:{}: {}", file, p.0, p.1, m));
    let r = |x: &E| spec(x, params, ens, file);
    Ok(match &e.k {
        EK::Int(v) => v.to_string(),
        EK::Name(n) if n == "result" => {
            if !ens {
                return err(e.p, "`result` chỉ dùng trong ensures");
            }
            "%r".into()
        }
        EK::Name(n) if params.contains(n) => format!("%{}", mangle(n)),
        EK::Name(n) if n.chars().next().is_some_and(|c| c.is_ascii_uppercase()) || n.contains('.') => n.clone(),
        EK::Name(n) => return err(e.p, &format!("'{}' không phải tham số (đặc tả chỉ nói về tham số, result và hằng HOA)", n)),
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
        EK::Bin(op @ ("+" | "-" | "*"), ..) => {
            return err(
                e.p,
                &format!(
                    "`{}` trong đặc tả: chưa có số học toán học (P3). Dùng `{}%` nếu chấp nhận quay vòng mod 2^64",
                    op, op
                ),
            )
        }
        EK::Bin(op, a, b) => {
            let n = match *op {
                "&" => "and",
                "|" => "or",
                "^" => "xor",
                "<<" => "shl",
                ">>" => "lshr",
                "/" => "udiv",
                "%" => "urem",
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
        EK::Index(..) | EK::Range(..) | EK::Field(..) => {
            return err(e.p, "đặc tả chưa nói được về nội dung bộ nhớ (P3: forall / old)")
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

    for it in &items {
        match it {
            Item::Include(s, p) => {
                let inc = dir.join(s);
                let m = crate::parser::parse_file(&inc.display().to_string())
                    .map_err(|e| format!("Dòng {}: include '{}' lỗi:\n{}", org(*p), s, e))?;
                decls.add_module(&m);
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
                    TyB::Ptr(..) => VT::Other,
                });
                decls.funcs.insert(f.name.clone(), Sig { nparams: f.params.len(), ret });
            }
        }
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
        for e in &f.req {
            out.push((format!("    @req {}", spec(e, &params, false, &file)?), org(e.p)));
        }
        for e in &f.ens {
            if f.ret.is_none() {
                return Err(format!("Dòng {}: hàm không trả giá trị thì ensures chưa có gì để nói (P3: old/modifies)", org(e.p)));
            }
            out.push((format!("    @ens {}", spec(e, &params, true, &file)?), org(e.p)));
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
