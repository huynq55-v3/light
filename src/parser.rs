//! Parser dòng phẳng (Flat SSA Parser) & Pratt Expression Parser cho Light (.lit)
//! Thiết kế tối giản, tốc độ cao: dùng 1 bộ Single-Pass Tokenizer chung cho toàn bộ chỉ thị, câu lệnh và biểu thức.

use crate::ast::*;
use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Debug, Clone, PartialEq)]
enum Token {
    Ident(String), // Tên lệnh, tên biến/thanh ghi (%x, x), hoặc nhãn (.lbl)
    Int(i64),      // Hằng số nguyên có dấu (0..=i64::MAX)
    UInt(u64),     // Hằng số nguyên lớn > i64::MAX
    Bool(bool),    // true | false
    Str(String),   // Chuỗi ký tự đã unescape trong "..."
    TypeTok(Type), // Kiểu dữ liệu: i64, u64, u8, bool, ptr, arr<T, N>, slice<T>
    Len(String),   // Biểu thức/toán hạng độ dài: len(%arr)
    EqAssign,      // Dấu '='
    Arrow,         // Dấu '->'
    Colon,         // Dấu ':'
    Comma,         // Dấu ','
    LParen,        // Dấu '('
    RParen,        // Dấu ')'
    Bang,          // Toán tử 1 ngôi '!'
    Minus,         // Dấu '-' (trừ 2 ngôi hoặc âm 1 ngôi)
    Op(BinOp), // Các toán tử 2 ngôi còn lại (+, *, /, %, ==, !=, <=, >=, <, >, <<, >>, &&, ||, &, |, ^)
}

#[derive(Debug, Clone)]
pub struct ParseError {
    pub line_no: usize,
    pub message: String,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Syntax error at line {}: {}", self.line_no, self.message)
    }
}

impl std::error::Error for ParseError {}

/// Bộ đọc Token tuần tự giúp loại bỏ việc truyền `(tokens, &mut pos, line_no)` lặp lại
struct TokenCursor<'a> {
    tokens: &'a [Token],
    pos: usize,
    line_no: usize,
}

impl<'a> TokenCursor<'a> {
    #[inline]
    fn new(tokens: &'a [Token], line_no: usize) -> Self {
        Self {
            tokens,
            pos: 0,
            line_no,
        }
    }

    #[inline]
    fn peek(&self) -> Option<&'a Token> {
        self.tokens.get(self.pos)
    }

    #[inline]
    fn next(&mut self) -> Option<&'a Token> {
        let tok = self.tokens.get(self.pos)?;
        self.pos += 1;
        Some(tok)
    }

    #[inline]
    fn is_eof(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    fn eat(&mut self, expected: &Token) -> bool {
        if self.peek() == Some(expected) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_type(&mut self) -> Option<Type> {
        if let Some(Token::TypeTok(ty)) = self.peek() {
            let res = ty.clone();
            self.pos += 1;
            Some(res)
        } else {
            None
        }
    }

    fn next_ident(&mut self, syntax: &str) -> Result<String, ParseError> {
        match self.next() {
            Some(Token::Ident(s)) => Ok(s.clone()),
            _ => Err(Parser::err(self.line_no, format!("Syntax: {}", syntax))),
        }
    }

    fn next_usize(&mut self, label: &str) -> Result<usize, ParseError> {
        match self.next() {
            Some(Token::Int(n)) if *n >= 0 => Ok(*n as usize),
            Some(Token::UInt(u)) => Ok(*u as usize),
            _ => Err(Parser::err(
                self.line_no,
                format!("{} must be a positive integer", label),
            )),
        }
    }

    fn next_operand(&mut self) -> Result<Operand, ParseError> {
        let Some(tok) = self.next() else {
            return Err(Parser::err(self.line_no, "Missing operand"));
        };
        match tok {
            Token::Ident(s) => Ok(Operand::Reg(s.clone())),
            Token::Len(inner) => Ok(Operand::Reg(format!("len({})", inner))),
            Token::Bool(b) => Ok(Operand::Const(Value::Bool(*b))),
            Token::Int(n) => Ok(Operand::Const(Value::I64(*n))),
            Token::UInt(u) => Ok(Operand::Const(Value::U64(*u))),
            Token::Minus => match self.next() {
                Some(Token::Int(n)) => Ok(Operand::Const(Value::I64(n.wrapping_neg()))),
                Some(Token::UInt(9223372036854775808)) => Ok(Operand::Const(Value::I64(i64::MIN))),
                _ => Err(Parser::err(
                    self.line_no,
                    "Expected integer literal after '-' in operand",
                )),
            },
            other => Err(Parser::err(
                self.line_no,
                format!("Invalid operand: {:?}", other),
            )),
        }
    }

    fn expect_eof(&self, context: &str) -> Result<(), ParseError> {
        if let Some(tok) = self.peek() {
            Err(Parser::err(
                self.line_no,
                format!("Unexpected trailing token in {}: {:?}", context, tok),
            ))
        } else {
            Ok(())
        }
    }
}

pub struct Parser;

impl Parser {
    #[inline]
    fn err(line_no: usize, msg: impl Into<String>) -> ParseError {
        ParseError {
            line_no,
            message: msg.into(),
        }
    }

    /// Nạp và parse file gốc kèm tất cả các file được IMPORT đệ quy
    pub fn parse_file<P: AsRef<Path>>(file_path: P) -> Result<Program, ParseError> {
        let mut visited = HashSet::new();
        let mut all_functions = Vec::new();
        Self::parse_file_recursive(file_path.as_ref(), &mut visited, &mut all_functions)?;
        Ok(Program {
            functions: all_functions,
        })
    }

    fn parse_file_recursive(
        path: &Path,
        visited: &mut HashSet<PathBuf>,
        all_functions: &mut Vec<Function>,
    ) -> Result<(), ParseError> {
        let canonical = fs::canonicalize(path).map_err(|e| {
            Self::err(
                0,
                format!("Cannot find import file '{}': {}", path.display(), e),
            )
        })?;

        if !visited.insert(canonical.clone()) {
            return Ok(());
        }

        let source = fs::read_to_string(&canonical).map_err(|e| {
            Self::err(
                0,
                format!("Cannot read file '{}': {}", canonical.display(), e),
            )
        })?;

        let parent_dir = canonical.parent().unwrap_or_else(|| Path::new("."));
        let mut functions = Vec::new();
        Self::parse_lines(
            &source,
            &canonical.display().to_string(),
            Some((parent_dir, visited)),
            &mut functions,
        )?;

        for func in functions {
            if all_functions.iter().any(|f| f.name == func.name) {
                return Err(Self::err(
                    func.start_line,
                    format!("Duplicate function definition: '{}'", func.name),
                ));
            }
            all_functions.push(func);
        }

        Ok(())
    }

    /// Parse từ chuỗi (không kèm import ngoài)
    pub fn parse(source: &str) -> Result<Program, ParseError> {
        let mut functions = Vec::new();
        Self::parse_lines(source, "<memory>", None, &mut functions)?;
        Ok(Program { functions })
    }

    fn parse_lines(
        source: &str,
        file_label: &str,
        mut import_ctx: Option<(&Path, &mut HashSet<PathBuf>)>,
        out_functions: &mut Vec<Function>,
    ) -> Result<(), ParseError> {
        let mut current_func: Option<Function> = None;

        for (idx, raw_line) in source.lines().enumerate() {
            let line_no = idx + 1;
            let (tokens, clean_slice) = Self::tokenize_line_with_clean(raw_line, line_no)?;
            if tokens.is_empty() {
                continue;
            }

            if let Token::Ident(kw) = &tokens[0] {
                match kw.as_str() {
                    "IMPORT" => {
                        if current_func.is_some() {
                            return Err(Self::err(
                                line_no,
                                "IMPORT directives must be placed at the file top-level outside functions",
                            ));
                        }
                        let (Some(Token::Str(import_rel_path)), 2) = (tokens.get(1), tokens.len())
                        else {
                            return Err(Self::err(
                                line_no,
                                "IMPORT syntax requires double quotes: IMPORT \"file.lit\"",
                            ));
                        };
                        if let Some((parent_dir, ref mut visited)) = import_ctx {
                            let resolved_path = parent_dir.join(import_rel_path);
                            Self::parse_file_recursive(&resolved_path, visited, out_functions)?;
                        }
                        continue;
                    }
                    "FUNC" => {
                        if current_func.is_some() {
                            return Err(Self::err(
                                line_no,
                                "Nested function definitions are not allowed",
                            ));
                        }
                        current_func =
                            Some(Self::parse_func_signature(&tokens, file_label, line_no)?);
                        continue;
                    }
                    "END_FUNC" => {
                        if tokens.len() > 1 {
                            return Err(Self::err(line_no, "Unexpected tokens after END_FUNC"));
                        }
                        let Some(func) = current_func.take() else {
                            return Err(Self::err(
                                line_no,
                                "Encountered END_FUNC without an active function block",
                            ));
                        };
                        if out_functions.iter().any(|f| f.name == func.name) {
                            return Err(Self::err(
                                line_no,
                                format!("Duplicate function definition: '{}'", func.name),
                            ));
                        }
                        out_functions.push(func);
                        continue;
                    }
                    _ => {}
                }
            }

            let first_word = match &tokens[0] {
                Token::Ident(s) => s.as_str(),
                _ => "<token>",
            };
            let func = current_func.as_mut().ok_or_else(|| {
                Self::err(
                    line_no,
                    format!(
                        "Instruction '{}' must be placed inside a FUNC ... END_FUNC block",
                        first_word
                    ),
                )
            })?;

            let clean_text = clean_slice.to_string();
            let inst = Self::parse_instruction_tokens(&tokens, &clean_text, line_no)?;
            func.instructions.push(SpannedInstruction {
                inst,
                loc: Loc {
                    file: file_label.to_string(),
                    line: line_no,
                    text: clean_text,
                },
            });
        }

        if let Some(func) = current_func {
            return Err(Self::err(
                0,
                format!("Function '{}' was not closed with END_FUNC", func.name),
            ));
        }

        Ok(())
    }

    pub fn parse_type(s: &str, line_no: usize) -> Result<Type, ParseError> {
        let s = s.trim();
        match s {
            "i64" => Ok(Type::I64),
            "u64" => Ok(Type::U64),
            "u8" => Ok(Type::U8),
            "f64" => Err(Self::err(
                line_no,
                "Floating-point type 'f64' is not yet supported in Light SMT verifier (planned for future QF_FP support)",
            )),
            "bool" => Ok(Type::Bool),
            "ptr" => Ok(Type::Ptr),
            _ if s.starts_with("arr<") && s.ends_with('>') => {
                let inner = &s[4..s.len() - 1];
                // Dùng rsplit_once để hỗ trợ mảng nhiều chiều: arr<arr<u8, 4>, 10>
                let (elem_str, size_str) = inner.rsplit_once(',').ok_or_else(|| {
                    Self::err(
                        line_no,
                        format!("Malformed array type: '{}'. Expected: arr<type, size>", s),
                    )
                })?;
                let elem_ty = Self::parse_type(elem_str.trim(), line_no)?;
                let size = size_str.trim().parse::<usize>().map_err(|_| {
                    Self::err(
                        line_no,
                        format!("Array size must be a positive integer: {}", size_str.trim()),
                    )
                })?;
                Ok(Type::Array(Box::new(elem_ty), size))
            }
            _ if s.starts_with("slice<") && s.ends_with('>') => {
                let inner = &s[6..s.len() - 1];
                let elem_ty = Self::parse_type(inner.trim(), line_no)?;
                Ok(Type::Slice(Box::new(elem_ty)))
            }
            _ => Err(Self::err(
                line_no,
                format!(
                    "Unsupported type: '{}'. Supported: i64, u64, u8, bool, ptr, arr<T, N>, slice<T>",
                    s
                ),
            )),
        }
    }

    fn parse_func_signature(
        tokens: &[Token],
        file: &str,
        line_no: usize,
    ) -> Result<Function, ParseError> {
        // Kỳ vọng: FUNC <name> ( [param : type , ...] ) [-> ret_type]
        let mut cur = TokenCursor::new(tokens, line_no);
        cur.next(); // Bỏ qua từ khóa "FUNC"

        let name = cur
            .next_ident("FUNC <name>(...)")
            .map_err(|_| Self::err(line_no, "Function name cannot be empty"))?;

        if !cur.eat(&Token::LParen) {
            return Err(Self::err(line_no, "Missing '(' in FUNC signature"));
        }

        let mut params = Vec::new();
        while !cur.is_eof() && cur.peek() != Some(&Token::RParen) {
            let p_name = cur
                .next_ident("param: type")
                .map_err(|_| Self::err(line_no, "Expected parameter name in FUNC signature"))?;

            if !cur.eat(&Token::Colon) {
                return Err(Self::err(
                    line_no,
                    format!(
                        "Malformed parameter declaration '{}' (expected: name: type)",
                        p_name
                    ),
                ));
            }
            let Some(p_ty) = cur.eat_type() else {
                return Err(Self::err(
                    line_no,
                    format!("Expected valid type for parameter '{}'", p_name),
                ));
            };
            params.push(Param {
                name: p_name,
                ty: p_ty,
            });

            if !cur.eat(&Token::Comma) && cur.peek() != Some(&Token::RParen) {
                return Err(Self::err(
                    line_no,
                    "Expected ',' or ')' after parameter declaration",
                ));
            }
        }

        if !cur.eat(&Token::RParen) {
            return Err(Self::err(line_no, "Missing ')' in FUNC signature"));
        }

        let return_ty = if cur.eat(&Token::Arrow) {
            let Some(ret_ty) = cur.eat_type() else {
                return Err(Self::err(line_no, "Expected return type after '->'"));
            };
            Some(ret_ty)
        } else {
            None
        };

        cur.expect_eof("FUNC signature")?;

        Ok(Function {
            name,
            file: file.to_string(),
            start_line: line_no,
            params,
            return_ty,
            instructions: Vec::new(),
        })
    }

    fn parse_instruction_tokens(
        tokens: &[Token],
        raw_line: &str,
        line_no: usize,
    ) -> Result<Instruction, ParseError> {
        let mut cur = TokenCursor::new(tokens, line_no);
        if cur.is_eof() {
            return Err(Self::err(line_no, "Empty instruction line"));
        }

        // 1. Chỉ thị kiểm chứng toán học (Z3 Directives): REQUIRE, ENSURE, INVARIANT, DECREASES, ASSERT
        if let Some(Token::Ident(kw)) = cur.peek() {
            if matches!(
                kw.as_str(),
                "REQUIRE" | "ENSURE" | "INVARIANT" | "DECREASES" | "ASSERT"
            ) {
                let kw = kw.as_str();
                cur.next();
                if cur.is_eof() {
                    return Err(Self::err(
                        line_no,
                        format!("Missing expression after {}", kw),
                    ));
                }
                let expr = Self::parse_expr_bp(&mut cur, 0)?;
                cur.expect_eof(kw)?;
                return Ok(match kw {
                    "REQUIRE" => Instruction::Require(expr),
                    "ENSURE" => Instruction::Ensure(expr),
                    "INVARIANT" => Instruction::Invariant(expr),
                    "DECREASES" => Instruction::Decreases(expr),
                    _ => Instruction::Assert(expr),
                });
            }
        }

        // 2. Tách phần `%dest =` (nếu có)
        let dest = if tokens.len() >= 3 && tokens[1] == Token::EqAssign {
            let Token::Ident(d) = &tokens[0] else {
                return Err(Self::err(
                    line_no,
                    "Invalid destination register before '='",
                ));
            };
            cur.pos = 2;
            Some(d.clone())
        } else {
            None
        };

        let Some(Token::Ident(op_str)) = cur.next() else {
            return Err(Self::err(
                line_no,
                format!("Unrecognized instruction: '{}'", raw_line),
            ));
        };
        let op = op_str.as_str();

        // 3. Các lệnh dùng chung cho cả có `dest` và không có `dest`: CALL, SYSCALL, ALLOC
        let inst = match op {
            "CALL" => {
                let func_name = cur.next_ident("[%dest =] CALL func_name arg1 ...")?;
                let mut args = Vec::new();
                while !cur.is_eof() {
                    args.push(cur.next_operand()?);
                }
                Instruction::Call {
                    dest,
                    func_name,
                    args,
                }
            }
            "SYSCALL" => {
                if cur.is_eof() && dest.is_none() {
                    Instruction::Syscall {
                        dest: None,
                        rax: Operand::Reg("%rax".into()),
                        rdi: Operand::Reg("%rdi".into()),
                        rsi: Operand::Reg("%rsi".into()),
                        rdx: Operand::Reg("%rdx".into()),
                        r10: None,
                        r8: None,
                        r9: None,
                    }
                } else {
                    let rax = cur.next_operand()?;
                    let rdi = cur.next_operand()?;
                    let rsi = cur.next_operand()?;
                    let rdx = cur.next_operand()?;
                    let r10 = if !cur.is_eof() {
                        Some(cur.next_operand()?)
                    } else {
                        None
                    };
                    let r8 = if !cur.is_eof() {
                        Some(cur.next_operand()?)
                    } else {
                        None
                    };
                    let r9 = if !cur.is_eof() {
                        Some(cur.next_operand()?)
                    } else {
                        None
                    };
                    Instruction::Syscall {
                        dest,
                        rax,
                        rdi,
                        rsi,
                        rdx,
                        r10,
                        r8,
                        r9,
                    }
                }
            }
            "ALLOC" => match dest {
                None => {
                    let buf = cur.next_ident("ALLOC %buf <size>")?;
                    let len = cur.next_usize("Allocation size")?;
                    Instruction::Alloc {
                        dest: buf,
                        elem_ty: Type::U8,
                        len,
                    }
                }
                Some(d) => match cur.peek() {
                    Some(Token::TypeTok(Type::Slice(elem))) => {
                        let elem_ty = (**elem).clone();
                        cur.next();
                        let len = cur.next_usize("Slice length")?;
                        Instruction::Alloc {
                            dest: d,
                            elem_ty,
                            len,
                        }
                    }
                    Some(Token::TypeTok(_)) => {
                        return Err(Self::err(
                            line_no,
                            "ALLOC expects a slice<T> type or direct size",
                        ));
                    }
                    _ => {
                        let len = cur.next_usize("Allocation size")?;
                        Instruction::Alloc {
                            dest: d,
                            elem_ty: Type::U8,
                            len,
                        }
                    }
                },
            },

            // 4. Các lệnh chia theo nhóm không có `dest` vs có `dest`
            _ => match dest {
                None => match op {
                    "LABEL" | "JUMP" | "BREAK_IF" | "CONTINUE_IF" => {
                        let arg = cur.next_ident(&format!("{} <target>", op))?;
                        match op {
                            "LABEL" => Instruction::Label(arg),
                            "JUMP" => Instruction::Jump(arg),
                            "BREAK_IF" => Instruction::BreakIf(arg),
                            _ => Instruction::ContinueIf(arg),
                        }
                    }
                    "LOOP" | "END_LOOP" => {
                        let lbl = match cur.peek() {
                            Some(Token::Ident(s)) => {
                                let s = s.clone();
                                cur.next();
                                s
                            }
                            _ => "loop".to_string(),
                        };
                        if op == "LOOP" {
                            Instruction::Loop(lbl)
                        } else {
                            Instruction::EndLoop(lbl)
                        }
                    }
                    "BR_IF" | "BRANCH_IF" => {
                        let cond = cur.next_ident("BR_IF %cond <label>")?;
                        let target = cur.next_ident("BR_IF %cond <label>")?;
                        Instruction::BrIf { cond, target }
                    }
                    "RET" => {
                        let val = if !cur.is_eof() {
                            Some(cur.next_operand()?)
                        } else {
                            None
                        };
                        Instruction::Ret(val)
                    }
                    "RET_IF" => {
                        let cond = cur.next_ident("RET_IF %cond [%val]")?;
                        let val = if !cur.is_eof() {
                            Some(cur.next_operand()?)
                        } else {
                            None
                        };
                        Instruction::RetIf { cond, val }
                    }
                    "STORE8" | "STORE64" => {
                        let buf = cur.next_ident(&format!("{} %buf offset val", op))?;
                        let offset = cur.next_operand()?;
                        let val = cur.next_operand()?;
                        if op == "STORE8" {
                            Instruction::Store8 { buf, offset, val }
                        } else {
                            Instruction::Store64 { buf, offset, val }
                        }
                    }
                    "STORE_STR" => {
                        let buf = cur.next_ident("STORE_STR %buf [offset] \"string\"")?;
                        let (offset, content) = match (cur.next(), cur.peek()) {
                            (Some(Token::Str(s)), None) => (0usize, s.clone()),
                            (Some(Token::Int(off)), Some(Token::Str(_))) if *off >= 0 => {
                                let off = *off as usize;
                                let Some(Token::Str(s)) = cur.next() else {
                                    unreachable!()
                                };
                                (off, s.clone())
                            }
                            _ => {
                                return Err(Self::err(
                                    line_no,
                                    "Syntax: STORE_STR %buf [offset] \"string\"",
                                ));
                            }
                        };
                        Instruction::StoreStr {
                            buf,
                            offset,
                            content,
                        }
                    }
                    _ => {
                        return Err(Self::err(
                            line_no,
                            format!("Unrecognized instruction: '{}'", raw_line),
                        ));
                    }
                },

                Some(dest) => match op {
                    "MOV" => match cur.next_operand()? {
                        Operand::Reg(src) => Instruction::Mov { dest, src },
                        Operand::Const(val) => {
                            let ty = match &val {
                                Value::Bool(_) => Type::Bool,
                                Value::U64(_) => Type::U64,
                                Value::Ptr(_) => Type::Ptr,
                                Value::I64(_) => Type::I64,
                            };
                            Instruction::AssignConst { dest, ty, val }
                        }
                    },
                    "SLICE_PTR" | "SLICE_LEN" => {
                        let src = cur.next_ident(&format!("%dest = {} %src", op))?;
                        if op == "SLICE_PTR" {
                            Instruction::SlicePtr { dest, slice: src }
                        } else {
                            Instruction::SliceLen { dest, slice: src }
                        }
                    }
                    "LOAD8" | "LOAD64" => {
                        cur.eat_type(); // Bỏ qua type annotation tùy chọn
                        let buf = cur.next_ident(&format!("%dest = {} %buf %offset", op))?;
                        let offset = cur.next_operand()?;
                        if op == "LOAD8" {
                            Instruction::Load8 { dest, buf, offset }
                        } else {
                            Instruction::Load64 { dest, buf, offset }
                        }
                    }
                    "CONST" => {
                        let ty_opt = cur.eat_type();
                        let op_val = cur.next_operand()?;
                        let (ty, val) = match (ty_opt, op_val) {
                            (None, Operand::Const(Value::Bool(b))) => (Type::Bool, Value::Bool(b)),
                            (None, Operand::Const(Value::I64(n))) => (Type::I64, Value::I64(n)),
                            (None, Operand::Const(Value::U64(u))) => (Type::U64, Value::U64(u)),
                            (Some(Type::I64), Operand::Const(Value::I64(n))) => {
                                (Type::I64, Value::I64(n))
                            }
                            (Some(Type::U64), Operand::Const(Value::I64(n))) if n >= 0 => {
                                (Type::U64, Value::U64(n as u64))
                            }
                            (Some(Type::U64), Operand::Const(Value::U64(u))) => {
                                (Type::U64, Value::U64(u))
                            }
                            (Some(Type::U8), Operand::Const(Value::I64(n)))
                                if (0..=255).contains(&n) =>
                            {
                                (Type::U8, Value::U64(n as u64))
                            }
                            (Some(Type::Bool), Operand::Const(Value::Bool(b))) => {
                                (Type::Bool, Value::Bool(b))
                            }
                            (Some(Type::Ptr), Operand::Const(Value::I64(n))) if n >= 0 => {
                                (Type::Ptr, Value::Ptr(n as usize))
                            }
                            (Some(Type::Ptr), Operand::Const(Value::U64(u))) => {
                                (Type::Ptr, Value::Ptr(u as usize))
                            }
                            (Some(Type::Array(..) | Type::Slice(..)), _) => {
                                return Err(Self::err(
                                    line_no,
                                    "Cannot assign CONST directly to Array/Slice. Use ALLOC",
                                ));
                            }
                            _ => {
                                return Err(Self::err(
                                    line_no,
                                    "Invalid constant value or type mismatch in CONST",
                                ));
                            }
                        };
                        Instruction::AssignConst { dest, ty, val }
                    }
                    "NOT" | "BITNOT" => {
                        let ty = cur.eat_type().unwrap_or(if op == "BITNOT" {
                            Type::I64
                        } else {
                            Type::Bool
                        });
                        let src = cur.next_operand()?;
                        Instruction::Not { dest, ty, src }
                    }
                    "ADD" | "SUB" | "MUL" | "DIV" | "MOD" | "EQ" | "NEQ" | "LT" | "LTE" | "GT"
                    | "GTE" | "AND" | "OR" | "BAND" | "BOR" | "XOR" | "SHL" | "SHR" | "SAR" => {
                        let ty = cur.eat_type().unwrap_or(
                            if matches!(
                                op,
                                "EQ" | "NEQ" | "LT" | "LTE" | "GT" | "GTE" | "AND" | "OR"
                            ) {
                                Type::Bool
                            } else {
                                Type::I64
                            },
                        );
                        let src1 = cur.next_operand()?;
                        let src2 = cur.next_operand()?;
                        let bin_op = match op {
                            "ADD" => BinOp::Add,
                            "SUB" => BinOp::Sub,
                            "MUL" => BinOp::Mul,
                            "DIV" => BinOp::Div,
                            "MOD" => BinOp::Mod,
                            "EQ" => BinOp::Eq,
                            "NEQ" => BinOp::Neq,
                            "LT" => BinOp::Lt,
                            "LTE" => BinOp::Lte,
                            "GT" => BinOp::Gt,
                            "GTE" => BinOp::Gte,
                            "BAND" => BinOp::BitAnd,
                            "BOR" => BinOp::BitOr,
                            "AND" => {
                                if matches!(ty, Type::Bool) {
                                    BinOp::And
                                } else {
                                    BinOp::BitAnd
                                }
                            }
                            "OR" => {
                                if matches!(ty, Type::Bool) {
                                    BinOp::Or
                                } else {
                                    BinOp::BitOr
                                }
                            }
                            "XOR" => BinOp::Xor,
                            "SHL" => BinOp::Shl,
                            "SHR" => BinOp::Shr,
                            "SAR" => BinOp::Sar,
                            _ => unreachable!(),
                        };
                        Instruction::Binary {
                            op: bin_op,
                            ty,
                            dest,
                            src1,
                            src2,
                        }
                    }
                    _ => {
                        return Err(Self::err(
                            line_no,
                            format!("Unrecognized instruction: '{}'", raw_line),
                        ));
                    }
                },
            },
        };

        cur.expect_eof(op)?;
        Ok(inst)
    }

    #[inline]
    fn tokenize_line(line: &str, line_no: usize) -> Result<Vec<Token>, ParseError> {
        Ok(Self::tokenize_line_with_clean(line, line_no)?.0)
    }

    /// Quét 1 lượt trả về cả danh sách Token lẫn slice chuỗi đã cắt bỏ comment `#`
    fn tokenize_line_with_clean(
        line: &str,
        line_no: usize,
    ) -> Result<(Vec<Token>, &str), ParseError> {
        let mut tokens = Vec::new();
        let bytes = line.as_bytes();
        let n = bytes.len();
        let mut i = 0;
        let mut clean_end = n;

        while i < n {
            let b = bytes[i];
            // 1. Bỏ qua khoảng trắng
            if b.is_ascii_whitespace() {
                i += 1;
                continue;
            }
            // 2. Comment '#' -> dừng quét phần còn lại của dòng và đánh dấu vị trí cắt comment
            if b == b'#' {
                clean_end = i;
                break;
            }
            // 3. Chuỗi ký tự "..." (Unescape chuẩn 1 lượt)
            if b == b'"' {
                i += 1;
                let mut s = String::new();
                let mut closed = false;
                while i < n {
                    let ch = line[i..].chars().next().unwrap();
                    i += ch.len_utf8();
                    if ch == '"' {
                        closed = true;
                        break;
                    } else if ch == '\\' {
                        if i >= n {
                            return Err(Self::err(line_no, "Trailing backslash in string literal"));
                        }
                        let esc = line[i..].chars().next().unwrap();
                        i += esc.len_utf8();
                        match esc {
                            '0' => s.push('\0'),
                            'n' => s.push('\n'),
                            't' => s.push('\t'),
                            'r' => s.push('\r'),
                            '"' => s.push('"'),
                            '\\' => s.push('\\'),
                            other => {
                                s.push('\\');
                                s.push(other);
                            }
                        }
                    } else {
                        s.push(ch);
                    }
                }
                if !closed {
                    return Err(Self::err(
                        line_no,
                        "Missing closing quote in string literal",
                    ));
                }
                tokens.push(Token::Str(s));
                continue;
            }

            // 4. Các dấu câu & toán tử 2 ký tự
            if i + 1 < n {
                let two = &line[i..i + 2];
                let tok_opt = match two {
                    "->" => Some(Token::Arrow),
                    "||" => Some(Token::Op(BinOp::Or)),
                    "&&" => Some(Token::Op(BinOp::And)),
                    "==" => Some(Token::Op(BinOp::Eq)),
                    "!=" => Some(Token::Op(BinOp::Neq)),
                    "<=" => Some(Token::Op(BinOp::Lte)),
                    ">=" => Some(Token::Op(BinOp::Gte)),
                    "<<" => Some(Token::Op(BinOp::Shl)),
                    ">>" => Some(Token::Op(BinOp::Shr)),
                    _ => None,
                };
                if let Some(tok) = tok_opt {
                    tokens.push(tok);
                    i += 2;
                    continue;
                }
            }

            // 5. Ký tự '%' -> Phân biệt thanh ghi `%reg` vs phép chia dư Modulo `%`
            if b == b'%' {
                if i + 1 < n && (bytes[i + 1].is_ascii_alphabetic() || bytes[i + 1] == b'_') {
                    let start = i;
                    i += 1;
                    while i < n && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                        i += 1;
                    }
                    tokens.push(Token::Ident(line[start..i].to_string()));
                } else {
                    tokens.push(Token::Op(BinOp::Mod));
                    i += 1;
                }
                continue;
            }

            // 6. Các dấu câu & toán tử 1 ký tự
            let single_opt = match b {
                b'(' => Some(Token::LParen),
                b')' => Some(Token::RParen),
                b':' => Some(Token::Colon),
                b',' => Some(Token::Comma),
                b'=' => Some(Token::EqAssign),
                b'!' => Some(Token::Bang),
                b'+' => Some(Token::Op(BinOp::Add)),
                b'-' => Some(Token::Minus),
                b'*' => Some(Token::Op(BinOp::Mul)),
                b'/' => Some(Token::Op(BinOp::Div)),
                b'<' => Some(Token::Op(BinOp::Lt)),
                b'>' => Some(Token::Op(BinOp::Gt)),
                b'&' => Some(Token::Op(BinOp::BitAnd)),
                b'|' => Some(Token::Op(BinOp::BitOr)),
                b'^' => Some(Token::Op(BinOp::Xor)),
                _ => None,
            };
            if let Some(tok) = single_opt {
                tokens.push(tok);
                i += 1;
                continue;
            }

            // 7. Chữ số (Number literals)
            if b.is_ascii_digit() {
                let start = i;
                while i < n && (bytes[i].is_ascii_digit() || bytes[i] == b'.') {
                    i += 1;
                }
                let num_str = &line[start..i];
                if num_str.contains('.') {
                    return Err(Self::err(
                        line_no,
                        "Floating-point numbers are not supported in Light contracts (use scaled integers instead)",
                    ));
                }
                if let Ok(v) = num_str.parse::<i64>() {
                    tokens.push(Token::Int(v));
                } else if let Ok(u) = num_str.parse::<u64>() {
                    tokens.push(Token::UInt(u));
                } else {
                    return Err(Self::err(
                        line_no,
                        format!("Invalid integer literal: {}", num_str),
                    ));
                }
                continue;
            }

            // 8. Định danh (Identifiers), Nhãn (.label), Kiểu phức hợp (arr<...>, slice<...>), hoặc len(...)
            if b.is_ascii_alphabetic() || b == b'_' || b == b'.' {
                let start = i;
                while i < n
                    && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_' || bytes[i] == b'.')
                {
                    i += 1;
                }
                let word = &line[start..i];

                if (word == "arr" || word == "slice") && i < n && bytes[i] == b'<' {
                    let mut depth = 0i32;
                    while i < n {
                        if bytes[i] == b'<' {
                            depth += 1;
                        } else if bytes[i] == b'>' {
                            depth -= 1;
                            if depth == 0 {
                                i += 1;
                                break;
                            }
                        }
                        i += 1;
                    }
                    let ty = Self::parse_type(&line[start..i], line_no)?;
                    tokens.push(Token::TypeTok(ty));
                    continue;
                }

                if word == "len" && i < n && bytes[i] == b'(' {
                    let inner_start = i + 1;
                    let rel_close = line[inner_start..]
                        .find(')')
                        .ok_or_else(|| Self::err(line_no, "Unclosed 'len(...)' expression"))?;
                    let inner = line[inner_start..inner_start + rel_close].trim();
                    if inner.is_empty() {
                        return Err(Self::err(line_no, "Empty 'len()' expression"));
                    }
                    i = inner_start + rel_close + 1;
                    tokens.push(Token::Len(inner.to_string()));
                    continue;
                }

                match word {
                    "true" => tokens.push(Token::Bool(true)),
                    "false" => tokens.push(Token::Bool(false)),
                    "i64" | "u64" | "u8" | "bool" | "ptr" | "f64" => {
                        tokens.push(Token::TypeTok(Self::parse_type(word, line_no)?));
                    }
                    _ => tokens.push(Token::Ident(word.to_string())),
                }
                continue;
            }

            return Err(Self::err(
                line_no,
                format!("Unexpected character '{}' in line: {}", b as char, line),
            ));
        }

        Ok((tokens, line[..clean_end].trim()))
    }

    pub fn parse_expr(s: &str, line_no: usize) -> Result<Expr, ParseError> {
        let tokens = Self::tokenize_line(s, line_no)?;
        let mut cur = TokenCursor::new(&tokens, line_no);
        if cur.is_eof() {
            return Err(Self::err(line_no, "Empty contract expression"));
        }
        let expr = Self::parse_expr_bp(&mut cur, 0)?;
        cur.expect_eof("expression")?;
        Ok(expr)
    }

    fn infix_binding_power(tok: &Token) -> Option<(BinOp, u8, u8)> {
        let (op, l_bp) = match tok {
            Token::Op(BinOp::Or) => (BinOp::Or, 1),
            Token::Op(BinOp::And) => (BinOp::And, 3),
            Token::Op(BinOp::BitOr) => (BinOp::BitOr, 5),
            Token::Op(BinOp::Xor) => (BinOp::Xor, 7),
            Token::Op(BinOp::BitAnd) => (BinOp::BitAnd, 9),
            Token::Op(
                op @ (BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Lte | BinOp::Gt | BinOp::Gte),
            ) => (op.clone(), 11),
            Token::Op(op @ (BinOp::Shl | BinOp::Shr)) => (op.clone(), 13),
            Token::Op(BinOp::Add) => (BinOp::Add, 15),
            Token::Minus => (BinOp::Sub, 15),
            Token::Op(op @ (BinOp::Mul | BinOp::Div | BinOp::Mod)) => (op.clone(), 17),
            _ => return None,
        };
        Some((op, l_bp, l_bp + 1))
    }

    fn parse_expr_bp(cur: &mut TokenCursor<'_>, min_bp: u8) -> Result<Expr, ParseError> {
        let line_no = cur.line_no;
        let Some(tok) = cur.next() else {
            return Err(Self::err(line_no, "Unexpected end of expression"));
        };

        let mut lhs = match tok {
            Token::Int(n) => Expr::IntConst(*n),
            Token::UInt(u) => Expr::UIntConst(*u),
            Token::Bool(b) => Expr::BoolConst(*b),
            Token::Len(v) => Expr::Len(v.clone()),
            Token::Ident(v) => Expr::Var(v.clone()),
            Token::Bang => {
                let rhs = Self::parse_expr_bp(cur, 19)?;
                Expr::Not(Box::new(rhs))
            }
            Token::Minus => {
                let rhs = Self::parse_expr_bp(cur, 19)?;
                match rhs {
                    Expr::IntConst(n) => Expr::IntConst(n.wrapping_neg()),
                    Expr::UIntConst(9223372036854775808) => Expr::IntConst(i64::MIN),
                    other => Expr::Binary {
                        op: BinOp::Sub,
                        lhs: Box::new(Expr::IntConst(0)),
                        rhs: Box::new(other),
                    },
                }
            }
            Token::LParen => {
                let inner = Self::parse_expr_bp(cur, 0)?;
                if !cur.eat(&Token::RParen) {
                    return Err(Self::err(line_no, "Missing closing ')' in expression"));
                }
                inner
            }
            other => {
                return Err(Self::err(
                    line_no,
                    format!("Unexpected token in expression: {:?}", other),
                ));
            }
        };

        while let Some(tok) = cur.peek() {
            let Some((op, l_bp, r_bp)) = Self::infix_binding_power(tok) else {
                break;
            };
            if l_bp < min_bp {
                break;
            }
            cur.next();
            let rhs = Self::parse_expr_bp(cur, r_bp)?;
            lhs = Expr::Binary {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            };
        }

        Ok(lhs)
    }
}
