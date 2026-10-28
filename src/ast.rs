//! Định nghĩa Abstract Syntax Tree (AST) & ISA cho ngôn ngữ Light (.lit)
//! Hỗ trợ đầy đủ 6 kiểu dữ liệu: i64, u64, f64, bool, ptr, mảng cố định arr<T, N> & slice<T>.

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    I64,
    U64,
    U8,
    F64,
    Bool,
    Ptr,
    /// Mảng cố định phần tử với kích thước biết trước: arr<i64, 10>
    Array(Box<Type>, usize),
    /// Con trỏ mảng động kèm độ dài: slice<u8>
    Slice(Box<Type>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    I64(i64),
    U64(u64),
    F64(f64),
    Bool(bool),
    Ptr(usize),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Operand {
    Reg(String),
    Const(Value),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,
    And,
    Or,
}

/// Các biểu thức logic dùng trong kiểm chứng (Verification Expressions)
/// Cho phép AI viết biểu thức toán học tự nhiên trong REQUIRE, ENSURE, INVARIANT, ASSERT
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Var(String),
    IntConst(i64),
    FloatConst(f64),
    BoolConst(bool),
    Binary {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Not(Box<Expr>),
    /// Lấy độ dài của một mảng/slice: len(%arr)
    Len(String),
}

/// Tập lệnh (ISA) & Chỉ thị kiểm chứng của Light
#[derive(Debug, Clone, PartialEq)]
pub enum Instruction {
    // --- CHỈ THỊ KIỂM CHỨNG TOÁN HỌC (Z3 FIRST-CLASS CITIZEN) ---
    /// Tiền điều kiện đầu vào của hàm: REQUIRE <expr>
    Require(Expr),
    /// Cam kết đầu ra của hàm: ENSURE <expr>
    Ensure(Expr),
    /// Bất biến vòng lặp: INVARIANT <expr>
    Invariant(Expr),
    /// Khẳng định điều kiện tại một thời điểm: ASSERT <expr>
    Assert(Expr),

    // --- TẬP LỆNH TÍNH TOÁN & THAO TÁC BIẾN (FLAT SSA / TAC) ---
    /// Gán hằng số: %reg = CONST <type> <val>
    AssignConst {
        dest: String,
        ty: Type,
        val: Value,
    },
    /// Copy giá trị: %reg = MOV %src
    Mov {
        dest: String,
        src: String,
    },
    /// Phép toán 2 ngôi: %dest = OP <type> %src1 %src2
    Binary {
        op: BinOp,
        ty: Type,
        dest: String,
        src1: Operand,
        src2: Operand,
    },

    /// Gọi hàm: %dest = CALL func_name arg1 arg2 ...
    Call {
        dest: Option<String>,
        func_name: String,
        args: Vec<Operand>,
    },

    // --- BỘ NHỚ AN TOÀN (BUFFER, ARRAYS & SLICES) ---
    /// Cấp phát slice an toàn: %dest = ALLOC slice<T> <len>
    AllocSlice {
        dest: String,
        elem_ty: Type,
        len: usize,
    },
    /// Lấy con trỏ thô từ slice: %ptr = SLICE_PTR %slice
    SlicePtr {
        dest: String,
        slice: String,
    },
    /// Lấy độ dài của slice: %len = SLICE_LEN %slice
    SliceLen {
        dest: String,
        slice: String,
    },
    /// Cấp phát bộ nhớ cục bộ an toàn: ALLOC %buf size
    Alloc {
        dest: String,
        size: usize,
    },
    /// Ghi 1 byte vào bộ nhớ: STORE8 %buf %offset %val
    Store8 {
        buf: String,
        offset: Operand,
        val: Operand,
    },
    /// Đọc 1 byte từ bộ nhớ: %dest = LOAD8 %buf %offset
    Load8 {
        dest: String,
        buf: String,
        offset: Operand,
    },
    /// Ghi 8 bytes (i64/u64/f64) vào bộ nhớ: STORE64 %buf %offset %val
    Store64 {
        buf: String,
        offset: Operand,
        val: Operand,
    },
    /// Đọc 8 bytes (i64/u64/f64) từ bộ nhớ: %dest = LOAD64 %buf %offset
    Load64 {
        dest: String,
        buf: String,
        offset: Operand,
    },
    /// Ghi chuỗi ký tự trực tiếp: STORE_STR %buf offset "string"
    StoreStr {
        buf: String,
        offset: usize,
        content: String,
    },

    // --- ĐIỀU KHIỂN LUỒNG CẤU TRÚC (STRUCTURED CONTROL FLOW - TURING COMPLETE) ---
    /// Bắt đầu vòng lặp: LOOP <label>
    Loop(String),
    /// Thoát vòng lặp nếu điều kiện đúng: BREAK_IF %cond
    BreakIf(String),
    /// Nhảy sang vòng lặp tiếp theo nếu điều kiện đúng: CONTINUE_IF %cond
    ContinueIf(String),
    /// Kết thúc vòng lặp: END_LOOP <label>
    EndLoop(String),

    // --- GIAO TIẾP HỆ ĐIỀU HÀNH & KẾT THÚC (NO LIBC, RAW LINUX SYSCALL) ---
    /// Gọi ngắt hệ điều hành Linux: SYSCALL rax rdi rsi rdx
    Syscall {
        rax: Operand,
        rdi: Operand,
        rsi: Operand,
        rdx: Operand,
    },
    /// Trả về kết quả: RET %reg hoặc RET const
    Ret(Option<Operand>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    pub name: String,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Function {
    pub name: String,
    pub params: Vec<Param>,
    pub return_ty: Option<Type>,
    pub instructions: Vec<Instruction>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub functions: Vec<Function>,
}
