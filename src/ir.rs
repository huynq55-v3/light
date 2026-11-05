// File: src/ir.rs (Ngân sách tối đa: 120 dòng - CẤM AI tự ý thêm Trait hay Wrapper)

pub type Reg = u32; // Biến SSA định danh bằng số (%0, %1, %2...) thay vì String gây tốn bộ nhớ
pub type BlockId = u32; // Nhãn nhảy cơ bản (Basic Block: @b0, @b1...)

/// 1. HỆ THỐNG KIỂU DỮ LIỆU TỐI GIẢN CHO AI & BARE-METAL OS
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Type {
    Bv8,
    Bv16,
    Bv32,
    Bv64, // Thanh ghi 64-bit tiêu chuẩn (dùng cho cả số nguyên lẫn giá trị logic)
    /// Con trỏ có miền giới hạn: trỏ tới Layout thứ `layout_id`, tối đa `max_elems` phần tử
    Ptr {
        layout_id: u16,
        max_elems: u64,
    },
    /// Thẻ quyền Phần cứng: chỉ cho phép gọi lệnh HwIo trong dải cổng [min..=max]
    Io {
        min: u16,
        max: u16,
    },
}

/// 2. KHAI BÁO CẤU TRÚC DỮ LIỆU PHẲNG (Thay thế hoàn toàn Struct/Class phức tạp)
#[derive(Debug, Clone)]
pub struct FieldDef {
    pub offset: u32,         // Offset cố định tính bằng byte (AI hoặc người viết tự căn)
    pub ty: Type,            // Kiểu của trường dữ liệu tại offset này
    pub inv: Option<Z3Expr>, // Bất biến kiểu (Type Invariant): Z3 tự kiểm tra mỗi khi Store
}

#[derive(Debug, Clone)]
pub struct Layout {
    pub name: String,
    pub size: u32, // Tổng kích thước (byte) của cấu trúc
    pub fields: Vec<FieldDef>,
}

/// 3. GỘP TOÀN BỘ PHÉP TOÁN SỐ HỌC & DỊCH BIT VÀO 1 ENUM DUY NHẤT (Chống Bloat)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    // Số học cơ bản (Ánh xạ thẳng sang bvadd, bvsub, bvmul... trong Z3)
    Add,
    Sub,
    Mul,
    UDiv,
    SDiv,
    URem,
    SRem,
    // Bitwise & Dịch bit cho OS (Ánh xạ thẳng sang bvand, bvor, bvshl, bvlshr...)
    And,
    Or,
    Xor,
    Shl,
    LShr,
    AShr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmpOp {
    Eq,
    Ne,
    Ult,
    Ule,
    Ugt,
    Uge,
    Slt,
    Sle,
    Sgt,
    Sge, // Tách biệt rõ có dấu (S) và không dấu (U)
}

/// 4. BIỂU THỨC RÀNG BUỘC DÀNH RIÊNG CHO BỘ KIỂM CHỨNG Z3
#[derive(Debug, Clone)]
pub enum Z3Expr {
    Reg(Reg),   // Giá trị của một biến SSA (%0, %1...)
    FieldVal,   // Giá trị đang được ghi vào trường của Layout (dùng cho @inv)
    Const(u64), // Hằng số 64-bit
    Bin(BinOp, Box<Z3Expr>, Box<Z3Expr>),
    Cmp(CmpOp, Box<Z3Expr>, Box<Z3Expr>),
    And(Box<Z3Expr>, Box<Z3Expr>),
    Or(Box<Z3Expr>, Box<Z3Expr>),
    Not(Box<Z3Expr>),
}

/// 5. TẬP CHỈ THỊ SSA CỐT LÕI (Chỉ đúng 12 lệnh cho cả Z3 lẫn x86_64 ELF64)
#[derive(Debug, Clone)]
pub enum Inst {
    /// %dst = const <val> : <ty>
    Const {
        dst: Reg,
        ty: Type,
        val: u64,
    },
    /// %dst = <op> %lhs, %rhs (Gộp tất cả cộng trừ nhân chia và dịch bit tại đây!)
    Bin {
        dst: Reg,
        op: BinOp,
        lhs: Reg,
        rhs: Reg,
    },
    /// %dst = cmp <op> %lhs, %rhs
    Cmp {
        dst: Reg,
        op: CmpOp,
        lhs: Reg,
        rhs: Reg,
    },

    Slice {
        dst: Reg,
        base: Reg,
        idx: Reg,
        ty: Type,
    },

    /// %dst = load % base_ptr, offset: <u32> (Z3 sẽ kiểm tra offset < max_elems * size + Field Invariant)
    Load {
        dst: Reg,
        ty: Type,
        base: Reg,
        offset: u32,
    },
    /// store %base_ptr, offset: <u32>, %val
    Store {
        base: Reg,
        offset: u32,
        val: Reg,
    },

    /// Lệnh đặc quyền cho OS Bare-metal (Đọc/ghi cổng I/O, thanh ghi CR3, MSR hoặc Syscall)
    HwIo {
        dst: Option<Reg>,
        cap: Reg,
        port_or_reg: u16,
        val: Option<Reg>,
        is_write: bool,
    },

    /// Điều hướng luồng thực thi (Control Flow)
    Br {
        cond: Reg,
        then_bb: BlockId,
        else_bb: BlockId,
    },
    Jmp {
        target_bb: BlockId,
        args: Vec<Reg>,
    },
    Call {
        dst: Option<Reg>,
        func_id: u32,
        args: Vec<Reg>,
    },
    CallPtr {
        dst: Option<Reg>,
        target: Reg,
        args: Vec<Reg>,
    },
    Ret {
        val: Option<Reg>,
    },

    /// Lệnh "Ghost" (Chỉ tồn tại ở bước verify.rs để Z3 kiểm chứng, elf64.rs bỏ qua 100%)
    Assume(Z3Expr), // Giả định tiền điều kiện
    Assert(Z3Expr), // Bắt buộc Z3 chứng minh UNSAT cho mệnh đề phủ định
}

/// 6. KHỐI CƠ BẢN (BASIC BLOCK), HÀM VÀ MODULE
#[derive(Debug, Clone)]
pub struct Block {
    pub id: BlockId,
    pub params: Vec<(Reg, Type)>, // Tham số của Block (Thay thế cho lệnh Phi rườm rà trong SSA cổ điển)
    pub invs: Vec<Z3Expr>,
    pub insts: Vec<Inst>,
}

#[derive(Debug, Clone)]
pub struct Func {
    pub name: String,
    pub params: Vec<(Reg, Type)>,
    pub ret_ty: Option<Type>,
    pub requires: Vec<Z3Expr>, // Hợp đồng đầu vào (@req)
    pub ensures: Vec<Z3Expr>,  // Hợp đồng đầu ra (@ens)
    pub blocks: Vec<Block>,
}

#[derive(Debug, Clone, Default)]
pub struct Module {
    pub layouts: Vec<Layout>, // Danh sách các cấu trúc dữ liệu phẳng
    pub funcs: Vec<Func>,     // Danh sách các hàm SSA
}
