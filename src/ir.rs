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
    /// Con trỏ có độ dài ĐỘNG: `ptr<L,%n>` — trỏ tới `len` phần tử Layout `layout_id`, với `len` là một biến SSA
    /// số nguyên (bất biến nên độ dài không thể đổi sau khi tạo). Quy tắc phạm vi (verify.rs):
    /// tham số hàm -> %n là tham số đứng trước; kiểu trả về -> %n là tham số hàm; tham số block -> %n là tham số
    /// đứng trước của cùng block hoặc tham số hàm; đích của slice -> %n bất kỳ đã định nghĩa và chi phối.
    /// Không được nằm trong Layout (không lưu vào bộ nhớ), không tạo được bằng const.
    /// Ngầm định: len * kích_thước_layout <= RAM, nên phép tính địa chỉ không tràn.
    DPtr {
        layout_id: u16,
        len: Reg,
    },
    /// Thẻ quyền Phần cứng: chỉ cho phép gọi lệnh HwIo trong dải cổng [min..=max]
    Io {
        min: u16,
        max: u16,
    },
    /// Thẻ quyền điều phối đa nhân (bảng SMP 0x7e000). Mờ: không load/store được, chỉ dùng cho
    /// `parallel` và `smp_workers`. Chỉ hàm giữ io<0,0xffff> mới tạo được bằng `const 0x7e000 smp`.
    Smp,
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
    // Số thực Điểm cố định Q16.16 (Fixed-Point Arithmetic: fxmul = (a*b)>>16, fxdiv = (a<<16)/b)
    FxMul,
    FxDiv,
    // Nửa cao 64 bit của tích KHÔNG DẤU 64x64 = 128 bit (x86 `mul`). Verifier coi kết quả lệnh là giá trị mờ (không đưa
    // phép nhân 128 bit vào Z3); trong biểu thức @req/@ens thì có ngữ nghĩa đúng.
    MulHi,
    // Phép số học tường minh khi tràn 64-bit. *Wrap: quay vòng, không đòi chứng minh. *Sat / *Ovf: bị parser HẠ thành các lệnh
    // gốc (xem parser::lower) nên verify/x86 không bao giờ thấy chúng.
    AddWrap,
    SubWrap,
    MulWrap,
    AddSat,
    SubSat,
    MulSat,
    AddOvf,
    SubOvf,
    MulOvf,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SimdOp {
    Add, // vadd256 %dst_ptr %lhs_ptr %rhs_ptr (AVX2 vpaddq 4x64-bit = 256-bit)
    Sub, // vsub256 %dst_ptr %lhs_ptr %rhs_ptr (AVX2 vpsubq 4x64-bit = 256-bit)
    Mul, // vmul256 %dst_ptr %lhs_ptr %rhs_ptr (AVX2 vpmuludq 4x64-bit = 256-bit)
    Xor, // vxor256 %dst_ptr %lhs_ptr %rhs_ptr (AVX2 vpxor 256-bit)
    Dot, // %dst_reg = vdot256 %lhs_ptr %rhs_ptr (AVX2 256-bit Horizontal Dot Product -> bv64)
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

    /// Tập lệnh Vector SIMD 256-bit (AVX2 YMM0..YMM15 / 32-byte Memory Vector Operations)
    Simd256 {
        op: SimdOp,
        dst: Reg,
        lhs: Reg,
        rhs: Reg,
    },

    /// Fork-join đa nhân CHẶN: `parallel %smp %n <hàm> %base %arg`
    /// Chia %base (ptr<L,M>) thành n phần liên tiếp, phần i = ptr<L,K> (K = kiểu tham số đầu của hàm), gọi
    /// hàm(phần_i, %arg, i) cho i = 0..n-1 trên các nhân AP (phần 0 và các phần không có AP online chạy trên nhân
    /// gọi), và CHỈ trả về khi mọi phần xong -> hàm cha không thể đụng vùng nhớ worker đang dùng.
    Parallel {
        smp: Reg,
        n: Reg,
        func_id: u32,
        base: Reg,
        arg: Reg,
    },
    /// %dst = smp_workers %smp: số nhân AP đang online (0..15)
    SmpWorkers {
        dst: Reg,
        smp: Reg,
    },

    /// %dst = narrow %src bv8|bv16|bv32: thu hẹp số nguyên xuống kiểu hẹp hơn. Z3 phải chứng minh giá trị vừa
    /// độ rộng đích (không cắt bit im lặng). Dùng để ghi thanh ghi MMIO 32-bit bằng giá trị tính toán.
    Narrow {
        dst: Reg,
        src: Reg,
        ty: Type,
    },
    /// %dst = view %src ptr<L2,N|%n>: nhìn CÙNG vùng nhớ theo Layout khác (vd mảng byte trên bộ đệm qword).
    /// Cả hai Layout phải không có @inv; Z3 chứng minh số byte đích <= số byte nguồn. Mã máy: một lệnh mov.
    View {
        dst: Reg,
        src: Reg,
        ty: Type,
    },
    /// %dst = addr TÊN: con trỏ ptr<L,count> tới dữ liệu tĩnh `data TÊN L` (địa chỉ tương đối RIP, ghi được).
    Addr {
        dst: Reg,
        data_id: u32,
        ty: Type,
    },

    /// Lệnh đặc quyền cho OS Bare-metal (Đọc/ghi cổng I/O, thanh ghi CR3, MSR hoặc Syscall)
    HwIo {
        dst: Option<Reg>,
        cap: Reg,
        port_or_reg: u16,
        val: Option<Reg>,
        is_write: bool,
    },

    /// Đọc `nsec` sector từ cổng dữ liệu ATA 0x1F0 (rep insd) vào [ptr + idx*512] — an toàn vì Z3 chứng minh (idx+nsec)*512 <= kích thước vùng ptr
    AtaRead {
        cap: Reg,
        ptr: Reg,
        idx: Reg,
        nsec: Reg,
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
    /// `@dec <biểu_thức>`: biến giảm (variant) của vòng lặp có đầu là block này — mỗi cạnh lùi phải làm nó giảm ngặt
    /// (so sánh không dấu). Không ghi thì verifier tự thử `p`, `X - p`, `p - X` (p = tham số block, X = cận bất biến vòng).
    pub dec: Option<Z3Expr>,
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
    pub block_names: Vec<(BlockId, String)>, // nhãn có tên (@tên) -> số block; chỉ để báo lỗi
    pub names: Vec<(Reg, String)>, // tên biến người viết (%tên) -> số SSA; chỉ để báo lỗi, sắp theo số
    pub origin: String,        // "file:dòng" nơi khai báo hàm (chỉ để báo lỗi/ tài liệu, không tham gia kiểm chứng)
}

#[derive(Debug, Clone, Default)]
pub struct Module {
    pub layouts: Vec<Layout>, // Danh sách các cấu trúc dữ liệu phẳng
    pub funcs: Vec<Func>,     // Danh sách các hàm SSA
    pub datas: Vec<Data>,     // Dữ liệu tĩnh (`data TÊN Layout { ... }`), đặt sau mã máy
}

/// Dữ liệu tĩnh khởi tạo sẵn: `count` phần tử Layout `layout_id` (Layout không có @inv), lấy bằng `%p = addr TÊN`.
#[derive(Debug, Clone)]
pub struct Data {
    pub name: String,
    pub layout_id: u16,
    pub count: u64,
    pub bytes: Vec<u8>,
}

impl Type {
    /// Layout của một con trỏ (tĩnh hoặc động)
    pub fn ptr_layout(&self) -> Option<u16> {
        match *self {
            Type::Ptr { layout_id, .. } | Type::DPtr { layout_id, .. } => Some(layout_id),
            _ => None,
        }
    }
}

impl Inst {
    /// Thanh ghi đích của lệnh (nếu có) — danh sách đầy đủ duy nhất, dùng chung cho verifier, hạ lệnh và cấp số
    pub fn dst(&self) -> Option<Reg> {
        match self {
            Inst::Const { dst, .. }
            | Inst::Bin { dst, .. }
            | Inst::Cmp { dst, .. }
            | Inst::Slice { dst, .. }
            | Inst::Load { dst, .. }
            | Inst::Narrow { dst, .. }
            | Inst::View { dst, .. }
            | Inst::Addr { dst, .. }
            | Inst::SmpWorkers { dst, .. }
            | Inst::Simd256 { op: SimdOp::Dot, dst, .. } => Some(*dst),
            Inst::HwIo { dst, .. } | Inst::Call { dst, .. } | Inst::CallPtr { dst, .. } => *dst,
            _ => None,
        }
    }
}
