//! JIT Engine & Native ELF64 Machine Code Emitter cho Light (.lit)
//! - Bắn thẳng mã máy x86_64 vào bộ nhớ RAM có quyền PROT_EXEC (Zero-Overhead JIT)
//! - Hoặc đóng gói thành file thực thi độc lập Linux ELF64 (Standalone Executable, không cần C runtime/libc)

use crate::ast::*;
use std::collections::HashMap;
use std::fs::File;
use std::io::Write;
use std::os::unix::fs::PermissionsExt;

// Định nghĩa các mã số thanh ghi x86_64
#[allow(dead_code)]
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum X86Reg {
    Rax = 0,
    Rcx = 1,
    Rdx = 2,
    Rbx = 3,
    Rsp = 4,
    Rbp = 5,
    Rsi = 6,
    Rdi = 7,
    R8 = 8,
    R9 = 9,
    R10 = 10,
    R11 = 11,
}

pub struct MachineCodeEmitter {
    pub code: Vec<u8>,
    pub data_section: Vec<u8>,
    pub reg_map: HashMap<String, X86Reg>,
}

impl MachineCodeEmitter {
    pub fn new() -> Self {
        let mut reg_map = HashMap::new();
        // Ánh xạ các thanh ghi Light vào thanh ghi vật lý x86_64
        reg_map.insert("%rax".into(), X86Reg::Rax);
        reg_map.insert("%rdi".into(), X86Reg::Rdi);
        reg_map.insert("%rsi".into(), X86Reg::Rsi);
        reg_map.insert("%rdx".into(), X86Reg::Rdx);
        reg_map.insert("%res".into(), X86Reg::Rax);
        reg_map.insert("%exit_rax".into(), X86Reg::Rax);
        reg_map.insert("%exit_code".into(), X86Reg::Rdi);

        Self {
            code: Vec::new(),
            data_section: Vec::new(),
            reg_map,
        }
    }

    /// Lấy thanh ghi vật lý tương ứng với tên biến/thanh ghi Light
    pub fn get_reg(&mut self, name: &str) -> X86Reg {
        if let Some(r) = self.reg_map.get(name) {
            return *r;
        }
        // Phân bổ vào các thanh ghi đa dụng an toàn (tránh đè thanh ghi syscall)
        let general_regs = [X86Reg::Rbx, X86Reg::R10, X86Reg::R8, X86Reg::R9, X86Reg::Rcx];
        let allocated = general_regs[self.reg_map.len() % general_regs.len()];
        self.reg_map.insert(name.to_string(), allocated);
        allocated
    }

    // --- CÁC HÀM EMIT MÃ MÁY x86_64 ---

    /// Emit: mov reg, imm64 (REX.W + B8+rd + imm64)
    pub fn emit_mov_reg_imm64(&mut self, reg: X86Reg, imm: i64) {
        let reg_code = reg as u8;
        if reg_code < 8 {
            self.code.push(0x48); // REX.W
            self.code.push(0xb8 + reg_code);
        } else {
            self.code.push(0x49); // REX.W | REX.B
            self.code.push(0xb8 + (reg_code - 8));
        }
        self.code.extend_from_slice(&imm.to_le_bytes());
    }

    /// Emit: mov dst, src (REX.W + 89 /r)
    pub fn emit_mov_reg_reg(&mut self, dst: X86Reg, src: X86Reg) {
        let dst_code = dst as u8;
        let src_code = src as u8;
        let mut rex = 0x48;
        if src_code >= 8 {
            rex |= 0x04; // REX.R
        }
        if dst_code >= 8 {
            rex |= 0x01; // REX.B
        }
        self.code.push(rex);
        self.code.push(0x89);
        let modrm = 0xc0 | ((src_code & 7) << 3) | (dst_code & 7);
        self.code.push(modrm);
    }

    /// Emit: add dst, src
    pub fn emit_add_reg_reg(&mut self, dst: X86Reg, src: X86Reg) {
        let dst_code = dst as u8;
        let src_code = src as u8;
        self.code.push(0x48);
        self.code.push(0x01);
        let modrm = 0xc0 | ((src_code & 7) << 3) | (dst_code & 7);
        self.code.push(modrm);
    }

    /// Emit: syscall (0F 05)
    pub fn emit_syscall(&mut self) {
        self.code.push(0x0f);
        self.code.push(0x05);
    }

    /// Emit: ret (C3)
    pub fn emit_ret(&mut self) {
        self.code.push(0xc3);
    }

    /// Biên dịch một hàm Light sang mã máy x86_64
    pub fn compile_function(&mut self, func: &Function, base_data_vaddr: u64) -> Result<(), String> {
        let mut buffer_offsets: HashMap<String, usize> = HashMap::new();

        for inst in &func.instructions {
            match inst {
                // Các chỉ thị kiểm chứng chỉ dùng cho Z3 ở bước trước, không sinh mã máy
                Instruction::Require(_) | Instruction::Ensure(_) | Instruction::Invariant(_) | Instruction::Assert(_) => {}

                Instruction::Alloc { dest, size } => {
                    let offset = self.data_section.len();
                    self.data_section.resize(offset + size, 0);
                    buffer_offsets.insert(dest.clone(), offset);
                }

                Instruction::StoreStr { buf, offset, content } => {
                    let buf_offset = buffer_offsets.get(buf).cloned().unwrap_or(0);
                    let target_offset = buf_offset + offset;
                    let bytes = content.as_bytes();
                    if target_offset + bytes.len() > self.data_section.len() {
                        self.data_section.resize(target_offset + bytes.len(), 0);
                    }
                    self.data_section[target_offset..target_offset + bytes.len()].copy_from_slice(bytes);
                }

                Instruction::AssignConst { dest, val, .. } => {
                    let reg = self.get_reg(dest);
                    match val {
                        Value::I64(n) => self.emit_mov_reg_imm64(reg, *n),
                        Value::U64(n) => self.emit_mov_reg_imm64(reg, *n as i64),
                        Value::Bool(b) => self.emit_mov_reg_imm64(reg, if *b { 1 } else { 0 }),
                        Value::Ptr(p) => self.emit_mov_reg_imm64(reg, *p as i64),
                        Value::F64(_) => return Err("f64 JIT đang trong quá trình phát triển".into()),
                    }
                }

                Instruction::Mov { dest, src } => {
                    // Nếu src là buffer mảng, ta nạp địa chỉ bộ nhớ (base_data_vaddr + offset) vào thanh ghi
                    if let Some(buf_offset) = buffer_offsets.get(src) {
                        let reg = self.get_reg(dest);
                        let vaddr = base_data_vaddr + (*buf_offset as u64);
                        self.emit_mov_reg_imm64(reg, vaddr as i64);
                    } else {
                        let dst_reg = self.get_reg(dest);
                        let src_reg = self.get_reg(src);
                        self.emit_mov_reg_reg(dst_reg, src_reg);
                    }
                }

                Instruction::Binary { op, dest, src1, src2, .. } => {
                    let dst_reg = self.get_reg(dest);
                    // Nạp src1 vào dst_reg
                    match src1 {
                        Operand::Const(Value::I64(n)) => self.emit_mov_reg_imm64(dst_reg, *n),
                        Operand::Reg(r) => {
                            let r_reg = self.get_reg(r);
                            self.emit_mov_reg_reg(dst_reg, r_reg);
                        }
                        _ => {}
                    }
                    // Thực hiện op với src2
                    let src2_reg = match src2 {
                        Operand::Const(Value::I64(n)) => {
                            let tmp = X86Reg::Rbx;
                            self.emit_mov_reg_imm64(tmp, *n);
                            tmp
                        }
                        Operand::Reg(r) => self.get_reg(r),
                        _ => X86Reg::Rbx,
                    };

                    match op {
                        BinOp::Add => self.emit_add_reg_reg(dst_reg, src2_reg),
                        _ => return Err(format!("Phép toán {:?} đang được bổ sung vào JIT backend", op)),
                    }
                }

                Instruction::Syscall { rax, rdi, rsi, rdx } => {
                    // Để tránh việc nạp thanh ghi này làm đè mất giá trị của thanh ghi kia:
                    // Ta nạp lần lượt: rdx, rsi, rdi, rax (ngược lại từ sau ra trước)
                    let args = [
                        (rdx, X86Reg::Rdx),
                        (rsi, X86Reg::Rsi),
                        (rdi, X86Reg::Rdi),
                        (rax, X86Reg::Rax),
                    ];

                    for (op, target_reg) in args {
                        match op {
                            Operand::Const(Value::I64(n)) => self.emit_mov_reg_imm64(target_reg, *n),
                            Operand::Reg(r) => {
                                if let Some(buf_offset) = buffer_offsets.get(r) {
                                    let vaddr = base_data_vaddr + (*buf_offset as u64);
                                    self.emit_mov_reg_imm64(target_reg, vaddr as i64);
                                } else {
                                    let src_reg = self.get_reg(r);
                                    if src_reg != target_reg {
                                        self.emit_mov_reg_reg(target_reg, src_reg);
                                    }
                                }
                            }
                            _ => {}
                        }
                    }

                    self.emit_syscall();
                }

                Instruction::Ret(val) => {
                    if let Some(op) = val {
                        match op {
                            Operand::Const(Value::I64(n)) => self.emit_mov_reg_imm64(X86Reg::Rax, *n),
                            Operand::Reg(r) => {
                                let src_reg = self.get_reg(r);
                                if src_reg != X86Reg::Rax {
                                    self.emit_mov_reg_reg(X86Reg::Rax, src_reg);
                                }
                            }
                            _ => {}
                        }
                    }
                    if func.name == "main" {
                        // Với Standalone ELF64, hàm main kết thúc bằng sys_exit(rax) để hệ điều hành thoát an toàn
                        // mov rdi, rax
                        self.emit_mov_reg_reg(X86Reg::Rdi, X86Reg::Rax);
                        // mov rax, 60 (sys_exit)
                        self.emit_mov_reg_imm64(X86Reg::Rax, 60);
                        self.emit_syscall();
                    } else {
                        self.emit_ret();
                    }
                }

                _ => {}
            }
        }

        // Đảm bảo kết thúc bằng ret nếu chưa có
        if self.code.last() != Some(&0xc3) {
            self.emit_ret();
        }

        Ok(())
    }

    /// Thực thi trực tiếp qua JIT Memory (mmap PROT_READ | PROT_WRITE | PROT_EXEC)
    pub unsafe fn run_jit(&self) -> Result<i64, String> {
        if self.code.is_empty() {
            return Err("Không có mã máy để thực thi JIT".into());
        }

        let page_size = 4096;
        let alloc_size = (self.code.len() + page_size - 1) & !(page_size - 1);

        unsafe {
            // Gọi syscall mmap cấp phát bộ nhớ ảo RWX
            let mem = libc_mmap(alloc_size)?;

            // Ghi mã máy vào RAM
            std::ptr::copy_nonoverlapping(self.code.as_ptr(), mem as *mut u8, self.code.len());

            // Ép kiểu con trỏ thành hàm và nhảy vào chạy
            let func: extern "C" fn() -> i64 = std::mem::transmute(mem);
            let ret = func();

            // Giải phóng vùng nhớ
            libc_munmap(mem, alloc_size)?;

            Ok(ret)
        }
    }

    /// Đóng gói thành file thực thi Linux độc lập (Minimal Standalone ELF64 Executable)
    /// File này KHÔNG CẦN libc, KHÔNG CẦN linker, kích thước chỉ ~250 bytes!
    pub fn emit_elf64(&self, output_path: &str) -> std::io::Result<()> {
        let mut file = File::create(output_path)?;

        let elf_header_size = 64usize;
        let prog_header_size = 56usize;
        let num_phdrs = 1usize;
        let headers_total = elf_header_size + prog_header_size * num_phdrs; // 120 bytes

        let base_vaddr = 0x400000u64;
        let entry_point = base_vaddr + (headers_total as u64);

        let total_filesz = (headers_total + self.code.len() + self.data_section.len()) as u64;

        // 1. ELF Header (64 bytes)
        let mut elf_header = vec![0u8; 64];
        elf_header[0..4].copy_from_slice(b"\x7fELF"); // Magic
        elf_header[4] = 2; // 64-bit
        elf_header[5] = 1; // Little endian
        elf_header[6] = 1; // ELF version
        elf_header[7] = 0; // System V ABI
        elf_header[16..18].copy_from_slice(&2u16.to_le_bytes()); // ET_EXEC
        elf_header[18..20].copy_from_slice(&0x3eu16.to_le_bytes()); // x86_64
        elf_header[20..24].copy_from_slice(&1u32.to_le_bytes()); // Version
        elf_header[24..32].copy_from_slice(&entry_point.to_le_bytes()); // Entry point
        elf_header[32..40].copy_from_slice(&(elf_header_size as u64).to_le_bytes()); // e_phoff = 64
        elf_header[40..48].copy_from_slice(&0u64.to_le_bytes()); // e_shoff = 0
        elf_header[48..52].copy_from_slice(&0u32.to_le_bytes()); // e_flags = 0
        elf_header[52..54].copy_from_slice(&(elf_header_size as u16).to_le_bytes()); // e_ehsize = 64
        elf_header[54..56].copy_from_slice(&(prog_header_size as u16).to_le_bytes()); // e_phentsize = 56
        elf_header[56..58].copy_from_slice(&(num_phdrs as u16).to_le_bytes()); // e_phnum = 1
        elf_header[58..60].copy_from_slice(&0u16.to_le_bytes()); // e_shentsize = 0
        elf_header[60..62].copy_from_slice(&0u16.to_le_bytes()); // e_shnum = 0
        elf_header[62..64].copy_from_slice(&0u16.to_le_bytes()); // e_shstrndx = 0

        // 2. Program Header: PT_LOAD RWX (56 bytes)
        let mut phdr = vec![0u8; 56];
        phdr[0..4].copy_from_slice(&1u32.to_le_bytes()); // PT_LOAD
        phdr[4..8].copy_from_slice(&7u32.to_le_bytes()); // PF_R | PF_W | PF_X
        phdr[8..16].copy_from_slice(&0u64.to_le_bytes()); // Offset 0
        phdr[16..24].copy_from_slice(&base_vaddr.to_le_bytes()); // Vaddr 0x400000
        phdr[24..32].copy_from_slice(&base_vaddr.to_le_bytes()); // Paddr 0x400000
        phdr[32..40].copy_from_slice(&total_filesz.to_le_bytes()); // File size
        phdr[40..48].copy_from_slice(&total_filesz.to_le_bytes()); // Mem size
        phdr[48..56].copy_from_slice(&0x1000u64.to_le_bytes()); // Align 4KB

        file.write_all(&elf_header)?;
        file.write_all(&phdr)?;
        file.write_all(&self.code)?;
        file.write_all(&self.data_section)?;

        let mut perms = file.metadata()?.permissions();
        perms.set_mode(0o755);
        file.set_permissions(perms)?;

        Ok(())
    }
}

// Cấp phát bộ nhớ ảo bằng raw Linux syscall sys_mmap (không cần libc crate)
unsafe fn libc_mmap(size: usize) -> Result<*mut u8, String> {
    let mut addr: *mut u8;
    // Syscall 9: sys_mmap(addr=0, len=size, prot=7 (RWX), flags=0x22 (MAP_PRIVATE | MAP_ANONYMOUS), fd=-1, offset=0)
    unsafe {
        std::arch::asm!(
            "syscall",
            in("rax") 9,
            in("rdi") 0,
            in("rsi") size,
            in("rdx") 7, // PROT_READ | PROT_WRITE | PROT_EXEC
            in("r10") 0x22, // MAP_PRIVATE | MAP_ANONYMOUS
            in("r8") -1,
            in("r9") 0,
            lateout("rax") addr,
            lateout("rcx") _,
            lateout("r11") _,
        );
    }

    if (addr as isize) < 0 && (addr as isize) > -4096 {
        return Err("mmap cấp phát vùng nhớ JIT thất bại".into());
    }
    Ok(addr)
}

unsafe fn libc_munmap(addr: *mut u8, size: usize) -> Result<(), String> {
    let ret: isize;
    // Syscall 11: sys_munmap(addr, len)
    unsafe {
        std::arch::asm!(
            "syscall",
            in("rax") 11,
            in("rdi") addr,
            in("rsi") size,
            lateout("rax") ret,
            lateout("rcx") _,
            lateout("r11") _,
        );
    }
    if ret != 0 {
        return Err("munmap thất bại".into());
    }
    Ok(())
}
