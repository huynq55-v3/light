// File: src/main.rs (Ngân sách: < 60 dòng - Thực tế: 45 dòng)
mod elf64;
mod ir;
mod parser;
mod verify;

use std::{env, fs, process};

fn run() -> Result<(), String> {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        return Err(format!("Cách dùng: {} <input.lt> [output.elf]", args[0]));
    }
    let in_path = &args[1];
    let out_path = args.get(2).cloned().unwrap_or_else(|| "a.out".to_string());

    // 1. Đọc và phân tích cú pháp SSA phẳng (.lt -> ir::Module)
    let module = parser::parse_file(in_path)?;
    println!(
        "[1/3] Parsed '{}' ({} layouts, {} funcs)",
        in_path,
        module.layouts.len(),
        module.funcs.len()
    );

    // 2. Kiểm chứng hình thức từng hàm bằng Z3 SMT Solver
    for func in &module.funcs {
        verify::verify_func(&module, func)?;
        println!("  ✓ Z3 Verified: func '{}'", func.name);
    }
    println!("[2/3] All functions passed Z3 formal verification!");

    // 3. Sinh mã máy x86_64 và đóng gói ELF64 binary
    let elf_bytes = elf64::compile_elf64(&module)?;
    fs::write(&out_path, &elf_bytes).map_err(|e| format!("Không thể ghi '{}': {}", out_path, e))?;

    // Tự động bật cờ thực thi (rwxr-xr-x) trên hệ thống Unix/Linux
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let _ = fs::set_permissions(&out_path, fs::Permissions::from_mode(0o755));
    }

    println!(
        "[3/3] Emitted ELF64 binary: '{}' ({} bytes)",
        out_path,
        elf_bytes.len()
    );
    Ok(())
}

fn main() {
    if let Err(err) = run() {
        eprintln!("\n❌ LỖI BIÊN DỊCH:\n{}", err);
        process::exit(1);
    }
}
