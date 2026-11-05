// File: src/main.rs (Biên dịch Kernel + Quản lý Virtual Storage VFS cho Light OS)
mod elf64;
mod ir;
mod parser;
mod verify;
pub mod vfs;

use std::path::Path;
use std::{env, fs, process};

fn compile_and_verify_app(path: &str) -> Result<Vec<u8>, String> {
    let m = parser::parse_file(path)?;
    for f in &m.funcs {
        verify::verify_func(&m, f)?;
    }
    println!("  ✓ Z3 Verified & Compiled App: '{}'", path);
    elf64::compile_app_bin(&m)
}

/// Tự động biên dịch tất cả file .lit trong `lit_program/apps/` thành .elf trong `storage/apps/`
pub fn compile_all_apps(src_dir: &str, out_dir: &str) -> Result<usize, String> {
    let _ = fs::remove_dir_all(out_dir); // Dọn sạch các .elf cũ đã bị xóa khỏi lit_program/apps/
    fs::create_dir_all(out_dir).map_err(|e| e.to_string())?;
    let src_path = Path::new(src_dir);
    if !src_path.exists() {
        return Ok(0);
    }

    let mut count = 0;
    for entry in fs::read_dir(src_path).map_err(|e| e.to_string())? {
        let entry = entry.map_err(|e| e.to_string())?;
        let path = entry.path();
        if path.is_file() && path.extension().and_then(|s| s.to_str()) == Some("lit") {
            let file_stem = path.file_stem().and_then(|s| s.to_str()).unwrap_or("app");
            if file_stem == "desktop_app" {
                continue;
            }
            let out_file = format!("{}/{}.elf", out_dir, file_stem);
            let bin = compile_and_verify_app(path.to_str().unwrap())?;
            fs::write(&out_file, &bin).map_err(|e| e.to_string())?;
            count += 1;
        }
    }
    Ok(count)
}

pub fn build_disk_img() -> Result<(), String> {
    fs::create_dir_all("storage/apps").map_err(|e| e.to_string())?;
    fs::create_dir_all("storage/data/proj").map_err(|e| e.to_string())?;

    // Khởi tạo 2 file dữ liệu mẫu nếu chưa tồn tại (do revert git)
    let note_path = Path::new("storage/data/note.txt");
    if !note_path.exists() {
        fs::write(
            note_path,
            b"NOTE.TXT: HELLO LIGHT OS! ZERO FLICKER VFS.\nMOUNTED DIRECTLY FROM LINUX STORAGE/DATA!\0",
        )
        .map_err(|e| e.to_string())?;
    }
    let demo_path = Path::new("storage/data/proj/demo.lit");
    if !demo_path.exists() {
        fs::write(
            demo_path,
            b"# FILE: STORAGE/DATA/PROJ/DEMO.LIT\nFUNC DEEP_TEST VOID {\n  RET\n}\0",
        )
        .map_err(|e| e.to_string())?;
    }

    // 1. Tự động duyệt và biên dịch toàn bộ apps
    let app_count = compile_all_apps("lit_program/apps", "storage/apps")?;
    println!("  ✓ Compiled {} app(s) into 'storage/apps/'", app_count);

    // 2. Đóng gói storage/ vào disk.img
    let sb = vfs::pack_storage_to_disk(Path::new("storage"), Path::new("disk.img"))?;

    println!(
        "[4/4] Mounted 'storage/' into 'disk.img' (Superblock: {} files, next_free_lba: {})",
        sb.total_files, sb.next_free_lba
    );
    Ok(())
}

fn run() -> Result<(), String> {
    let args: Vec<String> = env::args().collect();

    if args.len() > 1 && args[1] == "sync" {
        println!("🔄 Đang đồng bộ ngược từ 'disk.img' về 'storage/'...");
        let count = vfs::sync_disk_to_storage(Path::new("disk.img"), Path::new("storage"))?;
        println!("✓ Hoàn tất đồng bộ: {} file(s) được cập nhật.", count);
        return Ok(());
    }

    if args.len() > 1 && args[1] == "pack" {
        println!("📦 Đang đóng gói 'storage/' vào 'disk.img'...");
        return build_disk_img();
    }

    let default_in = "lit_program/os/kernel.lit".to_string();
    let in_path = args.get(1).unwrap_or(&default_in);
    let out_path = args
        .get(2)
        .cloned()
        .unwrap_or_else(|| "kernel.elf".to_string());

    let module = parser::parse_file(in_path)?;
    println!(
        "[1/4] Parsed '{}' ({} layouts, {} funcs)",
        in_path,
        module.layouts.len(),
        module.funcs.len()
    );

    for func in &module.funcs {
        verify::verify_func(&module, func)?;
        println!("  ✓ Z3 Verified: func '{}'", func.name);
    }
    println!("[2/4] All Kernel functions passed Z3 formal verification!");

    let elf_bytes = elf64::compile_elf64(&module)?;
    fs::write(&out_path, &elf_bytes).map_err(|e| format!("Không thể ghi '{}': {}", out_path, e))?;

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let _ = fs::set_permissions(&out_path, fs::Permissions::from_mode(0o755));
    }

    println!(
        "[3/4] Emitted ELF64 binary: '{}' ({} bytes)",
        out_path,
        elf_bytes.len()
    );

    build_disk_img()?;
    Ok(())
}

fn main() {
    if let Err(err) = run() {
        eprintln!("\n❌ LỖI BIÊN DỊCH:\n{}", err);
        process::exit(1);
    }
}
