// File: src/main.rs (Biên dịch Kernel + đóng gói/đồng bộ/kiểm tra ảnh đĩa LightFS cho Light OS)
mod elf64;
mod ir;
mod parser;
mod verify;
mod x86;
mod lightfs;

use std::path::Path;
use std::{env, fs, process};

fn compile_and_verify_app(path: &str) -> Result<Vec<u8>, String> {
    let m = parser::parse_file(path)?;
    verify::check_module(&m)?;
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

/// Kích thước ảnh: `--size <byte>` nếu có, mặc định 64MB
fn size_arg(args: &[String]) -> Result<u64, String> {
    match args.iter().position(|a| a == "--size") {
        Some(i) => {
            let v: u64 = args.get(i + 1).and_then(|s| s.parse().ok()).ok_or("--size cần số byte")?;
            Ok(v / lightfs::SECTOR as u64)
        }
        None => Ok(lightfs::DEFAULT_SECTORS),
    }
}

pub fn build_disk_img(total: u64) -> Result<(), String> {
    fs::create_dir_all("storage/apps").map_err(|e| e.to_string())?;
    fs::create_dir_all("storage/data").map_err(|e| e.to_string())?;

    // Khởi tạo file dữ liệu mẫu nếu chưa tồn tại (do revert git)
    let note_path = Path::new("storage/data/note.txt");
    if !note_path.exists() {
        fs::write(note_path, b"Hello world from light os!").map_err(|e| e.to_string())?;
    }

    // 1. Tự động duyệt và biên dịch toàn bộ apps
    let app_count = compile_all_apps("lit_program/apps", "storage/apps")?;
    println!("  ✓ Compiled {} app(s) into 'storage/apps/'", app_count);

    // 2. Đóng gói storage/ vào disk.img (LightFS)
    let lfs = lightfs::pack(Path::new("storage"), Path::new("disk.img"), total)?;
    let used = lfs.used_blocks().iter().filter(|&&u| u).count();
    println!(
        "[4/4] LightFS 'disk.img': {} MB, {} mục, {} / {} khối 4KB đã dùng",
        total / 2048,
        lfs.table.iter().filter(|e| e.used()).count(),
        used,
        lfs.blocks
    );
    Ok(())
}

/// `light fsck [ảnh]`: in báo cáo, mã thoát 1 nếu có lỗi
fn cmd_fsck(img: &str) -> Result<(), String> {
    let r = lightfs::fsck(lightfs::Dev::open(Path::new(img), false)?);
    for n in &r.notes {
        println!("  {}", n);
    }
    for e in &r.errors {
        println!("  LỖI: {}", e);
    }
    println!("{}: {} file, {} thư mục, {} khối dữ liệu, {} lỗi", img, r.files, r.dirs, r.used_blocks, r.errors.len());
    if r.errors.is_empty() { Ok(()) } else { Err(format!("fsck: {} lỗi", r.errors.len())) }
}

fn run() -> Result<(), String> {
    let args: Vec<String> = env::args().collect();

    if args.len() > 1 && args[1] == "sync" {
        // light sync [ảnh hoặc phân vùng, mặc định disk.img]
        let img = args.get(2).map(|s| s.as_str()).unwrap_or("disk.img");
        println!("🔄 Đang đồng bộ ngược từ '{}' về 'storage/'...", img);
        let (n, bad) = lightfs::sync(lightfs::Dev::open(Path::new(img), false)?, Path::new("storage"))?;
        for b in &bad {
            println!("  bỏ qua: {}", b);
        }
        println!("✓ Hoàn tất đồng bộ: {} file", n);
        return Ok(());
    }

    if args.len() > 1 && args[1] == "fsck" {
        return cmd_fsck(args.get(2).map(|s| s.as_str()).unwrap_or("disk.img"));
    }

    if args.len() > 2 && args[1] == "check" {
        let m = parser::parse_file(&args[2])?;
        verify::check_module(&m)?;
        for f in &m.funcs {
            verify::verify_func(&m, f)?;
        }
        println!("OK: {} hàm đã qua kiểm chứng", m.funcs.len());
        return Ok(());
    }

    if args.len() > 2 && args[1] == "check-app" {
        // Kiểm chứng + kiểm tra ABI App (giống lúc pack) nhưng không ghi file
        compile_and_verify_app(&args[2])?;
        println!("OK: App hợp lệ");
        return Ok(());
    }

    if args.len() > 1 && args[1] == "pack" {
        println!("📦 Đang đóng gói 'storage/' vào 'disk.img'...");
        return build_disk_img(size_arg(&args)?);
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

    verify::check_module(&module)?;
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

    build_disk_img(lightfs::DEFAULT_SECTORS)?;
    Ok(())
}

fn main() {
    if let Err(err) = run() {
        eprintln!("\n❌ LỖI BIÊN DỊCH:\n{}", err);
        process::exit(1);
    }
}
