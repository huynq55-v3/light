mod ast;
mod jit;
mod parser;
mod verifier;
mod vm;

use jit::MachineCodeEmitter;
use parser::Parser;
use verifier::{VerificationResult, Verifier};
use vm::VirtualMachine;
use std::env;
use std::fs;

fn main() {
    let args: Vec<String> = env::args().collect();

    println!("╔══════════════════════════════════════════════════════════════╗");
    println!("║       LIGHT COMPILER & VERIFIER (.lit) - v0.1.0             ║");
    println!("║       AI-Native • Flat SSA • Z3 SMT • Zero C Dependency     ║");
    println!("╚══════════════════════════════════════════════════════════════╝\n");

    if args.len() < 2 {
        print_usage();
        return;
    }

    let command = &args[1];
    match command.as_str() {
        "run" => {
            if args.len() < 3 {
                eprintln!("Lỗi: Thiếu đường dẫn file .lit để chạy!");
                return;
            }
            execute_file(&args[2], true);
        }
        "jit" => {
            if args.len() < 3 {
                eprintln!("Lỗi: Thiếu đường dẫn file .lit để chạy JIT!");
                return;
            }
            execute_jit(&args[2]);
        }
        "build" => {
            if args.len() < 3 {
                eprintln!("Lỗi: Thiếu đường dẫn file .lit để build!");
                return;
            }
            let out = if args.len() >= 5 && args[3] == "-o" {
                &args[4]
            } else {
                "a.out"
            };
            build_elf(&args[2], out);
        }
        "verify" => {
            if args.len() < 3 {
                eprintln!("Lỗi: Thiếu đường dẫn file .lit để kiểm chứng!");
                return;
            }
            execute_file(&args[2], false);
        }
        _ => {
            execute_file(command, true);
        }
    }
}

fn print_usage() {
    println!("Cách sử dụng:");
    println!("  cargo run -- run <file.lit>               # Kiểm chứng Z3 và chạy qua Safe VM");
    println!("  cargo run -- jit <file.lit>               # Biên dịch & chạy mã máy x86_64 qua JIT RAM");
    println!("  cargo run -- build <file.lit> -o <bin>    # Xuất file nhị phân độc lập ELF64 (~500B)");
    println!("  cargo run -- verify <file.lit>            # Chỉ kiểm chứng toán học với Z3\n");
}

fn execute_file(file_path: &str, run_vm: bool) {
    println!("📂 Đang nạp mã nguồn: {}", file_path);
    println!("⚡ Đang phân tích cú pháp & giải quyết IMPORT...");
    let program = match Parser::parse_file(file_path) {
        Ok(p) => {
            println!("✅ Cú pháp hợp lệ! Đã phát hiện {} hàm.", p.functions.len());
            p
        }
        Err(e) => {
            eprintln!("❌ {}", e);
            return;
        }
    };

    println!("\n🧠 Đang kiểm chứng toán học bằng Z3 SMT Solver...");
    if !run_verification(&program) {
        eprintln!("\n❌ BIÊN DỊCH THẤT BẠI: Phát hiện lỗi logic/bộ nhớ! Trình biên dịch từ chối thực thi.");
        std::process::exit(1);
    }

    if run_vm {
        println!("\n🚀 Bắt đầu thực thi chương trình trên Safe VM...");
        let main_func = program.functions.iter().find(|f| f.name == "main");
        if let Some(func) = main_func {
            let mut vm = VirtualMachine::with_program(&program);
            match vm.run_function(func, &[]) {
                Ok(ret) => {
                    if let Some(val) = ret {
                        println!("✨ Hàm main() trả về: {:?}", val);
                    }
                }
                Err(e) => {
                    eprintln!("❌ Lỗi thực thi VM: {}", e);
                }
            }
        }
    }
}

fn execute_jit(file_path: &str) {
    println!("📂 Đang nạp mã nguồn JIT: {}", file_path);
    let program = match Parser::parse_file(file_path) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("❌ {}", e);
            return;
        }
    };
    if !run_verification(&program) {
        eprintln!("\n❌ JIT THẤT BẠI: Phát hiện lỗi logic/bộ nhớ! Trình biên dịch từ chối phát mã máy.");
        std::process::exit(1);
    }

    println!("\n⚡ [JIT] Đang phát sinh mã máy x86_64 cho toàn bộ hàm...");
    let mut emitter = MachineCodeEmitter::new();
    let data_vaddr = emitter.data_section.as_ptr() as u64;
    emitter.compile_program(&program, data_vaddr).expect("Compile program");

    println!("🔥 Đã sinh {} bytes mã máy x86_64!", emitter.code.len());
    println!("🚀 Đang gọi CPU thực thi trực tiếp qua mmap PROT_EXEC...");
    unsafe {
        match emitter.run_jit() {
            Ok(code) => println!("✨ Mã thoát từ JIT Native: {}", code),
            Err(e) => eprintln!("❌ Lỗi JIT: {}", e),
        }
    }
}

fn build_elf(file_path: &str, output_path: &str) {
    println!("📂 Đang biên dịch Standalone ELF64: {}", file_path);
    let program = match Parser::parse_file(file_path) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("❌ {}", e);
            return;
        }
    };

    if !run_verification(&program) {
        eprintln!("\n❌ BIÊN DỊCH THẤT BẠI: Phát hiện lỗi logic/bộ nhớ! Trình biên dịch từ chối xuất file thực thi.");
        std::process::exit(1);
    }

    println!("\n🛠️ [Codegen] Đang đóng gói file thực thi ELF64 Linux...");
    let mut emitter = MachineCodeEmitter::new();
    
    // Đo độ dài code ước lượng: Pass 1
    let _ = emitter.compile_program(&program, 0x400000 + 120);
    let code_len = emitter.code.len();

    // Reset và compile pass 2 với địa chỉ data chính xác
    let mut emitter = MachineCodeEmitter::new();
    let elf_data_vaddr = 0x400000u64 + 120u64 + (code_len as u64);
    emitter.compile_program(&program, elf_data_vaddr).expect("Compile program");

    emitter.emit_elf64(output_path).expect("Emit ELF");
    let metadata = fs::metadata(output_path).expect("Metadata");
    println!("🎉 Đã tạo file thực thi độc lập: '{}' (Kích thước: {} bytes!)", output_path, metadata.len());
    println!("💡 Bạn có thể chạy trực tiếp: ./{}", output_path);
}

fn run_verification(program: &ast::Program) -> bool {
    let mut has_failure = false;
    for func in &program.functions {
        let results = Verifier::verify_function(func);
        for res in results {
            match res {
                VerificationResult::Verified { goal_name } => {
                    println!("  🛡️ [PASS] {}", goal_name);
                }
                VerificationResult::Failed { goal_name, reason, counter_example } => {
                    has_failure = true;
                    eprintln!("  🚨 [FAIL] {}", goal_name);
                    eprintln!("     Nguyên nhân: {}", reason);
                    if let Some(ce) = counter_example {
                        eprintln!("     🔍 Phản ví dụ từ Z3:\n{}", ce);
                    }
                }
                VerificationResult::SolverNotFound { goal_name, .. } => {
                    println!("  ⚠️ [CHƯA CÓ Z3] {}", goal_name);
                }
            }
        }
    }
    !has_failure
}
