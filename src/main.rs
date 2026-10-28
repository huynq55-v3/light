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
                eprintln!("Error: Missing .lit source file path to run!");
                return;
            }
            execute_file(&args[2], true);
        }
        "jit" => {
            if args.len() < 3 {
                eprintln!("Error: Missing .lit source file path for JIT execution!");
                return;
            }
            execute_jit(&args[2]);
        }
        "build" => {
            if args.len() < 3 {
                eprintln!("Error: Missing .lit source file path to build!");
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
                eprintln!("Error: Missing .lit source file path to verify!");
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
    println!("Usage:");
    println!("  cargo run -- run <file.lit>               # Verify contracts via Z3 & run on Safe VM");
    println!("  cargo run -- jit <file.lit>               # Direct x86_64 JIT execution via RAM");
    println!("  cargo run -- build <file.lit> -o <bin>    # Emit standalone minimal ELF64 binary (~300B)");
    println!("  cargo run -- verify <file.lit>            # Mathematical formal verification only\n");
}

fn execute_file(file_path: &str, run_vm: bool) {
    println!("📂 Loading source file: {}", file_path);
    println!("⚡ Parsing flat SSA instructions & resolving IMPORTs...");
    let program = match Parser::parse_file(file_path) {
        Ok(p) => {
            println!("✅ Valid syntax! Detected {} function(s).", p.functions.len());
            p
        }
        Err(e) => {
            eprintln!("❌ {}", e);
            std::process::exit(1);
        }
    };

    println!("\n🧠 Performing formal verification via Z3 SMT Solver...");
    if !run_verification(&program) {
        eprintln!("\n❌ VERIFICATION FAILED: Logical or memory safety contract violated!");
        std::process::exit(1);
    }

    if run_vm {
        println!("\n🚀 Executing program on Safe Virtual Machine...");
        let main_func = program.functions.iter().find(|f| f.name == "main");
        if let Some(func) = main_func {
            let mut vm = VirtualMachine::with_program(&program);
            match vm.run_function(func, &[]) {
                Ok(ret) => {
                    if let Some(val) = ret {
                        println!("✨ main() returned: {:?}", val);
                    }
                }
                Err(e) => {
                    eprintln!("❌ VM runtime error: {}", e);
                }
            }
        }
    }
}

fn execute_jit(file_path: &str) {
    println!("📂 Loading source file for JIT: {}", file_path);
    let program = match Parser::parse_file(file_path) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("❌ {}", e);
            std::process::exit(1);
        }
    };
    if !run_verification(&program) {
        eprintln!("\n❌ JIT ABORTED: Contract verification failed!");
        std::process::exit(1);
    }

    println!("\n⚡ [JIT] Emitting native x86_64 machine code for all functions...");
    let mut emitter = MachineCodeEmitter::new();
    let data_vaddr = emitter.data_section.as_ptr() as u64;
    emitter.compile_program(&program, data_vaddr).expect("Compile program");

    println!("🔥 Generated {} bytes of native x86_64 machine code!", emitter.code.len());
    println!("🚀 Calling CPU directly via mmap PROT_EXEC...");
    unsafe {
        match emitter.run_jit() {
            Ok(code) => println!("✨ Exit code from native JIT: {}", code),
            Err(e) => eprintln!("❌ JIT Error: {}", e),
        }
    }
}

fn build_elf(file_path: &str, output_path: &str) {
    println!("📂 Compiling standalone ELF64 binary: {}", file_path);
    let program = match Parser::parse_file(file_path) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("❌ {}", e);
            std::process::exit(1);
        }
    };

    if !run_verification(&program) {
        eprintln!("\n❌ BUILD ABORTED: Contract verification failed! Binary will not be emitted.");
        std::process::exit(1);
    }

    println!("\n🛠️ [Codegen] Packaging standalone Linux ELF64 executable...");
    let mut emitter = MachineCodeEmitter::new();
    
    // Estimate code size in pass 1
    let _ = emitter.compile_program(&program, 0x400000 + 120);
    let code_len = emitter.code.len();

    // Pass 2 with exact data virtual address
    let mut emitter = MachineCodeEmitter::new();
    let elf_data_vaddr = 0x400000u64 + 120u64 + (code_len as u64);
    emitter.compile_program(&program, elf_data_vaddr).expect("Compile program");

    emitter.emit_elf64(output_path).expect("Emit ELF");
    let metadata = fs::metadata(output_path).expect("Metadata");
    println!("🎉 Generated standalone executable: '{}' (Size: {} bytes!)", output_path, metadata.len());
    println!("💡 You can run it directly: ./{}", output_path);
}

fn run_verification(program: &ast::Program) -> bool {
    let mut has_failure = false;
    for func in &program.functions {
        let results = Verifier::verify_function(func, Some(program));
        for res in results {
            match res {
                VerificationResult::Verified { goal_name } => {
                    println!("  🛡️ [PASS] {}", goal_name);
                }
                VerificationResult::Failed { goal_name, reason, counter_example } => {
                    has_failure = true;
                    eprintln!("  🚨 [FAIL] {}", goal_name);
                    eprintln!("     Reason: {}", reason);
                    if let Some(ce) = counter_example {
                        eprintln!("     🔍 Z3 Counter-example:\n{}", ce);
                    }
                }
                VerificationResult::SolverNotFound { goal_name, .. } => {
                    println!("  ⚠️ [NO Z3 CLI] {}", goal_name);
                }
            }
        }
    }
    !has_failure
}
