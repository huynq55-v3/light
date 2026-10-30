mod ast;
mod codegen;
mod ivl;
mod parser;
mod vcgen;
mod verifier;

use codegen::MachineCodeEmitter;
use parser::Parser;
use verifier::{VerificationResult, Verifier};
use std::env;
use std::fs;
use std::process::Command;

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
    println!("  cargo run -- run <file.lit>               # Verify contracts via Z3 & run natively (AOT compile-and-exec)");
    println!("  cargo run -- build <file.lit> -o <bin>    # Emit standalone minimal ELF64 binary (~1KB)");
    println!("  cargo run -- verify <file.lit>            # Mathematical formal verification only\n");
}

fn execute_file(file_path: &str, run_binary: bool) {
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

    if run_binary {
        println!("\n🚀 Compiling & Executing standalone native ELF64 binary...");
        let pid = std::process::id();
        let tmp_bin = format!("/tmp/light_run_{}_{}", pid, std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0));
        
        let mut emitter = MachineCodeEmitter::new();
        if let Err(e) = emitter.compile_for_elf(&program) {
            eprintln!("❌ Code generation error: {}", e);
            std::process::exit(1);
        }

        if let Err(e) = emitter.emit_elf64(&tmp_bin) {
            eprintln!("❌ ELF packaging error: {}", e);
            std::process::exit(1);
        }

        let status = Command::new(&tmp_bin).status();
        let _ = fs::remove_file(&tmp_bin);

        match status {
            Ok(s) => {
                if let Some(code) = s.code() {
                    println!("✨ Process finished with exit code: {}", code);
                }
            }
            Err(e) => {
                eprintln!("❌ Process execution failed: {}", e);
                std::process::exit(1);
            }
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
    emitter.compile_for_elf(&program).expect("Compile program");

    emitter.emit_elf64(output_path).expect("Emit ELF");
    let metadata = fs::metadata(output_path).expect("Metadata");
    println!("🎉 Generated standalone executable: '{}' (Size: {} bytes!)", output_path, metadata.len());
    println!("💡 You can run it directly: ./{}", output_path);
}

fn run_verification(program: &ast::Program) -> bool {
    let mut has_failure = false;

    // 0. Function-scoped Symbol & Loop Label Uniqueness Check
    for func in &program.functions {
        let mut seen_labels: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
        for s_inst in &func.instructions {
            let label_name = match &s_inst.inst {
                ast::Instruction::Loop(l) => Some(l),
                ast::Instruction::Label(l) => Some(l),
                _ => None,
            };
            if let Some(lbl) = label_name {
                if let Some(prev_line) = seen_labels.get(lbl) {
                    has_failure = true;
                    eprintln!("  🚨 [FAIL] Symbol Collision in {}(): Duplicate label/loop '{}'", func.name, lbl);
                    eprintln!("     Conflict between line {} and line {}", prev_line, s_inst.loc.line);
                } else {
                    seen_labels.insert(lbl.clone(), s_inst.loc.line);
                }
            }
        }
    }

    for func in &program.functions {
        let results = Verifier::verify_function(func, Some(program));
        for res in results {
            match res {
                VerificationResult::Verified { goal_name, category } => {
                    println!("  🛡️ [PASS - {}] {}", category.badge(), goal_name);
                }
                VerificationResult::Failed { goal_name, category, reason, counter_example, stack_trace } => {
                    has_failure = true;
                    eprintln!("  🚨 [FAIL - {}] {}", category.badge(), goal_name);
                    eprintln!("     Reason: {}", reason);
                    if let Some(ce) = counter_example {
                        eprintln!("     🔍 Z3 Counter-example:\n{}", ce);
                    }
                    if !stack_trace.is_empty() {
                        eprintln!("     📍 Verification Stack Trace (most recent call first):");
                        for (idx, frame) in stack_trace.iter().enumerate() {
                            let rel_file = if let Ok(cwd) = std::env::current_dir() {
                                frame.file.strip_prefix(cwd.to_str().unwrap_or("")).unwrap_or(&frame.file).trim_start_matches('/')
                            } else {
                                &frame.file
                            };
                            eprintln!("       ↳ [{}] {}:{} in {}", idx + 1, rel_file, frame.line, frame.function);
                            eprintln!("             | {}  <-- {}", frame.snippet, frame.role);
                        }
                    }
                }
                VerificationResult::Unknown { goal_name, category, reason, stack_trace } => {
                    has_failure = true;
                    eprintln!("  ❓ [UNKNOWN - {}] {}", category.badge(), goal_name);
                    eprintln!("     Reason: {}", reason);
                    if !stack_trace.is_empty() {
                        eprintln!("     📍 Verification Stack Trace (most recent call first):");
                        for (idx, frame) in stack_trace.iter().enumerate() {
                            let rel_file = if let Ok(cwd) = std::env::current_dir() {
                                frame.file.strip_prefix(cwd.to_str().unwrap_or("")).unwrap_or(&frame.file).trim_start_matches('/')
                            } else {
                                &frame.file
                            };
                            eprintln!("       ↳ [{}] {}:{} in {}", idx + 1, rel_file, frame.line, frame.function);
                            eprintln!("             | {}  <-- {}", frame.snippet, frame.role);
                        }
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
