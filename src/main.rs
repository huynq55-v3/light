// File: src/main.rs — CLI của trình biên dịch / kiểm chứng Light: check, doc, stack-report
mod elf64;
mod front;
mod ir;
mod parser;
mod verify;
mod x86;
#[macro_use]
mod tooling;

use std::{env, fs, process};

fn run() -> Result<(), String> {
    let mut args: Vec<String> = env::args().collect();
    let json = args.iter().any(|a| a == "--json");
    let no_cache = args.iter().any(|a| a == "--no-cache");
    args.retain(|a| a != "--json" && a != "--no-cache");
    tooling::set_flags(json, no_cache);

    if args.len() > 1 && args[1] == "stack-report" {
        // Biên dịch mọi file .lit được chỉ định (mặc định: lit_program/std), đối chiếu khung stack thật với cận verifier
        let mut files: Vec<String> = args[2..].to_vec();
        if files.is_empty() {
            for e in fs::read_dir("lit_program/std").map_err(|e| e.to_string())? {
                let p = e.map_err(|e| e.to_string())?.path();
                if matches!(p.extension().and_then(|s| s.to_str()), Some("lit" | "lt")) {
                    files.push(p.to_string_lossy().into_owned());
                }
            }
            files.sort();
        }
        let mut total = 0;
        let mut worst = i64::MAX;
        for f in &files {
            let m = parser::parse_file(f)?;
            let _ = x86::take_frames();
            elf64::compile_code(&m, false)?;
            let (n, slack) = verify::check_frames(&m, &x86::take_frames())?;
            say!("  {}: {} hàm, khoảng trống nhỏ nhất {} byte", f, n, slack);
            total += n;
            worst = worst.min(slack);
        }
        say!("OK: {} hàm, khung thật luôn <= cận verifier (khoảng trống nhỏ nhất {} byte)", total, worst);
        return Ok(());
    }

    // light lower FILE.lt: in văn bản SSA mà front-end cú pháp B sinh ra (cột phải: vị trí gốc)
    if args.len() > 2 && args[1] == "lower" {
        for (line, origin) in front::lower_file(std::path::Path::new(&args[2]))? {
            if args.iter().any(|a| a == "--origins") {
                println!("{:<60} # {}", line, origin);
            } else {
                println!("{}", line);
            }
        }
        return Ok(());
    }

    // light tokens FILE.lt|-: số token cú pháp B (để so độ dài với SSA)
    if args.len() > 2 && args[1] == "tokens" {
        let src = if args[2] == "-" {
            let mut s = String::new();
            std::io::Read::read_to_string(&mut std::io::stdin(), &mut s).map_err(|e| e.to_string())?;
            s
        } else {
            std::fs::read_to_string(&args[2]).map_err(|e| e.to_string())?
        };
        println!("{}", front::count_tokens(&src)?);
        return Ok(());
    }

    if args.len() > 1 && args[1] == "doc" {
        return tooling::cmd_doc(&args[2..]);
    }

    if args.len() > 2 && args[1] == "check" {
        let m = parser::parse_file(&args[2])?;
        tooling::register_module(&m);
        verify::check_module(&m)?;
        // Báo MỌI hàm hỏng trong một lượt (không dừng ở hàm đầu tiên)
        for f in &m.funcs {
            if let Err(e) = tooling::verify_cached(&m, f) {
                tooling::push_error(e);
            }
        }
        let bad = tooling::take_errors();
        if !bad.is_empty() {
            let n = bad.len();
            if tooling::json_mode() {
                for e in bad {
                    tooling::push_error(e);
                }
            } else {
                for e in &bad {
                    eprintln!("{}\n", tooling::pretty_err(e));
                }
            }
            return Err(format!("{} hàm không qua kiểm chứng", n));
        }
        say!("OK: {} hàm đã qua kiểm chứng ({})", m.funcs.len(), tooling::cache_summary());
        return Ok(());
    }

    Err("cách dùng: light check FILE.lit|FILE.lt | light lower FILE.lt [--origins] | light doc [...] | light stack-report [FILE.lit...]  (thêm --json, --no-cache)".into())
}

fn main() {
    match run() {
        Ok(()) => {
            if tooling::json_mode() && !env::args().any(|a| a == "doc") {
                println!("{}", tooling::ok_json());
            }
        }
        Err(err) => {
            if tooling::json_mode() {
                println!("{}", tooling::error_json(&err));
            } else {
                eprintln!("\n❌ LỖI BIÊN DỊCH:\n{}", tooling::pretty_err(&err));
            }
            process::exit(1);
        }
    }
}
