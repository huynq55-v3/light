// File: src/bin/litfmt.rs
// Công cụ Format mã nguồn .lit tự động (Auto-Formatter cho ngôn ngữ Light)
use std::path::Path;
use std::{env, fs, process};

#[derive(Clone, Copy, PartialEq)]
enum Scope {
    Top,
    Layout,
    FuncHeader,
    Block,
}

pub fn format_lit_source(src: &str) -> String {
    let mut out = String::new();
    let mut scope = Scope::Top;
    let mut prev_blank = true;

    for raw_line in src.lines() {
        let trimmed = raw_line.trim();

        // 1. Xử lý dòng trống (Không để quá 1 dòng trống liên tiếp)
        if trimmed.is_empty() {
            if !prev_blank {
                out.push('\n');
                prev_blank = true;
            }
            continue;
        }

        // 2. Xử lý dòng chỉ chứa comment (# ...)
        if trimmed.starts_with('#') {
            let indent = match scope {
                Scope::Top => "",
                Scope::Layout | Scope::FuncHeader => "    ",
                Scope::Block => "        ",
            };
            out.push_str(indent);
            out.push_str(trimmed);
            out.push('\n');
            prev_blank = false;
            continue;
        }

        // 3. Tách phần lệnh SSA (bảo toàn chuỗi "...") và phần comment cuối dòng (inline comment)
        let mut toks = Vec::new();
        let mut cur = String::new();
        let mut comment_part: Option<String> = None;
        let mut chars = trimmed.chars().peekable();
        let mut in_quotes = false;

        while let Some(c) = chars.next() {
            if in_quotes {
                cur.push(c);
                if c == '\\' {
                    if let Some(nc) = chars.next() {
                        cur.push(nc);
                    }
                } else if c == '"' {
                    in_quotes = false;
                    toks.push(std::mem::take(&mut cur));
                }
            } else {
                match c {
                    '#' => {
                        if !cur.is_empty() {
                            toks.push(std::mem::take(&mut cur));
                        }
                        let rest: String = chars.collect();
                        comment_part = Some(rest.trim().to_string());
                        break;
                    }
                    '"' => {
                        if !cur.is_empty() {
                            toks.push(std::mem::take(&mut cur));
                        }
                        cur.push('"');
                        in_quotes = true;
                    }
                    w if w.is_whitespace() => {
                        if !cur.is_empty() {
                            toks.push(std::mem::take(&mut cur));
                        }
                    }
                    _ => cur.push(c),
                }
            }
        }
        if !cur.is_empty() {
            toks.push(cur);
        }
        if toks.is_empty() {
            continue;
        }
        let norm_code = toks.join(" ");
        let first = toks[0].as_str();

        // 4. Xác định cấp độ thụt lề (Indent) và chuyển trạng thái Scope
        let indent = match first {
            "}" => {
                scope = Scope::Top;
                ""
            }
            "layout" => {
                scope = Scope::Layout;
                ""
            }
            "func" => {
                scope = Scope::FuncHeader;
                ""
            }
            "include" | "def" => "",
            "@req" | "@ens" => "    ",
            b if b.starts_with('@') && b != "@inv" => {
                // Tự động chèn 1 dòng trống trước mỗi Basic Block (@b0, @b1...)
                if !prev_blank {
                    out.push('\n');
                }
                scope = Scope::Block;
                "    "
            }
            _ => match scope {
                Scope::Top => "",
                Scope::Layout | Scope::FuncHeader => "    ",
                Scope::Block => "        ",
            },
        };

        let mut line_out = format!("{}{}", indent, norm_code);

        // 5. Căn thẳng cột comment cuối dòng (cột 44)
        if let Some(cmt) = &comment_part {
            let pad = if line_out.len() < 44 {
                44 - line_out.len()
            } else {
                2
            };
            for _ in 0..pad {
                line_out.push(' ');
            }
            line_out.push_str("# ");
            line_out.push_str(cmt);
        }

        out.push_str(&line_out);
        out.push('\n');
        prev_blank = false;
    }

    out.trim_end().to_string() + "\n"
}

fn format_path(path: &Path, count: &mut usize) -> Result<(), String> {
    if path.is_dir() {
        for entry in fs::read_dir(path).map_err(|e| e.to_string())? {
            let entry = entry.map_err(|e| e.to_string())?;
            format_path(&entry.path(), count)?;
        }
    } else if path.extension().and_then(|s| s.to_str()) == Some("lit") {
        let original = fs::read_to_string(path).map_err(|e| e.to_string())?;
        let formatted = format_lit_source(&original);
        if original != formatted {
            fs::write(path, formatted).map_err(|e| e.to_string())?;
            println!("  ✨ Formatted: {}", path.display());
        } else {
            println!("  ✓ Clean:     {}", path.display());
        }
        *count += 1;
    }
    Ok(())
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let targets = if args.len() > 1 {
        args[1..].to_vec()
    } else {
        vec!["lit_program".to_string(), "storage".to_string()]
    };

    let mut count = 0;
    for t in targets {
        let p = Path::new(&t);
        if p.exists() {
            if let Err(e) = format_path(p, &mut count) {
                eprintln!("❌ Lỗi format '{}': {}", t, e);
                process::exit(1);
            }
        }
    }
    println!("✅ Hoàn tất kiểm tra & format {} file(s) .lit!", count);
}
