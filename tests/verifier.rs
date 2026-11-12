//! Bộ test hồi quy cho parser + verifier Light.
//!
//! - `tests/lit/must_fail/*.lit`: PHẢI bị từ chối. Dòng `# EXPECT: <chuỗi>` = đoạn thông báo lỗi bắt buộc xuất hiện
//!   (để chắc chắn bị từ chối đúng lý do, không phải vì một lỗi cú pháp vô tình).
//! - `tests/lit/must_pass/*.lit`: PHẢI qua kiểm chứng (chống verifier quá khắt khe sau khi sửa).
//! - `tests/lit/known_holes/*.lit`: lỗ hổng ĐÃ BIẾT nhưng CHƯA vá — hiện vẫn qua kiểm chứng. Khi vá xong, test này sẽ
//!   báo đỏ: thêm `# EXPECT:` rồi chuyển file sang `must_fail/`.
//! - Cuối cùng: toàn bộ lit_program/std phải qua kiểm chứng.

use std::path::{Path, PathBuf};
use std::process::Command;

fn light(args: &[&str]) -> (bool, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_light"))
        .args(args)
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("không chạy được binary light");
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    (out.status.success(), text)
}

fn lit_files(dir: &str) -> Vec<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/lit").join(dir);
    let Ok(rd) = std::fs::read_dir(&d) else {
        assert!(dir == "known_holes", "thiếu thư mục {}", d.display());
        return vec![];
    };
    let mut v: Vec<PathBuf> = rd
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "lit"))
        .collect();
    v.sort();
    assert!(!v.is_empty() || dir == "known_holes", "thư mục {} không có file .lit", d.display());
    v
}

fn header(src: &str, key: &str) -> Option<String> {
    src.lines()
        .filter_map(|l| l.trim().strip_prefix('#'))
        .find_map(|l| l.trim().strip_prefix(key).map(|v| v.trim().to_string()))
}

fn run_file(p: &Path) -> (bool, String) {
    light(&["check", p.to_str().unwrap()])
}

fn report(fails: Vec<String>) {
    assert!(fails.is_empty(), "\n{}\n", fails.join("\n\n"));
}

#[test]
fn must_fail_cases_are_rejected_for_the_right_reason() {
    let mut fails = vec![];
    for p in lit_files("must_fail") {
        let src = std::fs::read_to_string(&p).unwrap();
        let name = p.file_name().unwrap().to_string_lossy().to_string();
        let Some(expect) = header(&src, "EXPECT:") else {
            fails.push(format!("{}: thiếu dòng `# EXPECT: ...`", name));
            continue;
        };
        let (ok, out) = run_file(&p);
        if ok {
            fails.push(format!("{}: LỖ HỔNG — verifier chấp nhận chương trình phải bị từ chối", name));
        } else if !out.contains(&expect) {
            fails.push(format!(
                "{}: bị từ chối nhưng sai lý do.\n  cần: {}\n  được: {}",
                name,
                expect,
                out.trim()
            ));
        }
    }
    report(fails);
}

#[test]
fn must_pass_cases_are_accepted() {
    let mut fails = vec![];
    for p in lit_files("must_pass") {
        let (ok, out) = run_file(&p);
        if !ok {
            fails.push(format!("{}: {}", p.display(), out.trim()));
        }
    }
    report(fails);
}

#[test]
fn known_holes_are_still_open() {
    let mut fails = vec![];
    for p in lit_files("known_holes") {
        let (ok, out) = run_file(&p);
        if !ok {
            fails.push(format!(
                "{}: lỗ hổng này giờ đã bị chặn ({}). Thêm `# EXPECT:` và chuyển file sang tests/lit/must_fail/.",
                p.display(),
                out.trim().lines().last().unwrap_or("")
            ));
        }
    }
    report(fails);
}

#[test]
fn real_std_verifies() {
    // Toàn bộ lit_program/std phải qua kiểm chứng (kể cả chứng minh dừng)
    let mut fails = vec![];
    let std_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("lit_program/std");
    for e in std::fs::read_dir(std_dir).unwrap() {
        let p = e.unwrap().path();
        if p.extension().is_some_and(|x| x == "lit") {
            let (ok, out) = light(&["check", p.to_str().unwrap()]);
            if !ok {
                fails.push(format!("{}: {}", p.display(), out.trim()));
            }
        }
    }
    report(fails);
}
