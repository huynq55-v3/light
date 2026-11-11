//! Test vi sai cho bộ sinh mã x86-64: chạy `cgtest` (mã máy thật trên host vs trình thông dịch tham chiếu) trên
//! tests/lit/codegen/*.lit và 1000 chương trình ngẫu nhiên.
use std::process::Command;

#[test]
fn codegen_matches_interpreter() {
    let out = Command::new(env!("CARGO_BIN_EXE_cgtest"))
        .args(["--runs", "500", "--fuzz", "1000"])
        .output()
        .expect("không chạy được cgtest");
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success() && text.contains("\nOK"), "cgtest thất bại:\n{}", text);
}
