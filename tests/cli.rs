// Kiểm thử công cụ dòng lệnh: chẩn đoán JSON, light doc, cache Z3.
use std::path::PathBuf;
use std::process::Command;

fn light(dir: &PathBuf, args: &[&str]) -> (String, String, bool) {
    let o = Command::new(env!("CARGO_BIN_EXE_light")).args(args).current_dir(dir).output().unwrap();
    (String::from_utf8_lossy(&o.stdout).into(), String::from_utf8_lossy(&o.stderr).into(), o.status.success())
}

fn scratch(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("light_cli_{}_{}", name, std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).unwrap();
    d
}

const BAD: &str = "func bad_add bv64 %0:bv64 %1:bv64 {\n    @b0\n        %2 = add %0 %1\n        ret %2\n}\n\nfunc bad_div bv64 %0:bv64 %1:bv64 {\n    @b0\n        %2 = udiv %0 %1\n        ret %2\n}\n\nfunc good bv64 %0:bv64 {\n    @req ult %0 100\n    @b0\n        %1 = const 1 bv64\n        %2 = add %0 %1\n        ret %2\n}\n";

#[test]
fn json_reports_every_bad_function_with_counterexample_and_hint() {
    let d = scratch("json");
    std::fs::write(d.join("bad.lit"), BAD).unwrap();
    let (out, _, ok) = light(&d, &["check", "bad.lit", "--json", "--no-cache"]);
    assert!(!ok);
    assert!(out.starts_with("{\"ok\":false"), "{}", out);
    assert!(out.contains("\"func\":\"bad_add\"") && out.contains("\"func\":\"bad_div\""), "{}", out);
    assert!(!out.contains("\"func\":\"good\""), "{}", out);
    assert!(out.contains("\"counterexample\":[{\"reg\""), "{}", out);
    assert!(out.contains("\"hint\":\"Phép toán"), "{}", out);
    assert!(out.contains("bad.lit:1"), "origin phải trỏ tới dòng khai báo hàm: {}", out);
}

#[test]
fn json_parse_error_has_origin_and_source() {
    let d = scratch("parse");
    std::fs::write(d.join("p.lit"), "func x bv64 %0:bv64 {\n    @b0\n        %1 = bogus %0\n        ret %1\n}\n").unwrap();
    let (out, _, ok) = light(&d, &["check", "p.lit", "--json"]);
    assert!(!ok);
    assert!(out.contains("\"kind\":\"parse\"") && out.contains("p.lit:3") && out.contains("%1 = bogus %0"), "{}", out);
}

#[test]
fn cache_hits_on_second_run_and_invalidates_on_change() {
    let d = scratch("cache");
    let good = "func inc bv64 %0:bv64 {\n    @req ult %0 100\n    @b0\n        %1 = const 1 bv64\n        %2 = add %0 %1\n        ret %2\n}\n";
    std::fs::write(d.join("g.lit"), good).unwrap();
    let (a, _, ok) = light(&d, &["check", "g.lit", "--json"]);
    assert!(ok && a.contains("\"verified\":1,\"cache_hits\":0"), "{}", a);
    let (b, _, _) = light(&d, &["check", "g.lit", "--json"]);
    assert!(b.contains("\"verified\":0,\"cache_hits\":1"), "{}", b);
    // đổi hợp đồng -> phải kiểm chứng lại (và lần này sai vì có thể tràn)
    std::fs::write(d.join("g.lit"), good.replace("ult %0 100", "ule %0 0xffffffffffffffff")).unwrap();
    let (c, _, ok) = light(&d, &["check", "g.lit", "--json"]);
    assert!(!ok && c.contains("Tràn số cộng"), "{}", c);
}

#[test]
fn doc_lists_contracts_and_supports_json() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let (t, _, ok) = light(&root, &["doc", "q512"]);
    assert!(ok && t.contains("func q512(") && t.contains("@req ult %1 512"), "{}", t);
    let (j, _, _) = light(&root, &["doc", "lfs_find_child", "--json"]);
    assert!(j.starts_with("[{\"kind\":\"func\",\"name\":\"lfs_find_child\"") && j.contains("\"ensures\":[\"ult %20 256\"]"), "{}", j);
}
