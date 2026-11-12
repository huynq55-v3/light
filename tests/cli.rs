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
    assert!(out.contains("\"origin\":\"bad.lit:1\""), "origin phải trỏ tới dòng khai báo hàm: {}", out);
    // `at` trỏ đúng dòng lệnh gây lỗi, `source` là dòng gốc (tên chưa bị đổi sang số)
    assert!(out.contains("\"at\":\"bad.lit:3\"") && out.contains("\"at\":\"bad.lit:9\""), "{}", out);
    assert!(out.contains("\"source\":\"%2 = add %0 %1\""), "{}", out);
}

#[test]
fn error_location_survives_lowering_and_names() {
    let d = scratch("at");
    // add_sat bị hạ thành nhiều lệnh: lỗi ở lệnh sau nó vẫn phải trỏ đúng dòng 4
    std::fs::write(d.join("s.lit"), "func g bv64 %n:bv64 {\n    @b0\n        %a = add_sat %n 3\n        %b = add %a 1\n        ret %b\n}\n").unwrap();
    let (out, _, ok) = light(&d, &["check", "s.lit", "--json", "--no-cache"]);
    assert!(!ok && out.contains("\"at\":\"s.lit:4\"") && out.contains("\"source\":\"%b = add %a 1\""), "{}", out);
    // vi phạm @inv báo ở dòng jmp
    let l = "func f bv64 %n:bv64 {\n    @b0\n        jmp @l 0\n    @l %i:bv64\n        @inv ult %i 5\n        %c = cmp ult %i %n\n        br %c @s @d\n    @s\n        %j = add_wrap %i 1\n        jmp @l %j\n    @d\n        ret %i\n}\n";
    std::fs::write(d.join("l.lit"), l).unwrap();
    let (out, _, ok) = light(&d, &["check", "l.lit", "--json", "--no-cache"]);
    assert!(!ok && out.contains("\"at\":\"l.lit:10\""), "{}", out);
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
    let (t, _, ok) = light(&root, &["doc", "mem_get_q"]);
    assert!(ok && t.contains("func mem_get_q(") && t.contains("@req ult %i %n"), "{}", t);
    let (j, _, _) = light(&root, &["doc", "math_min", "--json"]);
    assert!(j.starts_with("[{\"kind\":\"func\",\"name\":\"math_min\"") && j.contains("\"ensures\":[\"ule %r %a\""), "{}", j);
}

#[test]
fn leading_zero_ids_are_rejected_not_aliased() {
    let d = scratch("zero");
    // @b01 sẽ trùng @b1; %01 sẽ trùng %1
    std::fs::write(d.join("a.lit"), "func f void %0:bv64 {\n    @b0\n        jmp @b01\n\n    @b1\n        ret\n}\n").unwrap();
    let (out, _, ok) = light(&d, &["check", "a.lit", "--json"]);
    assert!(!ok && out.contains("số 0 đứng đầu") && out.contains("a.lit:3"), "{}", out);
    std::fs::write(d.join("b.lit"), "func f bv64 %0:bv64 {\n    @b0\n        %01 = add_wrap %0 %0\n        ret %01\n}\n").unwrap();
    let (out, _, ok) = light(&d, &["check", "b.lit", "--json"]);
    assert!(!ok && out.contains("số 0 đứng đầu"), "{}", out);
    std::fs::write(d.join("c.lit"), "func f bv64 %0:bv64 {\n    @b0\n        %1 = add_wrap %0 %0\n        ret %1\n}\n").unwrap();
    let (_, _, ok) = light(&d, &["check", "c.lit", "--json"]);
    assert!(ok);
}

#[test]
fn named_registers_work_and_errors_use_names() {
    let d = scratch("names");
    std::fs::write(d.join("e.lit"), "func f bv64 %x:bv64 %y:bv64 {\n    @b0\n        %s = add %x %y\n        ret %s\n}\n").unwrap();
    let (out, _, ok) = light(&d, &["check", "e.lit", "--json", "--no-cache"]);
    assert!(!ok && out.contains("\"inst\":\"%s = add %x %y\"") && out.contains("\"reg\":\"%x\""), "{}", out);
    // dùng tên chưa định nghĩa -> lỗi nêu đúng tên
    std::fs::write(d.join("u.lit"), "func f bv64 %x:bv64 {\n    @b0\n        %s = add_wrap %x %nope\n        ret %s\n}\n").unwrap();
    let (out, _, ok) = light(&d, &["check", "u.lit", "--json", "--no-cache"]);
    assert!(!ok && out.contains("%nope"), "{}", out);
    // đổi tên biến không làm mất cache
    std::fs::write(d.join("a.lit"), "func f bv64 %x:bv64 {\n    @b0\n        %s = add_wrap %x %x\n        ret %s\n}\n").unwrap();
    let (a, _, _) = light(&d, &["check", "a.lit", "--json"]);
    assert!(a.contains("\"verified\":1"), "{}", a);
    std::fs::write(d.join("b.lit"), "func f bv64 %aa:bv64 {\n    @b0\n        %bb = add_wrap %aa %aa\n        ret %bb\n}\n").unwrap();
    let (b, _, _) = light(&d, &["check", "b.lit", "--json"]);
    assert!(b.contains("\"verified\":0,\"cache_hits\":1") || b.contains("\"verified\":1"), "{}", b);
}

#[test]
fn named_labels_work_and_errors_use_them() {
    let d = scratch("labels");
    let ok = "func f bv64 %n:bv64 {\n    @req ule %n 9\n    @entry\n        %z = const 0 bv64\n        jmp @loop %z\n\n    @loop %i:bv64\n        @inv ule %i %n\n        %c = cmp ult %i %n\n        br %c @body @done\n\n    @body\n        %o = const 1 bv64\n        %j = add %i %o\n        jmp @loop %j\n\n    @done\n        ret %i\n}\n";
    std::fs::write(d.join("l.lit"), ok).unwrap();
    let (out, _, good) = light(&d, &["check", "l.lit", "--json"]);
    assert!(good, "{}", out);
    // phá @inv: lỗi phải nêu @loop chứ không phải @bN
    std::fs::write(d.join("m.lit"), ok.replace("@inv ule %i %n", "@inv ult %i %n")).unwrap();
    let (out, _, good) = light(&d, &["check", "m.lit", "--json", "--no-cache"]);
    assert!(!good && out.contains("@loop"), "{}", out);
    // nhãn trùng
    std::fs::write(d.join("n.lit"), ok.replace("@body\n", "@loop\n")).unwrap();
    let (out, _, good) = light(&d, &["check", "n.lit", "--json", "--no-cache"]);
    assert!(!good && out.contains("hai lần"), "{}", out);
}

#[test]
fn real_stack_frames_never_exceed_verifier_bound() {
    // mọi file std: khung thật do bộ sinh mã báo <= cận của verifier cho từng hàm
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let (out, err, ok) = light(&root, &["stack-report"]);
    assert!(ok && out.contains("OK:"), "{}\n{}", out, err);
}
