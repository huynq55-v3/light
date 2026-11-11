// File: src/tooling.rs — công cụ cho người và AI: chẩn đoán JSON, `light doc`, cache kết quả Z3.
use crate::ir::{Func, Inst, Module};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::io::Write;
use std::path::Path;
use std::sync::{Mutex, OnceLock};

// ---------------------------------------------------------------------------------------------------------------
// Chế độ --json và đếm cache
// ---------------------------------------------------------------------------------------------------------------
static JSON: OnceLock<bool> = OnceLock::new();
static NO_CACHE: OnceLock<bool> = OnceLock::new();
static ORIGINS: Mutex<Option<HashMap<String, String>>> = Mutex::new(None);
static STATS: Mutex<(u32, u32)> = Mutex::new((0, 0)); // (trúng cache, kiểm chứng mới)
static CACHE: Mutex<Option<HashSet<u64>>> = Mutex::new(None);
static ERRS: Mutex<Vec<String>> = Mutex::new(Vec::new());

/// Ghi nhận lỗi của 1 hàm để `check` báo hết mọi hàm hỏng trong một lượt
pub fn push_error(e: String) {
    ERRS.lock().unwrap().push(e);
}
pub fn take_errors() -> Vec<String> {
    std::mem::take(&mut *ERRS.lock().unwrap())
}

pub fn set_flags(json: bool, no_cache: bool) {
    let _ = JSON.set(json);
    let _ = NO_CACHE.set(no_cache);
}
pub fn json_mode() -> bool {
    *JSON.get().unwrap_or(&false)
}

/// In tiến trình cho người đọc; im lặng khi --json để stdout chỉ còn JSON
#[macro_export]
macro_rules! say {
    ($($t:tt)*) => { if !$crate::tooling::json_mode() { println!($($t)*); } };
}

pub fn register_module(m: &Module) {
    let mut g = ORIGINS.lock().unwrap();
    let map = g.get_or_insert_with(HashMap::new);
    for f in &m.funcs {
        map.insert(f.name.clone(), f.origin.clone());
    }
}
fn origin_of(name: &str) -> Option<String> {
    ORIGINS.lock().unwrap().as_ref().and_then(|m| m.get(name).cloned())
}

pub fn esc(s: &str) -> String {
    let mut o = String::with_capacity(s.len() + 2);
    o.push('"');
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            '\r' => o.push_str("\\r"),
            '\t' => o.push_str("\\t"),
            c if (c as u32) < 0x20 => o.push_str(&format!("\\u{:04x}", c as u32)),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

// ---------------------------------------------------------------------------------------------------------------
// Chẩn đoán có cấu trúc
// ---------------------------------------------------------------------------------------------------------------
#[derive(Default, Debug)]
pub struct Diag {
    pub kind: String, // z3_fail | z3_timeout | func | parse | other
    pub func: String,
    pub block: String,
    pub inst: String,
    pub message: String,
    pub counterexample: Vec<(String, String)>,
    pub origin: String,
    pub source: String,
    pub hint: String,
}

fn hint_for(msg: &str, kind: &str) -> &'static str {
    let m = msg;
    if kind == "z3_timeout" {
        "Z3 hết giờ: chia hàm thành các hàm nhỏ có @req/@ens rõ ràng (kiểm chứng theo hợp đồng), hoặc đơn giản biểu thức nhiều phép nhân/chia."
    } else if m.contains("Tràn số cộng index") || m.contains("Tràn biên mảng khi slice") || m.contains("Tràn vùng nhớ") || m.contains("vượt độ dài động") {
        "Chỉ số/offset có thể vượt vùng ptr: thêm @req ult %idx <kích thước> cho tham số, hoặc kẹp bằng std_min(%idx, N-1) trước khi slice/load/store."
    } else if m.contains("Tràn số") {
        "Phép toán số học có thể tràn 64-bit: giới hạn toán hạng bằng @req (vd @req ule %x 0xffffffff), hoặc dùng std_min/std_sat_add/std_sat_sub trước khi tính."
    } else if m.contains("Vi phạm bất biến (@inv") {
        "Giá trị truyền vào jmp không thỏa @inv của block đích: kiểm tra bộ đếm vòng lặp tăng thế nào, thêm cận (vd @inv ule %i N) và buộc các biến liên quan (vd @inv ult %j %i)."
    } else if m.contains("Vi phạm @req") && m.contains("khi gọi hàm") {
        "Đối số chưa chứng minh được thỏa @req của hàm được gọi: thêm @req tương ứng cho tham số của hàm này, hoặc kẹp giá trị trước khi gọi."
    } else if m.contains("Vi phạm điều kiện đầu ra") {
        "@ens chưa được chứng minh: ràng buộc giá trị trả về trên MỌI đường đi tới ret (có thể cần @inv trên block tham số cuối)."
    } else if m.contains("chia cho 0") {
        "Thêm @req ne %d 0 hoặc kiểm tra bằng cmp/br trước khi chia."
    } else if m.contains("stack") && m.contains("ngân sách") {
        "Kích thước frame tính từ SỐ SSA LỚN NHẤT (không phải số giá trị): đừng đặt tên kiểu %70000; đánh số liên tục từ nhỏ, và tránh chuỗi gọi hàm quá sâu."
    } else if m.contains("br không được nhảy") {
        "br không nhảy được tới block có tham số: thêm block trung gian (không tham số) rồi jmp kèm đối số."
    } else if m.contains("bị định nghĩa") {
        "Mỗi %số chỉ được gán đúng một lần trong hàm: đổi sang số chưa dùng."
    } else if m.contains("mâu thuẫn") {
        "Các @req/@inv loại trừ nhau nên không có đầu vào nào hợp lệ: xem lại dấu so sánh."
    } else if m.contains("không phải tham số") {
        "@req/@ens chỉ được dùng tham số hàm (và thanh ghi trả về cho @ens)."
    } else if m.contains("Không tìm thấy") {
        "Kiểm tra đường dẫn include (tương đối so với file chứa dòng include)."
    } else if kind == "z3_fail" {
        "Z3 đưa phản ví dụ (counterexample): thêm @req/@inv loại giá trị đó hoặc sửa phép tính để không xảy ra."
    } else {
        ""
    }
}

/// Phân tích chuỗi lỗi hiện có thành bản ghi có cấu trúc
pub fn parse_err(s: &str) -> Diag {
    let mut d = Diag::default();
    let first = s.lines().next().unwrap_or("");
    if let Some(rest) = first.strip_prefix("[Z3 FAIL] func ").or_else(|| first.strip_prefix("[Z3 TIMEOUT] func ")) {
        d.kind = if first.starts_with("[Z3 FAIL]") { "z3_fail" } else { "z3_timeout" }.into();
        // "<func> @b<N>: '<inst>' -> <msg> when <ce>"
        let (func, r) = rest.split_once(' ').unwrap_or((rest, ""));
        d.func = func.into();
        let (blk, r) = r.split_once(": ").unwrap_or((r, ""));
        d.block = blk.trim_start_matches('@').into();
        let r = r.trim_start_matches('\'');
        let (inst, r) = r.split_once("' -> ").unwrap_or((r, ""));
        d.inst = inst.into();
        let (msg, ce) = match r.split_once(" when ") {
            Some((m, c)) => (m, c),
            None => (r, ""),
        };
        d.message = msg.into();
        let (primary, ctx) = match ce.split_once(" [ctx: ") {
            Some((p, c)) => (p, c.trim_end_matches(']')),
            None => (ce, ""),
        };
        for part in primary.split(", ").chain(ctx.split(' ')) {
            if let Some((k, v)) = part.split_once(" = ").or_else(|| part.split_once('=')) {
                let k = k.trim();
                if k.starts_with('%') && !v.trim().is_empty() {
                    d.counterexample.push((k.into(), v.trim().into()));
                }
            }
        }
        d.origin = origin_of(&d.func).unwrap_or_default();
    } else if let Some(rest) = first.strip_prefix("[func '") {
        d.kind = "func".into();
        let (func, msg) = rest.split_once("'] ").unwrap_or((rest, ""));
        d.func = func.into();
        d.message = msg.into();
        d.origin = origin_of(func).unwrap_or_default();
    } else if let Some(rest) = first.strip_prefix("Dòng ") {
        d.kind = "parse".into();
        // "Dòng file:line: msg" — file có thể chứa ':' hiếm gặp, tách theo ": " đầu tiên
        let (loc, msg) = rest.split_once(": ").unwrap_or((rest, ""));
        d.origin = loc.into();
        d.message = msg.into();
        if let Some(src) = s.lines().nth(1) {
            d.source = src.trim_start_matches("    > ").into();
        }
    } else if let Some(rest) = first.strip_prefix("Hàm '") {
        d.kind = "func".into();
        let (func, msg) = rest.split_once("' ").unwrap_or((rest, ""));
        d.func = func.into();
        d.message = msg.into();
        d.origin = origin_of(func).unwrap_or_default();
    } else {
        d.kind = "other".into();
        d.message = s.trim().into();
    }
    d.hint = hint_for(&d.message, &d.kind).into();
    d
}

pub fn diag_json(d: &Diag) -> String {
    let ce: Vec<String> = d
        .counterexample
        .iter()
        .map(|(k, v)| format!("{{\"reg\":{},\"value\":{}}}", esc(k), esc(v)))
        .collect();
    format!(
        "{{\"kind\":{},\"func\":{},\"block\":{},\"inst\":{},\"message\":{},\"counterexample\":[{}],\"origin\":{},\"source\":{},\"hint\":{}}}",
        esc(&d.kind), esc(&d.func), esc(&d.block), esc(&d.inst), esc(&d.message), ce.join(","), esc(&d.origin), esc(&d.source), esc(&d.hint)
    )
}

pub fn error_json(err: &str) -> String {
    let mut all = take_errors();
    if all.is_empty() {
        all.push(err.to_string());
    }
    let v: Vec<String> = all.iter().map(|e| diag_json(&parse_err(e))).collect();
    format!("{{\"ok\":false,\"errors\":[{}]}}", v.join(","))
}

pub fn ok_json() -> String {
    let (h, v) = *STATS.lock().unwrap();
    format!("{{\"ok\":true,\"verified\":{},\"cache_hits\":{}}}", v, h)
}

pub fn cache_summary() -> String {
    let (h, v) = *STATS.lock().unwrap();
    format!("{} hàm kiểm chứng mới, {} hàm lấy từ cache", v, h)
}

// ---------------------------------------------------------------------------------------------------------------
// Cache kết quả Z3 (.light-cache/z3.keys): khóa = băm(mã verifier + layouts + hàm đã chuẩn hóa + hợp đồng hàm được gọi)
// ---------------------------------------------------------------------------------------------------------------
fn fnv(bytes: &[u8], mut h: u64) -> u64 {
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

const CACHE_FILE: &str = ".light-cache/z3.keys";

fn func_key(module: &Module, func: &Func) -> u64 {
    // Mã nguồn bộ kiểm chứng + IR + phiên bản: đổi verifier thì cache tự mất hiệu lực
    let mut h = 0xcbf29ce484222325u64;
    h = fnv(include_bytes!("verify.rs"), h);
    h = fnv(include_bytes!("ir.rs"), h);
    h = fnv(env!("CARGO_PKG_VERSION").as_bytes(), h);
    h = fnv(format!("{:?}", module.layouts).as_bytes(), h);
    // Chuẩn hóa: id hàm -> băm tên, bỏ origin (dòng đổi không làm mất cache)
    let mut f = func.clone();
    f.origin.clear();
    let mut callees: Vec<u32> = Vec::new();
    for b in &mut f.blocks {
        for i in &mut b.insts {
            let id = match i {
                Inst::Call { func_id, .. } | Inst::Parallel { func_id, .. } => func_id,
                _ => continue,
            };
            callees.push(*id);
            *id = (fnv(module.funcs[*id as usize].name.as_bytes(), 0xcbf29ce484222325) & 0xffff_ffff) as u32;
        }
    }
    h = fnv(format!("{:?}", f).as_bytes(), h);
    callees.sort_by_key(|&id| module.funcs[id as usize].name.clone());
    callees.dedup();
    for id in callees {
        let c = &module.funcs[id as usize]; // chỉ HỢP ĐỒNG của hàm được gọi, không phải thân
        h = fnv(format!("{}|{:?}|{:?}|{:?}|{:?}", c.name, c.params, c.ret_ty, c.requires, c.ensures).as_bytes(), h);
    }
    h
}

fn cache_load() -> HashSet<u64> {
    fs::read_to_string(CACHE_FILE)
        .map(|s| s.lines().filter_map(|l| u64::from_str_radix(l.trim(), 16).ok()).collect())
        .unwrap_or_default()
}

/// Kiểm chứng hàm, bỏ qua Z3 nếu cache đã có bản chứng minh cho đúng nội dung này. Trả true nếu trúng cache.
pub fn verify_cached(module: &Module, func: &Func) -> Result<bool, String> {
    if *NO_CACHE.get().unwrap_or(&false) || std::env::var_os("LIGHT_NO_CACHE").is_some() {
        crate::verify::verify_func(module, func)?;
        STATS.lock().unwrap().1 += 1;
        return Ok(false);
    }
    let key = func_key(module, func);
    {
        let mut g = CACHE.lock().unwrap();
        let set = g.get_or_insert_with(cache_load);
        if set.contains(&key) {
            STATS.lock().unwrap().0 += 1;
            return Ok(true);
        }
    }
    let assumes = crate::verify::verify_func(module, func)?;
    STATS.lock().unwrap().1 += 1;
    if assumes == 0 {
        // hàm có `assume` không vào cache để cảnh báo luôn được in lại
        CACHE.lock().unwrap().as_mut().unwrap().insert(key);
        let _ = fs::create_dir_all(".light-cache");
        if let Ok(mut f) = fs::OpenOptions::new().create(true).append(true).open(CACHE_FILE) {
            let _ = writeln!(f, "{:016x}", key);
        }
    }
    Ok(false)
}

// ---------------------------------------------------------------------------------------------------------------
// light doc
// ---------------------------------------------------------------------------------------------------------------
struct Item {
    kind: &'static str, // func | def
    name: String,
    file: String,
    line: usize,
    ret: String,
    params: Vec<(String, String)>,
    requires: Vec<String>,
    ensures: Vec<String>,
    doc: String,
    value: String,
}

fn collect_files(dir: &Path, out: &mut Vec<String>) {
    if let Ok(rd) = fs::read_dir(dir) {
        let mut v: Vec<_> = rd.filter_map(|e| e.ok()).map(|e| e.path()).collect();
        v.sort();
        for p in v {
            if p.is_dir() {
                collect_files(&p, out);
            } else if p.extension().and_then(|e| e.to_str()) == Some("lit") {
                out.push(p.to_string_lossy().into_owned());
            }
        }
    }
}

fn scan_file(path: &str, items: &mut Vec<Item>) {
    let Ok(src) = fs::read_to_string(path) else { return };
    let lines: Vec<&str> = src.lines().collect();
    for (i, raw) in lines.iter().enumerate() {
        let l = raw.trim();
        // chú thích liền kề phía trên
        let comment = |i: usize| -> String {
            let mut c: Vec<String> = Vec::new();
            let mut j = i;
            while j > 0 {
                let p = lines[j - 1].trim();
                if let Some(t) = p.strip_prefix('#') {
                    c.push(t.trim().to_string());
                    j -= 1;
                } else {
                    break;
                }
            }
            c.reverse();
            c.join(" ")
        };
        if let Some(rest) = l.strip_prefix("def ") {
            let mut t = rest.splitn(2, char::is_whitespace);
            let name = t.next().unwrap_or("").to_string();
            let value = t.next().unwrap_or("").split('#').next().unwrap_or("").trim().to_string();
            items.push(Item { kind: "def", name, file: path.into(), line: i + 1, ret: String::new(), params: vec![], requires: vec![], ensures: vec![], doc: comment(i), value });
        } else if let Some(rest) = l.strip_prefix("func ") {
            let head = rest.split('{').next().unwrap_or("");
            let mut t = head.split_whitespace();
            let name = t.next().unwrap_or("").to_string();
            let ret = t.next().unwrap_or("").to_string();
            let params: Vec<(String, String)> = t
                .filter_map(|p| p.split_once(':').map(|(a, b)| (a.to_string(), b.to_string())))
                .collect();
            let (mut req, mut ens) = (Vec::new(), Vec::new());
            let mut j = i + 1;
            while j < lines.len() {
                let q = lines[j].trim();
                if let Some(r) = q.strip_prefix("@req ") {
                    req.push(r.split('#').next().unwrap_or("").trim().to_string());
                } else if let Some(r) = q.strip_prefix("@ens ") {
                    ens.push(r.split('#').next().unwrap_or("").trim().to_string());
                } else if !(q.is_empty() || q.starts_with('#')) {
                    break;
                }
                j += 1;
            }
            items.push(Item { kind: "func", name, file: path.into(), line: i + 1, ret, params, requires: req, ensures: ens, doc: comment(i), value: String::new() });
        }
    }
}

fn item_json(it: &Item) -> String {
    let list = |v: &Vec<String>| v.iter().map(|s| esc(s)).collect::<Vec<_>>().join(",");
    if it.kind == "def" {
        return format!("{{\"kind\":\"def\",\"name\":{},\"value\":{},\"file\":{},\"line\":{},\"doc\":{}}}", esc(&it.name), esc(&it.value), esc(&it.file), it.line, esc(&it.doc));
    }
    let ps: Vec<String> = it.params.iter().map(|(a, b)| format!("{{\"reg\":{},\"type\":{}}}", esc(a), esc(b))).collect();
    format!(
        "{{\"kind\":\"func\",\"name\":{},\"ret\":{},\"params\":[{}],\"requires\":[{}],\"ensures\":[{}],\"file\":{},\"line\":{},\"doc\":{}}}",
        esc(&it.name), esc(&it.ret), ps.join(","), list(&it.requires), list(&it.ensures), esc(&it.file), it.line, esc(&it.doc)
    )
}

/// light doc [TRUY_VẤN] [--file F]... [--brief] [--defs] [--json]
pub fn cmd_doc(args: &[String]) -> Result<(), String> {
    let (mut query, mut files, mut brief, mut defs) = (None::<String>, Vec::<String>::new(), false, false);
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--brief" => brief = true,
            "--defs" => defs = true,
            "--file" => {
                i += 1;
                files.push(args.get(i).ok_or("--file cần đường dẫn")?.clone());
            }
            a => query = Some(a.to_lowercase()),
        }
        i += 1;
    }
    if files.is_empty() {
        collect_files(Path::new("lit_program"), &mut files);
    }
    let mut items = Vec::new();
    for f in &files {
        scan_file(f, &mut items);
    }
    let hit = |it: &Item| -> bool {
        (it.kind == "func" || defs || query.is_some())
            && query.as_ref().map_or(true, |q| it.name.to_lowercase().contains(q) || it.doc.to_lowercase().contains(q) || it.file.to_lowercase().contains(q))
    };
    let sel: Vec<&Item> = items.iter().filter(|it| hit(it)).collect();
    if json_mode() {
        println!("[{}]", sel.iter().map(|it| item_json(it)).collect::<Vec<_>>().join(","));
        return Ok(());
    }
    for it in &sel {
        if it.kind == "def" {
            println!("{}:{}  def {} = {}", it.file, it.line, it.name, it.value);
            continue;
        }
        let ps: Vec<String> = it.params.iter().map(|(a, b)| format!("{}:{}", a, b)).collect();
        println!("{}:{}  func {}({}) -> {}", it.file, it.line, it.name, ps.join(", "), it.ret);
        if !brief {
            if !it.doc.is_empty() {
                println!("    # {}", it.doc);
            }
            for r in &it.requires {
                println!("    @req {}", r);
            }
            for r in &it.ensures {
                println!("    @ens {}", r);
            }
        }
    }
    eprintln!("({} mục)", sel.len());
    Ok(())
}
