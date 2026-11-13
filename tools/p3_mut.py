#!/usr/bin/env python3
"""Chống chứng minh rỗng cho bench/p3: mỗi đột biến (mã sai / đặc tả mạnh hơn mã) PHẢI bị verifier từ chối.

    python3 tools/p3_mut.py
"""
import subprocess, sys, os
os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
M = {
 "01_sum_q.lt": [("s +%= a[i];", "s +%= a[i]; s +%= 1;"), ("for i in 0..n invariant", "for i in 1..n invariant"),
                 ("if k == 0 { 0 } else { sum(n, a, k - 1) + a[k - 1] }", "if k == 0 { 0 } else { sum(n, a, k - 1) + a[k - 1] + 1 }")],
 "06_count_lines_b.lt": [("c += u64(s[i] == '\\n');", "c += u64(s[i] == ' ');"), ("    return c;", "    return c - c;"),
                         ("(if s[k - 1] == '\\n' { 1 } else { 0 })", "(if s[k - 1] == '\\n' { 1 } else { 1 })")],
 "10_prefix_sum_q.lt": [("out[i] = s;", "out[i] = s +% 1;"), ("        s +%= a[i];\n        out[i] = s;", "        out[i] = s;\n        s +%= a[i];"),
                        ("requires out == a || out + 8 * m <= a || a + 8 * n <= out", "requires n >= 0")],
 "14_gcd.lt": [("        x = y;\n        y = m;", "        x = m;\n        y = m;"), ("    return x;", "    return y;"),
               ("if b == 0 { a } else { g(b, a % b) }", "if b == 0 { a } else { g(b, a % b) + 1 }")],
 "02_max_q.lt": [("m = math_max(m, v);", "m = math_min(m, v);"), ("var m = a[0];", "var m = a[n - 1];"), ("for i in 1..n", "for i in 2..n"),
                 ("ensures forall j in 0..n: a[j] <= result", "ensures forall j in 0..n: a[j] < result")],
 "03_find_q.lt": [("if a[i] == x { return i; }", "if a[i] == x { return i; } if a[i] == 7 { return i; }"), ("return n;", "return 0;")],
 "04_eq_b.lt": [("if a[i] != b[i] { return 0; }", "if a[i] != b[i] { return 0; } if i == 5 { return 1; }"),
                ("for i in 0..k", "for i in 1..k"), ("return 1;", "return 0;")],
 "05_strnlen_b.lt": [("if s[i] == 0 { break; }", "if s[i] == 1 { break; }"), ("i += 1;", "i += 1; if i == 3 { break; }")],
 "07_parse_dec.lt": [("acc = t + d;", "acc = t + d - d;"), ("if v < '0' || v > '9'", "if v < '0' || v > ':'"),
                     ("    out[0] = acc;\n    return 1;", "    return 1;"), ("if n == 0 { return 0; }", "if n == 0 { return 1; }")],
 "09_reverse_q.lt": [("a[j] = x;", "a[j] = y;"), ("a[i] = y;", "a[i] = x;"), ("while j - i > 1", "while j - i > 2"),
                     ("a[j] = x;", "a[j] = x; a[0] = x;")],
 "11_is_sorted_q.lt": [("a[i - 1] > a[i]", "a[i - 1] >= a[i]"), ("for i in 1..n", "for i in 2..n"), ("return 1;", "return 0;")],
 "13_base64_enc.lt": [("return o + 4;", "return o + 3;"), ("(n + 2) / 3)\n{", "(n + 1) / 3)\n{"),
                      ("if rest == 0 { return o; }", "if rest == 0 { return o + 4; }"),
                      ("requires cap >= 4 * ((n + 2) / 3)", "requires cap >= 4 * (n / 3)")],
 "12_lower_bound_q.lt": [("if a[mid] < x", "if a[mid] <= x"), ("lo = mid + 1;", "lo = mid;"),
                         ("requires forall j in 0..n: forall k in j..n: a[j] <= a[k]", "requires n >= 0")],
}
# phải là lỗi KIỂM CHỨNG thật (không tính lỗi cú pháp, hết giờ Z3)
CAUGHT = ("Vi phạm", "không còn đúng", "sai ngay khi vào", "không chắc dừng")
TMP = "bench/_mut"  # ngoài bench/p3 (cổng glob bench/p3/*.lt): chạy dở không làm hỏng cổng
os.makedirs(TMP, exist_ok=True)
bad = 0
n_unk = 0
for f, muts in M.items():
    src = open(f"bench/p3/{f}").read()
    for a, b in muts:
        assert a in src, (f, a)
        open(f"{TMP}/_mut.lt", "w").write(src.replace(a, b, 1))
        r = subprocess.run(["./target/release/light", "check", "--no-cache", f"{TMP}/_mut.lt"], capture_output=True, text=True, timeout=600)
        out = (r.stdout + r.stderr).strip().splitlines()
        viol = any(w in l for l in out for w in CAUGHT) and not any("không kết luận" in l for l in out)
        unk = any("không kết luận" in l for l in out)  # bị từ chối vì Z3 không kết luận (bản gốc thì qua)
        ok = r.returncode != 0 and (viol or unk)
        bad += not ok
        n_unk += ok and not viol
        tag = "BẮT  " if viol else ("BẮT? " if ok else "LỌT! ")
        print(tag + f, "|", b[:50], "|", (out[0] if out else "")[:140])
os.remove(f"{TMP}/_mut.lt")
os.rmdir(TMP)
n = sum(len(v) for v in M.values())
print(f"p3_mut: {bad}/{n} đột biến lọt" if bad else f"p3_mut: cả {n} đột biến bị bắt ({n_unk} do Z3 không kết luận, còn lại có phản ví dụ)")
sys.exit(1 if bad else 0)
