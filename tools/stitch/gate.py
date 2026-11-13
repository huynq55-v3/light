#!/usr/bin/env python3
"""Cổng an toàn của Light: mọi thay đổi ngôn ngữ / std chỉ được nhận khi cổng này qua hết.

    python3 tools/stitch/gate.py

Các bước:
  1. cargo build --release
  2. `light check` từng file lit_program/std/*.lit (kiểm chứng Z3, kể cả chứng minh dừng)
  3. cargo test --release (verifier must_pass / must_fail, codegen, CLI)
  4. light stack-report (khung stack thật <= cận verifier)
  5. cgtest --fuzz (mã máy == trình thông dịch trên chương trình ngẫu nhiên)
  6. tools/mandel_model.py test (đối chiếu TỪNG BIT các hàm số học của std với mô hình Python)
  7. Light-Bench: `light check` + stack-report từng file bench/today/*.lit, rồi tools/bench.py test (mã máy == mô hình)
  8. Cú pháp B (P1): `light check` + stack-report bench/p1/*.lt (+ bản SSA song sinh *.lit), rồi tools/p1_diff.py (mã máy bản B == bản SSA gốc, từng bit)
  9. Cú pháp B (P2, vòng lặp): `light check` + stack-report bench/p2/*.lt (15 bài) và bench/p2/std/*.lt, rồi
     tools/bench.py --dir bench/p2 test (mã máy bản B == mô hình Python); bench/p2/std được p1_diff.py ở bước 8 đối chiếu
 10. P3 (đặc tả đầy đủ, checker số nguyên): `light check` bench/p3/*.lt rồi tools/bench.py --dir bench/p3 test
 10b. tools/p3_mut.py: mọi đột biến của bench/p3 phải bị từ chối (chống chứng minh rỗng)
 11. tools/int_shadow.py: checker số nguyên chạy trên MỌI hàm đúng (phải qua) và một mình trên must_fail đặc tả (không được nhận)
"""
import glob
import os
import subprocess
import sys
import time

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PY = sys.executable


def step(name, cmd):
    t = time.monotonic()
    r = subprocess.run(cmd, cwd=REPO, capture_output=True, text=True)
    ok = r.returncode == 0
    print(f"[{'OK' if ok else 'FAIL'}] {name} ({time.monotonic() - t:.1f}s)")
    if not ok:
        print((r.stdout + r.stderr)[-3000:])
    return ok


def main():
    ok = step("cargo build --release", ["cargo", "build", "--release", "--quiet"])
    for f in sorted(glob.glob(os.path.join(REPO, "lit_program", "std", "*.lit"))):
        ok = ok and step(f"light check {os.path.relpath(f, REPO)}", ["./target/release/light", "check", f])
    ok = ok and step("cargo test --release", ["cargo", "test", "--release", "--quiet"])
    ok = ok and step("light stack-report", ["./target/release/light", "stack-report"])
    ok = ok and step("cgtest --fuzz 1000", ["./target/release/cgtest", "--fuzz", "1000"])
    ok = ok and step("mandel_model.py test", [PY, "tools/mandel_model.py", "test"])
    bench = sorted(glob.glob(os.path.join(REPO, "bench", "today", "*.lit")))
    for f in bench:
        ok = ok and step(f"light check {os.path.relpath(f, REPO)}", ["./target/release/light", "check", f])
    ok = ok and step("light stack-report bench", ["./target/release/light", "stack-report", *bench])
    ok = ok and step("bench.py test", [PY, "tools/bench.py", "test"])
    p1 = sorted(glob.glob(os.path.join(REPO, "bench", "p1", "*.lt")) + glob.glob(os.path.join(REPO, "bench", "p1", "*.lit")))
    for f in p1:
        ok = ok and step(f"light check {os.path.relpath(f, REPO)}", ["./target/release/light", "check", f])
    ok = ok and step("light stack-report bench/p1", ["./target/release/light", "stack-report", *p1])
    ok = ok and step("p1_diff.py (B == SSA gốc)", [PY, "tools/p1_diff.py"])
    p2 = sorted(glob.glob(os.path.join(REPO, "bench", "p2", "*.lt")) + glob.glob(os.path.join(REPO, "bench", "p2", "std", "*.lt"))
                + glob.glob(os.path.join(REPO, "bench", "p2", "std", "*.lit")))
    for f in p2:
        ok = ok and step(f"light check {os.path.relpath(f, REPO)}", ["./target/release/light", "check", f])
    ok = ok and step("light stack-report bench/p2", ["./target/release/light", "stack-report", *p2])
    ok = ok and step("bench.py --dir bench/p2 test", [PY, "tools/bench.py", "--dir", "bench/p2", "test"])
    p3 = sorted(glob.glob(os.path.join(REPO, "bench", "p3", "*.lt")))
    for f in p3:
        ok = ok and step(f"light check {os.path.relpath(f, REPO)}", ["./target/release/light", "check", f])
    ok = ok and step("bench.py --dir bench/p3 test", [PY, "tools/bench.py", "--dir", "bench/p3", "test"])
    ok = ok and step("p3_mut.py (đột biến bench/p3)", [PY, "tools/p3_mut.py"])
    ok = ok and step("int_shadow.py (đối chiếu checker số nguyên)", [PY, "tools/int_shadow.py"])
    print("CỔNG:", "QUA" if ok else "TRƯỢT")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
