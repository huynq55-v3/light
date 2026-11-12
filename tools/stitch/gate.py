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
    print("CỔNG:", "QUA" if ok else "TRƯỢT")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
