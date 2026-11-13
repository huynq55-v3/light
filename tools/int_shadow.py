#!/usr/bin/env python3
"""Đối chiếu chéo checker số nguyên (src/verify_int.rs) với checker bit-vector.

    python3 tools/int_shadow.py

1. LIGHT_INT_ALL=1: checker số nguyên chứng minh MỌI mệnh đề của mọi hàm (kể cả mệnh đề BV thuần). Mọi file phải qua
   (nếu không là lỗ hổng tính đầy đủ cần sửa, hoặc mã hoá sai).
2. LIGHT_INT_ONLY=1: CHỈ chạy checker số nguyên trên tests/lit/must_fail có EXPECT là vi phạm đặc tả. File nào nó báo OK phải nằm trong danh sách
   miền chỉ-BV bên dưới (Layout @inv, worker parallel). Nếu nó chấp nhận một ensures / invariant / requires sai -> mã
   hoá số nguyên không chặt (unsound).
Luôn --no-cache.
"""
import glob
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LIGHT = os.path.join(REPO, "target", "release", "light")
# chỉ checker BV xử lý (checker số nguyên không mô hình @inv của Layout / quy tắc parallel)
BV_ONLY = {"ata_read_into_inv_layout", "imm_field_inv", "narrow_store_layout_inv", "store_violates_field_inv",
           "parallel_worker_req_some_index"}


SPEC_WORDS = ("điều kiện đầu ra", "@ens", "@inv", "@req", "invariant", "bất biến", "ensures", "requires")


def is_spec(f):
    """must_fail mà lỗi mong đợi là vi phạm đặc tả (không phải an toàn bộ nhớ / dừng / cú pháp — miền của checker BV)"""
    for line in open(f, encoding="utf-8"):
        if "EXPECT:" in line:
            e = line.split("EXPECT:", 1)[1]
            return any(w in e for w in SPEC_WORDS) and "dừng" not in e and "giảm" not in e
    return False


def run(f, env):
    e = dict(os.environ, **env)
    r = subprocess.run([LIGHT, "check", "--no-cache", f], cwd=REPO, env=e, capture_output=True, text=True, timeout=600)
    return f, r.returncode == 0 and "OK:" in r.stdout + r.stderr, r.stdout + r.stderr


def main():
    g = lambda *p: sorted(glob.glob(os.path.join(REPO, *p)))
    good = (g("lit_program", "std", "*.lit") + g("bench", "today", "*.lit") + g("bench", "p1", "*.lt") + g("bench", "p1", "*.lit")
            + g("bench", "p2", "*.lt") + g("bench", "p2", "std", "*.lt") + g("bench", "p2", "std", "*.lit") + g("bench", "p3", "*.lt")
            + g("tests", "lit", "must_pass", "*.lit") + g("tests", "lit", "must_pass", "*.lt"))
    bad = [f for f in g("tests", "lit", "must_fail", "*.lit") + g("tests", "lit", "must_fail", "*.lt") if is_spec(f)]
    ok = True
    with ThreadPoolExecutor(8) as ex:
        for f, passed, out in ex.map(lambda f: run(f, {"LIGHT_INT_ALL": "1"}), good):
            if not passed:
                ok = False
                print(f"[FAIL] LIGHT_INT_ALL {os.path.relpath(f, REPO)}\n{out[-1500:]}")
        n_bv = 0
        for f, passed, out in ex.map(lambda f: run(f, {"LIGHT_INT_ONLY": "1"}), bad):
            name = os.path.splitext(os.path.basename(f))[0]
            if passed and name not in BV_ONLY:
                ok = False
                print(f"[FAIL] LIGHT_INT_ONLY chấp nhận file sai: {os.path.relpath(f, REPO)}")
            n_bv += passed
    print(f"int_shadow: {len(good)} file đúng, {len(bad)} file sai ({n_bv} thuộc miền chỉ-BV) -> {'QUA' if ok else 'TRƯỢT'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
