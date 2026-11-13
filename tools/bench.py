#!/usr/bin/env python3
"""Light-Bench: bộ hàm mẫu để đo mức thân thiện với AI của cú pháp Light qua từng giai đoạn (P0 = cú pháp SSA hiện tại).

    python3 tools/bench.py metrics     # bảng số dòng / token / lệnh / mức đặc tả cho bench/today/*.lit
    python3 tools/bench.py test        # đối chiếu mã máy thật (cgtest --call) với mô hình Python, kể cả ca biên
    python3 tools/bench.py             # cả hai

Đề bài (độc lập ngôn ngữ) + đặc tả mong muốn ở bench/tasks.md. Z3 chỉ chứng minh được đặc tả YẾU (không nói được về
nội dung bộ nhớ), nên tính đúng của chính bộ mẫu được bảo đảm bằng kiểm thử ở đây, không phải bằng verifier.
"""
import glob
import os
import random
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO, "tools", "stitch"))
import litparse  # noqa: E402

BENCH = os.path.join(REPO, "bench", "today")
CGTEST = os.path.join(REPO, "target", "release", "cgtest")
M64 = (1 << 64) - 1
B64 = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"


# ----------------------------------------------------------------------------------------------------------------
# Gọi mã máy thật
# ----------------------------------------------------------------------------------------------------------------
def call(file, func, rows):
    """rows: list các list đối số (int, hoặc list Qword = bộ đệm). Trả list (kết quả, [bộ đệm sau lời gọi])."""
    fmt = lambda t: "[" + ",".join(hex(v) for v in t) + "]" if isinstance(t, list) else hex(t)
    inp = "\n".join(" ".join(fmt(t) for t in r) for r in rows) + "\n"
    out = subprocess.run([CGTEST, "--call", os.path.join(BENCH, file), func], input=inp,
                         capture_output=True, text=True, check=True).stdout
    res = []
    for line in out.splitlines():
        parts = line.split(" ")
        # `&k+off` = kết quả là con trỏ vào bộ đệm k (cgtest in tương đối); hàm void có rax rác nên có thể gặp
        r = parts[0] if parts[0].startswith("&") else int(parts[0], 16)
        res.append((r, [[int(x, 16) for x in b[1:-1].split(",") if x] for b in parts[1:]]))
    return res


def pack(bs, cap=None):
    """bytes -> list Qword (little-endian), đệm 0 tới ít nhất `cap` byte"""
    bs = bytes(bs) + b"\0" * max(0, (cap or 0) - len(bs))
    bs += b"\0" * (-len(bs) % 8)
    return [int.from_bytes(bs[i:i + 8], "little") for i in range(0, len(bs), 8)] or [0]


def unpack(qs, n):
    return b"".join(q.to_bytes(8, "little") for q in qs)[:n]


# ----------------------------------------------------------------------------------------------------------------
# Mô hình Python + sinh dữ liệu cho từng bài
# ----------------------------------------------------------------------------------------------------------------
def rand_q(rng):
    return rng.choice([0, 1, 2, 7, M64, M64 - 1, 1 << 63, rng.getrandbits(64), rng.getrandbits(8)])


def rand_arr(rng, lo=0, hi=12):
    return [rand_q(rng) for _ in range(rng.randint(lo, hi))]


def rand_bytes(rng, alphabet=None, lo=0, hi=24):
    n = rng.randint(lo, hi)
    if alphabet:
        return bytes(rng.choice(alphabet) for _ in range(n))
    return bytes(rng.getrandbits(8) for _ in range(n))


def t_sum(rng):
    a = rand_arr(rng)
    return [len(a), a or [0]], (sum(a) & M64, None)


def t_max(rng):
    a = rand_arr(rng, lo=1)
    return [len(a), a], (max(a), None)


def t_find(rng):
    a = [rng.choice([1, 2, 3, M64]) for _ in range(rng.randint(0, 10))]
    x = rng.choice([1, 2, 3, M64, 9])
    return [len(a), a or [0], x], (a.index(x) if x in a else len(a), None)


def t_eq(rng):
    a = rand_bytes(rng, b"ab", hi=12)
    b = bytearray(a + rand_bytes(rng, b"ab", hi=3))
    if b and rng.random() < 0.5:
        b[rng.randrange(len(b))] ^= 1
    k = rng.randint(0, min(len(a), len(b)))
    return [len(a), pack(a), len(b), pack(b), k], (int(a[:k] == bytes(b[:k])), None)


def t_strnlen(rng):
    s = rand_bytes(rng, b"\0xyz")
    return [len(s), pack(s)], (s.index(0) if 0 in s else len(s), None)


def t_lines(rng):
    s = rand_bytes(rng, b"\nab", hi=40)
    return [len(s), pack(s)], (s.count(b"\n"), None)


def t_parse(rng):
    pick = rng.random()
    if pick < 0.2:
        s = rng.choice([b"", b"0", b"18446744073709551615", b"18446744073709551616", b"99999999999999999999",
                        b"00000000000000000000000001", b"1844674407370955161", b"12a", b"-1", b"/", b":"])
    else:
        s = str(rng.getrandbits(rng.choice([4, 32, 64, 66]))).encode()
        if rng.random() < 0.2:
            s = s[:rng.randint(0, len(s))] + rng.choice([b"x", b" ", b"/", b":"]) + s[:2]
    ok = len(s) > 0 and s.isdigit() and int(s) <= M64
    exp = (1, [int(s)]) if ok else (0, [0xdead])
    return [len(s), pack(s), [0xdead]], (exp[0], [None, None, exp[1]])


def t_fmt(rng):
    v = rand_q(rng) if rng.random() < 0.7 else rng.choice([0, 9, 10, 99, 100, 10**19 - 1, 10**19])
    d = str(v).encode()
    return [24, [0x2a2a2a2a2a2a2a2a] * 3, v], (len(d), [None, pack(d.ljust(24, b"*"))])


def t_reverse(rng):
    a = rand_arr(rng)
    return [len(a), a or [0]], (0, [None, a[::-1] or [0]])


def t_prefix(rng):
    a = rand_arr(rng)
    out, s = [], 0
    for v in a:
        s = (s + v) & M64
        out.append(s)
    m = len(a) + rng.randint(0, 2)
    tail = [0x77] * (m - len(a))
    return [len(a), a or [0], m, (([0x77] * len(a)) + tail) or [0]], (0, [None, None, None, (out + tail) or [0]])


def t_sorted(rng):
    a = sorted(rand_arr(rng))
    if len(a) > 1 and rng.random() < 0.5:
        i = rng.randrange(len(a) - 1)
        a[i], a[i + 1] = a[i + 1], a[i]
    return [len(a), a or [0]], (int(all(a[j] <= a[j + 1] for j in range(len(a) - 1))), None)


def t_lbound(rng):
    a = sorted(rng.choice([1, 3, 5, 5, 8, M64]) for _ in range(rng.randint(0, 12)))
    x = rng.choice([0, 1, 2, 3, 5, 6, 8, 9, M64])
    return [len(a), a or [0], x], (next((j for j, v in enumerate(a) if v >= x), len(a)), None)


def b64(s):
    import base64
    return base64.b64encode(s)


def t_base64(rng):
    s = rand_bytes(rng, hi=20)
    e = b64(s)
    cap = len(e) + rng.randint(0, 5)
    return [len(s), pack(s), cap, pack(b"#" * cap)], (len(e), [None, None, None, pack(e + b"#" * (cap - len(e)))])


def t_gcd(rng):
    import math
    a, b = rng.choice([0, 1, rng.getrandbits(64), rng.getrandbits(20) * 6]), rng.choice([0, 1, rng.getrandbits(64), 12])
    return [a, b], (math.gcd(a, b), None)


def t_isqrt(rng):
    import math
    x = rng.choice([0, 1, 2, 3, 4, 15, 16, M64, (1 << 32) ** 2 - 1, rng.getrandbits(64), rng.getrandbits(30)])
    return [x], (math.isqrt(x), None)


TASKS = [
    ("01_sum_q.lit", "sum_q", t_sum),
    ("02_max_q.lit", "max_q", t_max),
    ("03_find_q.lit", "find_q", t_find),
    ("04_eq_b.lit", "eq_b", t_eq),
    ("05_strnlen_b.lit", "strnlen_b", t_strnlen),
    ("06_count_lines_b.lit", "count_lines_b", t_lines),
    ("07_parse_dec.lit", "parse_dec", t_parse),
    ("08_fmt_dec.lit", "fmt_dec", t_fmt),
    ("09_reverse_q.lit", "reverse_q", t_reverse),
    ("10_prefix_sum_q.lit", "prefix_sum_q", t_prefix),
    ("11_is_sorted_q.lit", "is_sorted_q", t_sorted),
    ("12_lower_bound_q.lit", "lower_bound_q", t_lbound),
    ("13_base64_enc.lit", "base64_enc", t_base64),
    ("14_gcd.lit", "gcd", t_gcd),
    ("15_isqrt.lit", "isqrt", t_isqrt),
]


def test(n=300):
    rng = random.Random(20261112)
    bad = 0
    for file, func, gen in TASKS:
        cases = [gen(rng) for _ in range(n)]
        got = call(file, func, [c[0] for c in cases])
        fails = 0
        for (args, (exp_r, exp_bufs)), (r, bufs) in zip(cases, got):
            ok = r == exp_r if func not in ("reverse_q", "prefix_sum_q") else True
            # exp_bufs xếp theo VỊ TRÍ ĐỐI SỐ; cgtest chỉ trả các đối số là bộ đệm -> chọn đúng vị trí list
            buf_pos = [k for k, a in enumerate(args) if isinstance(a, list)]
            assert len(bufs) == len(buf_pos), (func, len(bufs), buf_pos)
            if exp_bufs:
                assert len(exp_bufs) <= len(args), func
                ok = ok and all(exp_bufs[k] is None or exp_bufs[k] == bufs[j]
                                for j, k in enumerate(buf_pos) if k < len(exp_bufs))
            if not ok:
                fails += 1
                if fails <= 3:
                    print(f"  {func}{args} -> {r} {bufs}; mong đợi {exp_r:#x} {exp_bufs}")
        print(f"[{'OK' if not fails else 'FAIL'}] {func}: {n - fails}/{n}")
        bad += fails
    return bad == 0


# ----------------------------------------------------------------------------------------------------------------
# Số đo
# ----------------------------------------------------------------------------------------------------------------
def code_lines(path):
    """Dòng mã (bỏ dòng trống / chỉ chú thích / include / data) của các hàm"""
    n, inside = 0, False
    for raw in open(path, encoding="utf-8"):
        s = raw.split("#", 1)[0].strip()
        if s.startswith("func "):
            inside = True
        if inside and s:
            n += 1
        if s == "}":
            inside = False
    return n


def metrics():
    rows, tot = [], [0, 0, 0, 0]
    for p in sorted(glob.glob(os.path.join(BENCH, "*.lit"))):
        fs = litparse.parse_file(p)
        toks = sum(litparse.func_tokens(f) for f in fs)
        insts = sum(len(list(f.insts())) for f in fs)
        spec = sum(1 for f in fs for c in f.contracts if c[0] in ("@req", "@ens"))
        annot = sum(len(b.annots) for f in fs for b in f.blocks)
        row = [code_lines(p), toks, insts, spec, annot]
        rows.append((os.path.basename(p), len(fs), row))
        tot = [a + b for a, b in zip(tot, row)]
    print(f"{'bài':24} {'hàm':>3} {'dòng':>5} {'token':>6} {'lệnh':>5} {'@req/@ens':>9} {'@inv/@dec':>9}")
    for name, nf, r in rows:
        print(f"{name:24} {nf:>3} {r[0]:>5} {r[1]:>6} {r[2]:>5} {r[3]:>9} {r[4]:>9}")
    print(f"{'TỔNG':24} {'':>3} {tot[0]:>5} {tot[1]:>6} {tot[2]:>5} {tot[3]:>9} {sum(r[2][4] for r in rows):>9}")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "all"
    if cmd in ("metrics", "all"):
        metrics()
    if cmd in ("test", "all"):
        sys.exit(0 if test() else 1)
