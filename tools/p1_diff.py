#!/usr/bin/env python3
"""Đối chiếu vi sai cú pháp B (P1): mỗi hàm trong bench/p1/*.lt chạy mã máy THẬT trên cùng đầu vào với bản SSA gốc
(lit_program/std/*.lit hoặc bench/today/*.lit) và phải cho KẾT QUẢ + BỘ NHỚ giống hệt từng bit.

    python3 tools/p1_diff.py            # 300 đầu vào / hàm
    python3 tools/p1_diff.py --stats    # thêm bảng so số dòng / token SSA gốc với cú pháp B

Đầu vào sinh tự động theo chữ ký của hàm gốc; chỉ giữ đầu vào thỏa MỌI @req (đánh giá biểu thức tiền tố của SSA ở đây),
vì ngoài @req hai bản được phép khác nhau. Đặc tả hôm nay yếu nên kiểm chứng Z3 một mình không bắt được lỗi hạ sai.
"""
import glob
import os
import random
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CGTEST = os.path.join(REPO, "target", "release", "cgtest")
M64 = (1 << 64) - 1
ORIG_FILES = sorted(glob.glob(os.path.join(REPO, "lit_program", "std", "*.lit"))) + [
    os.path.join(REPO, "bench", "today", "13_base64_enc.lit")] + sorted(glob.glob(os.path.join(REPO, "bench", "p1", "*.lit")))
LAYOUT_BYTES = {m.group(1): int(m.group(2), 0) for p in ORIG_FILES for l in open(p, encoding="utf-8")
                for m in [re.match(r"\s*layout\s+(\w+)\s+(\S+)", l)] if m}


def defs():
    d = {}
    for p in ORIG_FILES:
        for l in open(p, encoding="utf-8"):
            m = re.match(r"\s*def\s+(\w+)\s+(\S+)", l)
            if m:
                d[m.group(1)] = int(m.group(2), 0)
    return d


DEFS = defs()


def num(tok):
    if tok in DEFS:
        return DEFS[tok]
    return int(tok.split(":")[0], 0)


def find_orig(name):
    for p in ORIG_FILES:
        lines = open(p, encoding="utf-8").read().split("\n")
        for i, l in enumerate(lines):
            if re.match(rf"func {name}\s", l):
                sig = l.split("{")[0].split()
                reqs = []
                for l2 in lines[i + 1:]:
                    t = l2.split("#")[0].split()
                    if t and t[0] == "@req":
                        reqs.append(t[1:])
                    elif t and t[0] not in ("@ens",):
                        break
                params = [tuple(x[1:].split(":", 1)) for x in sig[3:]]
                return p, sig[2], params, reqs
    raise SystemExit(f"không tìm thấy hàm gốc {name}")


def to_signed(v):
    return v - (1 << 64) if v >> 63 else v


def ev(toks, env):
    """Đánh giá biểu thức tiền tố như Z3Expr (bit-vector 64-bit, quay vòng)"""
    t = toks.pop(0)
    bin2 = lambda: (ev(toks, env), ev(toks, env))
    if t == "not":
        x = ev(toks, env)
        return 1 - x if x in (0, 1) else ~x & M64
    ops = {
        "and": lambda a, b: a & b, "or": lambda a, b: a | b, "xor": lambda a, b: a ^ b,
        "add": lambda a, b: (a + b) & M64, "add_wrap": lambda a, b: (a + b) & M64,
        "sub": lambda a, b: (a - b) & M64, "sub_wrap": lambda a, b: (a - b) & M64,
        "mul": lambda a, b: (a * b) & M64, "mul_wrap": lambda a, b: (a * b) & M64,
        "udiv": lambda a, b: a // b if b else M64, "urem": lambda a, b: a % b if b else a,
        "shl": lambda a, b: (a << b) & M64 if b < 64 else 0, "lshr": lambda a, b: a >> b if b < 64 else 0,
        "eq": lambda a, b: int(a == b), "ne": lambda a, b: int(a != b), "ult": lambda a, b: int(a < b),
        "ule": lambda a, b: int(a <= b), "ugt": lambda a, b: int(a > b), "uge": lambda a, b: int(a >= b),
        "slt": lambda a, b: int(to_signed(a) < to_signed(b)), "sle": lambda a, b: int(to_signed(a) <= to_signed(b)),
        "sgt": lambda a, b: int(to_signed(a) > to_signed(b)), "sge": lambda a, b: int(to_signed(a) >= to_signed(b)),
    }
    if t in ops:
        a, b = bin2()
        return ops[t](a, b)
    if t.startswith("%"):
        return env[t[1:]]
    return num(t)


INTERESTING = [0, 1, 2, 3, 4, 7, 15, 16, 17, 31, 63, 64, 65, 79, 80, 90, 97, 122, 255, 256, 0xffffffff, 1 << 32,
               1 << 59, 1 << 60, 0x2000000000000000, 0xe000000000000000, 1 << 63, M64 - 1, M64]


def rand_val(rng, bits, small):
    if small or rng.random() < 0.45:
        v = rng.randint(0, 40)
    elif rng.random() < 0.5:
        v = rng.choice(INTERESTING)
    else:
        v = rng.getrandbits(64)
    return v & ((1 << bits) - 1)


def gen_case(rng, params, reqs):
    lens = {m.group(1) for _, ty in params for m in [re.match(r"ptr<\w+,%(\w+)>", ty)] if m}
    for _ in range(5000):
        env, row = {}, []
        for name, ty in params:
            m = re.match(r"ptr<(\w+),(%?\w+)>", ty)
            if m:
                lay, n = m.group(1), m.group(2)
                cnt = env[n[1:]] if n.startswith("%") else num(n)
                qwords = max(1, (cnt * LAYOUT_BYTES[lay] + 7) // 8)
                buf = [rng.choice([rng.getrandbits(64), rng.getrandbits(8) * 0x0101010101010101,
                                   0x3938373635343332, 0x5a41617a30393d2b]) for _ in range(qwords)]
                row.append(buf)
                env[name] = 0
            else:
                bits = int(ty[2:])
                v = rand_val(rng, bits, name in lens)
                env[name] = v
                row.append(v)
        if all(ev(list(r), env) for r in reqs):
            return row
    raise SystemExit(f"không sinh được đầu vào thỏa @req: {reqs}")


def call(file, func, rows):
    fmt = lambda t: "[" + ",".join(hex(v) for v in t) + "]" if isinstance(t, list) else hex(t)
    inp = "\n".join(" ".join(fmt(t) for t in r) for r in rows) + "\n"
    r = subprocess.run([CGTEST, "--call", file, func], input=inp, capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"cgtest --call {file} {func} lỗi:\n{r.stderr[-2000:]}")
    return r.stdout.splitlines()


def main(n=300):
    rng = random.Random(20261113)
    bad = 0
    rows_stats = []
    for lt in sorted(glob.glob(os.path.join(REPO, "bench", "p1", "*.lt"))):
        for name in re.findall(r"^fn (\w+)", open(lt, encoding="utf-8").read(), re.M):
            orig, ret, params, reqs = find_orig(name)
            cases = [gen_case(rng, params, reqs) for _ in range(n)]
            a, b = call(orig, name, cases), call(lt, name, cases)
            if ret == "void":  # rax rác: chỉ so bộ nhớ
                a = [x.split(" ", 1)[1] if " " in x else "" for x in a]
                b = [x.split(" ", 1)[1] if " " in x else "" for x in b]
            diff = [(c, x, y) for c, x, y in zip(cases, a, b) if x != y]
            ok = not diff and len(a) == len(b) == n
            print(f"[{'OK' if ok else 'FAIL'}] {name:16} ({os.path.relpath(lt, REPO)} vs {os.path.relpath(orig, REPO)}): "
                  f"{n - len(diff)}/{n} giống hệt")
            for c, x, y in diff[:3]:
                print(f"    vào {c}\n    gốc {x}\n    B   {y}")
            bad += len(diff) + (len(a) != len(b))
            if "/bench/p1/" not in orig:  # bản song sinh tự viết để thử trường có tên: không tính vào số đo std
                rows_stats.append((name, orig, lt))
    if "--stats" in sys.argv:
        stats(rows_stats)
    return bad == 0


def stats(rows):
    sys.path.insert(0, os.path.join(REPO, "tools", "stitch"))
    import litparse
    print(f"\n{'hàm':16} {'dòng SSA':>8} {'dòng B':>7} {'token SSA':>9} {'token B':>8} {'ký tự SSA':>9} {'ký tự B':>8}")
    tot = [0, 0, 0, 0, 0, 0]
    for name, orig, lt in rows:
        f = next(f for f in litparse.parse_file(orig) if f.name == name)
        src = open(orig, encoding="utf-8").read().split("\n")
        # dòng SSA: từ dòng func tới '}' đầu tiên, bỏ dòng trống / chú thích
        body = []
        for l in src[f.line - 1:]:
            s = l.split("#")[0].strip()
            if s:
                body.append(s)
            if s == "}":
                break
        ssa_lines = len(body)
        bsrc = open(lt, encoding="utf-8").read().split("\n")
        start = next(i for i, l in enumerate(bsrc) if re.match(rf"fn {name}\(", l))
        depth, blines, seen_open = 0, [], False
        for l in bsrc[start:]:
            s = l.split("//")[0].strip()
            if s:
                blines.append(s)
            depth += s.count("{") - s.count("}")
            seen_open |= "{" in s
            if seen_open and depth == 0:
                break
        btok = int(subprocess.run([os.path.join(REPO, "target", "release", "light"), "tokens", "-"],
                                  input="\n".join(blines), capture_output=True, text=True).stdout.strip() or 0)
        chars = lambda ls: sum(len("".join(l.split())) for l in ls)
        r = [ssa_lines, len(blines), litparse.func_tokens(f), btok, chars(body), chars(blines)]
        tot = [x + y for x, y in zip(tot, r)]
        print(f"{name:16} {r[0]:>8} {r[1]:>7} {r[2]:>9} {r[3]:>8} {r[4]:>9} {r[5]:>8}")
    print(f"{'TỔNG':16} {tot[0]:>8} {tot[1]:>7} {tot[2]:>9} {tot[3]:>8} {tot[4]:>9} {tot[5]:>8}")
    print("(token SSA đếm theo khoảng trắng: `%n:bv64` là 1 token; token B đếm cả dấu câu ( , : ; — hai cột không cùng thước;"
          " ký tự = không tính khoảng trắng / chú thích)")


if __name__ == "__main__":
    sys.exit(0 if main() else 1)
