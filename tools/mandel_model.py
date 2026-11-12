#!/usr/bin/env python3
"""Mô hình tham chiếu cho lit_program/std/fixq.lit (Q4.60) và App Mandelbrot — bắt chước TỪNG BIT phép tính số nguyên.

    python3 tools/mandel_model.py test          # đối chiếu fq_mul / mb_iter / mb_color với mã máy thật (cgtest --call)
    python3 tools/mandel_model.py const X Y     # đổi tọa độ thập phân sang hằng Q4.60 (hex bù hai)
    python3 tools/mandel_model.py render OUT.ppm CX CY STEP W H MAXIT   # ảnh tham chiếu (CX/CY/STEP dạng hex Q4.60)
    python3 tools/mandel_model.py target        # dò điểm đích tự phóng: bám biên tập Mandelbrot tới bước 2^-52 (256 bit)
    python3 tools/mandel_model.py depth         # đo đáy phóng: so Q4.60 với số điểm cố định 256 bit ở thung lũng cá ngựa
"""
import os
import random
import subprocess
import sys
from decimal import Decimal, getcontext

M64 = (1 << 64) - 1
ONE = 1 << 60
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LIT = os.path.join(REPO, "lit_program", "std", "fixq.lit")


def mask(a):
    return (0 - (a >> 63)) & M64


def fq_abs(a):
    m = mask(a)
    return ((a ^ m) - m) & M64


def fq_mul(a, b):
    ua, ub = fq_abs(a), fq_abs(b)
    sm = mask(a ^ b)
    ah, al, bh, bl = ua >> 32, ua & 0xffffffff, ub >> 32, ub & 0xffffffff
    hh, hl, lh, ll = (ah * bh) & M64, (ah * bl) & M64, (al * bh) & M64, (al * bl) & M64
    u = (((hh << 4) & M64) + (hl >> 28) + (lh >> 28) + (ll >> 60)) & M64
    return ((u ^ sm) - sm) & M64


def mb_iter(cx, cy, maxit):
    zx = zy = 0
    for n in range(maxit):
        if fq_abs(zx) > 2 * ONE or fq_abs(zy) > 2 * ONE:
            return n
        x2, y2 = fq_mul(zx, zx), fq_mul(zy, zy)
        if (x2 + y2) & M64 > 4 * ONE:
            return n
        xy = fq_mul(zx, zy)
        zy = (((xy << 1) & M64) + cy) & M64
        zx = (x2 - y2 + cx) & M64
    return maxit


KEYS = [0x000764, 0x206bcb, 0xedffff, 0xffaa00, 0x000200]


def mb_color(n, maxit):
    if n >= maxit:
        return 0
    t = n % 80
    k, f = t >> 4, t & 15
    a, b = KEYS[k], KEYS[(k + 1) % 5]
    c = 0
    for sh in (16, 8, 0):
        ca, cb = (a >> sh) & 0xff, (b >> sh) & 0xff
        c |= (((ca * (16 - f) + cb * f) >> 4) & 0xff) << sh
    return c


def signed(v):
    return v - (1 << 64) if v >> 63 else v


def to_fq(s):
    getcontext().prec = 60
    return int((Decimal(s) * (1 << 60)).to_integral_value()) & M64


def cg_call(func, rows):
    exe = os.path.join(REPO, "target", "release", "cgtest")
    inp = "\n".join(" ".join(hex(v) for v in r) for r in rows) + "\n"
    out = subprocess.run([exe, "--call", LIT, func], input=inp, capture_output=True, text=True, check=True).stdout
    return [int(x, 16) for x in out.split()]


# ---- std/bignum.lit: số dấu-độ lớn n limb, F = 60 + 64 (n - 1) bit lẻ ----
BN_LIB = os.path.join(REPO, "lit_program", "std", "bignum.lit")


def bn_pack(sign, mag, n):
    """-> 17 Qword như trong bộ nhớ (dấu, limb thấp trước)"""
    return [sign] + [(mag >> (64 * i)) & M64 for i in range(n)] + [0] * (16 - n)


def bn_unpack(q, n):
    return q[0], sum(q[1 + i] << (64 * i) for i in range(n))


def bn_norm(s, a):
    return (0 if a == 0 else s), a


def bn_addsub(a, b, n, neg_b):
    (sa, ma), (sb, mb) = a, b
    sb = (sb ^ neg_b) & 1
    mod = 1 << (64 * n)
    if sa == sb:
        return bn_norm(sa, (ma + mb) % mod)
    if ma >= mb:
        return bn_norm(sa, ma - mb)
    return bn_norm(sb, mb - ma)


def bn_mul(a, b, n):
    (sa, ma), (sb, mb) = a, b
    return bn_norm((sa ^ sb) & 1, ((ma * mb) >> (60 + 64 * (n - 1))) % (1 << (64 * n)))


def bn_from_q(v, n):
    m = mask(v)
    return bn_norm(v >> 63, ((v ^ m) - m) & M64) if False else bn_norm(v >> 63, (((v ^ m) - m) & M64) << (64 * (n - 1)))


def bn_to_q(a, n):
    s, mag = a
    top = (mag >> (64 * (n - 1))) & M64
    m = (0 - (s & 1)) & M64
    return ((top ^ m) - m) & M64


def bn_call(func, rows, lib=BN_LIB):
    """rows: list các list token (int hoặc list Qword = bộ đệm); trả (kết quả, [bộ đệm sau lời gọi])"""
    exe = os.path.join(REPO, "target", "release", "cgtest")
    fmt = lambda t: "[" + ",".join(hex(v) for v in t) + "]" if isinstance(t, list) else hex(t)
    inp = "\n".join(" ".join(fmt(t) for t in r) for r in rows) + "\n"
    out = subprocess.run([exe, "--call", lib, func], input=inp, capture_output=True, text=True, check=True).stdout
    res = []
    for line in out.splitlines():
        parts = line.split(" ")
        res.append((int(parts[0], 16), [[int(x, 16) for x in b[1:-1].split(",")] for b in parts[1:]]))
    return res


def bn_from_mp(x, n):
    """số mpmath -> (dấu, độ lớn) cắt về F bit lẻ"""
    from mpmath import mpf, floor
    F = 60 + 64 * (n - 1)
    return bn_norm(1 if x < 0 else 0, int(floor(abs(x) * mpf(2) ** F)))


def mb_ref_run(cr, ci, zr, zi, n, count):
    """Như mb_ref_run trong std/mbref.lit: trả (danh sách (qr, qi) đã ghi, zr, zi)"""
    out = []
    lim = 1 << 61
    for k in range(count):
        out.append((bn_to_q(zr, n), bn_to_q(zi, n)))
        top = lambda a: (a[1] >> (64 * (n - 1))) & M64
        if top(zr) > lim or top(zi) > lim:
            return out, zr, zi
        x2, y2, xy = bn_mul(zr, zr, n), bn_mul(zi, zi, n), bn_mul(zr, zi, n)
        zr = bn_addsub(bn_addsub(x2, y2, n, 1), cr, n, 0)
        zi = bn_addsub(bn_addsub(xy, xy, n, 0), ci, n, 0)
    return out, zr, zi


# Điểm đích phóng sâu: tâm Mandelbrot con chu kỳ 1530 (cỡ ~1e-26) gần điểm bám biên cũ, tìm bằng chu kỳ quả cầu + Newton
NUC_PERIOD = 1530


def nucleus(prec=800):
    from mpmath import mp, mpf, mpc
    mp.prec = prec
    c0 = mpc(mpf(-0.7383804474313052), mpf(0.14518910758297718))
    z = dz = mpc(0)
    p = None
    for k in range(1, 100000):
        dz = 2 * z * dz + 1
        z = z * z + c0
        if abs(z) < mpf(10) ** -14 * abs(dz):
            p = k
            break
    c = c0
    for _ in range(200):
        z = dz = mpc(0)
        for _ in range(p):
            dz = 2 * z * dz + 1
            z = z * z + c
        d = z / dz
        c -= d
        if abs(d) < mpf(2) ** (-prec + 16):
            break
    return c, p


def test_ref(n=4, count=2 * NUC_PERIOD + 7):
    """Quỹ đạo tham chiếu tại tâm chu kỳ 1530: mã máy == mô hình (từng bit, 2 lô liên tiếp), tuần hoàn, không thoát,
    và gần quỹ đạo mpmath"""
    from mpmath import mpc
    c, p = nucleus()
    cr, ci = bn_from_mp(c.real, n), bn_from_mp(c.imag, n)
    z0 = (0, 0)
    lib = os.path.join(REPO, "lit_program", "std", "mbref.lit")
    s = bn_pack(*cr, n) + bn_pack(*ci, n) + bn_pack(*z0, n) + bn_pack(*z0, n) + [0] * 51
    half = count // 2
    (r1, b1), = bn_call("mb_ref_run", [[s, [0] * 32, n, [0] * 4096, half]], lib)
    (r2, b2), = bn_call("mb_ref_run", [[b1[0], [0] * 32, n, [0] * 4096, count - half]], lib)
    got = [(b1[2][2 * k], b1[2][2 * k + 1]) for k in range(r1)] + [(b2[2][2 * k], b2[2][2 * k + 1]) for k in range(r2)]
    want, _, _ = mb_ref_run(cr, ci, z0, z0, n, count)
    ok = got == want and len(got) == count
    zp = max(abs(signed(want[p][0])), abs(signed(want[p][1]))) / ONE
    z = mpc(0); err = 0.0
    for k in range(count):
        e = max(abs(float(z.real) - signed(want[k][0]) / ONE), abs(float(z.imag) - signed(want[k][1]) / ONE))
        err = max(err, e)
        z = z * z + c
    print(f"mb_ref_run: chu kỳ {p}, n = {n} limb, {count} vòng (2 lô): {'khớp' if got == want else 'LỆCH'} mô hình, "
          f"{len(got)} Z đã ghi, |Z_p| = {zp:.1e}, lệch mpmath tối đa {err:.1e}")
    return ok and p == NUC_PERIOD


def test_bn(rnd):
    def rbn(n):
        r = rnd.random()
        bits = 64 * n
        if r < 0.1:
            mag = 0
        elif r < 0.2:
            mag = (1 << bits) - 1 >> rnd.choice([0, 4, 60])
        elif r < 0.3:
            mag = rnd.getrandbits(rnd.randrange(1, min(70, bits + 1)))
        else:
            mag = rnd.getrandbits(bits - rnd.choice([0, 1, 3, 4, 8]))
        return bn_norm(rnd.randrange(2), mag)
    bad = tot = 0
    # cộng / trừ, có đích trùng nguồn (gọi với cùng bộ đệm không được qua cgtest: thử riêng bằng hàm Light bọc ở dưới)
    rows, want = [], []
    for _ in range(3000):
        n = rnd.choice([1, 2, 3, 4, 5, 8, 16])
        a, b, neg = rbn(n), rbn(n), rnd.randrange(2)
        rows.append([[0] * 17, bn_pack(*a, n), bn_pack(*b, n), n, neg])
        want.append(bn_pack(*bn_addsub(a, b, n, neg), n))
    for (r, bufs), w in zip(bn_call("bn_addsub", rows), want):
        tot += 1; bad += bufs[0] != w
    print(f"bn_addsub: {tot} ca, lệch {bad}")
    b1 = bad
    rows, want = [], []
    for _ in range(3000):
        n = rnd.choice([1, 2, 3, 4, 5, 8, 16])
        a, b = rbn(n), rbn(n)
        rows.append([[0] * 17, bn_pack(*a, n), bn_pack(*b, n), n, [0] * 32])
        want.append(bn_pack(*bn_mul(a, b, n), n))
    bad = 0
    for row, (r, bufs), w in zip(rows, bn_call("bn_mul", rows), want):
        if bufs[0] != w and bad < 2:
            n = row[3]
            print("  lệch n", n, "a", row[1][:n + 1], "b", row[2][:n + 1], "\n   được", bufs[0][:n + 1], "\n   muốn", w[:n + 1])
        bad += bufs[0] != w
    print(f"bn_mul: {len(rows)} ca, lệch {bad}")
    b2 = bad
    rows, want = [], []
    for _ in range(1000):
        n = rnd.choice([1, 2, 4, 16])
        v = rnd.getrandbits(64)
        rows.append([[0] * 17, v, n])
        want.append(bn_pack(*bn_from_q(v, n), n))
    bad = sum(bufs[0] != w for (r, bufs), w in zip(bn_call("bn_from_q", rows), want))
    rows2 = []
    for _ in range(1000):
        n = rnd.choice([1, 2, 4, 16]); a = rbn(n)
        rows2.append(([bn_pack(*a, n), n], bn_to_q(a, n)))
    bad += sum(r != w for (r, _), (_, w) in zip(bn_call("bn_to_q", [x for x, _ in rows2]), rows2))
    print(f"bn_from_q / bn_to_q: 2000 ca, lệch {bad}")
    return b1 == 0 and b2 == 0 and bad == 0


def test():
    rnd = random.Random(1)

    def q(lim):  # số Q4.60 ngẫu nhiên trong (-lim, lim), có cả biên và giá trị nhỏ
        r = rnd.random()
        if r < 0.1:
            return rnd.choice([0, 1, M64, ONE, (-ONE) & M64, 2 * ONE, (-2 * ONE) & M64])
        if r < 0.2:
            return rnd.randrange(-1000, 1000) & M64
        return rnd.randrange(-lim, lim) & M64

    # 1. fq_mul: mã máy == mô hình (từng bit), và sai số so với tích chính xác <= 3 ulp
    rows = [(q(2 * ONE), q(2 * ONE)) for _ in range(20000)]
    got = cg_call("fq_mul", rows)
    bad = [(a, b, g) for (a, b), g in zip(rows, got) if g != fq_mul(a, b)]
    err = max(abs(signed(fq_mul(a, b)) * ONE - signed(a) * signed(b)) for a, b in rows) / ONE
    print(f"fq_mul: {len(rows)} ca, lệch mô hình {len(bad)}, sai số lớn nhất so với tích đúng {err:.2f} ulp")
    # 2. mb_iter
    rows = [(q(2 * ONE), q(2 * ONE), rnd.choice([1, 10, 100, 500])) for _ in range(3000)]
    # sát biên + maxit lớn (nơi dò chu kỳ của mã Light phải trả đúng như lặp đủ): quanh điểm đích tự phóng, nhiều độ sâu
    tx, ty = 0xf42f97fbe46d59db, 0x252b1d04cde76d3
    for _ in range(600):
        st = 1 << (60 - rnd.choice([4, 8, 12, 20, 28, 36, 44]))
        rows.append(((tx + rnd.randrange(-300, 300) * st) & M64, (ty + rnd.randrange(-300, 300) * st) & M64, rnd.choice([500, 2000])))
    for _ in range(300):  # trong tập: thân chính, bầu -1, sát biên trong
        rows.append((to_fq(str(rnd.uniform(-0.5, 0.2))), to_fq(str(rnd.uniform(-0.4, 0.4))), 3000))
        rows.append((to_fq(str(rnd.uniform(-1.2, -0.8))), to_fq(str(rnd.uniform(-0.2, 0.2))), 3000))
    got = cg_call("mb_iter", rows)
    bad2 = [r for r, g in zip(rows, got) if g != mb_iter(*r)]
    full = sum(1 for r in rows if mb_iter(*r) == r[2])
    print(f"mb_iter: {len(rows)} ca ({full} ca không thoát), lệch {len(bad2)}")
    # 3. mb_color
    rows = [(rnd.randrange(0, 2000), rnd.choice([100, 500, 2000])) for _ in range(3000)]
    got = cg_call("mb_color", rows)
    bad3 = [r for r, g in zip(rows, got) if (g & 0xffffffff) != mb_color(*r)]
    print(f"mb_color: {len(rows)} ca, lệch {len(bad3)}")
    okb = test_bn(rnd) and test_ref()
    ok = not bad and not bad2 and not bad3 and err <= 3 and okb
    print("OK" if ok else "SAI")
    return ok


def mb_iter_exact(cx, cy, maxit, bits=256):
    """Như mb_iter nhưng số điểm cố định `bits` bit lẻ (Python int, không tràn): tham chiếu "đúng"."""
    zx = zy = 0
    two, four = 2 << bits, 4 << bits
    for n in range(maxit):
        if abs(zx) > two or abs(zy) > two:
            return n
        x2, y2 = (zx * zx) >> bits, (zy * zy) >> bits
        if x2 + y2 > four:
            return n
        zy = ((zx * zy) >> (bits - 1)) + cy
        zx = x2 - y2 + cx
    return maxit


def maxit_of(step0, step):
    """Như mb_maxit trong apps/mandel.lit"""
    mag, k = step0 // max(step, 1), 0
    while mag > 1 and k < 64:
        mag, k = mag >> 1, k + 1
    return max(96, min(96 + 48 * k, 2000))


def find_target(cx="-0.7436438870371587", cy="0.1318259042053120", g=12, deep=52):
    """Bám biên: ở mỗi mức (bước 2^-e, e += 2) lưới g x g quanh tâm, lấy điểm ảnh THOÁT có số vòng lớn nhất (gần tâm
    nhất khi bằng nhau) làm tâm mới. Điểm cuối nằm trong mọi khung trước đó nên tự phóng vào nó luôn thấy biên."""
    B = 256
    x, y = int(Decimal(cx) * (1 << B)), int(Decimal(cy) * (1 << B))
    step0 = min(0x3400000000000000 // 796, 1 << 53)
    for e in range(8, deep + 1, 2):
        st = 1 << (B - e)
        mi = maxit_of(step0, 1 << (60 - e))
        best = None
        for j in range(g):
            for i in range(g):
                a, b = x + (i - g // 2) * st, y + (j - g // 2) * st
                n = mb_iter_exact(a, b, mi, B)
                if n < mi:
                    key = (n, -abs(i - g // 2) - abs(j - g // 2))
                    if best is None or key > best[0]:
                        best = (key, a, b)
        if best:
            x, y = best[1], best[2]
        print(f"2^-{e}: maxit {mi}, vòng lớn nhất {best[0][0] if best else '-'}", flush=True)
    return x >> (B - 60), y >> (B - 60)


def depth(w=40, h=24, cx=None, cy=None):
    if cx is None:
        cx, cy = to_fq("-0.7436438870371587"), to_fq("0.1318259042053120")
    step0 = min(0x3400000000000000 // 796, 1 << 53)
    print(f"điểm {signed(cx) / ONE} {signed(cy) / ONE}, lưới {w}x{h}")
    for e in (24, 32, 38, 42, 44, 46, 48, 50, 52):
        step = 1 << (60 - e)
        mi = maxit_of(step0, step)
        x0, y0 = signed(cx) - (w // 2) * step, signed(cy) + (h // 2) * step
        bad, seen = 0, set()
        for y in range(h):
            for x in range(w):
                a, b = x0 + x * step, y0 - y * step
                n = mb_iter(a & M64, b & M64, mi)
                r = mb_iter_exact(a << 196, b << 196, mi)
                bad += n != r
                seen.add(r)
        print(f"bước 2^-{e}: maxit {mi:4d}, lệch {100 * bad / (w * h):5.1f}% điểm ảnh, {len(seen)} mức vòng khác nhau (tham chiếu)", flush=True)


def render(out, cx, cy, step, w, h, maxit):
    """Như App: điểm (x, y) = (cx - (w/2)*step + x*step, cy + (h/2)*step - y*step)."""
    x0 = (cx - (w // 2) * step) & M64
    y0 = (cy + (h // 2) * step) & M64
    with open(out, "wb") as f:
        f.write(f"P6 {w} {h} 255\n".encode())
        for y in range(h):
            ci = (y0 - y * step) & M64
            row = bytearray()
            for x in range(w):
                c = mb_color(mb_iter((x0 + x * step) & M64, ci, maxit), maxit)
                row += bytes(((c >> 16) & 255, (c >> 8) & 255, c & 255))
            f.write(row)


if __name__ == "__main__":
    if sys.argv[1] == "test":
        sys.exit(0 if test() else 1)
    elif sys.argv[1] == "const":
        for s in sys.argv[2:]:
            print(s, hex(to_fq(s)))
    elif sys.argv[1] == "depth":
        a = [int(v, 16) for v in sys.argv[2:4]]
        depth(cx=a[0], cy=a[1]) if a else depth()
    elif sys.argv[1] == "target":
        tx, ty = find_target()
        print("MB_TGT_X", hex(tx & M64), "MB_TGT_Y", hex(ty & M64), signed(tx & M64) / ONE, signed(ty & M64) / ONE)
    elif sys.argv[1] == "render":
        o, cx, cy, st, w, h, mi = sys.argv[2:9]
        render(o, int(cx, 16), int(cy, 16), int(st, 16), int(w), int(h), int(mi))
