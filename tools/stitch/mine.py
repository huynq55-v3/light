#!/usr/bin/env python3
"""Light-Stitch giai đoạn 0 + 1: đo MDL của lit_program/ và dò mẫu lặp đáng thành primitive (CHỈ ĐỌC, không sửa mã).

    python3 tools/stitch/mine.py                 # báo cáo target/stitch/report.md + candidates.json
    python3 tools/stitch/mine.py --top 30 --maxk 16

MDL = số token (xem litparse.func_tokens). Hai loại ứng viên:
  A. đoạn lệnh thẳng trong một khối (không có br/jmp/ret), so khớp theo LUỒNG DỮ LIỆU: giá trị định nghĩa trong đoạn
     -> d0, d1...; giá trị từ ngoài -> đầu vào i0, i1... (cùng giá trị ngoài = cùng đầu vào); `%x = const N bvK` được
     gộp thành hằng; hằng ở vị trí giá trị (toán hạng, đối số call, giá trị store, chỉ số slice) khác nhau giữa các lần
     xuất hiện -> lỗ (tham số). Đoạn có > 1 giá trị dùng tiếp ở ngoài bị loại (hàm Light trả một giá trị).
  B. hàm gần-trùng: cả hàm giống nhau sau khi đổi tên và khoét hằng.
Điểm (tiêu chí "nén có khấu hao"): lợi = tổng(cỡ đoạn - cỡ lời gọi) - cỡ định nghĩa primitive. Thư viện đề xuất chọn
tham lam (như Stitch): lấy ứng viên lợi nhất, đánh dấu lệnh đã phủ, tính lại các ứng viên khác trên phần chưa phủ.
"""
import argparse
import collections
import re
import heapq
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import litparse as L  # noqa: E402

BINOPS = {"add", "sub", "mul", "udiv", "sdiv", "urem", "srem", "and", "or", "xor", "shl", "lshr", "ashr", "fxmul",
          "fxdiv", "add_wrap", "sub_wrap", "mul_wrap", "add_sat", "sub_sat", "mul_sat", "add_ovf", "sub_ovf", "mul_ovf"}
NO_FRAG = L.TERMINATORS | {"parallel", "ata_read", "smp_workers", "assume", "assert"}


def holeable(op, k):
    """Đối số thứ k của lệnh op có phải vị trí GIÁ TRỊ (hằng ở đây có thể thành tham số) không."""
    if op in BINOPS:
        return True
    if op == "cmp":
        return k >= 1
    if op == "call":
        return k >= 1
    if op == "store":
        return k == 2
    if op == "slice":
        return k == 1
    if op in ("jmp", "br"):  # giá trị truyền cho tham số khối (nhãn không bao giờ là hằng nên không bị đụng)
        return k >= 1
    return False


class FnInfo:
    """Hàm đã chuẩn hóa: bỏ dòng const (gộp vào chỗ dùng), kiểu của từng giá trị, chỗ dùng của từng giá trị."""

    def __init__(self, fn, sigs):
        self.fn = fn
        consts, types = {}, dict(fn.params)
        for b in fn.blocks:
            types.update(dict(b.params))
        for i in fn.insts():
            if i.op == "const" and i.dst and len(i.args) == 2:
                consts[i.dst] = i.args[0]  # mọi const (số, địa chỉ ptr, thẻ smp) gộp vào chỗ dùng
        self.consts = consts
        # khối -> danh sách (inst gốc, args đã thay hằng)
        self.blocks = []
        uses = collections.defaultdict(list)  # giá trị -> [(bi, ii)] ; ii = -1: chú giải / tham số khối
        for bi, b in enumerate(fn.blocks):
            for a in b.annots:
                for t in a:
                    for v in L.VAL_RE.findall(t):
                        uses[v].append((bi, -1))
            for _, t in b.params:  # kiểu phụ thuộc của tham số khối: ptr<Byte,%n>
                for v in L.VAL_RE.findall(t):
                    uses[v].append((bi, -1))
            row = []
            for i in b.insts:
                if i.op == "const" and i.dst in consts:
                    continue
                args = [consts.get(a, a) for a in i.args]
                ii = len(row)
                for a in args:  # kể cả tên nằm TRONG kiểu (slice %s %i ptr<Byte,%k>)
                    for v in L.VAL_RE.findall(a):
                        uses[v].append((bi, ii))
                row.append((i, args))
                if i.dst:
                    types[i.dst] = self._type(i, args, types, sigs)
            self.blocks.append(row)
        for c in fn.contracts:  # @ens có thể nhắc giá trị trả về (%r) — không phải giá trị trong thân
            pass
        self.uses = uses
        self.types = types

    @staticmethod
    def _type(i, args, types, sigs):
        op = i.op
        if op == "cmp":
            return "bool"
        if op in ("load", "slice", "view", "narrow", "const") and args:
            t = args[-1]
            return t if t.startswith(("bv", "ptr<", "smp")) else "bv64"  # load theo trường layout: coi là số
        if op == "call" and args:
            return sigs.get(args[0], "?")
        if op == "addr":
            return "ptr(data)"
        if op == "hwio_r":
            return "bv8"
        for a in args:
            if a.startswith("%") and a in types:
                return types[a]
        return "bv64"


def canon(fi, bi, s, e):
    """Đoạn [s, e) của khối bi -> (khóa, hằng ở các lỗ, đầu vào, đầu ra) hoặc None nếu không trích được."""
    row = fi.blocks[bi][s:e]
    inside, inputs, lits, out = {}, {}, [], []
    for k, (i, args) in enumerate(row):
        if i.op in NO_FRAG:
            return None
        ca = []
        for j, a in enumerate(args):
            if a.startswith("%"):
                if a in inside:
                    ca.append(inside[a])
                else:
                    inputs.setdefault(a, f"i{len(inputs)}")
                    ca.append(inputs[a])
            elif "%" in a:  # tên nằm trong kiểu
                ca.append(L.VAL_RE.sub(lambda m: inside.get(m.group(0)) or inputs.setdefault(m.group(0), f"i{len(inputs)}"), a))
            elif holeable(i.op, j):
                ca.append("?")
                lits.append(a)
            else:
                ca.append(a)
        d = ""
        if i.dst:
            inside[i.dst] = f"d{len(inside)}"
            d = inside[i.dst] + " = "
        out.append(d + i.op + " " + " ".join(ca))
    # đầu ra: giá trị trong đoạn được dùng ở ngoài đoạn
    live = []
    for v, cv in inside.items():
        for (ub, ui) in fi.uses.get(v, []):
            if ub != bi or ui < s or ui >= e:
                live.append(cv)
                break
    if len(live) > 1:
        return None
    # bool qua ranh giới hàm hợp lệ (đã thử bằng `light check`): không phạt
    key = tuple(out) + (("->" + live[0]) if live else "->void",)
    return key, tuple(lits), inputs, (False, True)


def frag_tokens(fi, bi, s, e):
    return sum(len(i.tokens()) for i, _ in fi.blocks[bi][s:e])


class Cand:
    def __init__(self, key):
        self.key = key
        self.occ = []  # (fn idx, bi, s, e, lits, inputs)
        self.kind = "frag"

    def finish(self, infos):
        lits = [o[4] for o in self.occ]
        self.holes = [j for j in range(len(lits[0])) if len({l[j] for l in lits}) > 1]
        self.ninputs = len(self.occ[0][5])
        # con trỏ: cỡ khác nhau giữa các chỗ dùng, hoặc cỡ phụ thuộc giá trị ngoài -> cần thêm tham số độ dài
        self.nlen = 0
        for j in range(self.ninputs):
            ts = {o[8][j] for o in self.occ}
            if any(t.startswith("ptr<") for t in ts) and (len(ts) > 1 or any("%" in t for t in ts)):
                self.nlen += 1
        self.out_bool = self.occ[0][6]
        self.nparams = self.ninputs + len(self.holes) + self.nlen
        self.size = frag_tokens(infos[self.occ[0][0]], *self.occ[0][1:4]) if self.occ[0][2] >= 0 else 0
        self.has_out = not self.key[-1].endswith("void")

    def call_cost(self):
        return (2 if self.has_out else 0) + 2 + self.nparams

    def def_cost(self):
        # đầu ra bool: không ret được bool -> br d @t @f / @t ret 1 / @f ret 0 thay cho ret d
        tail = (10 if self.out_bool else 2) if self.has_out else 1
        return 3 + self.nparams + 1 + self.size + tail

    def pick(self, covered):
        """Các lần xuất hiện không chồng nhau và không chạm lệnh đã phủ."""
        res, used = [], set()
        for o in self.occ:
            cells = {(o[0], o[1], x) for x in range(o[2], o[3])}
            if cells & covered or cells & used:
                continue
            used |= cells
            res.append(o)
        return res, used

    def gain(self, covered=frozenset()):
        res, _ = self.pick(covered)
        if len(res) < 2:
            return 0, res
        return sum(self.size - self.call_cost() - o[7] for o in res) - self.def_cost(), res

    def site(self, infos, o):
        fi = infos[o[0]]
        return f"{rel(fi.fn.file)}:{fi.blocks[o[1]][o[2]][0].line}"


class RCand(Cand):
    """Vùng nhiều khối liên tiếp (vòng lặp, if/else): một lối vào (jmp từ đúng một khối ngoài), tối đa một nhãn ra."""

    def finish(self, infos):
        super().finish(infos)
        self.kind = "region"
        fi = infos[self.occ[0][0]]
        self.size = region_tokens(fi, self.occ[0][1], self.occ[0][3])

    def call_cost(self):
        # khối ngoài: `jmp @l args` -> `%r = call f ...` + `jmp @X [%r]`
        return (2 if self.has_out else 0) + 2 + self.nparams + 2 + (1 if self.has_out else 0)

    def def_cost(self):
        # đầu hàm + khối vào `@b0 / jmp @l args`; lối ra `jmp @X v` thành `ret v` (ngang nhau)
        return 3 + self.nparams + 1 + 2 + self.nentry + self.size

    def pick(self, covered):
        res, used = [], set()
        for o in self.occ:
            cells = set()
            for bi in range(o[1], o[3]):
                cells |= {(o[0], bi, x) for x in range(len(infos_g[o[0]].blocks[bi]))}
            if cells & covered or cells & used:
                continue
            used |= cells
            res.append(o)
        return res, used

    def site(self, infos, o):
        fi = infos[o[0]]
        return f"{rel(fi.fn.file)}:{fi.fn.blocks[o[1]].line}"


infos_g = []


def region_tokens(fi, bs, be):
    n = 0
    for bi in range(bs, be):
        b = fi.fn.blocks[bi]
        n += 1 + len(b.params) + sum(len(a) for a in b.annots)
        n += sum(len(i.tokens()) for i, _ in fi.blocks[bi])
    return n


def preds(fi):
    idx = {b.label: k for k, b in enumerate(fi.fn.blocks)}
    pr = collections.defaultdict(list)
    for bi, row in enumerate(fi.blocks):
        for i, args in row:
            if i.op in ("br", "jmp"):
                for a in args:
                    if a in idx:
                        pr[idx[a]].append((bi, i.op))
    return idx, pr


def canon_region(fi, bs, be, idx, pr):
    blocks = fi.fn.blocks[bs:be]
    inside_lbl = {b.label: f"@L{k}" for k, b in enumerate(blocks)}
    ext_in = [p for p in pr.get(bs, []) if not (bs <= p[0] < be)]
    if len(ext_in) != 1 or ext_in[0][1] != "jmp":
        return None
    for bi in range(bs + 1, be):
        if any(not (bs <= p[0] < be) for p in pr.get(bi, [])):
            return None
    inside, inputs, lits, out, exits, exit_vals = {}, {}, [], [], set(), set()

    def val(a):
        if a in inside:
            return inside[a]
        inputs.setdefault(a, f"i{len(inputs)}")
        return inputs[a]

    nentry = len(blocks[0].params)
    for k, b in enumerate(blocks):
        for pn, _ in b.params:
            inside[pn] = (f"e{len(inside)}" if k == 0 else f"d{len(inside)}")
        out.append(inside_lbl[b.label] + " " + " ".join(inside[pn] + ":" + t for pn, t in b.params))
    out = [L.VAL_RE.sub(lambda m: inside.get(m.group(0), m.group(0)), x) for x in out]
    for k, b in enumerate(blocks):
        bi = bs + k
        for a in b.annots:
            pass  # chú giải xử lý sau khi biết mọi định nghĩa trong vùng
        for i, args in fi.blocks[bi]:
            if i.dst:
                inside[i.dst] = f"d{len(inside)}"
    for k, b in enumerate(blocks):
        bi = bs + k
        out.append(inside_lbl[b.label])
        for a in b.annots:
            out.append(" ".join(L.VAL_RE.sub(lambda m: val(m.group(0)), t) for t in a))
        for i, args in fi.blocks[bi]:
            if i.op == "ret" or (i.op in NO_FRAG and i.op not in ("br", "jmp")):
                return None
            ca, cur_ext = [], False
            for j, a in enumerate(args):
                if a.startswith("@"):
                    if a in inside_lbl:
                        ca.append(inside_lbl[a]); cur_ext = False
                    else:
                        exits.add(a); ca.append("@X"); cur_ext = True
                elif a.startswith("%"):
                    v = val(a)
                    ca.append(v)
                    if i.op == "jmp" and cur_ext:
                        exit_vals.add(v)
                elif "%" in a:
                    ca.append(L.VAL_RE.sub(lambda m: val(m.group(0)), a))
                elif holeable(i.op, j):
                    ca.append("?"); lits.append(a)
                else:
                    ca.append(a)
            d = (inside[i.dst] + " = ") if i.dst else ""
            out.append(d + i.op + " " + " ".join(ca))
    if len(exits) != 1:
        return None
    # giá trị trong vùng dùng ở ngoài (ngoài đường jmp @X v)
    live = set(exit_vals)
    rev = {}
    for v, cv in inside.items():
        rev[cv] = v
        for (ub, ui) in fi.uses.get(v, []):
            if not (bs <= ub < be):
                live.add(cv)
    if len(live) > 1:
        return None
    lv = next(iter(live)) if live else None
    key = ("R",) + tuple(out) + (("->" + lv) if lv else "->void",)
    ob = bool(lv) and fi.types.get(rev.get(lv, ""), "") == "bool"
    return key, tuple(lits), inputs, ob, nentry


def mine_regions(infos, maxb):
    groups = {}
    for fx, fi in enumerate(infos):
        idx, pr = preds(fi)
        nb = len(fi.blocks)
        for bs in range(nb):
            for be in range(bs + 2, min(nb, bs + maxb) + 1):
                c = canon_region(fi, bs, be, idx, pr)
                if c is None:
                    continue
                key, lits, inputs, ob, nentry = c
                g = groups.get(key)
                if g is None:
                    g = groups[key] = RCand(key)
                    g.nentry = nentry
                tys = tuple(fi.types.get(v, "?") for v in inputs)
                g.occ.append((fx, bs, -1, be, lits, inputs, ob, 6 if ob else 0, tys))
    out = []
    for g in groups.values():
        if len(g.occ) >= 2:
            g.finish(infos)
            g.nparams += g.nentry
            out.append(g)
    return out


def mine_frags(infos, mink, maxk, min_tok):
    groups = {}
    for fx, fi in enumerate(infos):
        for bi, row in enumerate(fi.blocks):
            n = len(row)
            for s in range(n):
                for e in range(s + mink, min(n, s + maxk) + 1):
                    if row[e - 1][0].op in NO_FRAG:
                        break
                    if frag_tokens(fi, bi, s, e) < min_tok:
                        continue
                    c = canon(fi, bi, s, e)
                    if c is None:
                        continue
                    key, lits, inputs, (ob, bro) = c
                    g = groups.get(key)
                    if g is None:
                        g = groups[key] = Cand(key)
                    tys = tuple(fi.types.get(v, "?") for v in inputs)
                    # chỗ gọi phải đổi kết quả bv64 về bool (cmp ne) nếu kết quả bool không chỉ dùng cho br
                    g.occ.append((fx, bi, s, e, lits, inputs, ob, 0 if (not ob or bro) else 6, tys))
    cands = []
    for g in groups.values():
        if len(g.occ) >= 2:
            g.finish(infos)
            cands.append(g)
    return cands


def existing_prims(infos):
    """Hàm một khối kết thúc bằng `ret v`: thân của nó có cùng khóa với đoạn nào -> primitive đã có sẵn trong kho."""
    out = {}
    for fi in infos:
        if len(fi.blocks) != 1 or not fi.blocks[0]:
            continue
        row = fi.blocks[0]
        if row[-1][0].op != "ret" or len(row) < 2:
            continue
        c = canon(fi, 0, 0, len(row) - 1)
        if c:
            out.setdefault(c[0], []).append(fi.fn.name)
    return out


def greedy(cands, top):
    covered, lib = set(), []
    heap = [(-c.gain()[0], id(c), c) for c in cands]
    heapq.heapify(heap)
    while heap and len(lib) < top:
        ng, _, c = heapq.heappop(heap)
        g, res = c.gain(covered)
        if g <= 0:
            continue
        if heap and g < -heap[0][0]:  # lợi đã giảm: đưa lại vào hàng đợi (lazy greedy)
            heapq.heappush(heap, (-g, id(c), c))
            continue
        _, cells = c.pick(covered)
        covered |= cells
        lib.append((c, g, res))
    return lib


def fn_clones(infos):
    groups = collections.defaultdict(list)
    for fx, fi in enumerate(infos):
        fn = fi.fn
        names, lits = {}, []
        for p, _ in fn.params:
            names[p] = f"p{len(names)}"
        labels = {b.label: f"@b{k}" for k, b in enumerate(fn.blocks)}

        def nm(t):
            if t.startswith("%"):
                return names.setdefault(t, f"v{len(names)}")
            if t.startswith("@"):
                return labels.get(t, t)
            return ty(t)

        def ty(t):  # tên trong kiểu (ptr<Byte,%n>) đổi tên; cỡ số của ptr thành lỗ
            t = L.VAL_RE.sub(lambda m: names.setdefault(m.group(0), f"v{len(names)}"), t)
            m = re.match(r"(ptr<[A-Za-z0-9_]+,)(\d+)>$", t)
            if m:
                lits.append(m.group(2))
                return m.group(1) + "?>"
            return t

        sig = [ty(fn.ret)] + [ty(t) for _, t in fn.params]
        body = []
        for c in fn.contracts:
            body.append(" ".join(nm(t) for t in c))
        for bi, b in enumerate(fn.blocks):
            for p, t in b.params:
                nm(p)
            body.append(labels[b.label] + " " + " ".join(nm(p) + ":" + ty(t) for p, t in b.params))
            for a in b.annots:
                body.append(" ".join(nm(t) for t in a))
            for i, args in fi.blocks[bi]:
                ca = []
                for j, a in enumerate(args):
                    if not a.startswith(("%", "@")) and holeable(i.op, j):
                        ca.append("?")
                        lits.append(a)
                    else:
                        ca.append(nm(a))
                d = (nm(i.dst) + " = ") if i.dst else ""
                body.append(d + i.op + " " + " ".join(ca))
        groups[(tuple(sig), tuple(body))].append((fx, tuple(lits)))
    out = []
    for k, occ in groups.items():
        if len(occ) < 2:
            continue
        lits = [l for _, l in occ]
        holes = [j for j in range(len(lits[0])) if len({l[j] for l in lits}) > 1]
        t = L.func_tokens(infos[occ[0][0]].fn)
        wrapper = 3 + len(infos[occ[0][0]].fn.params) + 1 + 4 + len(infos[occ[0][0]].fn.params) + len(holes) + 2
        gain = len(occ) * (t - wrapper) - (t + len(holes))
        out.append((gain, [infos[f].fn for f, _ in occ], holes, t))
    out.sort(key=lambda x: -x[0])
    return out


def show_frag(c, infos):
    o = c.occ[0]
    fi = infos[o[0]]
    holes = {j: f"h{n}" for n, j in enumerate(c.holes)}
    hk, lines = 0, []
    for line in c.key[:-1]:
        parts = []
        for t in line.split(" "):
            if t == "?":
                parts.append(holes.get(hk, o[4][hk]))
                hk += 1
            else:
                parts.append(t)
        lines.append(" ".join(parts))
    tys = [{o2[8][j] for o2 in c.occ} for j in range(c.ninputs)]
    ins = ", ".join(f"i{j}:{'|'.join(sorted(t))}" for j, t in enumerate(tys))
    return lines, ins


def rel(p):
    return os.path.relpath(p)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default="lit_program")
    ap.add_argument("--top", type=int, default=25)
    ap.add_argument("--mink", type=int, default=2)
    ap.add_argument("--maxk", type=int, default=16)
    ap.add_argument("--min-tok", type=int, default=8)
    ap.add_argument("--maxb", type=int, default=6, help="số khối tối đa của một vùng")
    ap.add_argument("--out", default="target/stitch")
    a = ap.parse_args()

    files, funcs = L.corpus(a.root)
    sigs = {f.name: f.ret for f in funcs}
    infos = [FnInfo(f, sigs) for f in funcs]
    total = sum(L.func_tokens(f) for f in funcs)
    per_dir = collections.Counter()
    for f in funcs:
        per_dir[os.path.dirname(rel(f.file))] += L.func_tokens(f)

    infos_g.extend(infos)
    cands = mine_frags(infos, a.mink, a.maxk, a.min_tok)
    regs = mine_regions(infos, a.maxb)
    lib = greedy(cands + regs, a.top)
    have = existing_prims(infos)
    clones = fn_clones(infos)
    saved = sum(g for _, g, _ in lib)

    os.makedirs(a.out, exist_ok=True)
    R = []
    R.append("# Light-Stitch: báo cáo giai đoạn 0 + 1\n")
    R.append(f"Kho mã `{a.root}`: {len(files)} file, {len(funcs)} hàm, "
             f"{sum(1 for f in funcs for _ in f.insts())} lệnh, **MDL = {total} token**.\n")
    R.append("| Thư mục | Token |\n|---|---|")
    for d, n in sorted(per_dir.items(), key=lambda x: -x[1]):
        R.append(f"| `{d}` | {n} |")
    cat = collections.Counter()
    for c, g, res in lib:
        nf = len({(infos[o[0]].fn.file, infos[o[0]].fn.name) for o in res})
        cat["có hàm cùng dạng" if c.key in have else ("trong 1 hàm" if nf == 1 else "nhiều hàm")] += g
    R.append(f"\nỨng viên đoạn lệnh (xuất hiện >= 2 lần, {a.mink}..{a.maxk} lệnh, >= {a.min_tok} token): {len(cands)}. "
             f"Thư viện tham lam {len(lib)} primitive: MDL giảm ước tính **{saved} token "
             f"({100 * saved / total:.1f}%)**. Đây là CẬN TRÊN: chưa tính hợp đồng @req/@ens của primitive, chưa thử viết lại "
             f"và kiểm chứng. Chia theo loại:\n")
    R.append(f"- nhiều hàm dùng chung (con số thật nhất): {cat['nhiều hàm']} token")
    R.append(f"- cùng dạng với hàm có sẵn (dùng lại, không tốn định nghĩa mới): {cat['có hàm cùng dạng']} token")
    R.append(f"- chỉ trong 1 hàm (thường nên viết lại thành vòng lặp, không phải primitive): {cat['trong 1 hàm']} token")
    R.append(f"- hàm gần-trùng (mục cuối, tính riêng, không cộng ở trên): {sum(max(0, c[0]) for c in clones)} token\n")
    J = {"mdl": total, "files": len(files), "funcs": len(funcs), "lib_saved": saved, "lib": [], "clones": []}
    for r, (c, g, res) in enumerate(lib, 1):
        body, ins = show_frag(c, infos)
        fns = {(infos[o[0]].fn.file, infos[o[0]].fn.name) for o in res}
        fls = sorted({rel(infos[o[0]].fn.file) for o in res})
        flags = []
        if len(fns) == 1:
            flags.append("chỉ trong 1 hàm (nên là vòng lặp?)")
        if c.out_bool:
            flags.append("đầu ra bool (ret 1/0)")
        if c.nlen:
            flags.append(f"+{c.nlen} tham số độ dài con trỏ")
        if c.key in have:
            flags.append("cùng dạng với hàm có sẵn: " + ", ".join(have[c.key]))
        R.append(f"## #{r} [{'vùng' if c.kind == 'region' else 'đoạn'}]: lợi {g} token — {len(res)} lần, {len(fns)} hàm, {len(fls)} file"
                 + (f" — ⚠ {'; '.join(flags)}" if flags else ""))
        R.append(f"tham số: {c.ninputs} đầu vào ({ins}) + {len(c.holes)} lỗ + {c.nlen} độ dài; "
                 f"đầu ra: {c.key[-1][2:]}; cỡ {c.size} token, lời gọi {c.call_cost()}\n")
        R.append("```\n" + "\n".join(body) + "\n```")
        R.append("chỗ dùng: " + ", ".join(f"`{c.site(infos, o)}` ({infos[o[0]].fn.name})" for o in res[:6])
                 + (f" … +{len(res) - 6}" if len(res) > 6 else "") + "\n")
        J["lib"].append({"rank": r, "kind": c.kind, "gain": g, "uses": len(res), "funcs": sorted(n for _, n in fns), "files": fls, "body": body,
                         "inputs": ins, "holes": len(c.holes), "flags": flags,
                         "sites": [c.site(infos, o) for o in res]})
    R.append("# Hàm gần-trùng (cả hàm giống nhau sau khi đổi tên và khoét hằng)\n")
    for g, fs, holes, t in clones[:15]:
        R.append(f"- lợi ~{g} token: {len(fs)} hàm × {t} token, {len(holes)} lỗ: "
                 + ", ".join(f"`{f.name}` ({rel(f.file)}:{f.line})" for f in fs[:6]) + (" …" if len(fs) > 6 else ""))
        J["clones"].append({"gain": g, "funcs": [f.name for f in fs], "holes": len(holes), "tokens": t})
    with open(os.path.join(a.out, "report.md"), "w", encoding="utf-8") as f:
        f.write("\n".join(R) + "\n")
    with open(os.path.join(a.out, "candidates.json"), "w", encoding="utf-8") as f:
        json.dump(J, f, ensure_ascii=False, indent=1)
    print(f"MDL {total} token; {len(cands)} ứng viên đoạn + {len(regs)} vùng; thư viện {len(lib)} primitive tiết kiệm {saved} "
          f"({100 * saved / total:.1f}%); {len(clones)} nhóm hàm gần-trùng -> {a.out}/report.md")


if __name__ == "__main__":
    main()
