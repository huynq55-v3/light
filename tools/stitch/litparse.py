"""Bộ phân tích .lit tối giản cho Light-Stitch (chỉ đọc): file -> hàm -> khối -> lệnh.

Chỉ cần đủ để đo và so khớp mẫu; nguồn chân lý về ngữ nghĩa vẫn là `light` (src/parser.rs + verifier).
Mỗi lệnh giữ dòng gốc (file, số dòng) để báo cáo chỉ đúng chỗ.
"""
import glob
import os
import re
from dataclasses import dataclass, field

ANNOT = ("@req", "@ens", "@inv", "@dec")
TERMINATORS = {"br", "jmp", "ret"}
VAL_RE = re.compile(r"%[A-Za-z0-9_]+")


@dataclass
class Inst:
    dst: str | None          # "%x" hoặc None
    op: str                  # "add", "call", "store", ...
    args: list[str]          # token còn lại (call: args[0] = tên hàm)
    file: str
    line: int

    def tokens(self):
        return ([self.dst, "="] if self.dst else []) + [self.op] + self.args

    def uses(self):
        return [a for a in self.args if a.startswith("%")]


@dataclass
class Block:
    label: str
    params: list[tuple[str, str]]   # (%tên, kiểu)
    annots: list[list[str]]         # token của @inv / @dec
    insts: list[Inst] = field(default_factory=list)
    line: int = 0


@dataclass
class Func:
    name: str
    ret: str
    params: list[tuple[str, str]]
    contracts: list[list[str]]      # @req / @ens
    blocks: list[Block]
    file: str
    line: int

    def insts(self):
        for b in self.blocks:
            yield from b.insts


def _strip(line):
    # Không có chuỗi trong thân hàm, nên cắt chú thích '#' là an toàn
    i = line.find("#")
    return (line if i < 0 else line[:i]).strip()


def _params(toks):
    out = []
    for t in toks:
        if ":" in t and t.startswith("%"):
            n, ty = t.split(":", 1)
            out.append((n, ty))
    return out


def parse_file(path):
    funcs, cur, blk = [], None, None
    with open(path, encoding="utf-8") as f:
        lines = f.readlines()
    depth_other = False  # đang trong data / layout { ... }
    for no, raw in enumerate(lines, 1):
        s = _strip(raw)
        if not s:
            continue
        if cur is None:
            if depth_other:
                if s.startswith("}"):
                    depth_other = False
                continue
            if s.startswith("func "):
                t = s.rstrip("{").split()
                cur = Func(t[1], t[2], _params(t[3:]), [], [], path, no)
                blk = None
            elif s.endswith("{") and (s.startswith("data ") or s.startswith("layout ")):
                depth_other = True
            continue
        if s.startswith("}"):
            funcs.append(cur)
            cur, blk = None, None
            continue
        t = s.split()
        if t[0] in ("@req", "@ens"):
            cur.contracts.append(t)
        elif t[0] in ("@inv", "@dec"):
            (blk.annots if blk else cur.contracts).append(t)
        elif t[0].startswith("@"):
            blk = Block(t[0], _params(t[1:]), [], [], no)
            cur.blocks.append(blk)
        else:
            if blk is None:  # lệnh trước nhãn đầu tiên (không gặp trong mã hiện tại)
                blk = Block("@entry", [], [], [], no)
                cur.blocks.append(blk)
            if len(t) >= 3 and t[1] == "=":
                blk.insts.append(Inst(t[0], t[2], t[3:], path, no))
            else:
                blk.insts.append(Inst(None, t[0], t[1:], path, no))
    return funcs


def corpus(root="lit_program"):
    """Mọi .lit dưới root (mỗi file một lần; include không nhân bản hàm)."""
    files = sorted(glob.glob(os.path.join(root, "**", "*.lit"), recursive=True))
    funcs = []
    for p in files:
        funcs.extend(parse_file(p))
    return files, funcs


def func_tokens(fn):
    """MDL của một hàm = số token: đầu hàm + hợp đồng + nhãn khối (kèm tham số, chú giải) + lệnh."""
    n = 3 + len(fn.params) + sum(len(c) for c in fn.contracts)
    for b in fn.blocks:
        n += 1 + len(b.params) + sum(len(a) for a in b.annots)
        n += sum(len(i.tokens()) for i in b.insts)
    return n
