#!/usr/bin/env python3
"""Cổng an toàn của Light-Stitch: mọi thay đổi mã Light (giai đoạn 2 trở đi) chỉ được nhận khi cổng này qua hết.

    python3 tools/stitch/gate.py            # đủ các bước
    python3 tools/stitch/gate.py --no-qemu  # bỏ bước golden (máy không có QEMU / KVM)

Các bước:
  1. `light` build đủ: kiểm chứng Z3 kernel + mọi App (ghi kernel.elf / disk.img như build thường)
  2. `cargo test --release`
  3. `light stack-report`
  4. golden kênh Agent: mỗi tools/stitch/golden/gN.txt chạy trên QEMU (đĩa mới chép từ disk.img), so với
     gN.expected.jsonl (bỏ trường thời gian `ms`). Dòng đặc biệt: `BIG PATH N`, `GEN PATH N`, `WF PATH HEX` ghi file
     qua write_file; dòng `#!` bị bỏ qua.
Chỉ kill tiến trình QEMU do chính cổng này khởi động (theo PID).
"""
import json
import os
import shutil
import subprocess
import sys
import time

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
GOLD = os.path.join(REPO, "tools", "stitch", "golden")
WORK = os.path.join(REPO, "target", "stitch", "gate")
sys.path.insert(0, os.path.join(REPO, "tools"))
import light_mcp as m  # noqa: E402


def step(name, cmd):
    t = time.monotonic()
    r = subprocess.run(cmd, cwd=REPO, capture_output=True, text=True)
    ok = r.returncode == 0
    print(f"[{'OK' if ok else 'FAIL'}] {name} ({time.monotonic() - t:.1f}s)")
    if not ok:
        print((r.stdout + r.stderr)[-3000:])
    return ok


def run_golden(cmdfile, disk, sock):
    if os.path.exists(sock):
        os.remove(sock)
    accel = ["-enable-kvm", "-cpu", "host"] if os.access("/dev/kvm", os.W_OK) else []
    proc = subprocess.Popen(["qemu-system-x86_64", *accel, "-m", "4G", "-smp", "4", "-kernel",
                             os.path.join(REPO, "kernel.elf"), "-drive", f"file={disk},format=raw,if=ide",
                             "-display", "none", "-serial", f"unix:{sock},server,nowait"],
                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    res = []
    try:
        for _ in range(50):
            if os.path.exists(sock):
                break
            time.sleep(0.1)
        ch = m.Channel(sock)
        ch.connect()
        deadline = time.monotonic() + 60  # chờ Kernel báo sẵn sàng (ag_init in "@@LREADY")
        while b"@@LREADY" not in ch.buf:
            left = deadline - time.monotonic()
            if left <= 0:
                raise TimeoutError("Light OS không báo @@LREADY trong 60s")
            ch.sock.settimeout(left)
            ch.buf += ch.sock.recv(65536)
        ch.buf = ch.buf.split(b"@@LREADY", 1)[1]
        for c in open(cmdfile).read().split("\n"):
            if not c or c.startswith("#!"):
                continue
            if c.startswith("BIG "):
                _, path, n = c.split(" ")
                line = "".join(chr(97 + i % 26) for i in range(79)) + "\n"
                r = m.write_file(ch, path, (line * (int(n) // 80 + 1))[:int(n)], 120)
            elif c.startswith("GEN "):
                _, path, n = c.split(" ")
                r = m.write_file(ch, path, "".join(f"{(i * 7919) % int(n)}\n" for i in range(int(n))), 120)
            elif c.startswith("WF "):
                _, path, hexs = c.split(" ", 2)
                r = m.write_file(ch, path, bytes.fromhex(hexs).decode("latin-1"), 60)
            else:
                r = ch.run(c, 60)
            res.append({"cmd": c[:120], **r})
    finally:
        proc.terminate()
        proc.wait(timeout=10)
    return res


def app_sizes_norm(r):
    """Cỡ file App đổi mỗi khi mã App / thư viện đổi: `size: N` của lệnh nhắc /apps/X.elf phải bằng cỡ file
    storage/apps/X.elf vừa build, rồi được thay bằng `size: <app>` trước khi so."""
    import re
    cmd = r.get("cmd", "")
    m = re.search(r"/apps/([A-Za-z0-9_]+\.elf)", cmd)
    if not m or "size: " not in r.get("stdout", ""):
        return r
    want = os.path.getsize(os.path.join(REPO, "storage", "apps", m.group(1)))
    out = re.sub(r"size: (\d+)", lambda x: "size: <app>" if int(x.group(1)) == want else x.group(0), r["stdout"])
    return {**r, "stdout": out}


def golden():
    os.makedirs(WORK, exist_ok=True)
    ok = True
    for name in sorted(f for f in os.listdir(GOLD) if f.endswith(".txt")):
        base = name[:-4]
        disk = os.path.join(WORK, base + ".img")
        shutil.copy(os.path.join(REPO, "disk.img"), disk)
        with open(disk, "r+b") as f:
            f.truncate(64 << 20)
        t = time.monotonic()
        got = run_golden(os.path.join(GOLD, name), disk, os.path.join(WORK, "a.sock"))
        want = [json.loads(l) for l in open(os.path.join(GOLD, base + ".expected.jsonl"))]
        got = [app_sizes_norm(r) for r in got]
        bad = [k for k, (g, w) in enumerate(zip(got, want)) if g != w]
        same = len(got) == len(want) and not bad
        print(f"[{'OK' if same else 'FAIL'}] golden {base} ({len(got)} lệnh, {time.monotonic() - t:.1f}s)")
        if not same:
            ok = False
            if len(got) != len(want):
                print(f"   số kết quả {len(got)} != {len(want)}")
            for k in bad[:3]:
                print(f"   lệnh {k}: {want[k]['cmd']!r}\n     muốn: {json.dumps(want[k])[:300]}\n     được: {json.dumps(got[k])[:300]}")
    return ok


def main():
    qemu = "--no-qemu" not in sys.argv
    ok = step("cargo build --release", ["cargo", "build", "--release", "--quiet"])
    ok = ok and step("light: kiểm chứng kernel + App", ["./target/release/light"])
    ok = ok and step("cargo test --release", ["cargo", "test", "--release", "--quiet"])
    ok = ok and step("light stack-report", ["./target/release/light", "stack-report"])
    if ok and qemu:
        ok = golden()
    print("CỔNG:", "QUA" if ok else "TRƯỢT")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
