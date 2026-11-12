#!/usr/bin/env python3
r"""MCP server (stdio) bridging Claude to the Light OS agent channel on QEMU's COM1.

Light OS side: lit_program/os/agent.lit. QEMU must expose COM1 as a unix socket:
    bash tools/qemu_run.sh --agent            (window)   or   --agent --headless
Socket path: $LIGHT_SERIAL (default: <repo>/target/light_serial.sock).

Protocol on the wire (ASCII lines):
    host -> OS : "<id> <command>\n"
    OS -> host : "@@LR|<id>|<exit>|<trunc>|<stdout>|<stderr>"  (fields escaped: \\ \n \t \xHH)
Everything else on the serial line (boot / diag output) is ignored.

Usage:
    python3 tools/light_mcp.py                 # MCP server on stdin/stdout (for Claude Code)
    python3 tools/light_mcp.py --run "ls /"    # one command, print the result (manual test)
    python3 tools/light_mcp.py --install terminal   # build + hot-install one app (see install_app)
No third-party dependencies. Only JSON-RPC goes to stdout in server mode; logs go to stderr.
"""
import json
import os
import re
import socket
import subprocess
import sys
import time

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SOCK = os.environ.get("LIGHT_SERIAL", os.path.join(REPO, "target", "light_serial.sock"))
PROTOCOL = "2025-06-18"
MAX_LINE = 131000  # AG_RX_CAP (os/agent.lit) is 131072 bytes including "<id> "


def log(*a):
    print("light_mcp:", *a, file=sys.stderr, flush=True)


def unescape(s):
    out, i = bytearray(), 0
    while i < len(s):
        c = s[i]
        if c == "\\" and i + 1 < len(s):
            n = s[i + 1]
            if n == "n":
                out += b"\n"; i += 2; continue
            if n == "t":
                out += b"\t"; i += 2; continue
            if n == "\\":
                out += b"\\"; i += 2; continue
            if n == "x" and i + 3 < len(s) and re.fullmatch(r"[0-9a-f]{2}", s[i + 2:i + 4]):
                out.append(int(s[i + 2:i + 4], 16)); i += 4; continue
        out += c.encode("latin-1", "replace"); i += 1
    return out.decode("utf-8", "replace")


class Channel:
    def __init__(self, path):
        self.path, self.sock, self.buf, self.next_id = path, None, b"", 1

    def connect(self):
        if self.sock:
            return
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        try:
            s.connect(self.path)
        except OSError as e:
            s.close()
            raise RuntimeError(f"cannot connect to Light OS serial socket {self.path}: {e}. "
                               "Start QEMU with: bash tools/qemu_run.sh --agent")
        self.sock, self.buf = s, b""

    def close(self):
        if self.sock:
            self.sock.close()
        self.sock = None

    def run(self, cmd, timeout):
        if "\n" in cmd or "\r" in cmd:
            raise ValueError("command must be a single line")
        data = cmd.encode("ascii", "strict") if cmd.isascii() else None
        if data is None:
            raise ValueError("command must be ASCII (Light OS shell is ASCII-only)")
        if len(data) > MAX_LINE:
            raise ValueError(f"command longer than {MAX_LINE} bytes")
        self.connect()
        rid = self.next_id
        self.next_id += 1
        try:
            self.sock.sendall(f"{rid} ".encode() + data + b"\n")
        except OSError:
            self.close()
            raise RuntimeError("serial socket closed (did QEMU exit?)")
        deadline = time.monotonic() + timeout
        prefix = f"@@LR|{rid}|".encode()
        while True:
            while b"\n" in self.buf:
                line, self.buf = self.buf.split(b"\n", 1)
                line = line.rstrip(b"\r")
                if line.startswith(prefix):
                    f = line.decode("ascii", "replace").split("|")
                    if len(f) != 6:
                        raise RuntimeError(f"malformed reply: {line[:200]!r}")
                    t = int(f[3])
                    return {"exit": int(f[2]), "stdout": unescape(f[4]), "stderr": unescape(f[5]),
                            "truncated": {"stdout": bool(t & 1), "stderr": bool(t & 2)}}
            left = deadline - time.monotonic()
            if left <= 0:
                raise TimeoutError(f"no reply within {timeout}s (Light OS still booting or hung?)")
            self.sock.settimeout(left)
            try:
                chunk = self.sock.recv(65536)
            except socket.timeout:
                continue
            if not chunk:
                self.close()
                raise RuntimeError("serial socket closed (did QEMU exit?)")
            self.buf += chunk


def escape_bytes(data):
    """Bytes -> tokens for the Light shell TEXT syntax (\\n \\t \\\\ \\xHH), safe inside single quotes."""
    out = []
    for b in data:
        if b == 0x27:
            out.append("\\x27")
        elif b == 0x5C:
            out.append("\\\\")
        elif b == 0x0A:
            out.append("\\n")
        elif b == 0x09:
            out.append("\\t")
        elif 0x20 <= b <= 0x7E:
            out.append(chr(b))
        else:
            out.append(f"\\x{b:02x}")
    return out


def check_path(path):
    if (not isinstance(path, str) or not path or not path.isascii() or "'" in path
            or any(ord(c) < 32 or ord(c) == 127 for c in path)):
        raise ValueError("path must be non-empty printable ASCII without single quotes")


def write_file(ch, path, content, timeout):
    return write_bytes(ch, path, content.encode("utf-8"), timeout)


def write_bytes(ch, path, data, timeout):
    check_path(path)
    tokens = escape_bytes(data)
    room = WRITE_CHUNK
    chunks, cur, size = [], [], 0
    for t in tokens:
        if size + len(t) > room:
            chunks.append("".join(cur)); cur, size = [], 0
        cur.append(t); size += len(t)
    chunks.append("".join(cur))
    for i, c in enumerate(chunks):
        r = ch.run(f"{'write' if i == 0 else 'append'} '{path}' '{c}'", timeout)
        if r["exit"] != 0:
            r["stderr"] += f"(failed at chunk {i + 1}/{len(chunks)})\n"
            return r
    return {"exit": 0, "stdout": f"wrote {len(data)} bytes to {path} in {len(chunks)} command(s)\n",
            "stderr": "", "truncated": {"stdout": False, "stderr": False}}


STAGE = "/install.tmp"  # file tạm trên đĩa Light OS cho install_app (xóa sau khi cài)


def install_app(ch, name, timeout):
    """Biên dịch + kiểm chứng lit_program/apps/NAME.lit trên host, gửi .elf qua kênh, cài nóng vào slot của App."""
    if not isinstance(name, str) or not re.fullmatch(r"[a-z0-9_]{1,40}", name):
        raise ValueError("'name' must be an app name like 'terminal' (lit_program/apps/<name>.lit)")
    src = os.path.join(REPO, "lit_program", "apps", name + ".lit")
    if not os.path.isfile(src):
        raise ValueError(f"no such app source: lit_program/apps/{name}.lit")
    out_dir = os.path.join(REPO, "target", "hot")
    os.makedirs(out_dir, exist_ok=True)
    out = os.path.join(out_dir, name + ".elf")
    try:
        b = subprocess.run(["cargo", "run", "--quiet", "--release", "--bin", "light", "--", "build-app", src, out],
                           cwd=REPO, capture_output=True, text=True, timeout=900)
    except subprocess.TimeoutExpired:
        raise RuntimeError("build timed out (900 s)")
    if b.returncode != 0:
        log_txt = (b.stdout + b.stderr)[-4000:]
        return {"exit": 1, "stdout": "", "stderr": f"build/verify failed:\n{log_txt}",
                "truncated": {"stdout": False, "stderr": False}}
    with open(out, "rb") as f:
        data = f.read()
    w = write_bytes(ch, STAGE, data, timeout)
    if w["exit"] != 0:
        ch.run(f"rm '{STAGE}'", timeout)
        return w
    r = ch.run(f"appinstall {STAGE} /apps/{name}.elf", max(timeout, 30))
    ch.run(f"rm '{STAGE}'", timeout)
    r["stdout"] = f"built {name}.elf ({len(data)} bytes, verified)\n" + r["stdout"]
    return r


WRITE_CHUNK = 120000  # escaped bytes per write/append command (<= MAX_LINE; each append re-reads and rewrites the file)

TOOLS = [{
    "name": "run",
    "description": (
        "Run one shell command inside Light OS (running in QEMU) and return its exit code, stdout and stderr. "
        "The shell session (current directory) persists between calls. Commands are ASCII, one line. "
        "Same shell as the Light OS Terminal app (run `help` for usage). Commands: help echo pwd cd ls stat cat write "
        "append mkdir touch rm grep wc head tail sort uniq find env unset true false; agent-only: appinstall SRC APP "
        "(prefer the install_app tool). "
        "Syntax: 'single' and \"double\" quotes, $VAR ${VAR} $? (exit code), NAME=value, pipes a | b, "
        "redirection > >> <, sequences a ; b, a && b, a || b. No globbing (find -name takes * ?), no subshells, "
        "no $(...), no 2>. A backslash only escapes shell special characters; other backslash sequences reach the "
        "command unchanged. TEXT of write/append and echo -e uses escapes \\n \\t \\\\ \\xHH (prefer the write_file "
        "tool for file content). grep matches a fixed string (^ and $ anchor it). Each command's output (pipes, "
        "> and >>) is limited to 128 KiB; a cut pipeline is never written to a file. "
        "Exit codes: 0 ok, 1 error, 2 usage/syntax, 127 unknown command. stdout is capped at 64 KiB, stderr at 1 KiB."),
    "inputSchema": {
        "type": "object",
        "properties": {
            "command": {"type": "string", "description": "the command line, e.g. \"ls /apps\""},
            "timeout_s": {"type": "number", "description": "seconds to wait for the reply (default 10)"},
        },
        "required": ["command"],
    },
}, {
    "name": "read_file",
    "description": "Read a file from the Light OS disk (LightFS) and return its content as text (UTF-8, invalid bytes "
                   "replaced). Same as `cat PATH`. Content over 64 KiB is truncated.",
    "inputSchema": {"type": "object", "properties": {"path": {"type": "string"}}, "required": ["path"]},
}, {
    "name": "write_file",
    "description": "Create or replace a file on the Light OS disk with the given text (UTF-8). The parent directory "
                   "must exist; app files under /apps are read-only. Maximum file size 1 MiB.",
    "inputSchema": {"type": "object", "properties": {"path": {"type": "string"}, "content": {"type": "string"}},
                    "required": ["path", "content"]},
}, {
    "name": "install_app",
    "description": "Hot-install an app: compile + Z3-verify lit_program/apps/<name>.lit on the host (`light build-app`), "
                   "send the binary to Light OS and replace /apps/<name>.elf in place (same Dock slot), then restart the "
                   "app (its window state is reset, like closing it with [X]) and bring its window to the foreground. "
                   "Only apps already loaded at boot can be replaced; new apps need a reboot. The change persists on the "
                   "QEMU working disk. Only for changes inside the app: edits to kernel code or shared ABI (lib/os_layout.lit, "
                   "IPC, LightFS API) need a full build + reboot, and std/shell.lit edits reach the Terminal but not the "
                   "kernel's agent shell. Note: app code runs directly in the kernel, so this tool gives the host the same "
                   "power as rebuilding disk.img.",
    "inputSchema": {"type": "object", "properties": {
        "name": {"type": "string", "description": "app name, e.g. \"terminal\""},
        "timeout_s": {"type": "number", "description": "seconds per Light OS command (default 10)"}},
        "required": ["name"]},
}]


def call_tool(ch, name, args):
    timeout = max(0.5, min(float(args.get("timeout_s", 10)), 120))
    if name == "read_file":
        check_path(args.get("path"))
        return ch.run(f"cat '{args['path']}'", timeout)
    if name == "write_file":
        content = args.get("content")
        if not isinstance(content, str):
            raise ValueError("'content' must be a string")
        return write_file(ch, args.get("path"), content, timeout)
    if name == "install_app":
        return install_app(ch, args.get("name"), timeout)
    if name != "run":
        raise ValueError(f"unknown tool: {name}")
    cmd = args.get("command")
    if not isinstance(cmd, str):
        raise ValueError("'command' must be a string")
    timeout = float(args.get("timeout_s", 10))
    return ch.run(cmd, max(0.5, min(timeout, 120)))


def serve():
    ch = Channel(SOCK)
    for raw in sys.stdin:
        raw = raw.strip()
        if not raw:
            continue
        try:
            msg = json.loads(raw)
        except json.JSONDecodeError:
            log("bad json", raw[:200])
            continue
        mid, method = msg.get("id"), msg.get("method")
        if mid is None:  # notification (e.g. notifications/initialized)
            continue
        try:
            if method == "initialize":
                ver = msg.get("params", {}).get("protocolVersion", PROTOCOL)
                result = {"protocolVersion": ver, "capabilities": {"tools": {}},
                          "serverInfo": {"name": "light-vm", "version": "0.1"}}
            elif method == "ping":
                result = {}
            elif method == "tools/list":
                result = {"tools": TOOLS}
            elif method == "tools/call":
                p = msg.get("params", {})
                try:
                    r = call_tool(ch, p.get("name"), p.get("arguments") or {})
                    result = {"content": [{"type": "text", "text": json.dumps(r, ensure_ascii=False)}],
                              "structuredContent": r, "isError": False}
                except Exception as e:  # tool-level error: report to the model, keep serving
                    result = {"content": [{"type": "text", "text": f"error: {e}"}], "isError": True}
            else:
                raise LookupError(method)
            reply = {"jsonrpc": "2.0", "id": mid, "result": result}
        except LookupError as e:
            reply = {"jsonrpc": "2.0", "id": mid, "error": {"code": -32601, "message": f"method not found: {e}"}}
        sys.stdout.write(json.dumps(reply) + "\n")
        sys.stdout.flush()


def main():
    if len(sys.argv) == 3 and sys.argv[1] == "--install":
        r = install_app(Channel(SOCK), sys.argv[2], 10)
        sys.stdout.write(r["stdout"])
        sys.stderr.write(r["stderr"])
        sys.exit(r["exit"])
    if len(sys.argv) >= 3 and sys.argv[1] == "--run":
        r = Channel(SOCK).run(" ".join(sys.argv[2:]), 10)
        sys.stdout.write(r["stdout"])
        sys.stderr.write(r["stderr"])
        if any(r["truncated"].values()):
            print(f"[truncated: {r['truncated']}]", file=sys.stderr)
        sys.exit(r["exit"])
    serve()


if __name__ == "__main__":
    main()
