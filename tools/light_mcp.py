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
No third-party dependencies. Only JSON-RPC goes to stdout in server mode; logs go to stderr.
"""
import json
import os
import re
import socket
import sys
import time

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SOCK = os.environ.get("LIGHT_SERIAL", os.path.join(REPO, "target", "light_serial.sock"))
PROTOCOL = "2025-06-18"
MAX_LINE = 1000  # AG_RX is 1024 bytes including "<id> "


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


TOOLS = [{
    "name": "run",
    "description": (
        "Run one shell command inside Light OS (running in QEMU) and return its exit code, stdout and stderr. "
        "The shell session (current directory) persists between calls. Commands are ASCII, one line. "
        "Available now: help, echo TEXT, pwd, ls [PATH], cd [PATH], stat PATH. Run `help` for the current list. "
        "Exit codes: 0 ok, 1 error, 2 usage, 127 unknown command. stdout is capped at 8192 bytes."),
    "inputSchema": {
        "type": "object",
        "properties": {
            "command": {"type": "string", "description": "the command line, e.g. \"ls /apps\""},
            "timeout_s": {"type": "number", "description": "seconds to wait for the reply (default 10)"},
        },
        "required": ["command"],
    },
}]


def call_tool(ch, name, args):
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
