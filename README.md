# 🌟 Light (.lit) Programming Language

**Light** is an AI-native, line-oriented (Flat SSA / Three-Address Code) systems programming language featuring **formal mathematical verification with Z3 SMT Solver** and **zero C runtime dependencies** (direct Linux x86_64 syscalls).

---

## 💎 Core Highlights

1. **AI-Native Grammar:** Exactly one instruction per line. Zero braces `{ }`, zero mandatory indentations, zero ambiguous operator precedence. An LLM understands the complete specification in under 500 tokens.
2. **First-Class Z3 SMT Verification:**
   - `REQUIRE`: Function preconditions.
   - `ENSURE`: Function postconditions.
   - `INVARIANT`: Loop invariants (enabling 2-step mathematical induction to bypass the Halting Problem).
   - **Automatic Safety Checks:** Zero division and static memory bounds checks.
   - **Call-Site Interprocedural Verification:** Z3 verifies that arguments at `CALL` sites strictly satisfy callee contracts (preventing buffer over-reads).
   - **Precise UTF-8 Byte Counting:** Distinguishes between ASCII (1 byte) and multi-byte Unicode UTF-8 characters (e.g., Vietnamese diacritics).
3. **Zero C Dependency:** Emits minimal standalone Linux ELF64 binaries (~300 bytes) without libc or external linkers.
4. **Rich Type System:** `i64`, `u64`, `u8`, `f64`, `bool`, `ptr`, `arr<T, N>`, and `slice<T>` (Fat Pointers).
5. **Modular Imports:** Recursive, cycle-safe `IMPORT "path.lit"` module resolution.

---

## 🚀 Quick Start

### 1. Build and Run via Safe VM
```bash
cargo run -- run examples/08_slice_safe.lit
```

### 2. Verify Mathematical Contracts with Z3
```bash
cargo run -- verify examples/08_slice_safe.lit
```

### 3. Compile to Standalone Minimal ELF64 Executable
```bash
cargo run -- build examples/08_slice_safe.lit -o app_bin
./app_bin
```

---

## 📝 Syntax Overview

```light
IMPORT "stdlib/io.lit"

FUNC main() -> i64
  # Allocate an 18-byte slice for UTF-8 Vietnamese name
  %name = ALLOC slice<u8> 18
  STORE_STR %name "Nguyễn Quang Huy"

  # Print slice safely via verified stdlib function
  %len = CONST i64 18
  %res = CALL std_print_slice %name %len

  %exit_code = CONST i64 0
  RET %exit_code
END_FUNC
```

---

## 📜 License
Apache-2.0 / MIT
