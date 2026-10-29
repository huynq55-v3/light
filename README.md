# 🌟 Light (.lit) Programming Language

[![Self-Hosting](https://img.shields.io/badge/Self--Hosting-100%25%20Fixed--Point%20Proven-brightgreen.svg)]()
[![Verification](https://img.shields.io/badge/Formal%20Verification-Z3%20SMT%20Solver-blue.svg)]()
[![Runtime](https://img.shields.io/badge/C%20Dependency-Zero%20(Raw%20Linux%20Syscall)-orange.svg)]()
[![Architecture](https://img.shields.io/badge/Architecture-Flat%20SSA%20%2F%20TAC-purple.svg)]()

**Light** is an AI-native, line-oriented systems programming language featuring **formal mathematical verification with the Z3 SMT Solver**, **zero C runtime dependencies** (direct Linux x86_64 syscalls), and a **fully self-hosting native compiler (`lightc`)** that has reached a byte-for-byte fixed point!

---

## 💎 Why Light?

### 1. 🤖 AI-Native Architecture (Flat SSA)
Traditional languages with nested ASTs (`res = (a + b) * (c - d) / 2`), operator precedence rules, and indentation traps confuse LLMs.  
Light uses **Flat SSA (Three-Address Code)**:
- **Exactly one atomic instruction per line.**
- **No parentheses `()`, no curly braces `{ }`, no semicolons `;`.**
- Perfectly matches the token-by-token sequential thinking of generative AI. An LLM learns the complete specification in under 400 tokens with zero hallucinated syntax.

### 2. 🛡️ 100% Formal Mathematical Verification (Z3 SMT Solver)
Light bridges programming and formal logic:
- **`REQUIRE` & `ENSURE`:** Mathematically prove function contracts.
- **`INVARIANT`:** Bypasses the Halting Problem by proving loop bounds via 2-step mathematical induction (Base Case + Inductive Step).
- **Proactive Safety:** Division by zero, memory out-of-bounds, and call-site contract violations are detected and rejected *at compile time*. If a program compiles, it is mathematically proven not to crash.

### 3. ⚡️ Zero C Dependency (True Bare-Metal ELF64)
- No `libc`, no `musl`, no external C runtime, and no external linkers (`ld`/`lld`).
- Emits raw Linux x86_64 ELF executables from scratch (tiny binaries: 300 bytes to 70 KB).
- Interacts with the Linux kernel directly via raw machine-code `SYSCALL` instructions.

### 4. 🏆 Native Self-Hosting Achieved (Fixed-Point Proven)
The native Light compiler (`bootstrap/compiler.lit`), written entirely in Light without libc:
1. Stage 1 (`lightc`) compiles `bootstrap/compiler.lit` into a standalone native binary `lightc_v2`.
2. `lightc_v2` compiles `bootstrap/compiler.lit` into Stage 3.
3. **Fixed-Point Proof:** `sha256sum lightc_v2` is **100% byte-for-byte identical** to Stage 3 (`cmp` returns 0)!

---

## 🚀 Quick Start

### Prerequisites
- Linux x86_64
- Rust & Cargo (only for the initial bootstrap VM / verifier toolchain)
- Z3 SMT Solver (`libz3-dev` or dynamic library)

### 1. Run a Program via Safe VM
```bash
cargo run -- run tests/test_clean_syntax.lit
```

### 2. Formally Verify Contracts with Z3
```bash
cargo run -- verify examples/08_slice_safe.lit
cargo run -- verify bootstrap/compiler.lit
```

### 3. Build a Standalone Bare-Metal Executable
```bash
# Compiles to a standalone Linux ELF64 binary with zero dependencies
cargo run -- build tests/test_clean_syntax.lit -o app_bin
./app_bin
echo "Exit code: $?"
```

### 4. Stage 1: Build the Native Compiler (`lightc`)
Use the initial Rust bootstrap toolchain to build the native Light compiler executable:
```bash
# Compile bootstrap/compiler.lit into native x86_64 ELF binary
cargo run -- build bootstrap/compiler.lit -o lightc
```

### 5. Stage 2: Compiling with Native `lightc_v2` (100% Self-Hosted)
`lightc_v2` is a **pure standalone 74 KB native ELF64 executable** generated directly by Light, without `libc`, without Rust, and without external linkers.

#### A. Generate `lightc_v2` & Test Binaries via `lightc`
```bash
# Execute Stage 1 compiler
./lightc
```
This automatically compiles:
- All test programs in `tests/*.lit` &rarr; `syscall.bin`, `calc.bin`, `advanced.bin`, etc.
- The compiler source code `bootstrap/compiler.lit` &rarr; `lightc_v2` (Stage 2 binary).

#### B. Compile and Self-Host Directly with `lightc_v2`
From this point forward, you no longer need Rust or Cargo! You can compile programs and self-host entirely with `lightc_v2`:
```bash
# Execute Stage 2 native compiler
./lightc_v2
```
Output:
```text
🚀 Light Self-Hosting Compiler v0.1 starting compilation...
🎉 Successfully compiled test suite (syscall, calc, mem, mem64, func, args, branch, multi, vars)!
🚀 Self-Hosting Stage 2 Complete! Generated lightc_v2 via Light itself!
```

#### C. Run the Compiled Native Binaries
All executables produced by `lightc_v2` are pure bare-metal Linux binaries:
```bash
# Run calculation test
./calc.bin
echo "Exit code: $?" # Output: 42

# Run raw Linux syscall test
./syscall.bin
# Output: Hello from raw Linux x86_64 syscall!
```

#### D. Verify Fixed-Point Convergence (Reproducible Builds)
You can mathematically prove that the compiler has converged and reached an identical fixed-point:
```bash
# 1. Save Stage 2 binary
cp lightc_v2 lightc_stage2

# 2. Recompile using Stage 2 to produce Stage 3 (overwrites lightc_v2)
./lightc_stage2

# 3. Prove byte-for-byte bit identity
cmp lightc_stage2 lightc_v2
echo "Exit code: $?" # 0 (Files are 100% identical!)

sha256sum lightc_stage2 lightc_v2
```
Both files yield the exact same SHA-256 hash (`e1ea150bb84d17c9e1011844c9ab24d5aed8dc7939ea063010662d57b21088fa`), proving bit-for-bit mathematical deterministic self-hosting!

---

## 📝 Syntax at a Glance

```light
# Bare-metal Hello World in Light
FUNC main() -> i64
  # Allocate 32 bytes on stack/BSS
  %msg = ALLOC 32
  STORE_STR %msg "Hello, AI-Native Systems!\n"
  %len = SLICE_LEN %msg
  %ptr = SLICE_PTR %msg

  # Direct Linux sys_write(stdout=1, buf, len)
  %rax = CONST 1
  %rdi = CONST 1
  %rsi = MOV %ptr
  %rdx = MOV %len
  SYSCALL %rax %rdi %rsi %rdx

  # Exit process with code 0
  %zero = CONST 0
  RET %zero
END_FUNC
```

```light
# Formally verified mathematical loop
FUNC sum_to_n(n: i64) -> i64
  REQUIRE n >= 0 && n <= 10000

  %i = CONST 0
  %sum = CONST 0

  LOOP count_loop
    INVARIANT %i >= 0 && %i <= n
    INVARIANT %sum >= 0

    %done = GTE %i n
    BREAK_IF %done

    %next_i = ADD %i 1
    %sum = ADD %sum %next_i
    %i = MOV %next_i
  END_LOOP count_loop

  ENSURE %sum >= 0
  RET %sum
END_FUNC
```

---

## 📂 Project Structure

```text
├── bootstrap/
│   └── compiler.lit       # 100% Native Self-Hosting Compiler written in Light
├── src/                   # Bootstrap Compiler & Toolchain (Rust)
│   ├── ast.rs             # Flat SSA AST definition
│   ├── parser.rs          # Linear TAC / SSA parser
│   ├── verifier.rs        # Z3 SMT Mathematical Contract Verifier
│   ├── vm.rs              # Safe reference Virtual Machine
│   ├── jit.rs             # Bare-metal x86_64 Machine Code Emitter & ELF64 Packager
│   └── main.rs            # CLI Entrypoint (run, verify, build)
├── stdlib/                # Formally Verified Standard Library
│   ├── io.lit             # Formally verified I/O & printing
│   ├── string.lit         # Verified string manipulation & parsing
│   └── fs.lit             # Verified file system operations (open, read, write, close)
├── tests/                 # Unit & regression test suite
├── examples/              # Educational & verification bug demo programs
├── LIGHT_AI_SPEC.md       # Complete AI / LLM Context Specification
└── README.md              # Project documentation
```

---

## 📖 AI Specification
For detailed prompt templates and BNF instruction grammar designed for AI code generation, refer to [LIGHT_AI_SPEC.md](LIGHT_AI_SPEC.md).

---

## 📜 License
Apache-2.0 / MIT
