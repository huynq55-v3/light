# 🌟 Light (.lit) Programming Language

[![Formal Verification](https://img.shields.io/badge/Formal%20Verification-Z3%20SMT-blue.svg)]()
[![Implementation](https://img.shields.io/badge/Implementation-Rust-orange.svg)]()
[![Architecture](https://img.shields.io/badge/Architecture-Flat%20SSA%20%2F%20TAC-purple.svg)]()

**Light** is an experimental, line-oriented systems programming language featuring **formal verification with the Z3 SMT Solver**, **zero C runtime dependencies** (direct Linux x86_64 syscalls), and a **compiler/toolchain implemented in Rust**.

---

## 💡 Overview

### 1. 📐 Flat SSA Architecture (Three-Address Code)
Traditional languages with nested AST expressions (`res = (a + b) * (c - d) / 2`), complex operator precedence, and nested blocks can complicate static analysis and code generation.  
Light uses a **linear Three-Address Code (Flat SSA)** representation:
- **Exactly one atomic instruction per line.**
- **No parentheses `()`, no curly braces `{ }`, no semicolons `;`.**
- Clear, sequential semantics that make parsing, intermediate verification, and machine code generation straightforward.

### 2. 🛡️ Formal Verification with Z3 SMT Solver
Light integrates a verification condition generator (VCGen) modeled after Boogie-style Intermediate Verification Languages (IVL):
- **Contracts (`REQUIRE` & `ENSURE`):** Express function preconditions and postconditions.
- **Inductive Loops (`INVARIANT` & `DECREASES`):** Verify loop correctness via mathematical induction (Base Case + Inductive Step) and ensure termination via ranking functions.
- **Safety Checks:** Automatically verifies absence of division-by-zero, arithmetic overflow (`i64::MIN / -1`), buffer out-of-bounds, and undefined variable uses at verification time.

### 3. ⚡️ Direct Linux x86_64 Code Generation
- Generates standalone Linux x86_64 ELF executables directly without requiring `libc` or external linkers.
- Provides low-level Linux syscall support (`sys_read`, `sys_write`, `sys_open`, `sys_close`, `sys_exit`).
- Executes programs natively via AOT compile-and-run sandbox (similar to `go run`).

---

## 🚀 Quick Start

### Prerequisites
- Linux x86_64
- Rust & Cargo (1.70+)
- Z3 SMT Solver (`z3` CLI installed and available in `$PATH`)

### 1. Run a Program Natively
```bash
cargo run -- run examples/08_slice_safe.lit
```

### 2. Formally Verify Contracts with Z3
```bash
# Verify mathematical contracts and safety properties
cargo run -- verify examples/08_slice_safe.lit
```

### 3. Build a Standalone Executable
```bash
# Compiles to a standalone Linux ELF64 binary with zero libc dependency
cargo run -- build examples/01_hello.lit -o hello
./hello
```

---

## 📝 Syntax at a Glance

### Hello World (Linux Syscall)
```light
FUNC main() -> i64
  # Allocate 32 bytes on stack/BSS
  %msg = ALLOC slice<u8> 32
  STORE_STR %msg 0 "Hello from Light Lang!\n"
  %len = SLICE_LEN %msg
  %ptr = SLICE_PTR %msg

  # Direct Linux sys_write(stdout=1, buf=%ptr, count=%len)
  %rax = CONST i64 1
  %rdi = CONST i64 1
  %rsi = MOV %ptr
  %rdx = MOV %len
  SYSCALL

  # Exit process with code 0
  %zero = CONST i64 0
  RET %zero
END_FUNC
```

### Formally Verified Function with Loop
```light
FUNC sum_to_n(n: i64) -> i64
  REQUIRE n >= 0 && n <= 1000

  %i = CONST i64 0
  %acc = CONST i64 0

  LOOP sum_loop
    INVARIANT %i >= 0 && %i <= n
    INVARIANT %acc >= 0
    DECREASES n - %i

    %done = GTE i64 %i n
    BREAK_IF %done

    %next_i = ADD i64 %i 1
    %acc = ADD i64 %acc %next_i

    # Rebind loop state for next iteration
    %i = MOV %next_i
  END_LOOP sum_loop

  ENSURE %acc >= 0
  RET %acc
END_FUNC
```

---

## 📂 Project Structure

```text
├── src/                   # Compiler & Verification Toolchain (Rust)
│   ├── ast.rs             # Flat SSA AST & instruction definitions
│   ├── parser.rs          # Linear TAC parser
│   ├── ivl.rs             # Boogie-style Intermediate Verification Language (IVL)
│   ├── vcgen.rs           # SMT-LIB2 Verification Condition Generator (QF_ABV)
│   ├── verifier.rs        # Verification pipeline & Hoare logic engine
│   ├── codegen.rs         # Direct x86_64 Machine Code Emitter & ELF64 Packager
│   └── main.rs            # CLI Entrypoint (run, verify, build)
├── stdlib/                # Standard Library routines (.lit)
│   ├── io.lit             # I/O and printing helpers
│   ├── string.lit         # String manipulation
│   └── fs.lit             # Basic file operations
├── tests/                 # Test suites & formal verification regression tests
├── examples/              # Example Light programs
├── LIGHT_AI_SPEC.md       # AI & LLM Specification Guide
└── README.md              # Project documentation
```

---

## 📜 License
Apache-2.0 / MIT
