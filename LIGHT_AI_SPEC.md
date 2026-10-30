# 🌟 LIGHT PROGRAMMING LANGUAGE SPECIFICATION (.lit)
## An Experimental, Formally Verified Flat SSA Systems Language

> **Target Audience:** AI Models (LLMs), Code Generators, and Systems Engineers.  
> **Design Principle:** One instruction per line. Flat Three-Address Code (TAC/SSA). Zero nested syntax. Contract verification with Z3 SMT Solver before code generation. Direct Linux x86_64 Syscalls.

---

## 1. CORE SYNTAX & FORMATTING RULES
1. **One instruction per line.** No semicolons `;`, no curly braces `{ }`, no mandatory indentation.
2. **Registers & Variables:** Always start with `%` (e.g., `%res`, `%i`, `%msg`, `%ptr`).
3. **Single Assignment & Rebinding:** Each temporary is assigned once. Inside loops, state is updated at the loop latch via `%var = MOV %next_var`.
4. **Comments:** Single-line comments start with `#`.
5. **Function Definitions:**
   ```light
   FUNC func_name(param1: type1, param2: type2) -> return_type
     # Instructions...
     RET %result
   END_FUNC
   ```

---

## 2. DATA TYPES
- `i64`: 64-bit signed integer (default register arithmetic type).
- `u64`: 64-bit unsigned integer.
- `u8`: 8-bit unsigned integer (byte operations).
- `bool`: `true` or `false`.
- `ptr`: 64-bit raw memory address.
- `slice<u8>`: Fat pointer slice with pointer and length.

---

## 3. THE 16 CANONICAL CORE INSTRUCTIONS

### I. Mathematical Verification (Z3 SMT Directives)
Placed at the top of functions or loop bodies. Verified by Z3 SMT solver at compile time:
- `REQUIRE <expr>`: Preconditions that caller arguments MUST satisfy.
- `ENSURE <expr>`: Postconditions guaranteed by the function on its return value.
- `INVARIANT <expr>`: Loop invariant maintained across every iteration (inductive loop invariant).
- `DECREASES <expr>`: Loop ranking function (expression strictly decreases towards 0, proving termination and avoiding infinite loops).
- `ASSERT <expr>`: Static assertion at a specific execution point.

*Supported expressions in contracts:* `+`, `-`, `*`, `/`, `%`, `==`, `!=`, `<`, `<=`, `>`, `>=`, `&&`, `||`, `!`, `^`, `<<`, `>>`, `len(%slice)`.

### II. Constants & Value Movement
- `%dest = CONST <type> <val>`: Load typed constant (`%x = CONST i64 42`, `%flag = CONST bool true`).
  > **Note for AI:** Always specify the type explicitly (`i64` or `bool`). The compiler requires explicit typing for deterministic assembly code generation.
- `%dest = MOV %src`: Copy value between registers/variables.

### III. Arithmetic & Logic Operations (Explicitly Typed Flat TAC)
Binary operations take exactly 2 operands. Specifying the type explicitly (`i64`, `u64`, `u8`, `bool`) is strongly recommended:
- `%dest = ADD <type> %a %b`: Addition
- `%dest = SUB <type> %a %b`: Subtraction
- `%dest = MUL <type> %a %b`: Multiplication
- `%dest = DIV <type> %a %b`: Integer division (signed for `i64` via `idiv`/`bvsdiv`, unsigned for `u64`/`u8` via `div`/`bvudiv`; automatically checked for division-by-zero and signed overflow `i64::MIN / -1`)
- `%dest = MOD <type> %a %b`: Modulo (signed for `i64` via `idiv`/`bvsrem`, unsigned for `u64`/`u8` via `div`/`bvurem`)
- `%dest = EQ <type> %a %b`: Equal (`bool` result)
- `%dest = NEQ <type> %a %b`: Not equal (`bool` result)
- `%dest = LT <type> %a %b`: Less than (signed for `i64` via `setl`/`bvslt`, unsigned for `u64`/`u8` via `setb`/`bvult`)
- `%dest = LTE <type> %a %b`: Less than or equal (signed for `i64` via `setle`/`bvsle`, unsigned for `u64`/`u8` via `setbe`/`bvule`)
- `%dest = GT <type> %a %b`: Greater than (signed for `i64` via `setg`/`bvsgt`, unsigned for `u64`/`u8` via `seta`/`bvugt`)
- `%dest = GTE <type> %a %b`: Greater than or equal (signed for `i64` via `setge`/`bvsge`, unsigned for `u64`/`u8` via `setae`/`bvuge`)
- `%dest = AND <type> %a %b`: Logical AND (`bool`) or Bitwise AND (`i64`/`u64`/`u8` / `BAND`)
- `%dest = OR <type> %a %b`: Logical OR (`bool`) or Bitwise OR (`i64`/`u64`/`u8` / `BOR`)
- `%dest = XOR <type> %a %b`: Bitwise XOR (`i64`/`u64`/`u8`) or Logical XOR (`bool`)
- `%dest = SHL <type> %a %b`: Shift Left (x86_64 masked at 63 bits)
- `%dest = SHR <type> %a %b`: Logical Shift Right (chèn 0)
- `%dest = SAR <type> %a %b`: Arithmetic Shift Right (bảo toàn dấu)
- `%dest = NOT <type> %a`: Logical NOT (`bool`) or Bitwise NOT (`i64` / `BITNOT`)

> **Note on Types:** Floating-point `f64` is intentionally unsupported in the current version and rejected at parse/compile time to ensure 100% sound mathematical verification within the QF_ABV bitvector theory.

### IV. Functions & Control Flow
- `%dest = CALL <func_name> <arg1> <arg2> ...`: Call function with positional space-separated arguments (System V AMD64 ABI; passing a `slice<T>` passes fat pointer: 2 ABI registers pointer + length).
- `RET [%val]`: Return value from function (in `FUNC main()`, terminates process with exit code; omitting `RET` in `main()` automatically emits `sys_exit(0)`).
- `RET_IF %cond [%val]`: Early conditional return `%val` if `%cond` is true.
- `LOOP <label>` ... `END_LOOP <label>`: Structured loop block.
- `BREAK_IF %cond`: Exit innermost loop when `%cond` is true.
- `CONTINUE_IF %cond`: Jump to next loop iteration when `%cond` is true.
- `LABEL <name>`: Branch target label.
- `JUMP <name>`: Unconditional forward jump.
- `BR_IF %cond <name>`: Conditional forward jump when `%cond` is true.

### V. Memory & Slices (Safe Zero-Overhead Memory)
- `%buf = ALLOC slice<u8> <size_in_bytes>` or `ALLOC %buf <size_in_bytes>`: Allocate contiguous buffer memory in data section.
- `STORE8 %buf/%ptr %offset %val`: Store 1 byte (0..255) at address `%buf + %offset`.
- `%dest = LOAD8 %buf/%ptr %offset`: Read 1 byte from address `%buf + %offset`.
- `STORE64 %buf/%ptr %offset %val`: Store 8 bytes (i64/u64) at address `%buf + %offset`. Must be 8-byte aligned (`%offset % 8 == 0`).
- `%dest = LOAD64 %buf/%ptr %offset`: Read 8 bytes (i64/u64) from address `%buf + %offset`. Must be 8-byte aligned (`%offset % 8 == 0`).
- **Memory Sort Soundness Rule:** To guarantee formal verification soundness in SMT QF_ABV array theory, 8-bit operations (`LOAD8`/`STORE8`) and 64-bit operations (`LOAD64`/`STORE64`) cannot be mixed on the same buffer.
- `STORE_STR %buf [<offset>] "string\n"`: Store string literal into `%buf` at runtime via `rep movsb` machine code.
- `%len = SLICE_LEN %buf`: Get length in bytes.
- `%ptr = SLICE_PTR %buf`: Extract raw 64-bit pointer.

### VI. Linux Bare-Metal Syscall (Zero libc)
- `%dest = SYSCALL %rax %rdi %rsi %rdx [%r10 [%r8 [%r9]]]`: Direct Linux x86_64 syscall.
  - `sys_read`: `%rax = 0`, `%rdi = fd`, `%rsi = buf_ptr`, `%rdx = count`
  - `sys_write`: `%rax = 1`, `%rdi = fd (1=stdout)`, `%rsi = buf_ptr`, `%rdx = count`
  - `sys_open`: `%rax = 2`, `%rdi = path_ptr`, `%rsi = flags`, `%rdx = mode`
  - `sys_close`: `%rax = 3`, `%rdi = fd`
  - `sys_mmap`: `%rax = 9`, `%rdi = addr`, `%rsi = len`, `%rdx = prot`, `%r10 = flags`, `%r8 = fd`, `%r9 = off`
  - `sys_munmap`: `%rax = 11`, `%rdi = addr`, `%rsi = len`
  - `sys_exit`: `%rax = 60`, `%rdi = exit_code`

---

## 4. CANONICAL CODE PATTERNS

### Pattern 1: Loop with State Mutation (Rebinding) & Termination Proof
```light
FUNC sum_to_n(n: i64) -> i64
  REQUIRE n >= 0 && n <= 1000

  %i = CONST i64 0
  %acc = CONST i64 0

  LOOP sum_loop
    INVARIANT %i >= 0 && %i <= n
    INVARIANT %acc >= 0
    DECREASES n - %i

    %done = GTE %i n
    BREAK_IF %done

    %next_i = ADD %i 1
    %acc = ADD %acc %next_i

    # Rebind loop state for next iteration
    %i = MOV %next_i
  END_LOOP sum_loop

  ENSURE %acc >= 0
  RET %acc
END_FUNC
```

### Pattern 2: Bare-Metal Console Print via Linux Syscall
```light
FUNC main() -> i64
  %msg = ALLOC slice<u8> 32
  STORE_STR %msg "Hello from Light Flat SSA!\n"
  %len = SLICE_LEN %msg
  %ptr = SLICE_PTR %msg

  # Linux sys_write(stdout=1, ptr, len)
  %rax = CONST i64 1
  %rdi = CONST i64 1
  %rsi = MOV %ptr
  %rdx = MOV %len
  SYSCALL

  # Return code 0 (exits via sys_exit 60)
  %zero = CONST i64 0
  RET %zero
END_FUNC
```

### Pattern 3: Array / Buffer Processing
```light
FUNC fill_buffer(buf: slice<u8>, count: i64) -> i64
  REQUIRE count >= 0 && count <= len(buf)

  %i = CONST i64 0
  %char_a = CONST i64 65   # ASCII 'A'

  LOOP fill_loop
    INVARIANT %i >= 0 && %i <= count
    DECREASES count - %i

    %done = GTE %i count
    BREAK_IF %done

    STORE8 buf %i %char_a

    %next_i = ADD %i 1
    %i = MOV %next_i
  END_LOOP fill_loop

  RET count
END_FUNC
```

---

## 5. ANTI-PATTERNS (WHAT NEVER TO DO)
❌ **NEVER** write nested expressions: `res = (a + b) * c`  
✔️ **ALWAYS** break into atomic TAC lines:
```light
%t1 = ADD %a %b
%res = MUL %t1 %c
```

❌ **NEVER** write C-style control structures: `if (x) { ... }` or `for (i=0; i<n; i++)`  
✔️ **ALWAYS** use `BR_IF` or `LOOP` / `BREAK_IF` / `END_LOOP`.

❌ **NEVER** omit `%` for variables or temporary registers.
