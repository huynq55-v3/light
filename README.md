# 🌟 Light (.lit) Programming Language

**Light** là một ngôn ngữ lập trình dòng phẳng (Flat SSA), Turing-complete, được thiết kế tối ưu riêng cho **AI Agents** kết hợp kiểm chứng toán học hình thức bằng **Z3 SMT Solver** và không phụ thuộc vào C Runtime (gọi trực tiếp Linux Syscalls).

---

## 💎 Điểm Cốt Lõi

1. **AI-Native Grammar:** Mỗi dòng là một lệnh độc lập. Không ngoặc lồng `{ }`, không thụt đầu dòng, không ưu tiên toán tử rắc rối. AI chỉ cần đọc đặc tả 1 lần là viết code chuẩn 100%.
2. **First-Class Z3 Verification:** Tích hợp sẵn 4 mệnh đề kiểm chứng toán học:
   - `REQUIRE`: Ràng buộc điều kiện đầu vào (Precondition).
   - `ENSURE`: Cam kết tính đúng đắn của kết quả đầu ra (Postcondition).
   - `INVARIANT`: Bất biến vòng lặp (Loop Invariant) giúp cắt đứt Định lý Rice để quy nạp toán học.
   - `ASSERT`: Kiểm tra tính chất trạng thái tại chỗ.
   - **Tự động bắt lỗi ngầm:** Bắt trọn lỗi chia cho 0 (Division by zero) và tràn mảng (Bounds check).
3. **Zero C Dependency:** Giao tiếp trực tiếp với Linux Kernel qua raw syscalls (x86_64: `sys_write`=1, `sys_exit`=60).
4. **Đầy đủ 6 kiểu dữ liệu:** `i64`, `u64`, `f64`, `bool`, `ptr`, `arr<T, N>` và `slice<T>`.

---

## 🚀 Cách Sử Dụng

```bash
# 1. Chạy demo có sẵn
cargo run -- demo

# 2. Kiểm chứng toán học và chạy file .lit
cargo run -- run examples/01_hello.lit

# 3. Chỉ kiểm chứng toán học (Z3 Verification)
cargo run -- verify examples/02_verify_safe.lit
cargo run -- verify examples/03_verify_bug.lit
```
