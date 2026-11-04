# 🗺️ Lộ trình Phát triển Tiếp theo (Light & Light OS Roadmap)

Dự án đã hoàn thành **Giai đoạn 1 (Foundation)**: Xây dựng thành công trình biên dịch `light v2` (~650 dòng Rust) tích hợp Z3 BitVector Verifier và khởi chạy `Light OS` trên QEMU với Bộ cấp phát Heap, Bảng Task, Bộ lập lịch Sự kiện, Hộp thư Zero-Copy IPC, Driver Serial, Driver VGA, Thư viện Đồ họa 2D và Driver Bàn phím PS/2 tương tác thời gian thực.

Dưới đây là 5 giai đoạn phát triển tiếp theo:

---

## Giai đoạn 2: Lưu trữ Bền vững & Hệ thống Tệp Phẳng (Storage & Flat Object Store)
**Mục tiêu:** Cho phép `Light OS` đọc/ghi dữ liệu và nạp thêm các chương trình mới trực tiếp từ ổ đĩa cứng ảo của QEMU.
- [ ] **Driver Đĩa cứng ATA PIO (`drivers/ata_disk.lit`):**
  - Sử dụng thẻ quyền năng `io<0x1f0, 0x1f7>` (tận dụng lệnh I/O 16-bit `in ax, dx` / `out dx, ax` tại cổng `0x1F0` đã được hỗ trợ sẵn trong `elf64.rs`).
  - Viết hàm đọc/ghi Sector 512-byte (`ptr<DiskWord, 256>`) có vòng lặp quy nạp `@inv ule %i 256` được Z3 chứng minh không tràn bộ đệm DMA.
- [ ] **Hệ thống Lưu trữ Khối Phẳng (`lib/kv_store.lit`):**
  - Thay vì cây thư mục POSIX phức tạp dành cho con người, thiết kế hệ thống lưu trữ dạng **Bảng Chỉ mục Cố định (Flat Tensor/Block Store)** nơi mỗi tệp/mô hình là một dải Sector liên tục có gắn mã định danh 64-bit và chữ ký kiểm chứng.

---

## Giai đoạn 3: Giao diện Tương tác & Shell dành cho Tác nhân (Interactive Shell & Command Parser)
**Mục tiêu:** Biến `apps/desktop_app.lit` thành một môi trường điều khiển hoàn chỉnh.
- [ ] **Hỗ trợ Phím chức năng trong `kbd_drv.lit` & `desktop_app.lit`:**
  - Xử lý phím `Backspace` (Scancode `14` — lùi con trỏ `cursor_x` và xóa ký tự trên màn hình VGA), phím `Enter` (Scancode `28` — xuống dòng và thực thi lệnh vừa gõ).
- [ ] **Bộ Thông dịch Lệnh Tối giản (`apps/shell_app.lit`):**
  - Lưu các ký tự gõ từ `IpcChannel` vào bộ đệm dòng lệnh `ptr<CmdBuf, 64>`.
  - Khi nhấn `Enter`, thực thi các lệnh kiểm tra trạng thái Kernel: xem dung lượng Heap đã dùng (`heap_used`), số lượng Task đang chạy (`task_count`), hoặc đọc/ghi thử nghiệm lên Sector ổ đĩa.

---

## Giai đoạn 4: Vòng lặp Tự Sửa lỗi cho AI (Counter-Example Guided AI Synthesis Loop)
**Mục tiêu:** Kết nối trực tiếp trình biên dịch `light` với một Mô hình Ngôn ngữ Lớn (LLM API hoặc Local LLM) để AI tự viết các mô-đun mới cho `Light OS`.
- [ ] **Chuẩn hóa Đầu ra Phản ví dụ JSON (`verify.rs`):**
  - Khi một hàm `.lit` do AI sinh ra bị trượt kiểm chứng Z3 (`SatResult::Sat`), đóng gói tên hàm, vị trí lệnh lỗi và bộ giá trị `Counter-example` của Z3 thành chuỗi JSON siêu gọn.
- [ ] **Pipeline Tự động Sửa lỗi (Guided Repair CLI):**
  - Tự động bắn ngược `Counter-example` lại cho AI trong vòng lặp suy luận. Thực nghiệm cho thấy với phản ví dụ cụ thể của Z3 (ví dụ: `r2 = 0` gây chia cho 0, hoặc `r1 = 2000` gây tràn `slice`), AI chỉ mất 1-2 lượt để bổ sung đúng `@req` / `@inv` và sinh ra mô-đun `.lit` đạt chuẩn 100%.

---

## Giai đoạn 5: Tối ưu hóa Mã máy & Tập lệnh Ma trận/Tensor cho AI (Performance & Tensor Primitives)
**Mục tiêu:** Nâng cấp tốc độ thực thi của mã máy `x86_64` do `elf64.rs` sinh ra để chạy các tác vụ tính toán nặng của AI.
- [ ] **Cấp phát Thanh ghi Đơn giản (Linear-Scan Register Allocation trong `elf64.rs`):**
  - Hiện tại các biến SSA `%0, %1...` đang lưu trên Stack (`[rbp - offset]`). Ánh xạ trực tiếp 8 biến SSA đầu tiên của mỗi hàm vào các thanh ghi phần cứng (`r12..r15`, `rbx`, `r8..r10`) để tăng tốc độ vòng lặp lên gấp 5-10 lần.
- [ ] **Thư viện Toán học Điểm cố định & Ma trận (`lib/tensor.lit`):**
  - Xây dựng các hàm nhân ma trận (GEMM), tích vô hướng (Dot Product) và hàm kích hoạt (ReLU / Integer Softmax) trên kiểu `bv64`/`bv32` dùng `slice` và vòng lặp quy nạp Z3, cho phép chạy trực tiếp một mạng nơ-ron nhỏ (như nhận diện chữ số hoặc TinyLLM) ngay bên trong `Light OS` ở chế độ Bare-metal!

---

## Giai đoạn 6: Nhúng Trình biên dịch `Light` vào trong `Light OS` (Self-Hosting / JIT Kernel)
**Mục tiêu tối thượng:** Đưa bộ kiểm chứng `verify.rs` và bộ sinh mã `elf64.rs` vào chạy ngay bên trong nhân hệ điều hành.
- [ ] Cho phép `Light OS` nhận mã nguồn `.lit` mới qua cổng Serial hoặc mạng, tự kiểm chứng Z3 và dịch ra mã máy nạp thẳng vào vùng Heap để chạy nóng (Hot-swappable Verified Modules) mà không cần khởi động lại máy ảo!
