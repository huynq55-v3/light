# 🗺️ Lộ trình Light & Light OS

Cập nhật: 2026-11-11 · nhánh `cleanup-verifier-step1`

Mục tiêu gần: **Light OS chạy trên máy thật** (HP Pavilion 15-eg0xxx: i7-1165G7, 32GB, UEFI, NVMe Samsung 980 sau
Intel VMD, Iris Xe 1920×1080), đọc/ghi được ổ NVMe, có hệ thống tệp riêng (LightFS). Sau đó mới tới tối ưu mã máy
và vòng lặp AI tự sửa lỗi.

---

## ✅ Đã xong

| Bước | Nội dung | Commit |
|---|---|---|
| 1 | Dọn code `.lit` chết (~2.2k dòng), parser chặt, bộ test hồi quy `cargo test` (`tests/lit/{must_fail,must_pass,known_holes}`), lệnh `light check-app`, oracle vi sai (`src/bin/oracle.rs`) | f7eeadf, 2f5f424 |
| 2 | Vá verifier: bỏ `spawn/sync` → `parallel` fork-join + kiểu mờ `smp`; IDT 0..31 → `kernel_panic` (màn hình đỏ + serial); AP chỉ nhận APIC 1..15 | 69f35ef |
| 3a | Con trỏ độ dài động `ptr<L,%n>` (Z3 chứng minh mọi truy cập trong biên `%n`) | 8216702 |
| 4 | Cấp/thu hồi RAM tường minh cho App: heap `ptr<DiskQword,%n>` = đúng phần đã map; bể khung đọc từ Memory Map thật (≤ 48GB); xóa trắng chunk trước khi giao; AP xả TLB trước mỗi job; oracle dùng chung `RAM_TOP` với verifier | 792c06e |

---

## 🔨 Đang làm

### Bước 5 — NVMe + boot trên máy thật (code xong, đã test QEMU; chờ thử trên laptop)
- [x] Boot qua GRUB EFI (multiboot1): header xin framebuffer, cờ header đúng chuẩn (cờ 0x40 cũ bị GRUB từ chối),
      bảng section header tối thiểu (GRUB 2.14 bắt buộc). `qemu -kernel` vẫn chạy.
- [x] Màn hình: VRAM logic 1280×720 trong RAM, `fb_present_rect` chép ra framebuffer GOP thật (pitch bất kỳ, căn giữa).
      Bỏ việc đọc mò BAR0 của PCI 00:02.0 (trên Iris Xe đó là thanh ghi GPU).
- [x] x2APIC → xAPIC trong boot stub; PAT PA1 = WC; INIT chờ ~10ms + 2 SIPI.
- [x] Ngôn ngữ: lệnh `narrow` (thu hẹp có chứng minh), I/O 32-bit (ghi bv32, đọc 0xCFC).
- [x] PCI config (0xCF8/0xCFC), cửa sổ MMIO cố định qua PML4[1] (fb WC, BAR UC).
- [x] Driver NVMe bằng Light + Intel VMD + GPT `lightos` + kiểm tra biên phân vùng trong driver. Tầng `blk_*` thay mọi
      lời gọi ATA của kernel (ATA vẫn là dự phòng).
- [x] F1..F7 mở App, F12 khởi động lại; dòng trạng thái BLK/PART/PLEN trên màn hình.
- [x] `tools/install_lightos.sh` (dùng lại phân vùng rustos → lightos), `tools/qemu_uefi_nvme.sh` (môi trường giống máy thật).
- [x] Sửa SAVE của Editor (LBA file bị chính lệnh đọc file ghi đè → không bao giờ lưu).
- [x] **Boot trên laptop thật** (2026-11-11): `BLK 0002010007800438` = NVMe qua Intel VMD, thấy phân vùng `lightos`,
      khởi tạo OK, framebuffer GOP 1920×1080. (HP: tắt Secure Boot phải nhập mã 4 số khi khởi động lại mới có hiệu lực.)
- [x] Màn hình logic 1920×1080: desktop phủ kín, Dock giữa đáy, App vẽ qua khung nhìn `slice` căn giữa (App không phải sửa).
- [x] Installer: BootOrder của HP chứa số mục không tồn tại → lọc trước khi `efibootmgr -o`.
- [x] ATA: chờ trạng thái dừng ngay khi có ERR (trước đây đọc quá cuối đĩa mất > 4 phút trên `qemu -kernel`, giờ ~4 giây).

### Bước 5b — Chuột trên máy thật (chưa làm)
Laptop không có chuột PS/2: touchpad Synaptics `SYNA32A9` (06CB:CE17) nằm trên I2C (Intel Serial IO I2C #1, PCI 00:15.1,
DesignWare), chuột ngoài PixArt + bàn phím SINO WEALTH cắm USB (xHCI 8086:a0ed, PCI 00:14.0).
- [ ] Phương án A — touchpad: driver I2C DesignWare (MMIO BAR0, chế độ master, polling) + giao thức HID-over-I2C
      (đọc HID descriptor, reset, đọc input report; chế độ chuột mặc định trước khi bật PTP). Cần địa chỉ slave và
      thanh ghi HID descriptor (lấy từ ACPI `_CRS`/`_DSM`, hoặc ghi cứng sau khi đọc từ Linux).
- [ ] Phương án B — USB: driver xHCI (ring lệnh/sự kiện/truyền, context thiết bị, enumerate cổng gốc, HID boot protocol
      cho chuột + bàn phím). Lớn hơn nhưng dùng được mọi chuột/bàn phím USB.

## 📋 Tiếp theo

### Bước 3b — Giải phóng riêng lẻ (`free`)
- Kiểu tuyến tính cho `ptr<L,%n>` do allocator cấp: sau `release` không dùng lại được (verifier theo dõi trạng thái).
- Allocator trong heap App (bitmap/free-list viết bằng Light) thay cho co/giãn cả heap.

### Bước 6 — LightFS
- Thay VFS phẳng hiện tại (superblock + thư mục + string pool, file liên tục, không xóa/không mở rộng được) bằng hệ
  tệp có cấp phát extent, ghi an toàn khi mất điện (journal hoặc copy-on-write), checksum.
- Công cụ host: `light sync` đọc trực tiếp từ phân vùng/ảnh đĩa; fsck.
- Bộ test: ảnh đĩa hỏng, đầy đĩa, mất điện giữa chừng.

### Các lỗi/thiếu sót còn mở
- [ ] IPC dùng chung cho mọi App: yêu cầu đĩa của App chạy ngầm có thể bị tính cho App foreground.
- [ ] `smp_selftest` đếm worker khi AP còn đang boot (có lúc in `WORKERS=5` thay vì 7).
- [ ] Chưa có IST/TSS cho double fault; exception trên AP làm BSP treo chờ.
- [ ] Header App còn jmp thứ 3 (worker_offset) không dùng.
- [ ] `drv_ata_load_app` luôn đọc 2048 sector, kể cả phần quá cuối đĩa (nay ATA báo ERR và bỏ qua ngay; NVMe từ chối
      phần vượt phân vùng). Nên đọc đúng kích thước file App.
- [ ] NVMe: chưa dùng ngắt (MSI-X), mỗi lệnh chờ đồng bộ; chỉ 1 hàng đợi I/O; ghi không gọi Flush (dữ liệu có thể nằm
      trong cache của SSD nếu mất điện ngay sau khi lưu).
- [ ] Cửa sổ App vẫn cố định 880×540 (chỉ được dời ra giữa màn 1920×1080); App chưa biết kích thước màn hình.
- [ ] Cửa sổ ảo 32GB/App; tối đa 7 App.
- [ ] Không có ngắt (mọi thiết bị đều thăm dò); không có bộ đếm thời gian thật (timeout tính bằng số vòng lặp).
- [ ] USB (bàn phím/chuột ngoài) chưa hỗ trợ; touchpad I2C chưa hỗ trợ.

---

## 🔭 Xa hơn (giữ từ lộ trình cũ, đã chỉnh lại)

- **Vòng lặp AI tự sửa lỗi**: verifier xuất phản ví dụ Z3 dạng JSON (hàm, lệnh, giá trị các biến); CLI đẩy ngược cho
  LLM để bổ sung `@req/@inv` và sinh lại.
- **Tối ưu mã máy**: hiện ≈ `gcc -O0` (chậm ~4.6× so với `-O2`). Cấp phát thanh ghi linear-scan cho biến SSA nóng,
  bỏ load/store thừa qua stack.
- **Thư viện tensor** (`lib/tensor.lit`): GEMM/dot/ReLU trên `vxxx256` + `parallel`, chạy một mạng nhỏ bare-metal.
- **Self-hosting**: đưa verifier + codegen vào Light OS, nạp module `.lit` đã kiểm chứng lúc chạy.
- **Mạng**: driver NIC (Wi-Fi AX201 rất khó; ưu tiên USB-Ethernet hoặc virtio-net trên QEMU).
