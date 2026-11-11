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

### Bước 5b — Bàn phím/chuột USB (code xong, đã test QEMU; chờ thử trên laptop)
Laptop không có chuột PS/2. Chuột PixArt (low-speed) + bàn phím SINO WEALTH (full-speed) cắm USB, nối thẳng vào cổng gốc
của xHCI PCH 00:14.0 (8086:a0ed). Touchpad Synaptics trên I2C (00:15.1) chưa hỗ trợ.
- [x] Driver xHCI bằng Light (`drivers/usb_xhci.lit`): BIOS handoff, reset, scratchpad, ring lệnh/sự kiện/EP0/interrupt,
      reset cổng USB2, Address Device, Evaluate Context (MPS EP0), descriptor, HID boot, Configure Endpoint.
- [x] Báo cáo HID → gói PS/2 / scancode set 1, dùng chung `kbd_handle_scancode`. Thử nhiều controller lần lượt.
- [x] QEMU (`qemu-xhci` + `usb-kbd` + `usb-mouse`, tắt i8042): gõ phím, Shift, F2, click đóng cửa sổ, click Dock; cả đường
      `-kernel` lẫn OVMF/GRUB/NVMe (firmware đã dùng xHCI trước → phải giành lại).
- [ ] Thử trên laptop (dòng `USB` trên màn hình). Chưa hỗ trợ: hub USB, thiết bị không có boot protocol, bàn phím tự lặp
      phím khi giữ, đèn Caps Lock, phím mũi tên. Touchpad I2C: để sau.

### Bước 5c — Tối ưu mã máy (xong, đã test QEMU)
Bộ sinh mã mới `src/x86.rs` thay cho kiểu "mọi biến SSA nằm trên stack + 5 thanh ghi nóng" (≈ `gcc -O0`).
- [x] Liveness theo block + cấp phát thanh ghi linear scan trên 11 thanh ghi: rbx r12–r15 cho biến sống qua lời gọi,
      rsi rdi r8–r11 cho biến còn lại; thiếu thì tràn ra stack. Prologue chỉ lưu thanh ghi callee-saved thật sự dùng.
- [x] Hằng số làm toán hạng tức thời (không chiếm thanh ghi); `cmp` + `br` → `cmp` + `jcc`; bỏ `jmp` tới block kế tiếp;
      nhảy lùi gần dùng rel8; `slice` + `load/store` → một lệnh `[base + idx*sz + off]`; ghép đối số `jmp` với tham số
      block (biến vòng lặp ở yên một thanh ghi, không còn `mov` trước mỗi cạnh lùi).
- [x] **Sửa lỗi cũ**: đối số `jmp` được chép tuần tự → sai khi tham số block bị hoán vị (`jmp @b1 %y %x`). Nay chép song
      song (phá chu trình qua rax), đúng ngữ nghĩa SSA mà verifier giả định.
- [x] `cargo run --bin cgtest` (cũng chạy trong `cargo test`): chạy mã máy thật trên host so với trình thông dịch tham
      chiếu, trên `tests/lit/codegen/*.lit` + chương trình ngẫu nhiên; đã thử cài lỗi giả để chắc nó bắt được.
- Kết quả: vòng lặp load/and/add nhanh gấp 4.8×, nhân ma trận 64×64 gấp 3.9×; kernel.elf 134 KB → 43.5 KB, Terminal
  61 KB → 17 KB. QEMU: desktop, Terminal (`ls/sys/memup/memtest`), Editor, chuột/bàn phím USB, đường OVMF/NVMe.

### Bước 7 — Ngôn ngữ cho AI + stdlib + GUI lát 1 (2026-11-11, chưa commit)
- [x] Hằng làm toán hạng (`add %x 6`, `call f %p 0xff`), trường Layout có tên (`load %ipc IpcChannel.mouse_x`).
- [x] `view` (đổi Layout trên cùng vùng nhớ), `data`/`addr` (dữ liệu tĩnh sau mã máy); font chuyển sang bảng `data`.
- [x] Chứng minh vòng lặp dừng cho mọi hàm không giữ `io` (`@dec`, tự suy `n - i`, `i`, `p - X`).
- [x] `lit_program/std/` (core, mem, str, fmt, sys, surface); Terminal in số bằng `fmt_u64`.
- [x] Kênh IPC riêng cho từng App (phím/click chỉ tới App foreground, mem/LightFS/đóng/vùng bẩn theo kênh).
- [x] Sửa: `entry_offset` lấy hàm cuối (trước đây sẽ lấy offset của `data` cuối -> kernel không boot).

### GUI kiểu Wayland — các lát tiếp theo
1. ~~Kênh riêng mỗi App~~ (xong).
2. Surface ngoài màn hình: App vẽ vào bộ đệm riêng (cùng kiểu `ptr<VgaCell,1382400>` bước 1920 để không đổi ABI), compositor
   blit theo z-order + vùng bẩn của từng kênh. Cần chỗ RAM vật lý cho 7 × 5,5MB (cấp từ bể khung, map vào cửa sổ của App).
3. Quản lý cửa sổ: focus, đưa lên trên, kéo; khung cửa sổ do compositor vẽ (App không vẽ ui_win_draw nữa).
4. Surface động `(w, h, ptr)` + sự kiện `configure` khi đổi kích thước (đổi `check_app_abi` và test `app_abi_*`); toolkit trên `std/surface`.
5. Tách quyền: compositor không giữ `io<0,0xffff>` (chỉ ptr màn hình + surface).

## 📋 Tiếp theo

### Bước 3b — Giải phóng riêng lẻ (`free`)
- Kiểu tuyến tính cho `ptr<L,%n>` do allocator cấp: sau `release` không dùng lại được (verifier theo dõi trạng thái).
- Allocator trong heap App (bitmap/free-list viết bằng Light) thay cho co/giãn cả heap.

### Bước 6 — LightFS ✅
- Đã thay VFS phẳng bằng **LightFS**: khối 4KB, mỗi file một extent, bảng 256 mục (tên ≤ 63 byte, thư mục lồng nhau).
- Ghi an toàn khi mất điện bằng copy-on-write: dữ liệu → bảng sang vùng B/A → bản ghi commit (thế hệ + checksum) →
  `flush` giữa các bước; mount chọn commit hợp lệ có thế hệ cao nhất. Checksum FNV-1a cho header, bảng, commit và dữ liệu file.
- App không còn đụng LBA thô: mọi truy cập qua IPC của Kernel (TABLE/READ/WRITE/CREATE/DELETE); terminal có `ls cd cat mkdir touch rm write`.
- Công cụ host: `light sync` (host ⇄ ảnh/phân vùng), `light fsck`, `light pack [--size]`; test: ảnh đĩa hỏng, đầy đĩa, mất điện giữa chừng (`cargo test`).
- Còn lại: file chỉ 1 extent (ghi lại = cấp extent mới), bảng cố định 256 mục, installer vẫn ghi ảnh 64MB (không giãn theo phân vùng).

### Các lỗi/thiếu sót còn mở
- [x] IPC dùng chung cho mọi App — đã thay bằng kênh riêng mỗi slot (bước 7). Đã thử: chuyển Terminal ↔ Editor, LightFS,
      đóng bằng [X] và ESC. CHƯA thử App chạy ngầm: không code nào bật bit `bg_mask` (đường `shell_bg_tick_apps` là code
      chết từ trước bước 7).
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
- [ ] Touchpad I2C chưa hỗ trợ; USB chưa có hub, chưa có ngắt (thăm dò mỗi nhịp scheduler).

---

## 🔭 Xa hơn (giữ từ lộ trình cũ, đã chỉnh lại)

- **Vòng lặp AI tự sửa lỗi**: verifier xuất phản ví dụ Z3 dạng JSON (hàm, lệnh, giá trị các biến); CLI đẩy ngược cho
  LLM để bổ sung `@req/@inv` và sinh lại.
- **Tối ưu mã máy tiếp**: inline hàm nhỏ, xoay vòng lặp (bỏ `jmp` đầu vòng), khoảng sống có lỗ (linear scan hiện dùng
  một khoảng bảo thủ cho mỗi biến).
- **Thư viện tensor** (`lib/tensor.lit`): GEMM/dot/ReLU trên `vxxx256` + `parallel`, chạy một mạng nhỏ bare-metal.
- **Self-hosting**: đưa verifier + codegen vào Light OS, nạp module `.lit` đã kiểm chứng lúc chạy.
- **Mạng**: driver NIC (Wi-Fi AX201 rất khó; ưu tiên USB-Ethernet hoặc virtio-net trên QEMU).
