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
2. ~~Surface ngoài màn hình~~ (xong, `os/compositor.lit`): mỗi slot vẽ vào surface 6MB riêng tại `0x12000000 + slot*6MB`
   (21 khung đầu của bể VMM, giữ lúc boot bởi `comp_init` và ánh xạ đồng nhất vào `PD_0[144..164]`; phải < 2GB vì App/gfx
   đòi `@req ult %fb 0x80000000`). Cùng kiểu `ptr<VgaCell,1382400>` -> ABI không đổi. Không đủ khung -> tự tắt, vẽ thẳng.
   **Đính chính:** commit đầu của lát này kiểm "đang bật" bằng `PD_0[144] == 0x12000083`, nhưng CPU bật bit A/D (0x60)
   ngay lần chạm đầu -> compositor tự TẮT sau khi xóa surface lúc boot, mọi ảnh chụp khi đó là đường vẽ thẳng. Đã sửa
   (bỏ bit A/D trước khi so) và kiểm lại bằng `qt.py mon:xp ...` đọc bảng cảnh + ảnh hai cửa sổ chồng nhau.
3. ~~Quản lý cửa sổ: focus, đưa lên trên, kéo~~ (xong): bảng cảnh ở `0x79800` (thứ tự chồng + vị trí từng cửa sổ).
   App vẫn vẽ cửa sổ tại (200,60) trong surface; compositor đặt nó ở (wx, wy) và quy đổi chuột ngược lại -> App không
   biết bị dời. Nhấn cửa sổ dưới -> đưa lên trên (cú nhấn bị tiêu thụ); kéo thanh tiêu đề (trừ nút [X]) khi giữ nút trái;
   cửa sổ mới xếp tầng (+40, +16); đóng cửa sổ trên cùng -> cửa sổ kế tiếp nhận focus. Chỉ vẽ trong 1280 x 624 của khung
   nhìn (Dock không bị đè). Kiểm: 1 cửa sổ trùng từng điểm ảnh với bản trước; 2 cửa sổ: đưa lên, phím đúng cửa sổ, kéo,
   [X] trên cửa sổ đã dời (usb), ESC rồi focus về cửa sổ dưới; legacy/usb/uefi.
   Chưa làm: cửa sổ dưới không chạy nên nội dung của nó đứng yên tới khi được đưa lên; vùng kéo chỉ trong khung nhìn
   1280x720 (x 0..394, y 0..590).
3b. ~~Khung cửa sổ do compositor vẽ~~ (xong): thỏa thuận kiểu xdg-decoration — `IpcChannel` 256 byte, thêm `title`
   (App ghi, 8 ký tự) và `decor` (Kernel ghi 1 khi compositor bật). App gọi `ui_win_open`: decor = 1 -> chỉ tô vùng nội
   dung; decor = 0 (compositor tắt, RAM < ~330MB) -> tự vẽ đủ khung như cũ. `comp_frame` vẽ khung vào surface (focus:
   thanh tiêu đề đậm + [X] đỏ; không focus: xám), vẽ lại khi focus đổi hoặc App đổi tên; nút [X] do compositor bắt
   (`comp_click` trả 2 -> WM đóng App). Kiểm: 1 cửa sổ trùng từng điểm ảnh với bản trước; 2 cửa sổ: màu focus đúng, [X]
   của compositor đóng cửa sổ trên rồi focus về cửa sổ dưới (usb); uefi; RAM 320M -> đường App tự vẽ khung.
   Còn lại: thanh trạng thái của Terminal vẫn vẽ trên thanh tiêu đề (vùng của compositor) -> bị xóa khi focus đổi, hiện
   lại ở lần Terminal chạy kế tiếp; nên chuyển vào vùng nội dung.
4. ~~Đổi kích thước + configure + toolkit~~ (xong, KHÔNG đổi ABI App): kéo góc dưới-phải (ô 16x16) -> compositor ghi
   đề nghị `IpcChannel.cfg_w/cfg_h` + `configure = 1` (WM gọi App trên cùng dù không có input); App tự chọn kích thước
   (`wg_pick_w/h`, kẹp theo min/max của nó), vẽ lại, báo `win_w/win_h`; compositor CHỈ dùng kích thước App báo (hợp lệ:
   [300,1074] x [150,558], dời trái nếu tràn), vẽ khung mới, vẽ lại hợp vùng cũ + mới. Terminal/Editor báo cố định
   880x540 qua `ui_win_open` -> kéo góc không đổi gì. `IpcChannel` 320 byte: kênh riêng dời về `0x79200`, bảng cảnh về
   `0x79c00`. Toolkit `std/widget.lit` + App mẫu `apps/widgets.lit` (F3). Ban đầu định đổi `check_app_abi` sang surface
   động `(w, h, ptr)`; không cần: surface vẫn là khung nhìn 1920-stride cũ, chỉ phần được vẽ thay đổi.
   Kiểm: Terminal/Editor trùng từng điểm ảnh với `main`; Widgets lớn/nhỏ (bố cục theo kích thước, chụp ngay sau khi
   nhả chuột), co trên cửa sổ khác (cửa sổ dưới hiện lại đúng), nút +1; thử kéo góc Terminal -> chỉ khác con trỏ
   chuột; RAM 320M -> Widgets tự vẽ khung 600x400; legacy/usb/uefi; test must_pass/widget_all.
   Chưa làm: con trỏ không đổi hình ở góc kéo; đổi kích thước chỉ theo góc dưới-phải; Terminal/Editor chưa dùng toolkit.
5. ~~Tách quyền~~ (xong): toàn bộ logic compositor (`cs_*`: cảnh, z-order, đưa lên, kéo, đổi kích thước, khung, nút
   [X], vẽ lại, blit vùng bẩn) là hàm THUẦN — không có `io`, không `const` ra con trỏ, không `hwio`; verifier tự giam
   chúng ("Bảo mật"), chỉ được đụng con trỏ nhận qua tham số: `CompCtl` (0x79c00), `CompWin`×7 (0x79c80), kênh App
   `IpcChannel`×7 (0x79200), bảng `CompSlot`×7 (surface, cận < 1GB),
   cộng khung nhìn màn hình và kênh IPC chung/riêng do vỏ cầu nối truyền vào. Lớp "cầu nối kernel" còn 16 hàm giữ io: 4 hàm
   tạo con trỏ trên + các vỏ giữ tên cũ (`comp_present`, `comp_click`...) để WM/app_loader không đổi, và `comp_init`
   (hàm DUY NHẤT ghi `PD_0`). Kéo theo: cờ `CompCtl.enabled` thay cho đọc PD_0 (bỏ luôn mẹo che bit A/D); bảng thứ tự
   chồng `CompZ` gộp vào trường `CompWin.z`; tên cửa sổ vẽ qua `surf_char` (std/surface) thay cho gfx cần io.
   Test `must_fail/comp_no_io_forge.lit`: hàm không io tạo con trỏ tới PD_0 (0x12000) để ghi bảng trang bị từ chối.
   Kiểm: mọi ảnh chụp của lát 4 (mở, lớn, nhỏ, co trên cửa sổ khác, +1, RAM 320M, uefi) trùng từng điểm ảnh; [X] của
   compositor đóng Terminal (usb) -> `CompCtl.count = 1`, Editor còn lại; đưa Terminal lên trên + kéo thanh tiêu đề +
   gõ `sys` (usb) trùng từng điểm ảnh với `main`, bảng cảnh: Terminal ở (360,140) và trên cùng; `cargo test`;
   stack-report 577 hàm.
   Giới hạn còn lại: cầu nối vẫn chạy trong kernel (chưa phải tiến trình riêng); cs_* tin con trỏ cầu nối đưa vào.
6. ~~Làm lại Dock~~ (xong; người dùng yêu cầu 2026-11-11 vì Dock cũ "xấu"): `os/dock.lit` = phần vẽ THUẦN (`dk_*`, không
   io) + cầu nối trong `wm.lit` (`dock_load_apps` lúc boot: nạp App + đọc tên file trong LightFS; `dock_redraw`: gọi mã App
   vẽ icon; `dock_tick` mỗi nhịp WM). Trạng thái `DockState` tại 0x79e00 (ô rê chuột, App đang mở, App focus, số ô, tên).
   Giao diện: bảng bo góc căn giữa theo số App (rộng n*68+12) + bóng đổ + viền + vệt sáng trên; icon 52x52 cắt góc tròn;
   rê chuột -> ô nền sáng, icon nâng 4 điểm, nhãn tên App ("Editor", "Terminal", "Widgets" — từ tên file); dưới icon:
   chấm xám = App đang mở (theo cảnh compositor, `comp_run_mask`), vạch xanh = App focus. Chỉ vẽ lại khi trạng thái đổi,
   rồi đưa vùng Dock lên màn hình + vẽ lại con trỏ. Hàm vẽ bo góc `dk_rrect` / `dk_inset` (góc tròn tính bằng số nguyên).
   Click Dock và phím F1..F7 dùng chung bố cục: `dk_hit`; kernel ghi tâm ô 0 vào `IpcChannel.dock_x0` (kênh chung, byte
   296) cho driver bàn phím (F-phím giờ trỏ vào x = dock_x0 + 68*ô, y 1025). Phím F đặt chuột lên icon nhưng ghi
   `IpcChannel.kbd_pick` -> Dock không bật hover cho tới khi chuột thật di chuyển (máy chỉ có bàn phím không bị kẹt nhãn).
   Kiểm: rê chuột/nhãn/chỉ báo khi mở 2-3 App, ESC đóng App -> chỉ báo đổi; click chuột PS/2 thật (legacy); RAM 320M
   (compositor tắt -> chỉ báo theo App foreground); uefi; phím F sau khi đóng App (dock_x0 vẫn 0x37c), không hover sau
   phím F, có hover sau khi rê thật; kịch bản đưa lên + kéo của lát 5 (bù vị trí phím F) trùng từng điểm ảnh sau khi che
   vùng Dock, ô con trỏ và dòng "mouse x,y" của Terminal (lệch 1 điểm do chuột); `cargo test`; stack-report.
   Giới hạn: `dock_redraw` gọi mã icon của App lúc chạy (trước đây chỉ lúc boot) với con trỏ phủ hàng 359..1079 của bộ
   đệm sau (gồm cả phần dưới khung nhìn cửa sổ) -> nên đệm sẵn icon lúc boot; nhãn tên chỉ lấy 8 byte đầu tên file.
   Đề xuất tiếp (chưa làm, cần người dùng chọn): nền desktop gradient/hình nền; ẩn dòng chẩn đoán BLK/PART/USB ở góc
   trên-trái (chỉ hiện ở chế độ debug); thanh trên cùng (đồng hồ / tên App focus); khung cửa sổ bo góc + bóng mềm.
7. ~~Bàn phím máy thật~~ (2026-11-11; người dùng báo máy thật không nhận phím, QEMU vẫn chạy): driver i8042 cũ chỉ ghi
   3 byte cho chuột (A8, D4 F4), không chờ bộ điều khiển, không bật lại cổng bàn phím, không đặt bit dịch mã. QEMU để sẵn
   mọi thứ nên chạy; firmware UEFI có thể để cổng bàn phím tắt / dịch mã tắt / quét phím tắt. Nay `i8042_setup`
   (drivers/kbd_drv.lit): chờ có giới hạn trước mỗi lần ghi / đọc; tắt 2 cổng + xả bộ đệm; cấu hình = bật dịch mã (bit 6),
   bật clock 2 cổng, tắt IRQ (WM đọc kiểu thăm dò); bật cổng; bàn phím F6 (mặc định), F0 02 (set 2 -> dịch ra set 1), F4
   (bật quét); chuột D4 F4; đọc lại cấu hình. Kết quả ghi HW[300] = dòng KBD của màn chẩn đoán.
   Kiểm: QEMU legacy giả lập trạng thái xấu (F5 + cấu hình 0x10): bản cũ không nhận F2, bản mới nhận và gõ được
   (KBD 3040FAFAFAFAFA00); legacy 7140FAFA..; uefi 7744FAFA..; usb (không có i8042) KBD = 1, bàn phím USB vẫn chạy.
   CHƯA kiểm trên máy thật. Nếu vẫn không nhận phím: màn chẩn đoán sẽ TỰ HIỆN khi bàn phím không ACK lệnh F4 -> chụp dòng KBD.
   Dòng chẩn đoán phần cứng: ẩn mặc định, F10 bật / tắt (`diag_tick`), tự hiện khi bàn phím i8042 lỗi.
8. ~~Thanh trên cùng + cửa sổ bo góc, bóng mềm~~ (2026-11-11, người dùng chọn đề xuất 2, 3, 4 của lát 6):
   - Thanh trên cùng (`os/topbar.lit` vẽ thuần `tb_*` + cầu nối `topbar_tick`/`rtc_read` trong wm.lit): logo + "Light OS"
     | tên App focus (hoặc "Desktop") | "dd/mm/yyyy  hh:mm" từ RTC (cổng 0x70/0x71, BCD/nhị phân, 12/24h). Cộng
     `TB_TZ_HOURS` = 7 (RTC theo UTC như Ubuntu đặt; máy dùng chung Windows thì đặt 0). Chỉ vẽ lại khi đổi phút / đổi
     App focus. Dòng chẩn đoán (F10) dời xuống dưới thanh (y 42..150).
   - Cửa sổ: 4 góc bo bán kính 8 (`comp_draw_window` không vẽ điểm ngoài góc -> lộ cảnh dưới; `cs_frame` vẽ cung viền),
     bóng đổ mềm = làm tối cảnh bên dưới 3 mức (25% / 12% / 6%, `comp_shade`) thay cho dải đen 6 điểm vẽ trong surface.
     Bóng chỉ vẽ khi vẽ lại cảnh từ nền; đưa vùng bẩn của App lên (cs_present) không đụng bóng -> không tối dồn (kiểm:
     điểm ảnh bóng giữ nguyên sau 10 lệnh gõ trong Terminal).
   Kiểm: usb/legacy/uefi, RAM 320M (App tự vẽ khung vuông như cũ), giờ khớp đồng hồ máy chủ.
   Còn lại (đề xuất 1, chưa làm): nền desktop gradient / hình nền.
9. ~~Bàn phím USB ngoài~~ (2026-11-11; người dùng: bàn phím laptop nhận, bàn phím USB cắm thẳng cổng USB-A thì không,
   chuột USB cùng máy chạy): lỗi chồng lấn bảng XS của driver xHCI — kết quả phân tích descriptor ghi tạm ở XS[30..35],
   trùng bản ghi slot 2 (+6/+7) và slot 3 (+0..+3: loại/DCI/MPS/báo cáo trước). Dò thiết bị thứ 4 ghi đè slot 3 -> nếu
   bàn phím rơi vào slot 3 (laptop có webcam / Bluetooth / vân tay gắn trong chiếm slot 1-2) thì bàn phím chết, chuột
   (slot 4) vẫn chạy. Dời sang XS[200..204]. Tái hiện QEMU (`qt.py usbx`, QT_DEV = tablet, usb-net, kbd, mouse): bản cũ
   không gõ được, bản mới gõ + chuột đều chạy. Thêm: SET_IDLE(0) cho bàn phím; dòng chẩn đoán USBD/USBD2 (HW[44/45]):
   mỗi byte 1 slot = tốc độ << 4 | kết quả (1 bàn phím, 2 chuột, 3 hub, 4 không có HID boot, 8+bước = hỏng).
   CHƯA kiểm trên máy thật. Còn thiếu: hub USB (bàn phím có hub bên trong / qua hub ngoài -> USBD báo 3), cắm nóng sau
   boot, phục hồi endpoint sau lỗi truyền.
10. ~~Editor kiểu macOS + bộ component UI dùng lại~~ (2026-11-11):
   - Hình bo góc dùng chung `surf_round_inset` / `surf_round_rect` (std/surface.lit); Dock (`dk_rrect`, icon tròn góc)
     và compositor (`comp_inset8`) chuyển sang dùng nó, không còn bản sao riêng.
   - std/widget.lit thêm component kiểu macOS (thuần, vẽ trên surface client): `wg_rbox`, `wg_rframe`, `wg_text_center`,
     `wg_pbutton` (thường / đang chọn màu nhấn), `wg_field`, `wg_toolbar`, `wg_statusbar`, `wg_qtext`, `wg_number`,
     `wg_textarea` (tự xuống dòng, '\n', con trỏ vạch xanh), `wg_list_row`, `wg_icon_doc`, `wg_icon_folder`; `wg_button`
     cũ giữ chữ ký, vẽ bo góc (App Widgets đổi theo, không sửa App).
   - std/widget_fs.lit (mới): `wg_fs_name`, `wg_fs_list` (danh sách kiểu Finder, "< Back" + tên thư mục), `wg_fs_hit`
     (cùng mã trả về với `ui_fb_handle_click`).
   - apps/editor.lit: chỉ thay phần vẽ + phép bấm (logic New / Open / Save / READ / CREATE / WRITE giữ nguyên): thanh
     công cụ New / Open / Save, ô tên file ("Untitled" khi chưa lưu), vùng tài liệu trắng, thanh trạng thái (số ký tự,
     "Plain Text"); icon Dock mới.
   - Compositor: thanh tiêu đề sáng, tên căn giữa (chữ đầu hoa), 3 đèn đỏ / vàng / xanh; nút đóng = đèn đỏ (28 điểm
     đầu thanh, `WIN_XBTN`; đèn vàng không đóng), cửa sổ không focus đèn xám. Terminal đổi màu dòng trạng thái theo khung (sáng / tối).
   Kiểm QEMU (một phiên): gõ, Save -> data/note1.txt, New, Open -> data -> note1.txt (đúng nội dung), sửa + Save
   (WRITE) -> mở lại thấy bản mới, "< Back", đèn vàng không đóng, kéo thanh tiêu đề, đèn đỏ đóng; uefi + usb; RAM 320M (App tự vẽ khung
   cũ) vẫn chạy; Terminal + Widgets; cargo test; stack-report 714 hàm.
   Còn lại: đèn vàng / xanh chưa có chức năng (chưa có thu nhỏ / phóng to); chữ vẫn là font bitmap 8x16.
11. ~~Cửa sổ bị cắt ngang khi kéo xuống~~ (2026-11-11, người dùng thấy trên máy thật): compositor còn giới hạn vùng vẽ
   ở `VIEW_H` = 624 (đỉnh Dock CŨ nằm trong khung nhìn). Dock nay là bảng nổi ngoài khung nhìn -> `VIEW_H` = 720; kéo /
   phóng to bị kẹp để y + h + 6 <= 720 (cửa sổ dừng ở mép, không bị cắt). USB: khôi phục EP0 + thử lại đọc descriptor
   cấu hình (nhánh usb-ep0-retry), dòng chẩn đoán USBC; bàn phím USB ngoài đã chạy trên máy thật.
12. Độ sáng màn hình (2026-11-11, chưa thử máy thật): `drivers/backlight.lit` — GPU Intel 00:02.0 (máy thật: TigerLake-LP
   GT2 8086:9a49, Ubuntu `intel_backlight` max 96000), BAR0 ánh xạ PD_MMIO[6]; chọn bộ điều khiển PWM firmware đã bật
   (CTL 0xC8250 / 0xC8350 bit 31, FREQ != 0, theo đường cnp của i915), chỉ ghi DUTY, kẹp [FREQ/16, FREQ], 16 bậc.
   F8 / F9 qua `IpcChannel.hotkey` (đổi tên từ diag_toggle: 1 F10, 2 F8, 3 F9), Kernel gọi `bl_tick` mỗi nhịp.
   Dòng chẩn đoán BL. QEMU (không có GPU Intel): BL = E0, phím không ảnh hưởng gì khác.
   Còn lại: phím Fn sáng/tối của HP (qua EC / ACPI), nhớ độ sáng qua lần khởi động, hiện mức % trên màn hình.
13. Lõi shell + kênh Agent (2026-11-11, nhánh shell-core): `std/shell.lit` (`sh_exec`: `help echo pwd ls cd stat`, đường dẫn
   tuyệt đối / tương đối / `..`, stdout + stderr + mã thoát + cờ cắt), `os/agent.lit` (COM1: `<id> <lệnh>` ->
   `@@LR|...`), `drivers/serial.lit` thêm `drv_serial_getc` / `drv_serial_putc_wait`, `tools/light_mcp.py` (MCP stdio,
   công cụ `run`), `qemu_run.sh --agent --headless`. Kernel dò UART lúc khởi động (máy không có COM1 -> kênh tắt).
   Đã thử: lệnh qua kênh Agent trên QEMU legacy + usb (ca lỗi, dòng quá dài, cờ cắt stderr); desktop legacy / usb / uefi
   vẫn chạy và in `@@LREADY`; `-serial none` desktop vẫn chạy. Chưa thử `claude -p` thật, chưa thử máy thật.
   Thêm (cùng ngày): `cat write append mkdir touch rm` — lõi lập kế hoạch, Kernel thực hiện; LightFS tách
   `lfs_read_buf / lfs_write_buf / lfs_create_name` (App vẫn qua lớp bọc lfs_op_*); MCP `read_file` / `write_file`.
   Đã thử: ghi / đọc lại UTF-8 6KB, file 920KB (4 lệnh, ~21s — nút cổ chai là nhận serial từng byte), cat bị cắt ở 64KB,
   append vượt 1MB báo "file too large", đĩa trống (chưa gắn) chặn ghi, khởi động lại vẫn còn, `light fsck` 0 lỗi,
   Terminal cũ vẫn ghi / đọc được ở legacy / usb / uefi (NVMe), desktop vẫn phản hồi khi Agent ghi file lớn.
   Còn mở: Agent xóa / tạo lại mục trong khi App (Editor) còn giữ id cũ -> App có thể ghi nhầm vào mục id đó được dùng lại;
   append đọc lại + ghi lại cả file (O(kích thước)); chưa thử `claude -p` thật.
   Terminal mới (cùng ngày): viết lại `apps/terminal.lit` (2030 -> ~960 dòng) trên lõi shell + std/widget: bộ đệm cuộn
   32KB (= stdout của lõi), tự xuống dòng, đổi kích thước, cuộn, máy trạng thái IPC cho lệnh đĩa, giữ lệnh riêng
   clear / sys / mem / memup / memdown / memtest. Bàn phím: thêm ' ` \ và bảng Shift đầy đủ (@ $ ^ < > " | ~ ...);
   font thêm \ | ~ ` $ ^ (font nay đủ mọi ký tự in được). tools/qt.py gõ được ký hiệu.
   Đã thử: legacy / usb / uefi, cat 900KB (hiện phần đầu tới khi đầy + "[output truncated]"), Agent sửa đĩa thì
   Terminal thấy ngay, xóa thư mục đang đứng -> về /, đổi kích thước, đóng / mở lại.
   Shell v2 (cùng ngày): lõi thành bộ thông dịch chạy từng bước (`sh_begin` / `sh_step` / `sh_op_done`), xin mặt tiền
   thao tác LightFS mức thấp (READ / WRITE / CREATE / DELETE); mỗi lệnh ghi vào bộ đệm OUT rồi mới chuyển tới lệnh sau /
   file / stdout. Bộ tách từ: nháy ' ", `\` trước ký tự đặc biệt, `$VAR ${VAR} $?`, `TÊN=giá_trị`, `env`, `unset`,
   `; && || | > >> <`, lỗi cú pháp báo trước khi chạy. Lệnh mới: grep wc head tail sort uniq find true false, `cat`
   đọc stdin / `-`, `echo -n -e`. Đầu ra bị cắt không bao giờ được ghi vào file. Kernel chia lại vùng PD_0[11]
   (dòng lệnh 448KB -> 128KB, thêm vùng làm việc 448KB), MCP `write_file` gửi `write 'PATH' '...'` (khối 120000).
   Kernel: `IpcChannel.run_req` (thay trường cũ disk_req) — App xin được gọi lại mỗi nhịp, `app_sync_out` chép thành bit
   của slot trong `bg_mask`; Terminal dùng khi đang chạy lệnh (trước đây lệnh > 3 thao tác đĩa đứng chờ phím tiếp).
   Đã thử (QEMU legacy): bộ lệnh v1 cho kết quả giống hệt bản cũ (trừ `ls` trên đĩa trống không còn in dòng trống, và số
   lệnh chia khối khi ghi 1MB), khứ hồi `write_file` đúng từng byte (rỗng, `'`, `\` cuối, `\n` chữ, đủ 256 giá trị byte,
   300KB), ống / chuyển hướng / `&&` `||` / biến / lỗi cú pháp, file 1MB (grep / wc ~1,2s, phần lớn là đọc đĩa), sort
   6144 dòng ~40ms, 6145 dòng báo lỗi, ống tràn bị chặn khi ghi file, Terminal gõ lệnh có ống / chuyển hướng,
   `light fsck` 0 lỗi, stack-report OK; UEFI / NVMe và bàn phím USB: Agent + Terminal (ống, `<`, `>`, biến) chạy đúng.
   Chưa thử: máy thật, `claude -p` thật.
   Còn mở: một dòng lệnh Agent chạy hết trong MỘT nhịp Kernel (đọc file 1MB ~1,2s -> desktop đứng trong lúc đó; lõi đã
   chạy từng bước nên thêm hạn mức thao tác / nhịp là dễ); Terminal in stderr sau toàn bộ stdout của dòng; lệnh riêng
   của Terminal (sys, mem...) chỉ nhận khi là cả dòng, không đi qua ống được.
14. Cài App nóng (2026-11-12, nhánh hot-install): `light build-app`, lệnh riêng kênh Agent `appinstall SRC APP`
   (`ag_install`: kiểm tra trước, ghi đè cùng mục bằng `lfs_write_mode` cho phép file App, `shell_close_and_reset_app`,
   `app_dispatch_load_app`, mở cửa sổ + bit chạy ngầm một lần để App tự vẽ), MCP `install_app` (+ `write_bytes`),
   `ag_tick` nhận Backbuffer + kênh chung.
   Đã thử (QEMU legacy): từ chối SRC thiếu / thư mục / rác (sai lệnh nhảy) / 8 byte / APP không phải App / thừa đối số,
   `appinstall` trống in cách dùng; cài Terminal sửa banner -> cửa sổ tự vẽ banner mới không cần phím, gõ lệnh được; cài 2
   lần liên tiếp, cài lại bản cũ, cài khi Terminal đang chạy dở `grep` x5 trên file 1MB (ảnh chụp xác nhận chưa xong),
   cài Editor / Widgets lúc đóng (mở lên đúng); MCP qua JSON-RPC (`tools/list`, `install_app`, tên sai) và `--install`;
   khởi động lại cùng đĩa -> App mới được nạp (checksum đúng, cùng slot); `light sync` ra file trùng từng byte với `.elf` trên
   host; `light fsck` 0 lỗi; stack-report OK. Chưa thử: UEFI / NVMe, máy thật, `claude -p` thật, ghi lỗi khi đĩa đầy
   (an toàn nhờ thứ tự: kiểm tra + ghi trước, đóng / nạp sau).
   Còn mở: chỉ thay App đã có slot; `rm` chỉ nhận một PATH (đối số thừa bị bỏ qua, không báo lỗi).

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
