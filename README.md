# ⚡ Light & Light OS
**Ngôn ngữ Trung gian Kiểm chứng Hình thức dành cho AI (Verification-Native AI-IR) & Hệ điều hành Exokernel Không gian Địa chỉ Đơn (Single-Address-Space Capability OS)**

---

## 1. Tầm nhìn & Triết lý Thiết kế (Design Philosophy)

Các ngôn ngữ lập trình truyền thống (C, C++, Python, hay thậm chí là Rust) và các hệ điều hành truyền thống (Linux, Windows) đều được thiết kế xoay quanh **giới hạn sinh học của con người**:
- Ngôn ngữ cần cú pháp văn bản lồng nhau phức tạp, ẩn giấu trạng thái, nhưng lại thiếu khả năng chứng minh toán học tự động, dẫn đến hiện tượng **ảo giác (hallucination)** và lỗi tràn bộ nhớ khi AI sinh mã.
- Hệ điều hành phải dùng cơ chế phần cứng đắt đỏ (**Ring 0 / Ring 3, MMU Context Switch, TLB Flush**) để cách ly các chương trình không đáng tin cậy, làm lãng phí hàng nghìn chu kỳ CPU cho mỗi lời gọi hệ thống (`syscall`) hay giao tiếp liên tiến trình (`IPC`).

**Light (`.lit`)** và **Light OS** ra đời để định nghĩa lại từ gốc cả hai tầng này khi **AI là chủ thể viết và thực thi mã nguồn**:

### 4 Trụ cột Kiến trúc Cốt lõi:
1. **Verification-as-Isolation (Cách ly bằng Toán học thay vì Phần cứng):**
   - Trình biên dịch `light` tích hợp trực tiếp bộ giải **Z3 SMT Solver** (trên miền `BitVector 64-bit`) làm "Thần giữ cửa" bắt buộc.
   - Mọi đoạn mã (dù là Kernel, Driver hay Ứng dụng AI) đều phải được Z3 chứng minh là **UNSAT** (tuyệt đối không tràn số, không chia cho 0, không dịch bit lố, không truy cập ngoài biên bộ nhớ, không vi phạm hợp đồng hàm) trước khi được phép sinh ra mã máy `x86_64`.
2. **Single Address Space OS — SASOS (Không chia Userspace / Kernelspace):**
   - Nhờ mã máy đầu ra đã được chứng minh an toàn 100% lúc biên dịch, toàn bộ Kernel, Driver và Ứng dụng chạy chung trong **một không gian địa chỉ 64-bit phẳng duy nhất ở Ring 0**.
   - Giao tiếp giữa Ứng dụng, Driver và Kernel chỉ là lệnh `call` hàm trực tiếp ở tốc độ **nano-giây (Zero Context-Switch, Zero-Copy IPC)**.
3. **Unforgeable Capability-Based Security (Bảo mật theo Thẻ Quyền Năng Không thể Giả mạo):**
   - Trong toàn bộ trình biên dịch `light` **không tồn tại khái niệm hay từ khóa đặc quyền riêng cho Kernel**.
   - Quyền truy cập RAM và Phần cứng được quyết định hoàn toàn bởi 2 kiểu dữ liệu Thẻ quyền năng trên chữ ký hàm: **`ptr<Layout, MaxElems>`** (Thẻ Bộ nhớ) và **`io<MinPort, MaxPort>`** (Thẻ Phần cứng).
   - Không một hàm nào có thể tự chế tạo thẻ `io` hay ép kiểu từ số nguyên `bv64` sang con trỏ `ptr`. Quyền năng chỉ có thể được **thu hẹp (Capability Attenuation / Subtyping)** khi ủy quyền từ hàm cha xuống hàm con.
4. **Flat SSA (Cú pháp Phẳng cho LLM):**
   - Một dòng một lệnh, không biểu thức lồng, không AST đa tầng. Trình biên dịch Rust (`src/`: parser, verifier Z3, sinh mã x86-64, ELF64, LightFS, công cụ) ~6.000 dòng, xuất thẳng ELF64 bare-metal không cần `ld`.

### Vùng tin cậy (những gì KHÔNG được Z3 chứng minh)
- Bộ sinh mã `src/x86.rs` và `src/elf64.rs` (được kiểm vi sai bằng `cgtest`, không chứng minh).
- Mã assembly runtime `src/rt/*.s` (`parallel`, exception).
- Mọi `assume` trong hàm giữ `io<0,0xffff>`; `CallPtr` (chỉ hàm gốc).
- Z3 hết thời gian (10 giây/điều kiện) được coi là LỖI, không phải "qua".
- Vòng lặp trong hàm giữ thẻ `io<..>` (driver chờ phần cứng, scheduler) không bị buộc phải dừng; mọi hàm khác — kể cả toàn bộ App — phải chứng minh dừng (xem "Vòng lặp phải dừng").
---

## 2. Chi tiết Kỹ thuật Ngôn ngữ `Light` (`.lit`)

### 2.1. Hệ thống Kiểu Dữ liệu (`Type`)
- **`bv8`, `bv16`, `bv32`, `bv64`**: Các thanh ghi BitVector kích thước cố định. Loại bỏ hoàn toàn sự nhập nhằng giữa số có dấu (`signed`) và không dấu (`unsigned`) ở cấp độ kiểu; tính chất dấu nằm ở phép toán (`udiv` vs `sdiv`, `ult` vs `slt`), ánh xạ 1:1 với thanh ghi CPU `x86_64` và `Z3 BV`.
- **`ptr<Layout, MaxElems>`**: Con trỏ có miền giới hạn tĩnh. Luôn gắn chặt với một cấu trúc `Layout` và số phần tử tối đa `MaxElems`.
- **`io<MinPort, MaxPort>`**: Thẻ quyền năng truy cập cổng phần cứng I/O hoặc thanh ghi điều khiển trong dải `[MinPort..=MaxPort]`. Là kiểu "Ghost" (kiểm chứng ở Z3, tốn 0 byte ở mã máy).
- **`ptr<Layout, %n>`**: Con trỏ có độ dài **động** — `%n` là một biến SSA số nguyên (bất biến, nên độ dài không đổi sau khi tạo). Mọi `load/store/slice/vxxx256/ata_read/parallel` vẫn được Z3 chứng minh trong biên `%n`. Quy tắc:
  - Tham số hàm: `%n` phải là tham số số nguyên **đứng trước** (`func f void %0:bv64 %1:ptr<Q,%0>`). Kiểu trả về `ptr<L,%k>`: `%k` là tham số của hàm; người gọi nhận `ptr<L,%đối_số>`.
  - Tham số block: `%n` là tham số đứng trước của **cùng block** hoặc tham số hàm — vòng lặp mang cặp `(độ dài, ptr)` qua `jmp`.
  - Đích của `slice`: `%n` bất kỳ đã định nghĩa và chi phối (`%p = slice %arena %off ptr<Q,%n>`, chứng minh `off + n <= độ dài arena`).
  - Chuyển đổi tĩnh ↔ động, động ↔ động (gọi hàm, `jmp`, `ret`): Z3 chứng minh độ dài đích `<=` độ dài thật.
  - Không tạo được bằng `const`, không nằm trong Layout (không lưu vào bộ nhớ). Ngầm định `n * kích_thước <= RAM` nên tính địa chỉ không tràn.
  - Cấp phát: bộ cấp phát viết bằng Light trả về **offset** kèm `@ens`, người gọi `slice` ra `ptr<L,%n>` (xem `tests/lit/must_pass/dyn_ok.lit`, hàm `region_try`). Chưa có `free` riêng lẻ (bước 3b).
- **`smp`**: Thẻ quyền điều phối đa nhân (mờ: không load/store được). Chỉ hàm giữ `io<0,0xffff>` tạo được bằng `const 0x7e000 smp`; Kernel truyền cho App làm tham số thứ 6.

### 2.2. Bố cục Bộ nhớ Phẳng (`Layout`) & Bất biến Kiểu (`@inv`)
Thay thế `struct`/`class` truyền thống bằng bảng khai báo vị trí byte cố định (`offset`) kèm điều kiện bất biến Z3 (`@inv`):
```text
layout VgaCell 2 {
    0: bv8 @inv ult val 128     # Offset 0 (1 byte): Mã ASCII bắt buộc < 128
    1: bv8                      # Offset 1 (1 byte): Mã màu VGA
}
```
- Khi thực hiện lệnh `store`, `verify.rs` bắt buộc Z3 chứng minh giá trị ghi vào thỏa mãn `@inv`.
- Khi thực hiện lệnh `load`, biến đích tự động được thừa hưởng tính chất `@inv` của trường đó.

### 2.3. Tập Chỉ thị SSA
Mỗi biến được định danh bằng số thứ tự (`%0`, `%1`, `%2`...) và chỉ gán 1 lần duy nhất:
1. **`%d = const <val> <ty>`**: Khởi tạo hằng số. (Chỉ hàm giữ thẻ gốc `io<0,0xffff>` mới được phép ánh xạ địa chỉ vật lý `>= 0x10000` thành thẻ `ptr`).
2. **`%d = <binop> %lhs %rhs`**: Gom 13 phép toán số học & bitwise (`add, sub, mul, udiv, sdiv, urem, srem, and, or, xor, shl, lshr, ashr`). Tự động kiểm tra chống tràn số (`overflow/underflow`), chống chia cho `0`, và chống dịch bit `>= 64`.
3. **`%d = cmp <cmpop> %lhs %rhs`**: 10 phép so sánh (`eq, ne, ult, ule, ugt, uge, slt, sle, sgt, sge`).
4. **`%d = slice %base %idx ptr<Layout, M_new>`**: Cắt hoặc dịch chuyển thẻ bộ nhớ từ mảng lớn `%base` (`ptr<Layout, M_old>`) tại chỉ số `%idx`. Z3 tự động chứng minh `%idx + M_new <= M_old`.
5. **`%d = load %base <offset> <ty>`**: Đọc dữ liệu từ thẻ `ptr` (kiểm tra `base != 0`, `offset < max_bytes` và đúng kiểu trường).
6. **`store %base <offset> %val`**: Ghi dữ liệu 1/2/4/8 byte vào thẻ `ptr` (kiểm tra biên và bất biến `@inv`).
7. **`hwio_w %cap <port> %val`** & **`%d = hwio_r %cap <port>`**: Đọc/ghi cổng I/O và thanh ghi hệ thống (`CR3`), yêu cầu `%cap` có kiểu `io<Min, Max>` chứa `<port>`. Độ rộng: ghi theo kiểu giá trị (`bv32` → 32-bit, `bv16`/cổng 0x1F0 → 16-bit, còn lại 8-bit, Z3 chứng minh giá trị vừa); đọc theo cổng (0xCFC → 32-bit, 0x1F0 → 16-bit, còn lại 8-bit).
   - **`%d = narrow %x bv8|bv16|bv32`**: thu hẹp số nguyên; Z3 phải chứng minh `%x` vừa độ rộng đích (không cắt bit im lặng). Cần để ghi thanh ghi MMIO/cổng 32-bit bằng giá trị tính toán (kết quả phép toán luôn là `bv64`).
8. **`br %cond @then_bb @else_bb`**: Rẽ nhánh có điều kiện (Z3 tự động tích lũy điều kiện đường đi `cur_cond` qua các tầng nhánh lồng nhau).
9. **`jmp @target_bb [%arg0 %arg1 ...]`**: Nhảy vô điều kiện kèm truyền **Tham số Khối (`Block Params`)** thay cho hàm $\phi$ (Phi-node) cổ điển, đồng thời kích hoạt kiểm chứng quy nạp toán học trên `@inv` của khối đích.
10. **`[%d =] call <func_name> [%arg0 ...]`**: Gọi hàm trực tiếp. Tự động kiểm tra phép thu hẹp thẻ quyền năng (`can_delegate`), chứng minh tiền điều kiện `@req` và kế thừa hậu điều kiện `@ens`.
11. **`ret [%val]`**: Thoát hàm và chứng minh mọi hậu điều kiện `@ens` **tại từng `ret`**. Trong `@ens`, ngoài tham số được phép dùng đúng MỘT tên (thanh ghi không phải tham số, vd `%r`) chỉ giá trị trả về; mỗi `ret` gán tên đó bằng giá trị nó trả. Hàm nhiều đường thoát không cần block gom + `@inv` chép lại hậu điều kiện (xem `tests/lit/must_pass/ens_multi_ret.lit`).
12. **`parallel %smp %n <hàm> %base %arg`** & **`%d = smp_workers %smp`**: Fork-join đa nhân **chặn**. Chia `%base` (`ptr<L,M>`) thành `%n` (1..16) phần `ptr<L,K>` (K = kiểu tham số đầu của hàm), chạy `hàm(phần_i, %arg, i)` trên các nhân AP online (phần còn lại chạy trên nhân gọi) và chỉ trả về khi mọi phần xong. Z3 chứng minh `n*K <= M` và `@req` của worker đúng với mọi `i < n`; worker có chữ ký cố định `(ptr<L,K>, bv64, bv64)`, phải vừa stack AP 32KB và không lồng `parallel`. `smp_workers` trả số AP đang online (0..15).
13. **`assume <z3_prefix_expr>`** & **`assert <z3_prefix_expr>`**: Các chỉ thị Ghost phục vụ suy luận toán học, bị xóa bỏ 100% khi sinh mã máy `x86_64`. `assume` chỉ được dùng trong hàm giữ `io<0,0xffff>`.
14. **`vadd256|vsub256|vmul256|vxor256 %dst %a %b`** & **`%d = vdot256 %a %b`**: AVX2 trên 32 byte; Z3 chứng minh cả ba vùng đủ 32 byte, cấm ghi lên Layout có `@inv`.
15. **`fxmul`, `fxdiv`**: số điểm cố định Q16.16 (chống tràn như `mul`).
16. **`ata_read %cap %ptr %sec %n`**: đọc ATA PIO (chỉ khi build kernel, Layout đích không có `@inv`).
17. **`[%d =] call %fn_ptr ...`** (`CallPtr`): gọi gián tiếp, chỉ hàm giữ `io<0,0xffff>`.

---

## 3. Kiến trúc Hệ điều hành `Light OS`

`Light OS` được tổ chức theo kiến trúc **Capability Exokernel + Init Startup**, phân tách hoàn toàn cơ chế lõi khỏi các chương trình ngoại vi:

```text
lit_program/
├── os/        kernel.lit (vòng lặp scheduler), init.lit, wm.lit (desktop, cầu nối Dock), dock.lit (vẽ Dock thuần: bảng bo góc, hover, chỉ báo App), topbar.lit (thanh trên cùng: tên App, ngày giờ RTC), compositor.lit (surface riêng mỗi App, xếp chồng/kéo cửa sổ, vẽ khung), app_loader.lit (VMM, nạp App),
│              lightfs.lit (LightFS phía Kernel), hw.lit (framebuffer, PCI, MMIO), diag.lit (panic, selftest)
├── drivers/   blk, nvme, ata_disk, pci, usb_xhci, kbd_drv (PS/2 + chuột), vga_drv, serial
├── lib/       std_lib, os_layout (Layout dùng chung), gfx, font, ipc_bus, cap_mem, lightfs_api, ui_* (window, button,
│              canvas, text_view, file_browser)
└── apps/      terminal.lit, editor.lit (biên dịch riêng thành storage/apps/*.bin)
```

### 3.1. Bộ nhớ của App: cấp phát & thu hồi tường minh

- **Bể khung RAM vật lý** (khung 2MB từ 288MB, tối đa 24576 khung = 48GB): lúc boot `vmm_probe_ram` khóa toàn bộ bitmap rồi chỉ mở những khung nằm **trọn** trong vùng RAM type 1 của memory map (không bao giờ cấp lỗ PCI / ACPI / reserved).
- **Mỗi App** có cửa sổ ảo 64GB riêng; chunk c (2MB) = trang c+1. Chunk 0..14 (30MB) luôn được map; chunk 15.. lấy từ bể.
- **ABI hàm main của App**: `(VgaCell*, Ipc*, State ptr<DiskQword,≤3932160>, Q64, Q64, smp, %n:bv64, heap:ptr<DiskQword,%n>)`. `heap` phủ **đúng** các chunk đã map (`n = số_chunk × 262144`), nên Z3 chứng minh App không bao giờ chạm vùng chưa có RAM thật. App có thể khai báo ít tham số hơn (tiền tố).
- **Cấp / thu hồi**: App ghi số chunk mong muốn vào IPC offset 168 (`mem_req`, 15..16383). Ngay sau tick đó, Kernel cấp thêm (mỗi chunk được **xóa trắng** trước khi giao, chống rò dữ liệu giữa App) hoặc gỡ ánh xạ + trả khung về bể. Lần gọi tiếp theo App nhận heap với độ dài mới. Offset 176 (`mem_free`) = số khung còn trống.
- **Vì sao thu hồi an toàn**: App không thể giữ con trỏ qua tick (Layout cấm trường ptr; heap được truyền lại mỗi lần gọi). TLB: nhân BSP nạp lại CR3 sau khi gỡ; mỗi nhân AP nạp lại CR3 trước mỗi job `parallel`.
- Terminal có lệnh `mem`, `memup` (+1GB), `memdown` (trả hết), `memtest` (ghi/đọc lại mỗi trang 4KB của heap).

### 3.2. Boot trên máy thật, màn hình, đĩa NVMe

- **Boot**: GRUB EFI nạp `kernel.elf` bằng multiboot1. Header xin framebuffer 1920×1080×32; GRUB trả framebuffer GOP thật (kích thước bất kỳ). `qemu -kernel` vẫn chạy (không có framebuffer trong Multiboot Info → dùng Bochs VGA, PCI 1234:1111). ELF có bảng section header tối thiểu (GRUB 2.14 bắt buộc). Boot stub chuyển x2APIC → xAPIC nếu firmware để x2APIC, đặt PAT (PA1 = Write-Combining), gửi INIT + 2 SIPI.
- **Màn hình**: màn hình logic 1920×1080. VRAM logic `0x200000` và Backbuffer `0xC00000` (8MB mỗi bộ) nằm trong RAM; `fb_present_rect` (os/hw.lit) chép vùng thay đổi ra framebuffer thật (pitch bất kỳ, căn giữa nếu màn hình lớn hơn, cắt nếu nhỏ hơn). Hai kiểu con trỏ VRAM: `ptr<VgaCell,2073600>` = cả màn hình (kernel: nền, con trỏ, blit, present, các hàm `*_scr`); `ptr<VgaCell,1382400>` = khung nhìn 1280×720 bước dòng 1920 — kernel `slice` VRAM tại gốc (320,160) đưa cho App, tại (320,359) cho Dock, nên App giữ nguyên tọa độ cũ mà vẫn nằm giữa màn hình. Chuột: tọa độ màn hình ở IPC 184/192; mỗi nhịp kernel quy đổi sang tọa độ khung nhìn App (IPC 16/24, kẹp trong 1260×700).
- **USB** (`drivers/usb_xhci.lit`): driver xHCI viết bằng Light, thăm dò, không ngắt. Quét PCI bus 0 tìm controller 0C:03:30, thử lần lượt (laptop Intel có controller Thunderbolt đứng trước controller PCH). Giành quyền từ BIOS (USB Legacy Support), reset, dựng ring lệnh/sự kiện, reset cổng USB2, Address Device, đọc descriptor, chọn interface HID boot (bàn phím/chuột), Configure Endpoint, SET_PROTOCOL(boot). Chỉ thiết bị cắm thẳng vào cổng gốc (chưa hỗ trợ hub), tối đa 8 slot. Báo cáo chuột được đổi thành gói PS/2, mã phím HID đổi thành scancode set 1, rồi đi qua đúng code xử lý của driver PS/2 (`kbd_handle_scancode`). Vùng DMA 2MB cố định tại `0x1400000` (PD_0[10]); BAR0 ánh xạ ở PD_MMIO[2..3]. Dòng chẩn đoán `USB` trên màn hình: giai đoạn (0 = OK, 8 = không có thiết bị HID), dev PCI, số cổng, số slot, mã hoàn thành, số bàn phím/chuột, bước dò cuối.
- **MMIO**: Light không cho đổi số nguyên thành `ptr`, nên địa chỉ chỉ biết lúc chạy (framebuffer, BAR) được ánh xạ vào địa chỉ ảo cố định qua PML4[1]: `0x80_0000_0000` framebuffer (WC), `0x80_4000_0000` BAR NVMe (UC), `0x80_4200_0000` CFGBAR của Intel VMD (UC). Bảng HW ở `0x96000`.
- **Đĩa** (`drivers/blk.lit`): NVMe nếu có, ngược lại ATA PIO. Driver NVMe (`drivers/nvme.lit`, viết bằng Light): tìm NVMe trên PCI hoặc phía sau **Intel VMD** (laptop Intel đời 11+), 1 cặp hàng đợi Admin + 1 cặp I/O, thăm dò completion, DMA qua bộ đệm bounce 64KB ở `0x80000`. Chỉ dùng phân vùng GPT tên **`lightos`** có header **LightFS** (`LIGHTFS1`; copy-on-write + checksum, xem ROADMAP bước 6; host: `light sync/fsck/pack`); mọi LBA được kiểm tra `< kích thước phân vùng` ngay trong driver. Đĩa không có GPT (ảnh thô trên QEMU) → cả namespace.
- **Dòng trạng thái** góc trên trái (và serial): `BLK = backend<<48 | gpt<<40 | mã_lỗi_nvme<<32 | rộng<<16 | cao`, `PART` = LBA đầu phân vùng, `PLEN` = số sector. Backend 2 = NVMe, 1 = ATA, 0 = không có; gpt 1 = thấy `lightos`; mã lỗi NVMe xem đầu hàm `nvme_init_ctrl`.
- **Phím**: F1..F7 mở App ở ô Dock tương ứng (touchpad I2C của laptop chưa có driver), F8 / F9 giảm / tăng độ sáng màn hình (GPU Intel, `drivers/backlight.lit`), F10 hiện/ẩn dòng chẩn đoán phần cứng, F12 khởi động lại.

---

## 4. Hướng dẫn Cài đặt & Chạy thử nghiệm

### Yêu cầu hệ thống (Ubuntu / Debian):
```bash
sudo apt update && sudo apt install -y libz3-dev clang libclang-dev qemu-system-x86
```

### Biên dịch và Khởi chạy `Light OS` trên QEMU:
```bash
# 1. Phân tích cú pháp, kiểm chứng hình thức Z3 và xuất tệp thực thi ELF64 bare-metal
cargo run --release   # kernel.elf (lit_program/os/kernel.lit) + storage/apps/*.bin + disk.img

# 2. Khởi động trên QEMU có cửa sổ (gắn đĩa LightFS chứa App, 4G RAM, KVM; serial in ra terminal)
bash tools/qemu_run.sh            # --fresh: chép lại đĩa sạch, --usb: bàn phím/chuột USB
                                  # --agent: COM1 thành socket cho Claude (xem "Kênh Agent"), --headless: không cửa sổ

# 3. Giống hệt máy thật: OVMF (UEFI) -> GRUB lightos.efi -> multiboot, đĩa NVMe có GPT (ESP / lightos / ubuntu)
bash tools/qemu_uefi_nvme.sh
```

### Cài lên máy thật (UEFI, đĩa NVMe)
1. **Tắt Secure Boot** trong BIOS (HP: F10). GRUB khóa lệnh `multiboot` khi Secure Boot bật. Ubuntu vẫn khởi động bình thường khi tắt.
2. `cargo run --release` (tạo `kernel.elf` + `disk.img`), rồi chạy thử `sudo bash tools/install_lightos.sh` để xem kế hoạch, sau đó `sudo bash tools/install_lightos.sh --yes`. Script dùng lại phân vùng `rustos` (nvme0n1p2): sao lưu nội dung vào `~/lightos_backup_<ngày>/`, ghi `disk.img`, đổi tên GPT thành `lightos`, cài `EFI/lightos/{kernel.elf,lightos.efi}`, thêm mục UEFI "Light OS" ở **cuối** BootOrder (Ubuntu vẫn là mặc định).
3. Khởi động vào Light OS một lần: `sudo efibootmgr -n <số mục Light OS>` rồi reboot (hoặc F9 lúc bật máy). F12 trong Light OS để quay lại.
4. Cập nhật sau này: `--kernel-only --yes` (giữ dữ liệu trên phân vùng) hoặc `--disk-only --yes` (ghi lại `disk.img`).

## Công cụ cho người và AI

- `light check <file.lit> [--json]` — kiểm chứng MỌI hàm trong file (không dừng ở hàm lỗi đầu tiên). Với `--json`, stdout chỉ có một đối tượng
  `{"ok":false,"errors":[{"kind","func","block","inst","message","counterexample":[{"reg","value"}],"origin":"file:dòng","source","hint"}]}`
  hoặc `{"ok":true,"verified":N,"cache_hits":M}`; tiến trình nằm ở stderr/bị tắt.
- `light doc [TRUY_VẤN] [--brief] [--defs] [--file F]... [--json]` — chữ ký, `@req/@ens` và chú thích của hàm (và `def` với `--defs`) trong
  `lit_program/`; tra theo tên, chú thích hoặc đường dẫn. Dùng thay cho việc đọc cả file thư viện.
- Cache Z3: kết quả chứng minh lưu ở `.light-cache/z3.keys` (khóa = băm mã verifier + layouts + hàm + hợp đồng của hàm được gọi).
  Build lại không đổi gì mất ~0,06s thay vì ~7s. `--no-cache` hoặc `LIGHT_NO_CACHE=1` để tắt; xóa thư mục để làm mới.

## Kênh Agent: Claude chạy lệnh trong Light OS (QEMU)

Lõi shell `std/shell.lit` (thuần, không io) là bộ thông dịch CHẠY TỪNG BƯỚC: `sh_begin` rồi gọi `sh_step` tới khi xong;
mỗi khi cần đĩa, lõi dừng lại xin mặt tiền một thao tác LightFS mức thấp (READ / WRITE / CREATE / DELETE), mặt tiền làm
rồi trả kết quả bằng `sh_op_done`. Kết quả: stdout, stderr, mã thoát (0 / 1 lỗi / 2 cú pháp / 127 không có lệnh), cờ cắt.

- Lệnh: `help echo pwd cd ls stat cat write append mkdir touch rm grep wc head tail sort uniq find env unset true false`.
- Cú pháp: nháy `'...'` (nguyên văn) và `"..."` (thay `$VAR`), `$VAR ${VAR} $?`, `TÊN=giá_trị`, ống `a | b`,
  chuyển hướng `> >> <`, chuỗi lệnh `a ; b`, `a && b`, `a || b`. `\` chỉ thoát ký tự đặc biệt của shell; chuỗi `\n`... khác
  đi nguyên tới lệnh (`write`, `append`, `echo -e` hiểu `\n \t \\ \xHH`). Lỗi cú pháp được báo trước khi lệnh nào chạy.
  Chưa có: glob, `$(...)`, `2>`, chạy nền.
- Ống chạy tuần tự qua hai bộ đệm 128KB (A / B đổi vai); đầu ra của mỗi lệnh vào một bộ đệm rồi mới chuyển tiếp: lệnh
  sau, file (`>`, `>>`, `write`, `append` đều đi qua cùng một đường) hoặc stdout. Đầu ra bị cắt (tràn 128KB ở bất kỳ
  lệnh nào trong ống) KHÔNG BAO GIỜ được ghi vào file: lệnh báo "file too large" và trả 1.
- `grep` tìm chuỗi cố định (`^` / `$` neo đầu / cuối dòng, `-v -i -n -c`), `sort` tối đa 6144 dòng (`-r -n -u`, heapsort),
  `find` duyệt bảng LightFS (`-name` với `* ?`, `-type f|d`). Biến: 4KB, giữ qua các lệnh của phiên.

Kernel (`os/agent.lit`) đọc lệnh từ COM1 mỗi nhịp, chạy lõi tới hết (thao tác đĩa làm đồng bộ, `ag_op`, có chặn khi
chưa gắn hệ tệp) và trả một dòng `@@LR|id|exit|trunc|stdout|stderr` (thoát ký tự `\\ \n \t \xHH`); khởi động xong in
`@@LREADY`. Giới hạn: dòng lệnh 128KB, stdout 64KB, stderr 1KB, file 1MB. Bộ nhớ: vùng Kernel PD_0[11]
(stdout 0x1660000, dòng lệnh 0x1670000, vùng làm việc của lõi 448KB ở 0x1690000, nội dung file 0x1700000).
App Terminal (`apps/terminal.lit`) là mặt tiền thứ hai của CÙNG lõi: mỗi thao tác đĩa là một yêu cầu IPC; khi đang chạy
lệnh, App đặt `IpcChannel.run_req` để Kernel gọi lại mỗi nhịp (không cần phím), chỉ vẽ lại khi xong lệnh. Bộ đệm cuộn
32KB tự xuống dòng, cửa sổ đổi kích thước được, nút cuộn ^ / v; thêm lệnh riêng `clear sys mem memup memdown memtest`
(chỉ khi là cả dòng). Người và Claude gõ cùng một bộ lệnh.
MCP server có 3 công cụ: `run` (một dòng lệnh), `read_file`, `write_file` (gửi `write 'PATH' '<nội dung đã thoát>'`,
`'` thành `\x27`, chia thành `write` + `append` theo khối 120000 ký tự).

```bash
bash tools/qemu_run.sh --agent             # cửa sổ QEMU + socket target/light_serial.sock
python3 tools/light_mcp.py --run "ls /apps"  # thử tay: in stdout/stderr, mã thoát = mã của lệnh
# Claude Code dùng MCP server (stdio, không cần cài gì thêm) qua tools/light_mcp.json -> công cụ mcp__vm__run:
claude -p "liệt kê các App trong Light OS" --strict-mcp-config --mcp-config tools/light_mcp.json \
       --allowedTools "mcp__vm__run" --disallowedTools "Bash,Edit,Write,WebFetch,WebSearch"
```

## Số học tường minh khi tràn 64-bit

`add`/`sub`/`mul` thường đòi verifier chứng minh không tràn. Khi cần định nghĩa hành vi tràn, dùng (cả ba họ cho cộng, trừ, nhân):

| Lệnh | Khi tràn |
|---|---|
| `%d = add_sat %a %b` (`sub_sat`, `mul_sat`) | kẹp ở biên (0 hoặc 2^64-1), luôn qua verifier |
| `%d = add_wrap %a %b` (`sub_wrap`, `mul_wrap`) | quay vòng modulo 2^64 (hash, checksum), không đòi chứng minh |
| `%f = add_ovf %a %b` (`sub_ovf`, `mul_ovf`) | `%f` = 1 nếu phép tương ứng sẽ tràn, ngược lại 0 (bv64); dùng với `br`/`add_wrap` |

`*_sat` và `*_ovf` được parser hạ thành các lệnh bv64 thuần (không rẽ nhánh), nên verifier và bộ sinh mã không đổi; ngữ nghĩa được kiểm trên
mã máy thật với số học của Rust (`cgtest`, `tests/lit/codegen/ovf.lit`).

## Hằng làm toán hạng và trường có tên

Mọi vị trí toán hạng (phép toán, `cmp`, đối số `call`/`jmp`, `ret`, giá trị `store`/`hwio_w`, chỉ số `slice`, `%n`/`%arg` của
`parallel`) nhận hằng trực tiếp thay cho thanh ghi: số thập phân/hex, tên `def`, chuỗi ≤ 8 byte, hoặc có hậu tố kiểu `5:bv8`.
Parser hạ mỗi hằng thành một `const` ngay trước lệnh. Không có hậu tố thì kiểu lấy theo ngữ cảnh: tham số của hàm được gọi, kiểu
trường có tên của `store`, tham số block đích của `jmp`, kiểu trả về của `ret`; còn lại `bv64`.

Trường Layout có thể đặt tên: `16: bv64 mouse_x @inv ult val 1260`. `Layout.tên` dùng được ở mọi chỗ nhận số (offset của
`load`/`store`, `@req/@inv`), và `load` theo trường có tên không cần ghi kiểu:

```text
%x = load %ipc IpcChannel.mouse_x          # = load %ipc 16 bv64
store %ipc IpcChannel.click 0               # hằng 0 lấy kiểu bv64 của trường
%s = add %x 6
call gfx_fill_rect %fb %x %y 100 40 0x22d3ee   # 0x22d3ee lấy kiểu bv32 từ chữ ký hàm
```

## Dữ liệu tĩnh (`data`/`addr`) và nhìn bộ nhớ theo layout khác (`view`)

```text
data GREETING Byte {               # Layout không có @inv; giá trị theo thứ tự trường, chuỗi trải ra từng byte
    "Xin chao\n" 0
}
data NUMBUF Byte 24 {              # khai số phần tử: phần thiếu = 0 (bộ đệm tĩnh ghi được)
}
%s = addr GREETING                 # ptr<Byte,GREETING.len>;  GREETING.len dùng được ở mọi chỗ nhận số
%b = view %q ptr<Byte,%m>          # cùng vùng nhớ, Layout khác: cả hai Layout không có @inv, Z3 chứng minh m*1 <= số byte nguồn
```

`data` nằm ngay sau mã máy (địa chỉ tương đối RIP), ghi được, verifier không giả định gì về nội dung. Trong App, `data` là một phần
ảnh mã đã nạp nên giá trị ghi vào **còn nguyên sau khi đóng rồi mở lại App** (Kernel chỉ xóa State); đừng dùng nó cho trạng thái
cần làm mới khi mở lại. Font 8x16
(`lib/font.lit`, sinh bởi `fontgen`) là hai bảng `data` thay cho ~1.500 dòng `cmp/br`.

## Thư viện chuẩn `lit_program/std/`

Viết quanh vùng nhớ độ dài động `(%n, ptr<L,%n>)`, mọi hàm có `@ens` và được chứng minh dừng; không dùng cặp `@req` miền địa chỉ.

| Module | Nội dung |
|---|---|
| `core` | layout chung, `math_min/max/clamp`, `byte_u64` |
| `mem` | `mem_fill_{q,b,px}`, `mem_copy_{q,b}`, `mem_eq_b` |
| `str` | chuỗi = (độ dài, `ptr<Byte,%n>`): `str_eq`, `str_starts_with`, `str_find`, `str_skip_spaces`, `str_parse_u64`, `byte_lower` |
| `fmt` | ghi vào bộ đệm, trả vị trí mới `<= cap`: `fmt_byte`, `fmt_str`, `fmt_u64`, `fmt_hex` |
| `sys` | IPC theo tên trường: `sys_key_pop`, `sys_mouse_x/y`, `sys_click_take`, `sys_mem_request`, `sys_close`, `sys_damage` |
| `surface` | vẽ trên surface `(n, px, stride, w, h)`: `surf_put`, `surf_fill_rect`, `surf_frame`, `surf_char`, `surf_text`, `surf_round_inset`, `surf_round_rect` (hình bo góc dùng chung cho Dock / compositor / widget) |
| `widget` | cửa sổ đổi kích thước được: `wg_pick_w/h` (nhận đề nghị configure, kẹp theo min/max của App), `wg_window_open` (báo kích thước đã vẽ), `wg_client` (surface của vùng nội dung, tự cắt), `wg_label`, `wg_box`, `wg_button`, `wg_hit`, `wg_mouse_x/y`, `wg_damage`; component kiểu macOS: `wg_rbox`, `wg_rframe`, `wg_pbutton`, `wg_field`, `wg_toolbar`, `wg_statusbar`, `wg_textarea`, `wg_number`, `wg_qtext`, `wg_list_row`, `wg_icon_doc/folder` |
| `widget_fs` | duyệt LightFS kiểu Finder: `wg_fs_name`, `wg_fs_list`, `wg_fs_hit` (Editor dùng) |
| `shell` | lõi shell dùng chung: `sh_begin` / `sh_step` / `sh_op_done` / `sh_op_name` (bộ thông dịch chạy từng bước, `ShState` giữ cwd, `$?` và thao tác đĩa đang chờ; vùng làm việc `SH_WS` = 448KB), `sh_unescape`, `sh_resolve` (đường dẫn `/a/../b`) |

`surface` không đưa `y*stride` vào chứng minh (nhân hai biến làm Z3 hết giờ): offset tính bằng hàm mờ `surf_offset`, kiểm biên
lúc chạy trước khi `slice`, các hàng sau đi bằng phép cộng. Lõi shell in số bằng `fmt_u64` (`sh_out_dec`).

## Kênh IPC riêng cho từng App

Kênh `0x79000` là của driver/WM. Mỗi slot App có `IpcChannel` riêng ở `0x79100 + slot*240` (`app_chan`). Trước mỗi lần gọi App,
`app_sync_in` chép chuột/Shift và **chỉ App foreground** nhận phím/click; sau đó `app_sync_out` trả phím/click chưa dùng, lệnh đóng
cửa sổ và vùng bẩn về kênh chung. Yêu cầu RAM (`mem_req`) và LightFS được phục vụ trên đúng kênh của App đã gửi.

## Vòng lặp phải dừng (`@dec`)

App chạy hợp tác ở Ring 0 và chưa có ngắt timer, nên một vòng lặp vô hạn sẽ treo cả máy. Vì vậy mọi hàm **không giữ thẻ
`io<..>`** phải chứng minh từng vòng lặp dừng: trên mỗi cạnh lùi (jmp/br về block đứng trước theo thứ tự RPO, tức đầu vòng),
một biến giảm (variant) của đầu vòng phải **giảm ngặt theo so sánh không dấu** (nên không thể giảm mãi).

- Không ghi gì: verifier tự thử `p`, `X - p`, `p - X` với `p` là tham số số nguyên của đầu vòng và `X` là cận bất biến vòng
  (hằng, tham số hàm, biến định nghĩa trước vòng) lấy từ `@inv` của đầu vòng và các lệnh `cmp`. Đủ cho vòng `for i < n`, đếm lùi.
- Trường hợp khác: ghi `@dec <biểu_thức>` ở block đầu vòng, chỉ dùng tham số của block đó và biến định nghĩa trước vòng:

```text
@loop %a:bv64 %b:bv64
    @inv ult %a 1000
    @inv ult %b 1000
    @dec add %a %b          # mỗi vòng a hoặc b giảm 1
```

Vòng chờ một ô nhớ đổi giá trị (`br` về đầu vòng không tham số) không chứng minh được — trong App, thay bằng trả về và kiểm lại ở
nhịp sau.

"Dừng" không có nghĩa là "trả về nhanh": một vòng đã chứng minh dừng vẫn có thể chạy tới 2^64 lần. Vẫn cần watchdog bằng timer
(chưa có) để chặn App chạy quá lâu trong một nhịp.

## Tên biến và nhãn block

Thay cho số SSA/nhãn số, có thể viết `%tổng`, `%i`, `@loop`, `@done` (bắt đầu bằng chữ hoặc `_`). Parser đổi chúng thành số trước khi kiểm chứng
nên dùng được ở mọi vị trí (tham số, `@req/@ens/@inv`, kiểu `ptr<L,%n>`, đích `br/jmp`, tham chiếu tới trước); `%<số>` và `@b<số>` vẫn hợp lệ và
có thể dùng lẫn. Thông báo lỗi và `--json` in lại bằng tên. Tên nhãn không được là `req`, `ens`, `inv`; block đầu tiên trong văn bản là entry.

## Kiểm khung stack

Cận stack của verifier (`verify::local_stack_bound`) là một lập luận; `light stack-report` kiểm nó bằng đo đạc: bộ sinh mã báo khung THẬT của từng hàm
(địa chỉ trả về + rbp + thanh ghi push + vùng spill + đối số đẩy lên stack + `push rdi` của ata_read + khung `lt_parallel`) và lệnh fail nếu có hàm
vượt cận. Chạy trên kernel và mọi App; `cgtest` kiểm thêm trên mọi chương trình trong `tests/lit/codegen` và các chương trình fuzz (hàm có tới 8
tham số, nhiều lời gọi).
