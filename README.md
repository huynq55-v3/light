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
4. **Zero-Bloat & Flat SSA (Cú pháp Phẳng Tối ưu cho LLM & Micro-compiler):**
   - Toàn bộ trình biên dịch (`ir.rs`, `parser.rs`, `verify.rs`, `elf64.rs`, `main.rs`) được khóa chặt dưới **700 dòng code Rust** tinh khiết, không dùng AST đa tầng, không dùng Lexer/Pratt Parser phức tạp, xuất thẳng tệp thực thi nhị phân `ELF64` bare-metal mà không cần trình liên kết (`ld`) hay thư viện ngoài.

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

### 2.3. Tập Chỉ thị SSA Cốt lõi (13 Lệnh Nguyên thủy)
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
11. **`ret [%val]`**: Thoát hàm và bắt buộc chứng minh mọi hậu điều kiện `@ens`.
12. **`parallel %smp %n <hàm> %base %arg`** & **`%d = smp_workers %smp`**: Fork-join đa nhân **chặn**. Chia `%base` (`ptr<L,M>`) thành `%n` (1..16) phần `ptr<L,K>` (K = kiểu tham số đầu của hàm), chạy `hàm(phần_i, %arg, i)` trên các nhân AP online (phần còn lại chạy trên nhân gọi) và chỉ trả về khi mọi phần xong. Z3 chứng minh `n*K <= M` và `@req` của worker đúng với mọi `i < n`; worker có chữ ký cố định `(ptr<L,K>, bv64, bv64)`, phải vừa stack AP 32KB và không lồng `parallel`. `smp_workers` trả số AP đang online (0..15).
13. **`assume <z3_prefix_expr>`** & **`assert <z3_prefix_expr>`**: Các chỉ thị Ghost phục vụ suy luận toán học, bị xóa bỏ 100% khi sinh mã máy `x86_64`. `assume` chỉ được dùng trong hàm giữ `io<0,0xffff>`.

---

## 3. Kiến trúc Hệ điều hành `Light OS`

`Light OS` được tổ chức theo kiến trúc **Capability Exokernel + Init Startup**, phân tách hoàn toàn cơ chế lõi khỏi các chương trình ngoại vi:

```text
lit_program/
├── main.lit                 # Điểm vào biên dịch
├── os/
│   ├── kernel.lit           # Kernel Core: Quản lý Heap (kalloc), Bảng Task (kregister), IPC & Bộ lập lịch (kscheduler_loop)
│   └── init.lit             # Startup Manager: Khởi chạy tuần tự các chương trình Driver và App khi boot
├── drivers/
│   ├── vga_drv.lit          # Driver phần cứng màn hình VGA (0xB8000 & io<0x3d4,0x3d5>)
│   ├── kbd_drv.lit          # Driver bàn phím PS/2 (io<0x60,0x64>) giải mã Scancode 64-bit & đẩy vào IpcChannel
│   └── serial_drv.lit       # Driver cổng truyền thông COM1 (io<0x3f8,0x3ff>)
├── lib/
│   └── gfx.lit              # Thư viện đồ họa 2D thuần phần mềm (Không giữ quyền io)
└── apps/
    └── desktop_app.lit      # Ứng dụng giao diện tương tác thời gian thực qua hộp thư Zero-Copy IpcChannel
```

### 3.1. Bộ nhớ của App: cấp phát & thu hồi tường minh

- **Bể khung RAM vật lý** (khung 2MB từ 288MB, tối đa 24576 khung = 48GB): lúc boot `vmm_probe_ram` khóa toàn bộ bitmap rồi chỉ mở những khung nằm **trọn** trong vùng RAM type 1 của memory map (không bao giờ cấp lỗ PCI / ACPI / reserved).
- **Mỗi App** có cửa sổ ảo 64GB riêng; chunk c (2MB) = trang c+1. Chunk 0..14 (30MB) luôn được map; chunk 15.. lấy từ bể.
- **ABI hàm main của App**: `(VgaCell*, Ipc*, State ptr<DiskQword,≤3932160>, Q64, Q64, smp, %n:bv64, heap:ptr<DiskQword,%n>)`. `heap` phủ **đúng** các chunk đã map (`n = số_chunk × 262144`), nên Z3 chứng minh App không bao giờ chạm vùng chưa có RAM thật. App có thể khai báo ít tham số hơn (tiền tố).
- **Cấp / thu hồi**: App ghi số chunk mong muốn vào IPC offset 168 (`mem_req`, 15..16383). Ngay sau tick đó, Kernel cấp thêm (mỗi chunk được **xóa trắng** trước khi giao, chống rò dữ liệu giữa App) hoặc gỡ ánh xạ + trả khung về bể. Lần gọi tiếp theo App nhận heap với độ dài mới. Offset 176 (`mem_free`) = số khung còn trống.
- **Vì sao thu hồi an toàn**: App không thể giữ con trỏ qua tick (Layout cấm trường ptr; heap được truyền lại mỗi lần gọi). TLB: nhân BSP nạp lại CR3 sau khi gỡ; mỗi nhân AP nạp lại CR3 trước mỗi job `parallel`.
- Terminal có lệnh `mem`, `memup` (+1GB), `memdown` (trả hết), `memtest` (ghi/đọc lại mỗi trang 4KB của heap).

### 3.2. Boot trên máy thật, màn hình, đĩa NVMe

- **Boot**: GRUB EFI nạp `kernel.elf` bằng multiboot1. Header xin framebuffer 1280×720×32; GRUB trả framebuffer GOP thật (kích thước bất kỳ). `qemu -kernel` vẫn chạy (không có framebuffer trong Multiboot Info → dùng Bochs VGA, PCI 1234:1111). ELF có bảng section header tối thiểu (GRUB 2.14 bắt buộc). Boot stub chuyển x2APIC → xAPIC nếu firmware để x2APIC, đặt PAT (PA1 = Write-Combining), gửi INIT + 2 SIPI.
- **Màn hình**: giao diện vẫn là 1280×720. VRAM logic `0x200000` nằm trong RAM; `fb_present_rect` (os/hw.lit) chép vùng thay đổi ra framebuffer thật (pitch bất kỳ, căn giữa, cắt nếu màn hình nhỏ hơn).
- **MMIO**: Light không cho đổi số nguyên thành `ptr`, nên địa chỉ chỉ biết lúc chạy (framebuffer, BAR) được ánh xạ vào địa chỉ ảo cố định qua PML4[1]: `0x80_0000_0000` framebuffer (WC), `0x80_4000_0000` BAR NVMe (UC), `0x80_4200_0000` CFGBAR của Intel VMD (UC). Bảng HW ở `0x96000`.
- **Đĩa** (`drivers/blk.lit`): NVMe nếu có, ngược lại ATA PIO. Driver NVMe (`drivers/nvme.lit`, viết bằng Light): tìm NVMe trên PCI hoặc phía sau **Intel VMD** (laptop Intel đời 11+), 1 cặp hàng đợi Admin + 1 cặp I/O, thăm dò completion, DMA qua bộ đệm bounce 64KB ở `0x80000`. Chỉ dùng phân vùng GPT tên **`lightos`** có superblock `LIGHTVFS`; mọi LBA được kiểm tra `< kích thước phân vùng` ngay trong driver. Đĩa không có GPT (ảnh thô trên QEMU) → cả namespace.
- **Dòng trạng thái** góc trên trái (và serial): `BLK = backend<<48 | gpt<<40 | mã_lỗi_nvme<<32 | rộng<<16 | cao`, `PART` = LBA đầu phân vùng, `PLEN` = số sector. Backend 2 = NVMe, 1 = ATA, 0 = không có; gpt 1 = thấy `lightos`; mã lỗi NVMe xem đầu hàm `nvme_init_ctrl`.
- **Phím**: F1..F7 mở App ở ô Dock tương ứng (touchpad I2C của laptop chưa có driver), F12 khởi động lại.

---

## 4. Hướng dẫn Cài đặt & Chạy thử nghiệm

### Yêu cầu hệ thống (Ubuntu / Debian):
```bash
sudo apt update && sudo apt install -y libz3-dev clang libclang-dev qemu-system-x86
```

### Biên dịch và Khởi chạy `Light OS` trên QEMU:
```bash
# 1. Phân tích cú pháp, kiểm chứng hình thức Z3 và xuất tệp thực thi ELF64 bare-metal
cargo run -- lit_program/main.lit kernel.elf

# 2. Khởi động Hệ điều hành với cửa sổ đồ họa VGA và cổng Serial
qemu-system-x86_64 -kernel kernel.elf -serial stdio

# 3. Giống hệt máy thật: OVMF (UEFI) -> GRUB lightos.efi -> multiboot, đĩa NVMe có GPT (ESP / lightos / ubuntu)
bash tools/qemu_uefi_nvme.sh
```

### Cài lên máy thật (UEFI, đĩa NVMe)
1. **Tắt Secure Boot** trong BIOS (HP: F10). GRUB khóa lệnh `multiboot` khi Secure Boot bật. Ubuntu vẫn khởi động bình thường khi tắt.
2. `cargo run --release` (tạo `kernel.elf` + `disk.img`), rồi chạy thử `sudo bash tools/install_lightos.sh` để xem kế hoạch, sau đó `sudo bash tools/install_lightos.sh --yes`. Script dùng lại phân vùng `rustos` (nvme0n1p2): sao lưu nội dung vào `~/lightos_backup_<ngày>/`, ghi `disk.img`, đổi tên GPT thành `lightos`, cài `EFI/lightos/{kernel.elf,lightos.efi}`, thêm mục UEFI "Light OS" ở **cuối** BootOrder (Ubuntu vẫn là mặc định).
3. Khởi động vào Light OS một lần: `sudo efibootmgr -n <số mục Light OS>` rồi reboot (hoặc F9 lúc bật máy). F12 trong Light OS để quay lại.
4. Cập nhật sau này: `--kernel-only --yes` (giữ dữ liệu trên phân vùng) hoặc `--disk-only --yes` (ghi lại `disk.img`).
