# ⚡ Light
**Ngôn ngữ cấp thấp có kiểm chứng Z3, thiết kế để AI viết được code ĐÚNG — hướng tới app Linux userspace (gọi syscall trực tiếp).**

> Nhánh `lang-refactor` (2026-11-12): Light OS (kernel, driver, App, LightFS, công cụ QEMU) đã được xoá; lịch sử còn trên `main`.
> Hướng mới: viết app Linux bằng std Light, kiểm chứng ĐÚNG CHỨC NĂNG (không chỉ an toàn bộ nhớ). Lộ trình: `ROADMAP.md`.
> **Cú pháp B** (file `.lt`, kiểu Rust, hạ xuống SSA bên dưới): xem `SYNTAX_B.md`. Tài liệu dưới đây mô tả lớp SSA `.lit`.

---

## 1. Tầm nhìn & Triết lý Thiết kế

- **Kiểm chứng là cổng bắt buộc:** trình biên dịch `light` gọi **Z3** (BitVector 64-bit). Mọi hàm phải được chứng minh: không tràn số
  ngoài ý muốn, không chia cho 0, không dịch bit lố, không truy cập ngoài biên, vòng lặp dừng, đúng hợp đồng `@req/@ens` — trước khi sinh mã x86-64.
- **Cú pháp phẳng cho LLM:** một dòng một lệnh SSA, mỗi việc một cách viết; lỗi kiểm chứng kèm **phản ví dụ cụ thể** để AI tự sửa.
- **Thẻ quyền năng:** `ptr<Layout, N>` không thể giả mạo từ số nguyên; chỉ thu hẹp được khi truyền xuống hàm con.
- Trình biên dịch Rust (`src/`: parser, verifier Z3, sinh mã x86-64, công cụ) ~5.000 dòng.

### Vùng tin cậy (những gì KHÔNG được Z3 chứng minh)
- Bộ sinh mã `src/x86.rs` và `src/elf64.rs` (được kiểm vi sai bằng `cgtest`, không chứng minh).
- Mã assembly runtime `src/rt/rt_parallel.s` (`parallel`).
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
12. **`parallel %smp %n <hàm> %base %arg`** & **`%d = smp_workers %smp`**: Fork-join đa nhân **chặn**. Chia `%base` (`ptr<L,M>`) thành `%n` (1..16) phần `ptr<L,K>` (K = kiểu tham số đầu của hàm), chạy `hàm(phần_i, %arg, i)` trên các nhân AP online (phần còn lại chạy trên nhân gọi) và chỉ trả về khi mọi phần xong. Z3 chứng minh `n*K <= M` và `@req` của worker đúng với mọi `i < n`; worker có chữ ký cố định `(ptr<L,K>, bv64, bv64)`, phải vừa stack AP 32KB và không lồng `parallel`. `smp_workers` trả số AP đang online (0..15). Phần `i` chạy trên AP có APIC ID `i` (nếu online), phần 0 và mọi phần `i >= số nhân` chạy trên nhân gọi — muốn song song thật thì chọn `%n = smp_workers + 1` và cho mỗi phần nhiều việc hơn.
13. **`assume <z3_prefix_expr>`** & **`assert <z3_prefix_expr>`**: Các chỉ thị Ghost phục vụ suy luận toán học, bị xóa bỏ 100% khi sinh mã máy `x86_64`. `assume` chỉ được dùng trong hàm giữ `io<0,0xffff>`.
14. **`vadd256|vsub256|vmul256|vxor256 %dst %a %b`** & **`%d = vdot256 %a %b`**: AVX2 trên 32 byte; Z3 chứng minh cả ba vùng đủ 32 byte, cấm ghi lên Layout có `@inv`.
15. **`fxmul`, `fxdiv`**: số điểm cố định Q16.16 (chống tràn như `mul`).
16. **`ata_read %cap %ptr %sec %n`**: đọc ATA PIO (chỉ khi build kernel, Layout đích không có `@inv`).
17. **`[%d =] call %fn_ptr ...`** (`CallPtr`): gọi gián tiếp, chỉ hàm giữ `io<0,0xffff>`.

---

## 3. Biên dịch & thử

```bash
sudo apt install -y libz3-dev clang libclang-dev   # Ubuntu / Debian
cargo build --release
./target/release/light check lit_program/std/fmt.lit       # kiểm chứng một file
python3 tools/stitch/gate.py                                # cổng an toàn đầy đủ
```

## Công cụ cho người và AI

- `light check <file.lit> [--json]` — kiểm chứng MỌI hàm trong file (không dừng ở hàm lỗi đầu tiên). Với `--json`, stdout chỉ có một đối tượng
  `{"ok":false,"errors":[{"kind","func","block","inst","message","counterexample":[{"reg","value"}],"origin":"file:dòng","source","hint"}]}`
  hoặc `{"ok":true,"verified":N,"cache_hits":M}`; tiến trình nằm ở stderr/bị tắt.
- `light stack-report [FILE.lit...]` — đối chiếu khung stack thật với cận của verifier (mặc định: mọi file std).
- `light doc [TRUY_VẤN] [--brief] [--defs] [--file F]... [--json]` — chữ ký, `@req/@ens` và chú thích của hàm (và `def` với `--defs`) trong
  `lit_program/`; tra theo tên, chú thích hoặc đường dẫn. Dùng thay cho việc đọc cả file thư viện.
- Cache Z3: kết quả chứng minh lưu ở `.light-cache/z3.keys` (khóa = băm mã verifier + layouts + hàm + hợp đồng của hàm được gọi).
  Build lại không đổi gì mất ~0,06s thay vì ~7s. `--no-cache` hoặc `LIGHT_NO_CACHE=1` để tắt; xóa thư mục để làm mới.

## Số học tường minh khi tràn 64-bit

`add`/`sub`/`mul` thường đòi verifier chứng minh không tràn. Khi cần định nghĩa hành vi tràn, dùng (cả ba họ cho cộng, trừ, nhân):

| Lệnh | Khi tràn |
|---|---|
| `%d = add_sat %a %b` (`sub_sat`, `mul_sat`) | kẹp ở biên (0 hoặc 2^64-1), luôn qua verifier |
| `%d = add_wrap %a %b` (`sub_wrap`, `mul_wrap`) | quay vòng modulo 2^64 (hash, checksum), không đòi chứng minh |
| `%d = mulhi %a %b` | nửa cao 64 bit của tích KHÔNG DẤU 128 bit (x86 `mul`). Verifier coi kết quả là giá trị mờ, chỉ biết `%d <= %a` và `%d <= %b` (không đưa phép nhân 128 bit vào Z3); trong `@req/@ens` có ngữ nghĩa đúng nhưng vì thế không chứng minh được `@ens` về giá trị chính xác |
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
| `fixq` | số điểm cố định Q4.60 có dấu (`fq_mul` ghép 4 tích 32x32, sai số <= 3 ulp; `fq_abs`, `fq_clamp2`) + lõi Mandelbrot `mb_iter` (liền mạch, dò chu kỳ Brent) / `mb_color`. Phép `_wrap` nên đúng đắn số học do `tools/mandel_model.py test` đối chiếu từng bit với mã máy (`cgtest --call`) |
| `bignum` | số điểm cố định n limb (1..16, dấu-độ lớn, limb cao = Q4.60, F = 60 + 64(n-1) bit lẻ): `bn_addsub`, `bn_mul` (tích đủ 2n limb bằng `mulhi`, rồi cắt), `bn_from_q`, `bn_to_q`, `bn_cmp_mag`; đối chiếu từng bit bằng `tools/mandel_model.py test` |
| `mbref` | quỹ đạo tham chiếu Mandelbrot bằng `bignum`: `mb_ref_run` chạy tiếp từng lô, ghi Z_k dạng Q4.60 (cho phóng sâu kiểu nhiễu loạn) |

Mẹo khi Z3 hết giờ vì nhân hai biến (vd `y*stride`): tính offset bằng một hàm mờ (không `@ens`), kiểm biên lúc chạy
trước khi `slice`, các hàng sau đi bằng phép cộng.

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
vượt cận. Chạy trên mọi file std; `cgtest` kiểm thêm trên mọi chương trình trong `tests/lit/codegen` và các chương trình fuzz (hàm có tới 8
tham số, nhiều lời gọi).
