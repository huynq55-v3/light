# Cú pháp B của Light (file `.lt`) — tham chiếu

Cú pháp kiểu Rust, được front-end (`src/front.rs`) **hạ xuống SSA `.lit`**. Verifier Z3 và bộ sinh mã chỉ thấy SSA nên
mọi bảo đảm của Light giữ nguyên. Lỗi kiểm chứng chỉ đúng `file.lt:dòng:cột`, kèm dòng nguồn và dấu `^`.

```
light check  app.lt            # kiểm chứng (thêm --json cho AI; trường "at" = dòng:cột)
light lower  app.lt [--origins] # xem SSA sinh ra (và vị trí gốc của từng dòng)
```

Trạng thái: **P2**, gồm biểu thức, `let` / `var`, gán, bộ nhớ, gọi hàm, `if/else`, `while` / `for`, `break` /
`continue`, `return`, đặc tả không lượng từ và `invariant` / `decreases`. Số học toán học, `forall` và `old` trong đặc tả
thuộc P3 (xem `ROADMAP.md`).

## Ví dụ

```rust
include "../lit_program/std/str.lit";      // dùng được mọi hàm / layout / hằng của file SSA

const LIMIT = 100;

// ghi 1 byte nếu còn chỗ, trả vị trí mới
fn put(cap: u64, buf: ptr<u8, cap>, pos: u64, b: u8) -> u64
    requires pos <= cap
    ensures result <= cap, result >= pos
{
    if pos < cap {
        buf[pos] = b;
        return pos + 1;
    }
    return pos;
}
```

## Khai báo cấp file

| Viết | Nghĩa |
|---|---|
| `include "đường/dẫn.lit";` | Nạp file SSA (hoặc `.lt`) tương đối theo file hiện tại |
| `const TÊN = 123;` | Hằng (`def` của SSA). Tên hằng viết HOA |
| `data TÊN: u8 = "chuỗi";` / `data TÊN: u64 = [1, 2];` | Dữ liệu tĩnh; lấy con trỏ bằng `addr(TÊN)` (độ dài `TÊN.len`) |
| `fn f(a: u64, p: ptr<u8, n>) -> u64 requires … ensures … { … }` | Hàm. Không có `-> T` thì hàm không trả giá trị |

Kiểu: `u8 u16 u32 u64`, `ptr<T, n>`.
- Phần tử `T` là `u8` (Byte), `u32` (VgaCell), `u64` (DiskQword) hoặc tên layout bất kỳ.
- Độ dài `n` là tên một tham số đứng trước, hằng HOA hoặc số.

## Câu lệnh

| Viết | Ghi chú |
|---|---|
| `let x = e;` / `let x: u8 = e;` | Bất biến, không gán lại được. Tên trùng trong nhánh khác được tự đổi |
| `var x = e;` / `var x: u8 = e;` | Biến thay đổi được (chỉ số nguyên). Không ghi kiểu thì lấy kiểu của `e` (hằng: u64) |
| `x = e;` `x += e;` `x +%= e;` … | Gán. Chỉ gán được biến `var`, không gán được tham số, `let` hay chỉ số `for`. Có mọi phép gộp `+= -= *= /= %= &= \|= ^= <<= >>= +%= -%= *%= +\|= -\|= *\|=`. Giá trị phải vừa kiểu của biến: `c = u8(c + 1);` với `var c: u8` |
| `p[i] = e;` `p.f = e;` `p[i].f = e;` | Ghi bộ nhớ. Tính vế phải TRƯỚC rồi mới tới chỗ ghi (như Rust). Hằng tự lấy kiểu của ô đích (`buf[i] = '=';` với ô u8) |
| `f(a, b);` | Gọi hàm bỏ kết quả |
| `if c { … } else if c2 { … } else { … }` | `c` phải là điều kiện (so sánh, `&&`, `||`, `!`); với số thì viết `x != 0` |
| `while c invariant … decreases … { … }` | Xem mục vòng lặp |
| `for i in a..b invariant … { … }` | `i` chạy a, a+1, …, b−1. a, b tính MỘT lần trước vòng; a >= b thì không chạy vòng nào |
| `break;` / `continue;` | Thoát / sang vòng sau của vòng trong cùng (`continue` trong `for` vẫn tăng `i`) |
| `return e;` / `return;` | Có câu lệnh sau `return` / `break` / `continue` là lỗi |

Hàm trả con trỏ độ dài tĩnh (`-> ptr<u64, 17>`, `ptr<L, HẰNG>`) gọi được: `let z = mbr_num(s, 2);` rồi dùng `z` như
tham số con trỏ. Hàm trả con trỏ có độ dài theo tham số (`ptr<L, n>`) thì chưa gọi được.

**Gọi hàm phải đứng riêng.** Chỉ viết được `let x = f(..);`, `f(..);`, `return f(..);` hoặc `p[i] = f(..);`.
Khi cần lồng, viết `let t = f(x); … t + 1`. Nhờ vậy thứ tự tác dụng phụ luôn rõ.

## Biểu thức (độ ưu tiên giống Rust, từ thấp tới cao)

| Phép | Nghĩa |
|---|---|
| `\|\|` `&&` | **Ngắn mạch.** `i < n && a[i] == x` không đọc `a[i]` khi `i >= n` |
| `== != < <= > >=` | **Không dấu**, không nối tiếp được (`a < b < c` là lỗi). Có dấu: `lt_s(a,b)` `le_s` `gt_s` `ge_s` |
| `\|` `^` `&` | Phép bit |
| `<< >>` | Dịch (Z3 chứng minh số bit < 64); `>>` là dịch logic |
| `+ - *` `/ %` | **Có kiểm**: Z3 phải chứng minh không tràn / không chia 0 |
| `+% -% *%` | Quay vòng mod 2^64 (hash, checksum, bù hai) |
| `+\| -\| *\|` | Bão hòa (kẹp ở 0 / 2^64−1) |
| `!c` `~x` | Phủ định điều kiện / đảo bit |
| `p[i]` `p[a..b]` `p.f` `p[i].f` | Đọc phần tử / cắt (`p[x..x + K]` có độ dài tĩnh K) / đọc trường |
| `u8(x)` `u16(x)` `u32(x)` | Thu hẹp **có kiểm**: Z3 phải chứng minh `x` vừa. Không cắt bớt như `as` của Rust. Muốn cắt thì viết `u8(x & 0xff)` |
| `u64(x)` | Mở rộng |
| `mulhi(a, b)` | 64 bit cao của tích 128 bit |
| `addr(DATA)` | Con trỏ tới data tĩnh |
| `DATA.len` `Layout.trường` | Hằng: số phần tử của data / offset của trường (tên viết HOA là hằng, kể cả trong đặc tả) |
| `'a'` `'\n'` `0x1f` `1_000` | Hằng ký tự / hex / có gạch dưới |

Không có số âm. Dùng `0 -% x` để lấy bù hai.

## Đặc tả: `requires` / `ensures`

- Viết sau chữ ký hàm, trước `{`. Nhiều mệnh đề cách nhau bằng dấu phẩy hoặc lặp lại từ khoá.
- `ensures` gọi giá trị trả về là `result`.
- Có thể dùng so sánh, `lt_s/le_s/gt_s/ge_s` (có dấu), `&& || !`, `==>` (kéo theo), `<==>` (tương đương), phép bit,
  `/ %`, `<< >>`, `+% -% *%`. Tên trong đặc tả chỉ là tham số, `result` hoặc hằng HOA.
- `+ - *` bị **cấm** trong đặc tả cho tới P3. Trong mã chúng có kiểm tràn, còn đặc tả hiện tính trên bit-vector quay
  vòng, nên cùng một ký hiệu sẽ mang hai nghĩa. Viết `+%` nếu chấp nhận quay vòng.
- Đặc tả chưa đọc được bộ nhớ (`a[i]`) và chưa gọi được hàm. Phần này thuộc P3 (`forall`, `old`, hàm spec).

## Vòng lặp: `invariant` / `decreases`

```rust
fn find(n: u64, a: ptr<u8, n>, x: u8) -> u64
    ensures result <= n
{
    var i = 0;
    while i < n invariant i <= n {      // nhiều invariant: cách bằng dấu phẩy
        if a[i] == x { break; }
        i += 1;
    }
    return i;                            // biết i <= n (invariant) — KHÔNG biết i == n vì có break
}

fn gcd(a: u64, b: u64) -> u64 {
    var x = a;
    var y = b;
    while y != 0 decreases y {           // decreases: số không dấu giảm ngặt mỗi vòng
        let m = x % y;
        x = y;
        y = m;
    }
    return x;
}
```

- Z3 không đoán điều gì đúng qua các vòng: sau vòng lặp (và trong thân) chỉ biết **invariant**, điều kiện vòng và
  những gì đúng trước vòng với các biến KHÔNG bị gán trong thân. Thiếu invariant thường làm `p[i]` hoặc `ensures` không
  chứng minh được.
- Invariant phải đúng khi vào vòng và được giữ sau mỗi vòng (cả cạnh `continue`). Lỗi nói rõ trường hợp nào:
  `invariant #2 sai ngay khi vào vòng` (chỉ vào dòng `while`) hoặc `… không còn đúng sau một vòng` (chỉ vào `}` hoặc
  `continue`). Số thứ tự đếm từ 1 theo thứ tự viết.
- Sau `while c` không có `break`: biết thêm `!c`. Ví dụ với `while i < n invariant i <= n` thì sau vòng có `i == n`.
- `decreases` không bắt buộc. Thiếu nó, verifier tự thử `i`, `n - i`, `i - n` với biến của vòng. Thử không ra thì
  báo `Không chứng minh được vòng lặp dừng: thêm decreases …`. `for` tự có `decreases b - i` và
  `invariant a <= i <= b`.
- Trong `invariant` / `decreases` dùng được mọi biến đang thấy (tham số, `let`, `var`, chỉ số `for`), với cùng luật
  như đặc tả. Vì thế `+ - *` cũng bị cấm ở đây: viết `decreases n -% i` (đúng khi đã có `invariant i <= n`).
- Không có `loop` (vòng vô hạn). Viết `while <điều kiện> decreases …` và thoát bằng `break` / `return`.
- Không che tên biến `var`: `let x` / `var x` trùng tên một biến `var` đang thấy là lỗi (để mỗi tên chỉ một biến).

Hạ xuống SSA (xem `light lower`): đầu vòng là block có tham số cho chỉ số `for` và mọi biến `var` bị gán trong thân.
`@inv` / `@dec` gắn ở đó. Sau `if`, biến được gán khác nhau ở hai nhánh thành tham số của block nối. Hoán đổi kiểu
`let t = a; a = b; b = t;` được chép qua biến tạm, để cạnh lùi không bị lỗi parallel-copy.

Phản ví dụ hiện còn hiện tên phiên bản SSA của biến (`i`, `i_2`, `i_3`: giá trị lúc vào hàm, ở đầu vòng, sau `i += 1`).
