# Cú pháp B của Light (file `.lt`) — tham chiếu

Cú pháp kiểu Rust, được front-end (`src/front.rs`) **hạ xuống SSA `.lit`**. Verifier Z3 và bộ sinh mã chỉ thấy SSA nên
mọi bảo đảm của Light giữ nguyên. Lỗi kiểm chứng chỉ đúng `file.lt:dòng:cột`, kèm dòng nguồn và dấu `^`.

```
light check  app.lt            # kiểm chứng (thêm --json cho AI; trường "at" = dòng:cột)
light lower  app.lt [--origins] # xem SSA sinh ra (và vị trí gốc của từng dòng)
```

Trạng thái: **P2**, gồm biểu thức, `let` / `var`, gán, bộ nhớ, gọi hàm, `if/else`, `while` / `for`, `break` /
`continue`, `return`, đặc tả không lượng từ và `invariant` / `decreases`. P3 (đang làm): đã có số học toán học, `a[i]`,
`old(...)`, `forall` / `exists`, `spec fn`, `assert` trong đặc tả. Khung gọi hàm theo vùng và bổ đề chưa có (xem
`ROADMAP.md`).

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
- Trong đặc tả, `+ - * / %` là **số học toán học** (số nguyên không giới hạn, không tràn, không quay vòng). Ví dụ
  `ensures result == (lo + hi) / 2` đúng nghĩa trung bình kể cả khi `lo + hi` vượt 2^64. Trong mã, chúng có kiểm tràn.
  Viết `+% -% *%` nếu muốn phép quay vòng mod 2^64. `/ %` trên số không âm, chia cho 0 là không xác định (đừng viết).
- Riêng `decreases` dùng phép bit-vector (`n - i` hiểu là `n -% i`). Mọi cách hiểu đều đúng cho chứng minh dừng.
- Mệnh đề có số học toán học được chứng minh bởi **checker số nguyên** (`src/verify_int.rs`). Checker này chạy sau
  checker bit-vector, và chỉ chạy khi cần. Checker bit-vector vẫn là bên duy nhất chứng minh an toàn (tràn, biên,
  chia 0, dừng). Mệnh đề không có phép bit lồng quanh số học thì checker bit-vector tính được chính xác nên vẫn
  dùng làm giả thiết. Ngược lại (có `/ %` toán học), checker bit-vector bỏ qua mệnh đề đó, nên mã phải tự kiểm
  lúc chạy những gì an toàn cần (xem `bench/p3/13_base64_enc.lt`).
- Đặc tả đọc được bộ nhớ: `a[i]` là phần tử i của con trỏ `a` (tham số, hoặc biến đang thấy trong invariant).
  Trong requires, `a[i]` là giá trị lúc vào hàm. Trong ensures là lúc ra, trong invariant là ở đầu vòng.
  `old(e)` tính `e` trên bộ nhớ lúc vào hàm.
- Lượng từ trên khoảng nửa mở: `forall j in lo..hi: điều_kiện` và `exists j in lo..hi: điều_kiện`. Có thể lồng nhau,
  ví dụ mảng đã sắp xếp là `forall j in 0..n: forall k in j..n: a[j] <= a[k]`. Hãy viết dạng hai biến này: dạng
  "từng cặp kề nhau" `a[j-1] <= a[j]` cần quy nạp, Z3 không tự suy ra được.
- Hàm không trả giá trị vẫn có ensures về bộ nhớ, ví dụ `ensures forall t in 0..n: a[t] == old(a[n - 1 - t])`.
- Mô hình bộ nhớ (checker số nguyên, xem `bench/p3.md`):
  - Hai con trỏ có thể trỏ cùng chỗ, kể cả khi khác kiểu. Ghi `p[0]` thì không còn biết gì về `q[0]` (của bất kỳ
    con trỏ nào khác), trừ khi đặc tả nói `q` khác `p`.
  - Ghi qua kiểu u8 thì mọi mảng kiểu khác (u64, ...) coi như đã đổi.
  - Lệnh gọi hàm làm mất thông tin về các kiểu bộ nhớ mà hàm đó (hoặc hàm nó gọi) có ghi. Hàm không ghi gì thì
    giữ nguyên.
  - Trong vòng lặp có ghi, invariant phải nói rõ phần nào đã đổi và phần nào giữ nguyên.
- Sự thật về bộ nhớ chỉ checker số nguyên biết. Checker an toàn (tràn số, biên) không dùng được chúng: `requires
  a[0] < 1000` không giúp chứng minh `a[0] + a[0]` không tràn. Khi đó kiểm bằng `if`, hoặc dùng `+%`.
- Hàm spec (chỉ dùng trong đặc tả, không sinh mã), giá trị là số nguyên toán học:
  ```
  spec fn sum(n: u64, a: ptr<u64, n>, k: u64) -> int
      decreases k
  {
      if k == 0 { 0 } else { sum(n, a, k - 1) + a[k - 1] }
  }
  ```
  - Thân là MỘT biểu thức. `if c { x } else { y }` là biểu thức, chỉ dùng trong đặc tả.
  - Hàm spec chỉ gọi được chính nó, hoặc hàm spec khai báo trước nó. Đệ quy thì bắt buộc có `decreases`: verifier
    chứng minh nó >= 0 và giảm ngặt ở mỗi lời gọi đệ quy. Nếu không, định nghĩa có thể mâu thuẫn (`f(k) == f(k) + 1`).
  - Verifier mở định nghĩa tối đa 2 tầng mỗi chỗ dùng. Nên viết invariant dạng quy nạp: `s == sum(n, a, i)`, rồi
    bước `sum(n, a, i + 1) == sum(n, a, i) + a[i]` Z3 tự thấy.
  - Hàm có ghi bộ nhớ: áp hàm spec lên `old(...)`, ví dụ `out[k] == old(sum(n, a, k + 1)) % (M + 1)`. Bộ nhớ lúc
    vào không đổi, nên không cần chứng minh "ghi chỗ khác không làm đổi tổng" (Z3 không tự quy nạp được).
- `assert e;` là câu lệnh đặc tả. Verifier chứng minh `e` tại đó rồi dùng nó làm giả thiết. Dùng để gợi ý cho Z3
  một hạng nó không tự nghĩ ra, ví dụ `assert dec(n, s, i + 1) > M;` trước `return 0` khi tràn
  (`bench/p3/07_parse_dec.lt`).
- Khi đặc tả có hàm spec đệ quy, đặc tả sai thường bị từ chối với "không kết luận" (sau 10 s) thay vì có phản ví dụ.
  Lý do: Z3 khó dựng mô hình cho định nghĩa đệ quy. Bị từ chối vẫn là bị từ chối, nhưng muốn có phản ví dụ thì tách
  mệnh đề nhỏ hơn hoặc thêm `assert`.
- Chưa có: `p.trường` / `p[a..b]` trong đặc tả, `modifies`, khung theo vùng cho lệnh gọi, bổ đề (lemma) quy nạp.

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
