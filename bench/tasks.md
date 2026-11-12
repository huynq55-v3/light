# Light-Bench — đề bài

15 bài nhỏ để đo mức thân thiện với AI của Light qua từng giai đoạn (P0 → P3). Đề bài **độc lập ngôn ngữ**: một lượt đo
mới (người hoặc AI, phiên mới, không xem lời giải cũ) chỉ nhận phần *Đề* + *Giao diện* và phải viết lại bằng cú pháp
của giai đoạn đang đo. Lời giải P0 (cú pháp SSA hiện tại) ở `bench/today/`, số liệu ở `bench/baseline.md`.

Kiểm tra tính đúng: `python3 tools/bench.py test` (mã máy thật so với mô hình Python, 300 ca/bài kể cả ca biên).
Verifier hiện tại chỉ chứng minh được đặc tả yếu nên kiểm thử là lưới an toàn cho chính bộ mẫu.

Quy ước: mảng qword `a[0..n)` là cặp `(n, ptr<u64, n>)`, mảng byte tương tự với `u8`. Đặc tả mong muốn viết bằng cú
pháp (B) dự kiến (`forall j in a..b`, `old(x)`, `==>`, `<==>`); `+ * /` là số học toán học (không tràn).
Cột **Hôm nay** = đặc tả mạnh nhất Z3 chứng minh được ở P0; **Khoảng trống** = thứ còn thiếu để đạt đặc tả mong muốn.

| # | Đề | Giao diện | Đặc tả mong muốn | Hôm nay | Khoảng trống |
|---|---|---|---|---|---|
| 01 | Tổng các phần tử, quay vòng mod 2^64 | `sum_q(n, a) -> u64` | `r == sum(j in 0..n: a[j]) % 2^64` | không có gì | hàm spec đệ quy `sum`, nội dung bộ nhớ |
| 02 | Phần tử lớn nhất, mảng khác rỗng | `max_q(n, a) -> u64`, cần `n >= 1` | `(forall j in 0..n: a[j] <= r) && (exists j in 0..n: a[j] == r)` | `@req n >= 1` | forall/exists trên bộ nhớ |
| 03 | Chỉ số đầu tiên có `a[j] == x`, không có thì `n` | `find_q(n, a, x) -> u64` | `r <= n && (forall j in 0..r: a[j] != x) && (r < n ==> a[r] == x)` | `r <= n` | forall trên bộ nhớ |
| 04 | `a[0..k) == b[0..k)`? (1/0) | `eq_b(n, a, m, b, k) -> u64`, cần `k <= n, k <= m` | `r == 1 <==> forall j in 0..k: a[j] == b[j]` (và `r <= 1`) | `r <= 1` | forall, `<==>` |
| 05 | Vị trí byte 0 đầu tiên, không có thì `n` | `strnlen_b(n, s) -> u64` | `r <= n && (forall j in 0..r: s[j] != 0) && (r < n ==> s[r] == 0)` | `r <= n` | forall |
| 06 | Đếm byte `'\n'` (như `wc -l`) | `count_lines_b(n, s) -> u64` | `r == count(j in 0..n: s[j] == 10)` | `r <= n` | hàm spec `count` |
| 07 | `s[0..n)` là số thập phân hợp lệ (n ≥ 1, chỉ chữ số, < 2^64) → ghi giá trị vào `out[0]`, trả 1; ngược lại trả 0, không ghi | `parse_dec(n, s, out: ptr<u64,1>) -> u64` | `r == 1 <==> (n >= 1 && (forall j in 0..n: is_digit(s[j])) && dec(s, n) < 2^64)`; `r == 1 ==> out[0] == dec(s, n)`; `r == 0 ==> out[0] == old(out[0])` | `r <= 1` | hàm spec `dec`, `old`, `modifies` |
| 08 | Ghi số thập phân của `v` (không có số 0 đứng đầu, "0" cho 0) vào `buf`, trả số chữ số | `fmt_dec(cap, buf, v) -> u64`, cần `cap >= 20` | `r == ndigits(v) && dec(buf, r) == v && (r > 1 ==> buf[0] != '0')` | `1 <= r <= 20` | hàm spec, nội dung bộ đệm ra |
| 09 | Đảo ngược tại chỗ | `reverse_q(n, a)` | `forall j in 0..n: a[j] == old(a[n-1-j])`, `modifies a[0..n)` | không có gì | `old`, `modifies`, forall |
| 10 | `out[k] = (a[0] + … + a[k]) mod 2^64` | `prefix_sum_q(n, a, m, out)`, cần `n <= m` | `forall k in 0..n: out[k] == sum(j in 0..k+1: a[j]) % 2^64`, `modifies out[0..n)` | `@req n <= m` | hàm spec `sum`, `modifies` |
| 11 | Mảng không giảm? (1/0) | `is_sorted_q(n, a) -> u64` | `r == 1 <==> forall j in 0..n-1: a[j] <= a[j+1]` | `r <= 1` | forall |
| 12 | Mảng đã sắp: chỉ số nhỏ nhất `j` có `a[j] >= x`, không có thì `n` | `lower_bound_q(n, a, x) -> u64`, cần mảng đã sắp | `@req forall j in 0..n-1: a[j] <= a[j+1]`; `r <= n && (forall j in 0..r: a[j] < x) && (forall j in r..n: a[j] >= x)` | `r <= n` | forall cả ở `requires` |
| 13 | Base64 (RFC 4648, có `=`) của `s[0..n)` vào `out` | `base64_enc(n, s, cap, out) -> u64`, cần `cap >= 4*ceil(n/3)` | `r == 4 * ((n + 2) / 3) && forall j in 0..r: out[j] == b64(s, n)[j]` | `r <= cap && r % 4 == 0` (cắt bớt lúc chạy nếu thiếu chỗ) | **độ dài** viết được nhưng Z3 hết giờ (xem dưới); nội dung cần hàm spec |
| 14 | Ước chung lớn nhất (Euclid), `gcd(0,0) = 0` | `gcd(a, b) -> u64` | `r == gcd_spec(a, b)` (hoặc `a % r == 0 && b % r == 0 && forall d: (a%d==0 && b%d==0) ==> d <= r`) | `r != 0` trừ khi `a == b == 0` | bất biến `gcd(x,y) == gcd(a,b)` cần hàm spec / lemma |
| 15 | Căn bậc hai nguyên: `r` lớn nhất có `r*r <= x` | `isqrt(x) -> u64` | `r*r <= x && x < (r+1)*(r+1)` | `r < 2^32` | **viết được hôm nay** nhưng Z3 hết giờ (nhân phi tuyến 64-bit) |

## Hai bài viết được đặc tả nhưng Z3 không chứng minh nổi

Hai bài này cho thấy khoảng trống không chỉ nằm ở cú pháp. Phần nặng là cách verifier mã hoá số học.

- **Bài 13 (độ dài base64).** Đặc tả `r == 4 * ((n + 2) / 3)` hết giờ với `udiv`. Dạng tuyến tính không chia
  (`r % 4 == 0 && 4n <= 3r <= 4n + 8`) cũng hết giờ.
  - Thử riêng bằng Z3: cùng bài toán "`n % 3 != 0` ⇒ `(n+2)/3 == n/3 + 1`" mất **14–27 giây** với bit-vector 64-bit
    (bit-blast), còn với số nguyên toán học (LIA) chỉ mất **0,03 giây**.
  - Hướng xử lý: các hàng rào đặc tả dịch sang `Int` khi đã chứng minh được không tràn. Verus và Dafny đều làm vậy:
    `int` toán học trong spec, còn ràng buộc tràn nằm ở mã.
- **Bài 15 (isqrt).** `r*r <= x < (r+1)*(r+1)` là nhân phi tuyến 64×64 bit, vượt quá khả năng bit-blast trong 10 giây.
  Kể cả khi dịch sang số nguyên, phép nhân phi tuyến (NIA) vẫn khó. Thường phải có lemma hoặc gợi ý.
