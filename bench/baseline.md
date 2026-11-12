# Light-Bench — số liệu mốc P0 (cú pháp SSA hiện tại, 2026-11-12)

Đo bằng `python3 tools/bench.py metrics`; tính đúng bằng `python3 tools/bench.py test` (15 × 300 ca, tất cả qua; so cả giá trị trả về lẫn nội dung bộ đệm ra —
đã thử mô hình bị làm sai ở từng bài có bộ đệm ra thì đều trượt).

| bài | hàm | dòng | token | lệnh | @req/@ens | @inv/@dec | kiểm chứng trượt trước khi qua |
|---|---|---|---|---|---|---|---|
| 01 sum_q | 1 | 16 | 57 | 9 | 0 | 1 | 0 |
| 02 max_q | 1 | 19 | 74 | 11 | 1 | 1 | 0 |
| 03 find_q | 1 | 21 | 68 | 11 | 1 | 1 | 0 |
| 04 eq_b | 1 | 25 | 90 | 13 | 3 | 1 | 0 |
| 05 strnlen_b | 1 | 19 | 64 | 10 | 1 | 1 | 0 |
| 06 count_lines_b | 1 | 19 | 71 | 10 | 1 | 2 | 0 |
| 07 parse_dec | 1 | 37 | 144 | 25 | 1 | 1 | 0 |
| 08 fmt_dec | 1 | 48 | 193 | 28 | 3 | 6 | 0 |
| 09 reverse_q | 1 | 23 | 89 | 14 | 0 | 3 | 0 |
| 10 prefix_sum_q | 1 | 19 | 72 | 11 | 1 | 1 | 0 |
| 11 is_sorted_q | 1 | 24 | 84 | 14 | 1 | 1 | 0 |
| 12 lower_bound_q | 1 | 26 | 96 | 14 | 1 | 3 | 0 |
| 13 base64_enc | 3 | 112 | 460 | 77 | 8 | 4 | 7 (1 lỗi kiểu, 5 hết giờ, 1 phản ví dụ thật) |
| 14 gcd | 1 | 15 | 66 | 6 | 1 | 2 | 2 (1 thiếu @dec, 1 hết giờ → sửa verifier) |
| 15 isqrt | 1 | 24 | 82 | 12 | 1 | 3 | 1 hết giờ → bỏ đặc tả phi tuyến |
| **tổng** | 17 | **447** | **1710** | 265 | 24 | 31 | **10** |

**Lưu ý:** cột "trượt" do chính người viết bộ mẫu (Claude, phiên 2026-11-12, n = 1) tự đếm, không phải phép đo độc
lập. Lượt đo P1/P2 nên do một phiên mới chỉ nhận `bench/tasks.md`.

## Mức đặc tả: 0/15 bài đạt đặc tả mong muốn

| mức | bài |
|---|---|
| Đặc tả mong muốn **không viết được** (cần nội dung bộ nhớ, forall/exists, old, hàm spec) | 01–12, 13 (phần nội dung), 14 |
| Viết được nhưng **Z3 hết giờ** (bit-vector 64-bit) | 13 (độ dài `4*ceil(n/3)`), 15 (`r*r <= x < (r+1)^2`) |
| Đặc tả mong muốn chứng minh được hôm nay | không có |

Đặc tả hôm nay chỉ là cận (`r <= n`, `r <= 1`) và an toàn bộ nhớ. Một hàm trả hằng 0 (hoặc không làm gì, với bài void) vẫn qua đặc tả hôm nay ở 13/15 bài (trừ 08 và 14).

## Phát hiện

1. **Cú pháp không phải nút thắt chính khi viết.** 12/15 bài qua kiểm chứng ngay lần đầu. Cái giá nằm ở độ dài:
   trung bình 30 dòng / 114 token mỗi bài, base64 tới 112 dòng. Mỗi `load` tốn 2 lệnh (`slice` + `load`), mỗi
   nhánh nạp tuỳ chọn cần thêm block trung gian (vì `br` không mang đối số).
2. **Ngôn ngữ đặc tả là khoảng trống lớn nhất.** Không bài nào nói được "kết quả đúng". Đây chính là P3.
3. **Số học bit-vector làm Z3 hết giờ.** 7/10 lần trượt là hết giờ, không phải phản ví dụ, nên người viết không biết
   phải sửa gì. Ví dụ đo riêng: "`n % 3 != 0` ⇒ `(n+2)/3 == n/3 + 1`" mất 14–27 giây với bit-vector 64-bit, nhưng
   0,03 giây với số nguyên. Hệ quả là base64 phải kiểm tra chỗ trống lúc chạy thay cho chứng minh. Đề xuất cho P3:
   biểu thức đặc tả dùng số nguyên toán học (`int`) như Verus/Dafny.
4. **Lỗi kiểu với hằng số:** `store %p 0 61` bị từ chối vì hằng mặc định là bv64; phải viết `61:bv8` dù trường
   đích là bv8. Nên suy kiểu hằng từ trường đích (P1).

## Thay đổi verifier/parser đi kèm P0

- Lỗi Z3 giờ có thêm dòng `tại file:dòng` của chính lệnh gây lỗi (kể cả sau khi `*_sat`/`*_ovf` bị hạ thành nhiều
  lệnh). JSON có thêm trường `at` và `source` (dòng gốc, tên chưa đổi). `origin` vẫn là dòng khai báo hàm.
- `def` trùng tên (hoặc trùng `Layout.trường` / `TÊN.len`) giờ là lỗi; trước đây lặng lẽ lấy giá trị sau cùng.
- Bổ đề cho `urem`/`udiv` (có điều kiện `y != 0`): `x urem y < y`, `x urem y <= x`, `x udiv y <= x`. Nhờ vậy vòng
  Euclid (bài 14) được chứng minh dừng. Hai test must_fail (`udiv_lemma_off_path`, `urem_lemma_off_path`) bảo đảm bổ đề
  không giả định gì trên nhánh không chia. Đã thử: bỏ điều kiện `y != 0` thì cả hai test đều (sai) qua, nên chúng bắt được lỗi đó.
