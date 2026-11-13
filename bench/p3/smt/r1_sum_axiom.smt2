; hàm spec đệ quy sum(H, a, k) = tổng H[a + 8j], j < k — mã hoá: hàm không diễn giải + tiên đề mở một bước có pattern
; quy nạp bất biến vòng: s == sum(i) && i < n  =>  s + H[a+8i] == sum(i+1)
(declare-fun sum ((Array Int Int) Int Int) Int)
(assert (forall ((H (Array Int Int)) (a Int) (k Int)) (! (= (sum H a k) (ite (<= k 0) 0 (+ (sum H a (- k 1)) (select H (+ a (* 8 (- k 1))))))) :pattern ((sum H a k)))))
(declare-const H (Array Int Int)) (declare-const a Int) (declare-const i Int) (declare-const n Int) (declare-const s Int)
(assert (and (<= 0 i) (< i n) (= s (sum H a i))))
(assert (not (= (+ s (select H (+ a (* 8 i)))) (sum H a (+ i 1)))))
(check-sat)
