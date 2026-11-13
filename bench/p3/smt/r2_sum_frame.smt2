; prefix_sum: ghi H' = store H (a+8i) v; sum(H', a, i) == sum(H, a, i) cần khung (ô ghi nằm NGOÀI đoạn được tổng) -> quy nạp: Z3 không tự làm
; cách đo: bổ đề khung dạng forall có pattern: (forall k <= i: sum(store H p v, a, k) == sum(H, a, k)) khi p >= a+8i
(declare-fun sum ((Array Int Int) Int Int) Int)
(assert (forall ((H (Array Int Int)) (a Int) (k Int)) (! (= (sum H a k) (ite (<= k 0) 0 (+ (sum H a (- k 1)) (select H (+ a (* 8 (- k 1))))))) :pattern ((sum H a k)))))
(declare-const H (Array Int Int)) (declare-const a Int) (declare-const i Int) (declare-const v Int)
(assert (<= 0 i))
(define-fun H2 () (Array Int Int) (store H (+ a (* 8 i)) v))
(assert (not (= (sum H2 a i) (sum H a i))))
(check-sat)
