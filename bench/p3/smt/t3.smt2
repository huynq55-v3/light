; mảng con: b = a[3..], ghi b[k]; đặc tả nói theo a: forall j<3: a[j] không đổi
(declare-const M0 (Array Int Int)) (declare-const a Int) (declare-const n Int) (declare-const k Int) (declare-const v Int)
(define-fun A ((t Int)) Int (+ a (* 8 t)))
(define-fun b () Int (+ a (* 8 3)))
(assert (and (<= 0 a) (<= 4 n) (<= 0 k) (< k (- n 3))))
(define-fun M () (Array Int Int) (store M0 (+ b (* 8 k)) v))
(assert (not (and (forall ((j Int)) (=> (and (<= 0 j) (< j 3)) (= (select M (A j)) (select M0 (A j))))) (= (select M (A (+ k 3))) v))))
(check-sat)
