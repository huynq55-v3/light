; is_sorted: inv forall j in 0..i-1: a[j] <= a[j+1]; thân: a[i-1] <= a[i] -> giữ với i+1
(declare-const M (Array Int Int)) (declare-const a Int) (declare-const n Int) (declare-const i Int)
(define-fun A ((t Int)) Int (+ a (* 8 t)))
(assert (and (<= 0 a) (<= 1 i) (< i n)))
(assert (forall ((j Int)) (! (=> (and (<= 0 j) (< (+ j 1) i)) (<= (select M (A j)) (select M (A (+ j 1))))) :pattern ((select M (A j))))))
(assert (<= (select M (A (- i 1))) (select M (A i))))
(assert (not (forall ((j Int)) (=> (and (<= 0 j) (< (+ j 1) (+ i 1))) (<= (select M (A j)) (select M (A (+ j 1))))))))
(check-sat)
