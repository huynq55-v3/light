(declare-const nb (_ BitVec 64))
(define-fun n () Int (bv2nat nb))
(assert (not (=> (not (= (mod n 3) 0)) (= (div (+ n 2) 3) (+ (div n 3) 1)))))
(check-sat)
