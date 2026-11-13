(declare-const nb (_ BitVec 64))
(assert (not (=> (not (= (bvurem nb #x0000000000000003) #x0000000000000000)) (= (bvudiv (bvadd nb #x0000000000000002) #x0000000000000003) (bvadd (bvudiv nb #x0000000000000003) #x0000000000000001)))))
(assert (bvult nb #x0fffffffffffffff))
(check-sat)
