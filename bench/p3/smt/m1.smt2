; eq_b: inv forall j < i: M[a+j] == M[b+j]; thân: va == vb -> i+1 giữ inv. Bộ nhớ không đổi trong vòng.
(declare-const M (Array (_ BitVec 64) (_ BitVec 8)))
(declare-const a (_ BitVec 64)) (declare-const b (_ BitVec 64)) (declare-const i (_ BitVec 64)) (declare-const k (_ BitVec 64))
(assert (bvult i k)) (assert (bvult k #x0000100000000000)) (assert (bvult a #x0000100000000000)) (assert (bvult b #x0000100000000000))
(assert (forall ((j (_ BitVec 64))) (! (=> (bvult j i) (= (select M (bvadd a j)) (select M (bvadd b j)))) :pattern ((select M (bvadd a j))))))
(assert (= (select M (bvadd a i)) (select M (bvadd b i))))
(assert (not (forall ((j (_ BitVec 64))) (=> (bvult j (bvadd i #x0000000000000001)) (= (select M (bvadd a j)) (select M (bvadd b j)))))))
(check-sat)
