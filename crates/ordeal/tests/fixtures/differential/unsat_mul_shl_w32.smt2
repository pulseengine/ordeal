(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(assert (distinct (bvmul x #x00000002) (bvshl x #x00000001)))
(check-sat)
