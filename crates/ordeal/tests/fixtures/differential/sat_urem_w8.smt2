(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(assert (= (bvurem a #x05) #x03))
(check-sat)
