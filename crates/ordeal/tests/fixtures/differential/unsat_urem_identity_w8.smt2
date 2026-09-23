(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(assert (distinct (bvurem a #x01) #x00))
(check-sat)
