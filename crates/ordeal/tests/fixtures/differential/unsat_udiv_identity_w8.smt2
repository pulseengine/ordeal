(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(assert (distinct (bvudiv a #x01) a))
(check-sat)
