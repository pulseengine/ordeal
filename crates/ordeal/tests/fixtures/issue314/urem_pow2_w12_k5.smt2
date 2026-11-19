(set-logic QF_BV)
(declare-fun x () (_ BitVec 12))
(assert (distinct (bvurem x #x020) ((_ zero_extend 7) ((_ extract 4 0) x))))
(check-sat)
