(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (distinct (bvudiv x #x10) (concat #x0 ((_ extract 7 4) x))))
(check-sat)
