(declare-const x (_ BitVec 3))
(assert (= (bvshl x #b001) #b010))
(check-sat)
