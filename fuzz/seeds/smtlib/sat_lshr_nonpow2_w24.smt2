(set-logic QF_BV)
; soundness regression (0.22.1): non-power-of-two widths must not come back unsat
(declare-const y (_ BitVec 24))
(assert (= y #x000100))
(assert (= (bvlshr y #x000008) #x000001))
(check-sat)
