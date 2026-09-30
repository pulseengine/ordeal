(set-logic QF_BV)
; soundness regression (0.22.1): a valid identity at a non-power-of-two width stays certified unsat
(declare-const x (_ BitVec 5))
(assert (distinct ((_ rotate_left 2) ((_ rotate_right 2) x)) x))
(check-sat)
