(set-logic QF_BV)
; #191 evidence: rotate-left-by-1 equals its shift decomposition at width 12 (non-power-of-two, the #182 class). Z3: unsat.
(declare-const x (_ BitVec 12))
(declare-const b (_ BitVec 12))
(assert (bvult b #x00c))
(assert (distinct ((_ rotate_left 1) (bvlshr x b)) (bvor (bvshl (bvlshr x b) #x001) (bvlshr (bvlshr x b) #x00b))))
(check-sat)
