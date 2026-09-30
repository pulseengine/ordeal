(set-logic QF_BV)
; #191 evidence: (x << s) >> s equals x masked by (all-ones >> s) for s < 24 at width 24 (non-power-of-two). Z3: unsat.
(declare-const x (_ BitVec 24))
(declare-const s (_ BitVec 24))
(assert (bvult s #x000018))
(assert (distinct (bvlshr (bvshl x s) s) (bvand x (bvlshr #xffffff s))))
(check-sat)
