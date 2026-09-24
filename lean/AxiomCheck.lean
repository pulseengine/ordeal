/-
Axiom-cleanliness gate (issue #137 / TR-042).

docs/formal-verification.md and lean/README.md claim the soundness results
depend ONLY on Lean's three classical axioms — propext, Classical.choice,
Quot.sound — with no `sorryAx` and no `native_decide` (`ofReduceBool`).
Before this file, that claim was asserted in prose and checked nowhere: a
proof rewritten with `native_decide` (re-widening the TCB to the Lean
compiler) or a stray `axiom` would have passed every gate.

Each `#guard_msgs` below pins the EXACT axiom list of a capstone theorem;
any new axiom changes the message and fails elaboration — and this file is
a default lake target, so the required Lean CI job fails with it. The
sorry budget is guarded separately (ci.yml); this file guards everything
`sorry`-shaped guards miss.
-/
import Sound
import SatWitness
import BlasterProof
import BlasterArith
import BlasterCmp
import BlasterShift
import BlasterMul
import BlasterDiv

-- The checker soundness chain (Sound.lean).
/-- info: 'kernel.spec.lrat_check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.spec.lrat_check_sound

/-- info: 'kernel.spec.pure_check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.spec.pure_check_sound

/-- info: 'kernel.spec.kernel_refines_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.spec.kernel_refines_pure

-- One capstone rule theorem per blaster proof development.
/-- info: 'blast_kernel.spec.blast_xor_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blast_kernel.spec.blast_xor_bitvec

/-- info: 'blast_kernel.spec.blast_ult_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blast_kernel.spec.blast_ult_bitvec

/-- info: 'blast_kernel.spec.blast_sign_ext_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blast_kernel.spec.blast_sign_ext_bitvec

/-- info: 'blast_kernel.spec.blast_rotr_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blast_kernel.spec.blast_rotr_bitvec

/-- info: 'blast_kernel.spec.blast_mul_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blast_kernel.spec.blast_mul_bitvec

/-- info: 'blast_kernel.spec.blast_urem_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blast_kernel.spec.blast_urem_bitvec

-- The SAT-witness checker (SatWitness.lean, TR-044 / VER-039). These pins
-- are what surfaced the TR-038 regression: `clause_satisfied` used
-- `i32::unsigned_abs`, which the pinned Aeneas extracts as an opaque
-- `axiom`, and `check_sat_sound` listed it here. The kernel now spells
-- `|lit|` once (`lit_var`); ci.yml also fails on any `^axiom` in a
-- generated model.
/-- info: 'kernel.spec.check_binding_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.spec.check_binding_sound

/-- info: 'kernel.spec.check_sat_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.spec.check_sat_sound

/-- info: 'kernel.spec.verdicts_exclusive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.spec.verdicts_exclusive
