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
import BlasterRotr
import BlasterTseitin
import BlasterFrame
import BlasterCompact
import BlasterDerived
import BlasterDag
import BlasterCapstone
import QueryCheck
import TermCheck

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
/-- info: 'kernel.blast_kernel.spec.blast_xor_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.blast_xor_bitvec

/-- info: 'kernel.blast_kernel.spec.blast_ult_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.blast_ult_bitvec

/-- info: 'kernel.blast_kernel.spec.blast_sign_ext_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.blast_sign_ext_bitvec

-- The shift / rotate family at EVERY width (issue #201): the three shift
-- capstones (BlasterShift.lean) and the rotate capstone (BlasterRotr.lean,
-- which composes the barrel with the divider's `blast_urem`).
/-- info: 'kernel.blast_kernel.spec.blast_shl_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.blast_shl_bitvec

/-- info: 'kernel.blast_kernel.spec.blast_lshr_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.blast_lshr_bitvec

/-- info: 'kernel.blast_kernel.spec.blast_ashr_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.blast_ashr_bitvec

/-- info: 'kernel.blast_kernel.spec.blast_rotr_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.blast_rotr_bitvec

/-- info: 'kernel.blast_kernel.spec.blast_mul_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.blast_mul_bitvec

/-- info: 'kernel.blast_kernel.spec.blast_urem_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.blast_urem_bitvec

-- The model Tseitin encoder (BlasterTseitin.lean, issue #192 phase 1): the
-- satisfiability-preservation capstone, its `unsat`-form restatement, and
-- its composition with `lrat_check_sound` (the two proven halves meeting).
/-- info: 'kernel.blast_kernel.spec.tseitin_sat_preserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.tseitin_sat_preserving

/-- info: 'kernel.blast_kernel.spec.tseitin_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.tseitin_satisfiable

/-- info: 'kernel.blast_kernel.spec.tseitin_refutes_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.tseitin_refutes_outputs

-- The derived operations as proven rules (BlasterDerived.lean, issue #192
-- phase 5 / v0.28.0): `bvnot`, `bvneg`, `bvrotl`, `bvsdiv`, `bvsrem` were
-- untrusted term rewrites until phase 5; each is now a `DagNode` whose
-- composite rule is proven against the Lean `BitVec` operation SMT-LIB
-- names (`~~~`, `-`, `rotateLeft`, `smtSDiv`, `srem`), at every width.
/-- info: 'kernel.blast_kernel.spec.blast_bvnot_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.blast_bvnot_bitvec

/-- info: 'kernel.blast_kernel.spec.blast_neg_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.blast_neg_bitvec

/-- info: 'kernel.blast_kernel.spec.blast_rotl_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.blast_rotl_bitvec

/-- info: 'kernel.blast_kernel.spec.blast_sdiv_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.blast_sdiv_bitvec

/-- info: 'kernel.blast_kernel.spec.blast_srem_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.blast_srem_bitvec

-- The term-DAG encoder, the folding + hashing pass and their composition
-- with the checker (issue #192 phase 3 / v0.26.0): `encode_sound`
-- (BlasterDag.lean), `compact_sound` (BlasterCompact.lean) and the two
-- capstones `dag_refuted` / `dag_refuted_raw` (BlasterCapstone.lean) —
-- an accepted LRAT certificate against the CNF the shipped lowering
-- pipeline produced refutes the term DAG itself.
/-- info: 'kernel.blast_kernel.spec.encode_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.encode_sound

/-- info: 'kernel.blast_kernel.spec.compact_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.compact_sound

/-- info: 'kernel.blast_kernel.spec.dag_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.dag_refuted

/-- info: 'kernel.blast_kernel.spec.dag_refuted_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.blast_kernel.spec.dag_refuted_raw

-- The query re-check (QueryCheck.lean, issue #192 phase 4): `dag_wf_spec`
-- (the well-formedness check is exactly `DagWF` + "every width fits"),
-- `check_query_sound` (an accepted query has no satisfying assignment —
-- no hypothesis beyond the acceptance) and `check_query_refutes_cnf` (the
-- returned CNF is the one the checker refuted).
/-- info: 'kernel.spec.dag_wf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.spec.dag_wf_spec

/-- info: 'kernel.spec.check_query_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.spec.check_query_sound

/-- info: 'kernel.spec.check_query_refutes_cnf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.spec.check_query_refutes_cnf

-- The model re-check (QueryCheck.lean, issue #192 phase 6 / TR-065): the
-- SAT twin of `check_query_sound` — `check_query_model_sound` (an accepted
-- input assignment makes every root true, in the SAME `dagBool` semantics)
-- and `query_verdicts_exclusive` (no query has both an accepted refutation
-- and an accepted model).
/-- info: 'kernel.spec.check_query_model_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.spec.check_query_model_sound

/-- info: 'kernel.spec.query_verdicts_exclusive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.spec.query_verdicts_exclusive

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

-- The term-to-DAG correspondence check (TermCheck.lean, issue #192 phase 7
-- / TR-069): an accepted `check_term_dag` relates the TERM a v3 bundle
-- carries to the DAG the solver built, so the two query-level capstones
-- compose up to the term — the proof refutes the term, the model
-- satisfies it — and the proven model binding ties a named value to the
-- term variable's input bits.
/-- info: 'kernel.spec.check_term_dag_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.spec.check_term_dag_sound

/-- info: 'kernel.spec.check_term_unsat_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.spec.check_term_unsat_sound

/-- info: 'kernel.spec.check_term_model_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.spec.check_term_model_sound

/-- info: 'kernel.spec.term_verdicts_exclusive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.spec.term_verdicts_exclusive

/-- info: 'kernel.spec.check_input_value_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kernel.spec.check_input_value_sound
