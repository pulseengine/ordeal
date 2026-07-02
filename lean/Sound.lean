/- Specification and soundness obligation for the ordeal-lrat kernel.

   This file is HAND-WRITTEN (unlike Kernel.lean, which regen.sh generates).
   It states what "the checker is sound" means — the semantics of CNF
   satisfiability — and the theorem `lrat_check_sound` that issue #12
   discharges: kernel acceptance implies unsatisfiability of the input CNF.

   Spec-review notes (the property must be the RIGHT one, not just provable):
   * The assignment quantifies over ALL total maps from DIMACS variables to
     booleans — no finiteness assumption, no dependence on the kernel's own
     `Assignment` type.
   * Literal semantics follow DIMACS: literal `l` with variable `|l|` holds
     under σ iff σ(|l|) equals the sign of `l`. Literals 0 and i32::MIN are
     rejected KERNEL-SIDE for both the CNF (`load_cnf`) and every
     certificate clause (`apply_add`), so no assignment ever touches them
     in an accepted run — the `if` branch literal 0 takes is irrelevant to
     the theorem. (Spec review 2026-07-02: before `apply_add` validated,
     certificate clauses could smuggle literal 0 into the live set and the
     invariant below was false as stated; hardening the kernel — rejecting
     more is always sound — restored it.)
   * The theorem's CNF is the ACTUAL argument to `check_steps` (`cnf.val`,
     the mathematical list underlying the slice) — not anything derived from
     the certificate. This is what makes the parser untrusted.
   * Acceptance is the exact success value: outer Aeneas `Result.ok` (no
     panic/divergence) wrapping the inner Rust `Ok ()`.
-/
import Kernel

open Aeneas Aeneas.Std Result

namespace kernel.spec

/-- A total assignment of DIMACS variables to booleans. -/
abbrev Asn := Nat → Bool

/-- The DIMACS variable of a literal: its absolute value. -/
def litVar (lit : Std.I32) : Nat := lit.val.natAbs

/-- Literal semantics: a positive literal holds when its variable is true,
    a negative one when its variable is false. -/
def litHolds (σ : Asn) (lit : Std.I32) : Prop :=
  if 0 < lit.val then σ (litVar lit) = true else σ (litVar lit) = false

/-- Clause semantics: a disjunction — some literal holds. (The empty clause
    holds under no assignment.) -/
def clauseHolds (σ : Asn) (c : List Std.I32) : Prop :=
  ∃ lit ∈ c, litHolds σ lit

/-- CNF semantics: a conjunction — every clause holds. -/
def cnfHolds (σ : Asn) (cnf : List (List Std.I32)) : Prop :=
  ∀ c ∈ cnf, clauseHolds σ c

/-- Unsatisfiability: no assignment satisfies the CNF. -/
def unsat (cnf : List (List Std.I32)) : Prop :=
  ∀ σ : Asn, ¬ cnfHolds σ cnf

/-- One clause is semantically implied by a CNF. -/
def implies (cnf : List (List Std.I32)) (c : List Std.I32) : Prop :=
  ∀ σ : Asn, cnfHolds σ cnf → clauseHolds σ c

/- ── Proof plan (issue #12) ────────────────────────────────────────────────
   The invariant carried through `check_steps_loop`: every LIVE clause in
   `clauses` is implied (in the sense above) by the original CNF.
   * `load_cnf` establishes it (the live clauses ARE the CNF's clauses).
   * `apply_delete` preserves it (deleting only shrinks the live set).
   * `apply_add` first validates the clause (no literal 0 / i32::MIN — this
     is what makes the invariant true under EVERY σ; see the note above),
     then preserves it: `check_rup = ok` means assuming ¬C and unit-
     propagating through implied live clauses reaches a conflict, so C is
     implied (the classical RUP-soundness lemma, proved by induction over
     the hint chain with an `Assignment`-models-only-consequences invariant).
   * If the verified addition is the EMPTY clause, `implies cnf []` gives
     `unsat cnf` directly (the empty disjunction holds under no σ).
   Reasoning over the monadic model uses the Aeneas `progress` tactic and
   its loop lemmas. -/

/-- **The soundness theorem** (issue #12, TR-013/FEAT-002): if the kernel
    accepts a step list against `cnf`, then `cnf` is unsatisfiable.

    OPEN OBLIGATION: the `sorry` below is the tracked, deliberate gap — this
    library is NOT a default build target, and nothing in CI claims the
    theorem is discharged while it remains. -/
theorem lrat_check_sound
    (cnf : Slice (alloc.vec.Vec Std.I32)) (steps : Slice Step)
    (h : kernel.check_steps cnf steps = ok (core.result.Result.Ok ())) :
    unsat (cnf.val.map (fun c => c.val)) := by
  sorry

end kernel.spec
