/- The CNF semantics `lrat_check_sound` is stated in: what "unsatisfiable"
   means for the checker's input. Definitions only, no proofs, so the
   comparator challenge (lean/Challenge/LratCheckSound.lean) can import the
   statement's vocabulary without importing the proof (Sound.lean). The
   spec-review notes on these definitions are in Sound.lean's header.

   This file is part of the TRUSTED STATEMENT of the soundness theorem: a
   change here changes what the theorem says (scripts/check_challenge_files.sh).
-/
import Kernel

open Aeneas Aeneas.Std Result

namespace kernel.spec

/- ══════════════════════════ SEMANTICS ══════════════════════════ -/

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

end kernel.spec
