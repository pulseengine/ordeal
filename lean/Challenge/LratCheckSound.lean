/- COMPARATOR CHALLENGE: the trusted statement of the checker soundness theorem.

   `lake exe comparator` (lean/comparator/lrat_check_sound.json) checks that
   `kernel.spec.lrat_check_sound` in the solution module `Sound` proves EXACTLY
   this statement, using no axiom beyond propext / Quot.sound / Classical.choice,
   and that the Lean kernel (and nanoda, where it runs) accepts it.

   The statement must be elaborated in the same scope as the proof: imports
   only the generated model and the CNF semantics (CnfSpec), never Sound.
   Editing this file or its imports changes what ordeal claims; such a change
   is flagged for the owner's review (scripts/check_challenge_files.sh). -/
import CnfSpec

open Aeneas Aeneas.Std Result

namespace kernel.spec

theorem lrat_check_sound
    (cnf : Slice (alloc.vec.Vec Std.I32)) (steps : Slice Step)
    (hfit : cnf.val.length + steps.val.length ≤ Std.Usize.max)
    (h : kernel.check_steps cnf steps = ok (core.result.Result.Ok ())) :
    unsat (cnf.val.map (fun c => c.val)) :=
  sorry

end kernel.spec
