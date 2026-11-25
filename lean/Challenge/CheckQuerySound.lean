/- COMPARATOR CHALLENGE: the trusted statement of the query re-check theorem
   (checker + proven lowering, issue #192). Solution module: QueryCheck.
   Config: lean/comparator/check_query_sound.json. Imports only the generated
   model and the DAG semantics (`dagBool`, BlasterDag), never QueryCheck. -/
import BlasterDag

open Aeneas Aeneas.Std Result
open kernel.blast_kernel.spec

namespace kernel.spec

theorem check_query_sound (ns : Slice kernel.blast_kernel.DagNode) (bits : Slice Bool)
    (roots : Slice Std.Usize) (hints : Slice Std.Usize) (steps : Slice kernel.Step)
    (cnf : alloc.vec.Vec (alloc.vec.Vec Std.I32))
    (h : kernel.check_query ns bits roots hints steps = ok (core.result.Result.Ok cnf)) :
    ∀ inp : List Bool, ¬ (∀ (k : Nat) (hk : k < roots.val.length),
      dagBool inp bits.val ns.val (roots.val[k]).val = true) :=
  sorry

end kernel.spec
