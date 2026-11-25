/- COMPARATOR CHALLENGE: the trusted statement of the certified echo's UNSAT
   capstone (#281). Solution module: Echo. Config:
   lean/comparator/echo_unsat_sound.json. Imports only the generated model and
   the SMT-LIB model (EchoSpec: renderScript, PrintableL, Interp, ScriptSat),
   never Echo. -/
import EchoSpec

open Aeneas Aeneas.Std Result
open kernel.blast_kernel.spec

namespace kernel.spec

open kernel.spec.smt

theorem echo_unsat_sound (t : Slice blast_kernel.DagNode) (tbits : Slice Bool)
    (troots : Slice Std.Usize) (names : Slice Std.U8)
    (name_start name_len var_node var_width : Slice Std.Usize) (out : alloc.vec.Vec Std.U8)
    (map : Slice Std.Usize) (ns : Slice blast_kernel.DagNode) (bits : Slice Bool)
    (roots hints : Slice Std.Usize) (steps : Slice kernel.Step)
    (cnf : alloc.vec.Vec (alloc.vec.Vec Std.I32))
    (he : kernel.echo_kernel.echo_term t tbits troots names name_start name_len var_node var_width
      = ok (core.result.Result.Ok out))
    (ht : kernel.check_term_dag t tbits troots map ns bits roots = ok (core.result.Result.Ok ()))
    (hq : kernel.check_query ns bits roots hints steps = ok (core.result.Result.Ok cnf)) :
    ∃ cs, out.val = renderScript cs ∧ PrintableL cs ∧ ∀ I : Interp, ¬ ScriptSat I cs :=
  sorry

end kernel.spec
