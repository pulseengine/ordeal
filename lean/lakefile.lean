import Lake
open Lake DSL

-- The Aeneas Lean support library, pinned to the SAME revision as the
-- translator in regen.sh (the generated code and the library must match).
require aeneas from git
  "https://github.com/AeneasVerif/aeneas.git" @
  "9dd45ecf2de55e732a4a89e5fd065e96eeab3657" / "backends/lean"

package «ordeal-lrat-proof» {}

-- The generated model (regen.sh) — this is the CI gate: it must elaborate.
@[default_target] lean_lib «Kernel» {}

-- The spec + soundness proof (issue #12). Builds today with ONE remaining
-- `sorry` (`kernel_refines_pure`, the model↔pure simulation); the pure
-- soundness result `pure_check_sound` and everything it uses is complete
-- and `sorry`-free (verified via `#print axioms`). Not a default target
-- until the last `sorry` is gone; build with `lake build Sound`.
lean_lib «Sound» {}
