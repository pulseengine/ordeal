#!/usr/bin/env bash
# rivet: verifies VER-036
# rivet: verifies VER-039
# The axiom-cleanliness gate (issue #137 / TR-042), as one named, callable
# step: elaborate lean/AxiomCheck.lean, whose #guard_msgs-pinned
# `#print axioms` fail on any axiom beyond propext / Classical.choice /
# Quot.sound in the soundness chain or a blaster capstone. `lake build`
# already covers it as a default target; this wrapper exists so CI shows a
# distinct "Axiom gate" verdict and so the gate has a source-level
# evidence marker rivet can scan (its scanner has no Lean support — the
# .lean file itself cannot carry the marker; see rivet#992).
set -euo pipefail
cd "$(dirname "$0")/../lean"
lake build AxiomCheck
echo "axiom gate: AxiomCheck elaborated — soundness chain, SAT-witness theorems and blaster capstones depend only on propext / Classical.choice / Quot.sound"
