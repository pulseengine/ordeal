#!/usr/bin/env bash
# Regenerate the Aeneas-produced Lean models of the trusted Rust kernels.
#
#   lean/regen.sh [all|kernel]     (default: all; `blaster` is an alias)
#
#   kernel  → lean/Kernel.lean  from crates/ordeal-lrat/src/kernel.rs, which
#             `#[path]`-includes crates/ordeal-lrat/src/blast_kernel.rs (the
#             proven lowering) as its submodule `blast_kernel` — ONE
#             translation unit since #192 phase 4, so `check_query` (checker
#             + lowering composed) is modelled in the same file. Namespaces:
#             `kernel.*` (checker) and `kernel.blast_kernel.*` (lowering).
#
# TR-034 (issue #48): the generated models are BUILD PRODUCTS, not committed
# artifacts — they are .gitignored, and the Lean CI job runs this script
# before every proof build, so the proofs always certify the translation of
# the Rust that ships. There is no committed model to go stale. Run this
# once locally (requires nix) before proof development; afterwards
# iteration is pure `lake`.
#
# The Charon and Aeneas revisions are pinned — in exactly one place,
# lean/toolchain-pins.env — to each other (Aeneas's flake input decides the
# Charon it understands); bump them together.
set -euo pipefail
cd "$(dirname "$0")/.."

# shellcheck source=lean/toolchain-pins.env
source lean/toolchain-pins.env

LLBC_DIR=$(mktemp -d)
trap 'rm -rf "$LLBC_DIR"' EXIT

# Build the pinned tools to PERSISTENT GC ROOTS (lean/.nix-roots/, gitignored)
# instead of `nix run`: a run leaves no root, so any store gc — notably the
# CI nix-store cache's size trim — collects the built closures and every job
# rebuilds them from source (~20 min, measured on PRs #123-#125). With roots
# the cached store serves the binaries and a warm regen is seconds.
ROOTS="lean/.nix-roots"
mkdir -p "$ROOTS"
nix build "github:AeneasVerif/charon/$CHARON_REV" --out-link "$ROOTS/charon"
nix build "github:AeneasVerif/aeneas/$AENEAS_REV" --out-link "$ROOTS/aeneas"

regen() { # $1 = rust source, $2 = llbc name, $3 = generated file (for the log)
  "$ROOTS/charon/bin/charon" rustc \
    --preset=aeneas \
    --dest-file "$LLBC_DIR/$2" \
    -- --crate-type=lib "$1"
  "$ROOTS/aeneas/bin/aeneas" \
    -backend lean "$LLBC_DIR/$2" -dest lean
  echo "regenerated $3"
}

what="${1:-all}"
case "$what" in
  # One unit: kernel.rs is the crate root and pulls in blast_kernel.rs.
  kernel|blaster|all) regen crates/ordeal-lrat/src/kernel.rs kernel.llbc lean/Kernel.lean ;;
  *)
    echo "usage: lean/regen.sh [all|kernel]" >&2
    exit 2
    ;;
esac
