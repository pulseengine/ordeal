#!/usr/bin/env bash
# Regenerate lean/Blaster.lean — the Aeneas-produced Lean model of the
# bit-blaster kernel (issue #68, v0.15.0). Same pinned Charon/Aeneas as
# regen.sh; run after any change to crates/ordeal/src/blast_kernel.rs and
# commit the result. The proofs in lean/BlasterProof.lean are stated ABOUT
# this generated file (each rule = the formal BitVec semantics, all widths).
set -euo pipefail
cd "$(dirname "$0")/.."

AENEAS_REV=9dd45ecf2de55e732a4a89e5fd065e96eeab3657
CHARON_REV=40ee060a8df43f4e7e0842d3f05387b0a4426aaf

LLBC_DIR=$(mktemp -d)
trap 'rm -rf "$LLBC_DIR"' EXIT

nix run "github:AeneasVerif/charon/$CHARON_REV" -- rustc \
  --preset=aeneas \
  --dest-file "$LLBC_DIR/blast_kernel.llbc" \
  -- --crate-type=lib crates/ordeal/src/blast_kernel.rs

nix run "github:AeneasVerif/aeneas/$AENEAS_REV" -- \
  -backend lean "$LLBC_DIR/blast_kernel.llbc" -dest lean

echo "regenerated lean/BlastKernel.lean"
