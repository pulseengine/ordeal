#!/usr/bin/env bash
# Regenerate lean/Kernel.lean — the Aeneas-produced Lean model of the
# ordeal-lrat kernel (the trusted checking core).
#
# Requires nix. The Charon and Aeneas revisions are PINNED to each other
# (Aeneas's flake input decides the Charon it understands); bump them
# together. The generated file is committed so the proof work and CI don't
# need the (slow, OCaml) toolchain — run this after ANY change to
# crates/ordeal-lrat/src/kernel.rs and commit the result.
set -euo pipefail
cd "$(dirname "$0")/.."

AENEAS_REV=9dd45ecf2de55e732a4a89e5fd065e96eeab3657
CHARON_REV=40ee060a8df43f4e7e0842d3f05387b0a4426aaf

LLBC_DIR=$(mktemp -d)
trap 'rm -rf "$LLBC_DIR"' EXIT

nix run "github:AeneasVerif/charon/$CHARON_REV" -- rustc \
  --preset=aeneas \
  --dest-file "$LLBC_DIR/kernel.llbc" \
  -- --crate-type=lib crates/ordeal-lrat/src/kernel.rs

nix run "github:AeneasVerif/aeneas/$AENEAS_REV" -- \
  -backend lean "$LLBC_DIR/kernel.llbc" -dest lean

echo "regenerated lean/Kernel.lean"
