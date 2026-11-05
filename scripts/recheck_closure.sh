#!/usr/bin/env bash
# recheck_closure.sh — TR-075 / issue #277: `ordeal-recheck` must be built
# WITHOUT the solver. Reads the normal (shipped) dependency tree of the
# ordeal-recheck binary and FAILS if
#   - a crate named exactly `ordeal` (the solver) appears in it,
#   - a native solver crate (`cadical-sys`, `z3`, `z3-sys`) appears in it,
#   - the trusted checker `ordeal-lrat` is missing from it (it must be
#     re-checking with SOMETHING), or
#   - the tree is empty (a broken `cargo tree` must not read as "clean").
# Dev-dependencies (the integration tests build bundles with the real
# solver) are not part of the binary and are excluded by `-e normal`.
# Negative-controlled when it landed: adding `ordeal` as a normal
# dependency of crates/ordeal-recheck turns this red.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

TREE="$(cargo tree -p ordeal-recheck -e normal --prefix none)"
NAMES="$(printf '%s\n' "$TREE" | awk 'NF {print $1}' | sort -u)"

if [ -z "$NAMES" ]; then
  echo "FAIL  cargo tree -p ordeal-recheck came back empty" >&2
  exit 1
fi

echo "ordeal-recheck normal dependency closure:"
printf '  %s\n' $NAMES

fail=0
for forbidden in ordeal cadical-sys z3 z3-sys; do
  if printf '%s\n' "$NAMES" | grep -qxF "$forbidden"; then
    echo "FAIL  '$forbidden' is in ordeal-recheck's dependency closure (the re-checker must not depend on the solver)" >&2
    fail=1
  fi
done
for required in ordeal-recheck ordeal-cert ordeal-lrat; do
  if ! printf '%s\n' "$NAMES" | grep -qxF "$required"; then
    echo "FAIL  '$required' is missing from ordeal-recheck's dependency closure" >&2
    fail=1
  fi
done

if [ "$fail" -ne 0 ]; then
  exit 1
fi
echo "PASS  ordeal-recheck's closure has no solver (ordeal, cadical-sys, z3)"
