#!/usr/bin/env bash
# rivet: verifies VER-077
# MC/DC ratchet for the trusted checker crate `ordeal-lrat` (issue #279).
#
#   scripts/mcdc_gate.sh [OUTDIR]        # default: target/mcdc-ordeal-lrat
#
# Builds the row harness (mcdc/ordeal-lrat) for wasm32-wasip1, instruments it
# and runs every `run_row_*` export under `witness`, then writes the rollup
# and the per-decision truth table into OUTDIR and compares per-file gap
# counts with mcdc/baseline.txt (see scripts/mcdc_report.py). Non-zero exit
# when a checker file's uncovered-decision or gap-condition count INCREASES,
# when the report is vacuous, or when a checker source file has ZERO
# decisions in the table and is not on the printed waiver list
# (ZERO_DECISION_WAIVERS in scripts/mcdc_report.py; fail closed). A decrease prints an improvement note; the
# baseline is updated by hand, never by this script.
#
# witness: $WITNESS, else the varve-pinned layer (`varve which witness`),
# else `witness` on PATH. Needs the wasm32-wasip1 rust target.
#
# MCDC_ROOT overrides the repo root (the negative controls in docs/mcdc.md run
# the gate against a scratch copy; the real tree is never edited).
set -euo pipefail

ROOT="${MCDC_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OUT="${1:-$ROOT/target/mcdc-ordeal-lrat}"
HARNESS="$ROOT/mcdc/ordeal-lrat"
BASELINE="$ROOT/mcdc/baseline.txt"

WIT="${WITNESS:-}"
if [ -z "$WIT" ] && [ -x "$HOME/.varve/bin/varve" ]; then
  WIT="$("$HOME/.varve/bin/varve" which witness 2>/dev/null | head -1 || true)"
fi
if [ -z "$WIT" ]; then
  WIT="$(command -v witness || true)"
fi
if [ -z "$WIT" ] || [ ! -x "$WIT" ]; then
  echo "mcdc_gate: no witness binary (set WITNESS, or install the varve layer)" >&2
  exit 2
fi
echo "mcdc_gate: witness = $WIT ($("$WIT" --version 2>&1 | head -1))"

mkdir -p "$OUT"
OUT="$(cd "$OUT" && pwd)"
SCRATCH="$(mktemp -d)"
trap 'rm -rf "$SCRATCH"' EXIT

ROWS=$(grep -c '^run_row_' "$HARNESS/src/rows.rs")
echo "mcdc_gate: harness defines $ROWS rows"

cd "$HARNESS"
rm -rf target/witness
"$WIT" all --manifest-path . >"$OUT/witness-all.log" 2>&1 || {
  tail -30 "$OUT/witness-all.log" >&2
  echo "mcdc_gate: witness all failed (log: $OUT/witness-all.log)" >&2
  exit 2
}

# The two reports are independent and slow (minutes each): run them together.
"$WIT" report --input target/witness/run.json --format mcdc-json >"$SCRATCH/mcdc.json" 2>"$SCRATCH/json.err" &
J=$!
"$WIT" report --input target/witness/run.json --format mcdc-rollup >"$OUT/rollup.txt" 2>"$SCRATCH/rollup.err" &
R=$!
wait "$J" || { cat "$SCRATCH/json.err" >&2; echo "mcdc_gate: mcdc-json report failed" >&2; exit 2; }
wait "$R" || { cat "$SCRATCH/rollup.err" >&2; echo "mcdc_gate: mcdc-rollup report failed" >&2; exit 2; }

python3 -I "$ROOT/scripts/mcdc_report.py" \
  "$SCRATCH/mcdc.json" target/witness/run.json "$ROOT" "$OUT" "$BASELINE" "$ROWS"
