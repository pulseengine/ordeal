#!/usr/bin/env bash
# rivet: verifies VER-035
# wasm ↔ native behavioral differential (issue #135 / TR-041).
#
# The relay incident class: two green builds of the same software that are
# not behaviorally the same artifact. This harness runs the committed
# differential corpus through the NATIVE binary and the WASM component
# (under a wasm runtime) and demands byte-identical stdout — verdicts,
# models, and on unsat the full certificate (CNF + LRAT text via
# --format json; the pipeline is deterministic, so the proofs must match
# too) — plus identical exit codes. Any divergence is a hard failure.
#
# Usage:
#   scripts/wasm_native_differential.sh <native-bin> <wasm-runner...>
# e.g.
#   scripts/wasm_native_differential.sh \
#     target/release/ordeal \
#     wasmtime run --dir . target/wasm32-wasip2/release/ordeal.wasm
set -euo pipefail

if [ "$#" -lt 2 ]; then
  echo "usage: $0 <native-bin> <wasm-runner...>" >&2
  exit 2
fi
NATIVE="$1"
shift

CORPUS="crates/ordeal/tests/fixtures/differential"
test -d "$CORPUS" || { echo "corpus dir missing: $CORPUS" >&2; exit 2; }

fail=0
checked=0

# Agreement alone is not enough: two binaries that fail the same way agree
# byte for byte. Every fixture is named for its verdict (sat_* / unsat_*),
# so each invocation must also exit 0 and print that verdict: the plain
# text answer's first line, or the JSON report's "verdict" field.
expect_ok() { # <label> <expected verdict> <mode> <exit> <stdout>
  local label="$1" want="$2" mode="$3" code="$4" out="$5" got
  if [ "$code" != 0 ]; then
    echo "WRONG   $label: exit $code, expected 0 with verdict $want"; return 1
  fi
  if [ "$mode" = json ]; then
    got=$(printf '%s' "$out" | sed -n 's/.*"verdict":"\([a-z]*\)".*/\1/p' | head -1)
  else
    got=$(printf '%s\n' "$out" | head -1)
  fi
  if [ "$got" != "$want" ]; then
    echo "WRONG   $label: verdict '${got}', expected '$want'"; return 1
  fi
}

want_of() { # sat_foo.smt2 -> sat, unsat_foo.smt2 -> unsat
  case "$(basename "$1")" in
    sat_*) echo sat ;;
    unsat_*) echo unsat ;;
    *) echo "fixture $(basename "$1") is not named sat_* or unsat_*" >&2; exit 2 ;;
  esac
}
for f in "$CORPUS"/*.smt2; do
  for mode in text json; do
    if [ "$mode" = json ]; then
      args=(check - --format json)
    else
      args=(check -)
    fi
    set +e
    n_out=$("$NATIVE" "${args[@]}" <"$f" 2>/dev/null)
    n_code=$?
    w_out=$("$@" "${args[@]}" <"$f" 2>/dev/null)
    w_code=$?
    set -e
    checked=$((checked + 1))
    if [ "$n_code" != "$w_code" ] || [ "$n_out" != "$w_out" ]; then
      echo "DIVERGE $(basename "$f") [$mode]: native(exit=$n_code) != wasm(exit=$w_code)"
      diff <(printf '%s\n' "$n_out") <(printf '%s\n' "$w_out") | head -10 || true
      fail=1
    else
      echo "AGREE   $(basename "$f") [$mode] (exit $n_code)"
    fi
    expect_ok "$(basename "$f") [$mode] native" "$(want_of "$f")" "$mode" "$n_code" "$n_out" || fail=1
    expect_ok "$(basename "$f") [$mode] wasm" "$(want_of "$f")" "$mode" "$w_code" "$w_out" || fail=1
  done
done

# File-path mode on wasm requires a preopened dir (WASI); prove it works
# when preopened rather than leaving it an untested surface (#135 found it
# failing with os error 44 un-preopened — that is WASI semantics, but the
# preopened path must agree with native).
probe="$CORPUS/unsat_urem_identity_w8.smt2"
set +e
n_out=$("$NATIVE" check "$probe" 2>/dev/null); n_code=$?
w_out=$("$@" check "$probe" 2>/dev/null); w_code=$?
set -e
checked=$((checked + 1))
if [ "$n_code" != "$w_code" ] || [ "$n_out" != "$w_out" ]; then
  echo "DIVERGE file-mode probe: native(exit=$n_code) != wasm(exit=$w_code) (is the corpus dir preopened?)"
  fail=1
else
  echo "AGREE   file-mode probe (exit $n_code)"
fi
expect_ok "file-mode probe native" "$(want_of "$probe")" text "$n_code" "$n_out" || fail=1
expect_ok "file-mode probe wasm" "$(want_of "$probe")" text "$w_code" "$w_out" || fail=1

if [ "$fail" -ne 0 ]; then
  echo "wasm/native differential: DIVERGENCE FOUND across $checked invocations" >&2
  exit 1
fi
[ "$checked" -gt 0 ] || { echo "wasm/native differential: compared nothing" >&2; exit 1; }
echo "wasm/native differential: $checked invocations, byte-identical, each the fixture's expected verdict"
