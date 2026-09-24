#!/usr/bin/env bash
# rivet: verifies VER-043
# The Kani harness tiers — defined ONCE here, consumed by
# .github/workflows/kani.yml (TR-046 / issue #153).
#
#   scripts/kani_tiers.sh args <fast|wide|heavy:<harness>>   # "--harness a --harness b …"
#   scripts/kani_tiers.sh list <fast|wide|heavy|unscheduled>
#   scripts/kani_tiers.sh check                              # coverage gate (CI)
#
# Why a script and not a list in the workflow: #153 found the Kani job had
# not completed since 2026-07-16 — urem_8 sat in the PR "fast" tier after
# v0.10.0 made the divider native, and 44 of the 82 harnesses in
# crates/ordeal/src/blast/proofs.rs were in no tier at all, silently. A
# harness nobody runs is not a proof (the #138 gate-potency pattern), so
# `check` fails unless EVERY harness in proofs.rs is in exactly one tier or
# in the explicitly-unscheduled list below WITH a reason.
set -uo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
PROOFS="$HERE/crates/ordeal/src/blast/proofs.rs"

# PR + nightly. Width-8 rules without multiplication/division: 6–64 s each
# on the standard runner (2026-09-24 nightly log), ~8 min total.
FAST=(add_8 sub_8 and_8 or_8 xor_8 shl_8 lshr_8 ashr_8 rotr_8
  eq_8 ne_8 ult_8 ule_8 ugt_8 uge_8 slt_8 sle_8 sgt_8 sge_8
  concat_4_4 extract_16_hi extract_16_lo zext_8_8 sext_8_8 ite_8)

# Nightly, ONE JOB PER HARNESS with its own timeout: the shift-add
# multiplier and the restoring divider at width 8 are the harnesses that
# ran for hours; isolating them means a runner preemption costs one
# harness, not the tier (and not the nightly wide tier behind it).
HEAVY=(mul_8 udiv_8 urem_8)

# Nightly. Light rules at 32/64 (ripple-carry, bitwise) — measured
# feasible in the pre-#76 nightlies (~19 min for everything then scheduled).
WIDE=(add_32 add_64 sub_32 sub_64 and_32 and_64 or_32 or_64 xor_32 xor_64)

# Deliberately not scheduled — each with its reason. Promote a harness out
# of here only with a timed dispatch run in hand.
UNSCHEDULED=(
  # CBMC/SAT-infeasible: multiplier/divider at 32/64 (exhaustive-8 unit
  # tests + the required Lean Blaster* proofs at unbounded width carry them).
  mul_32 mul_64 udiv_32 udiv_64 urem_32 urem_64
  # Unmeasured at 32/64 (barrel shifters, comparators, structural rules,
  # mux): no timed run yet — do not put an unmeasured harness in a tier.
  shl_32 shl_64 lshr_32 lshr_64 ashr_32 ashr_64 rotr_32 rotr_64
  eq_32 eq_64 ne_32 ne_64 ult_32 ult_64 ule_32 ule_64 ugt_32 ugt_64
  uge_32 uge_64 slt_32 slt_64 sle_32 sle_64 sgt_32 sgt_64 sge_32 sge_64
  concat_16_16 concat_32_32 extract_32_mid extract_64_hi
  zext_16_16 zext_32_32 sext_16_16 sext_32_32 ite_32 ite_64
)

inventory() {
  grep -oE '^[a-z_]+_proof!\([a-z0-9_]+' "$PROOFS" | sed 's/.*(//'
}

args_for() {
  local out=""
  for h in "$@"; do out+=" --harness $h"; done
  echo "${out# }"
}

cmd="${1:-}"; shift || true
case "$cmd" in
  args)
    case "${1:-}" in
      fast) args_for "${FAST[@]}" ;;
      wide) args_for "${WIDE[@]}" ;;
      heavy:*) h="${1#heavy:}"
        for x in "${HEAVY[@]}"; do [ "$x" = "$h" ] && { args_for "$h"; exit 0; }; done
        echo "not a heavy harness: $h" >&2; exit 2 ;;
      *) echo "usage: $0 args <fast|wide|heavy:<harness>>" >&2; exit 2 ;;
    esac ;;
  list)
    case "${1:-}" in
      fast) printf '%s\n' "${FAST[@]}" ;;
      wide) printf '%s\n' "${WIDE[@]}" ;;
      heavy) printf '%s\n' "${HEAVY[@]}" ;;
      unscheduled) printf '%s\n' "${UNSCHEDULED[@]}" ;;
      *) echo "usage: $0 list <fast|wide|heavy|unscheduled>" >&2; exit 2 ;;
    esac ;;
  check)
    fail=0
    inv=$(inventory)
    n_inv=$(printf '%s\n' "$inv" | grep -c .)
    [ "$n_inv" -ge 82 ] || { echo "FAIL: inventory shrank to $n_inv harnesses (expected >= 82) — proofs.rs or this scanner changed"; fail=1; }
    all=$(printf '%s\n' "${FAST[@]}" "${HEAVY[@]}" "${WIDE[@]}" "${UNSCHEDULED[@]}")
    # every listed name must be a real harness
    for h in $all; do
      printf '%s\n' "$inv" | grep -qx "$h" || { echo "FAIL: '$h' is listed in a tier but is not a harness in proofs.rs"; fail=1; }
    done
    # every harness must be listed exactly once
    for h in $inv; do
      c=$(printf '%s\n' "$all" | grep -cx "$h")
      [ "$c" -eq 1 ] || { echo "FAIL: harness '$h' appears in $c tier list(s) (must be exactly 1: fast, heavy, wide, or unscheduled-with-reason)"; fail=1; }
    done
    echo "kani tiers: inventory $n_inv | fast ${#FAST[@]} | heavy ${#HEAVY[@]} | wide ${#WIDE[@]} | unscheduled ${#UNSCHEDULED[@]}"
    [ "$fail" -eq 0 ] && echo "PASS: every harness in proofs.rs is in exactly one tier" || exit 1 ;;
  *) echo "usage: $0 <args|list|check> …" >&2; exit 2 ;;
esac
