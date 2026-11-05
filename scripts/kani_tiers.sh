#!/usr/bin/env bash
# rivet: verifies VER-043
# The Kani harness tiers — defined ONCE here, consumed by
# .github/workflows/kani.yml (TR-046 / issue #153).
#
#   scripts/kani_tiers.sh args <fast|heavy:<harness>|wide:<harness>>
#   scripts/kani_tiers.sh list <fast|heavy|wide|unscheduled>
#   scripts/kani_tiers.sh json wide                          # kani.yml matrix
#   scripts/kani_tiers.sh check                              # coverage gate (CI)
#
# #192 phase 2 (2026-10-01): the harnesses in proofs.rs now call the proven
# `blast_kernel` rules on the reference arena and simulate with the kernel's
# own forward fold; they no longer go through `aig::Aig::and` (the replay
# bridge path does not terminate under CBMC — the reason and measurements
# are in proofs.rs). The tier lists below are unchanged; the timings quoted
# in the comments were measured on the pre-phase-2 harnesses and are kept as
# the record of what CI last ran — re-measure before promoting anything.
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

# Nightly, ONE JOB PER HARNESS with its own timeout, so a runner
# preemption costs one harness, not the tier. Measured on run 36019140498
# (Kani 0.68, ubuntu-latest): mul_8 374 s.
HEAVY=(mul_8)

# Nightly, ONE JOB PER HARNESS: the light rules at width 32/64 (#169).
# These never finished before (xor_32 > 88 min on CI; locally > 20 min and
# still in symbolic execution) — not because the rule is hard, but because
# CBMC applies array field sensitivity only up to 64 BYTES by default. A
# width-32 `Word` is 32 `Lit`s = 128 bytes, so each `word[i]` read inside
# the real blast_* rule came back as a symbolic Lit, every constant fold in
# `Aig::and` became a symbolic branch, and symex was still inside
# blast_xor's zip (iteration 27 of 32) after 20 min. Raising the limit
# (WIDE_CBMC) keeps those reads concrete. It is an encoding choice inside
# CBMC's symbolic execution, not an abstraction: the harness, the blast_*
# code under proof and the assertion are unchanged. Measured locally
# (Kani 0.67 / CBMC 6.8.0, arm64, 16 GB; Verification Time, peak RSS),
# 2026-09-30, with WIDE_CBMC:
#   xor_32 79-83 s (2.8 GB) | and_32 56 s | or_32 50 s | add_32 238 s (3.4 GB)
#   sub_32 297 s | xor_64 217 s (3.9 GB) | add_64 1019 s (5.2 GB)
#   and_64 115 s | or_64 114 s (3.8 GB) | sub_64 940 s (5.3 GB)
# Limit sweep on add_32: 256 -> 209 s, 1024 -> 238 s, 16384 -> 310 s (5.7 GB);
# 1024 is the setting every number above was measured with. Promote more
# 32/64 harnesses here only with a timed run under WIDE_CBMC.
# CI (ubuntu-latest, Kani 0.68), dispatch run 36759511157 on main 81fe397,
# 2026-09-30: all 8 below SUCCESS — job wall time xor_32 3m41s, and_32 1m49s,
# or_32 2m27s, add_32 8m56s, sub_32 9m00s, xor_64 8m20s, and_64 4m14s,
# or_64 4m34s. add_64 and sub_64 were cancelled by the runner (see below).
# #280 (2026-11-05): twelve more, timed locally under WIDE_CBMC (Kani 0.67 /
# CBMC, arm64, 16 GB; Verification Time, peak RSS): sext_16_16 58 s (1.6 GB)
# | zext_16_16 65 s (1.4 GB) | extract_32_mid 77 s (2.6 GB) | sext_32_32
# 105 s (2.1 GB) | zext_32_32 122 s (3.1 GB) | extract_64_hi 175 s (2.1 GB)
# | concat_16_16 187 s (3.4 GB) | ite_32 244 s (4.1 GB) | eq_32 251 s
# (4.5 GB) | concat_32_32 308 s (2.4 GB) | ite_64 587 s (4.3 GB) | ne_32
# 635 s (2.9 GB). CI (ubuntu-latest = ubuntu-26.04 image, Kani 0.68),
# dispatch run 42002290201 on this branch: all eleven kept below SUCCESS,
# job wall time sext_16_16 <1m, zext_16_16 1m, extract_32_mid 1m,
# sext_32_32 1m, zext_32_32 1m, extract_64_hi 1m, concat_16_16 1m,
# concat_32_32 1m, eq_32 1m, ite_32 3m, ne_32 3m; ite_64 lost the runner
# (see UNSCHEDULED).
WIDE=(xor_32 and_32 or_32 and_64 or_64
  sext_16_16 zext_16_16 extract_32_mid sext_32_32 zext_32_32 extract_64_hi
  concat_16_16 ite_32 eq_32 concat_32_32 ne_32)
WIDE_CBMC="-Z unstable-options --cbmc-args --max-field-sensitivity-array-size 1024"

# Deliberately not scheduled — each with its reason. Promote a harness out
# of here only with a timed dispatch run in hand.
UNSCHEDULED=(
  # The width-8 divider does not complete on ubuntu-latest: run 36019140498
  # had the runner shut down under udiv_8 / urem_8 at 3269 s / 2973 s (not a
  # Kani failure); locally (64 GB arm64, Kani 0.67) urem_8 is SUCCESSFUL in
  # 3035 s under minisat and 3123 s under cadical — the solver is not the
  # lever. Nor is the u128 reference (#280, 2026-11-05, local arm64 16 GB,
  # WIDE_CBMC): the same harness with the reference computed at 8 bits
  # (`u8` division, so CBMC encodes an 8-bit divider, not a 128-bit one)
  # crashes CBMC (status 139, stack) under the 8 MB default; with a 64 MB
  # stack udiv_8 is SUCCESSFUL in 3294 s (4.6 GB) and urem_8 runs past
  # 3600 s. The cost is the blasted divider circuit itself. (mul_8 with an
  # 8-bit reference: 500 s, 7.6 GB, no gain over the u128 shape either.) Covered by the exhaustive-8 unit tests and the required Lean
  # blast_udivrem_bitvec / blast_udiv_bitvec / blast_urem_bitvec proofs at
  # unbounded width. Tracked in #169.
  udiv_8 urem_8
  # Complete locally under WIDE_CBMC (add_64 1019 s / 5.2 GB, sub_64 940 s
  # / 5.3 GB) but on ubuntu-latest dispatch run 36759511157 the runner
  # cancelled both mid-Kani ("The operation was canceled") at 35m14s /
  # 31m55s, well inside the 75-min job timeout: the runner-shutdown
  # signature, not a Kani failure. The org self-hosted rust-cpu pool was
  # tried too (2026-10-01): run 36813381641 timed out at 90 min, and run
  # 36821560393 ran about 3 h until the runner itself dropped. Neither left
  # a log. Maintainer decision: accept the gap. blast_add/blast_sub are
  # proven at every width in Lean (BlasterArith.lean); since #192 phase 2
  # those proofs cover the rule code that runs. They are also tested
  # exhaustively at width 8 and randomized at 32/64. Local Kani completes
  # (add_64 1019 s, sub_64 940 s).
  add_64 sub_64
  # Promoted to WIDE on 2026-09-30 (one dispatch SUCCESS, 8-9 min) but on
  # the nightly schedule they never completed again: add_32, sub_32 and
  # xor_64 failed EVERY scheduled run from 2026-10-02 to 2026-11-05 (35
  # nights) with the runner-shutdown signature mid-solve (xor_64: CBMC at
  # 6.65M variables / 16.8M clauses, then "The runner has received a
  # shutdown signal" at 4-7 min), and the run badge stayed green because
  # of the job-level continue-on-error (now caught by the verdict job in
  # kani.yml). Dispatch run 42002290201 and its re-run (#280, 2026-11-05)
  # reproduced it on all three, twice each. ite_64 (local 587 s, 4.3 GB)
  # lost the runner at 50 min and again at 8 min in the same run. All four
  # are proven at every width in Lean (BlasterArith.lean add/sub,
  # BlasterProof.lean blast_xor_bitvec, BlasterCmp.lean blast_ite_bitvec) over the shipped rule code (#219), and tested
  # exhaustively at 8 and randomized at 32/64.
  add_32 sub_32 xor_64 ite_64
  # CBMC/SAT-infeasible: multiplier/divider at 32/64 (same coverage).
  mul_32 mul_64 udiv_32 udiv_64 urem_32 urem_64
  # Measured under WIDE_CBMC for #280 (2026-11-05, local arm64, 20-min cap)
  # and too slow for a hosted runner (CI runs ~2.7x the local time):
  # the barrel shifters and the 64-bit ordering comparators crash CBMC with
  # SIGSEGV (status 139, 0 failed checks: a stack overflow in symbolic
  # execution under the 8 MB default, not a counterexample) after 2-7 min;
  # with a 64 MB stack lshr_32, shl_32 and ult_64 no longer crash but run
  # past 25 min. eq_64, ne_64 and the eight ordering comparators at 32 ran
  # past 20 min. All are proven at every width in Lean (BlasterCmp.lean,
  # BlasterShift.lean, BlasterRotr.lean) over the shipped rule code (#219) and tested
  # exhaustively at 8 and randomized at 32/64.
  shl_32 shl_64 lshr_32 lshr_64 ashr_32 ashr_64 rotr_32 rotr_64
  eq_64 ne_64 ult_32 ult_64 ule_32 ule_64 ugt_32 ugt_64
  uge_32 uge_64 slt_32 slt_64 sle_32 sle_64 sgt_32 sgt_64 sge_32 sge_64
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
      heavy:*) h="${1#heavy:}"
        for x in "${HEAVY[@]}"; do [ "$x" = "$h" ] && { args_for "$h"; exit 0; }; done
        echo "not a heavy harness: $h" >&2; exit 2 ;;
      wide:*) h="${1#wide:}"
        # --exact on the qualified name: a plain --harness is a substring
        # match (`or_32` would also run xor_32). --cbmc-args must come last.
        for x in "${WIDE[@]}"; do
          [ "$x" = "$h" ] && { echo "--exact --harness blast::proofs::$h $WIDE_CBMC"; exit 0; }
        done
        echo "not a wide harness: $h" >&2; exit 2 ;;
      *) echo "usage: $0 args <fast|heavy:<harness>|wide:<harness>>" >&2; exit 2 ;;
    esac ;;
  list)
    case "${1:-}" in
      fast) printf '%s\n' "${FAST[@]}" ;;
      heavy) printf '%s\n' "${HEAVY[@]}" ;;
      wide) printf '%s\n' "${WIDE[@]}" ;;
      unscheduled) printf '%s\n' "${UNSCHEDULED[@]}" ;;
      *) echo "usage: $0 list <fast|heavy|wide|unscheduled>" >&2; exit 2 ;;
    esac ;;
  json)
    # The wide matrix for kani.yml, so the workflow cannot drift from WIDE.
    [ "${1:-}" = wide ] || { echo "usage: $0 json wide" >&2; exit 2; }
    out=""
    for h in "${WIDE[@]}"; do out+="\"$h\","; done
    echo "[${out%,}]" ;;
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
  *) echo "usage: $0 <args|list|json|check> …" >&2; exit 2 ;;
esac
