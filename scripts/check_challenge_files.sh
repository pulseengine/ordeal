#!/usr/bin/env bash
# Flag changes to the TRUSTED STATEMENTS of the comparator-checked theorems for
# the owner's review.
#
#   scripts/check_challenge_files.sh BASE_SHA HEAD_SHA   # in a PR
#   scripts/check_challenge_files.sh --self-test
#
# A pull request that changes any file below changes what ordeal claims to
# have proven. The check exits 1 and lists the files unless the PR carries the
# owner's `challenge-reviewed` label (CHALLENGE_REVIEWED=true from the
# workflow). The repository's rules cannot require a code-owner review, and
# every agent session pushes as the same account, so this is a visible flag for
# the owner, not an enforcement boundary.
#
# Trusted-statement files: the challenges and their configs, plus the
# definitions-only modules the challenges are stated in (CnfSpec for
# `unsat`, EchoSpec for the SMT-LIB model). `dagBool` (check_query_sound)
# still lives in BlasterDag.lean, a proof file, and is NOT flagged here.
#
# The diff is three-dot (BASE...HEAD): only what the PR branch changed since
# it left the base. A two-dot diff also lists base-side changes made after the
# branch point, in reverse, so a stale branch that touched none of these files
# was flagged (#347, which predated #346's lean/comparator edits).
set -uo pipefail

TRUSTED_RE='^lean/(Challenge/|comparator/|CnfSpec\.lean$|EchoSpec\.lean$)'

flag() { # stdin: changed paths; $1: reviewed (true|false). Exit 0 ok, 1 flagged.
  local hits
  hits=$(grep -E "$TRUSTED_RE" || true)
  if [ -z "$hits" ]; then echo "no trusted-statement file changed"; return 0; fi
  echo "trusted-statement files changed:"; echo "$hits" | sed 's/^/  /'
  if [ "$1" = true ]; then echo "label challenge-reviewed present: accepted"; return 0; fi
  echo "::error::this PR changes what ordeal claims to have proven; the owner must review it and add the 'challenge-reviewed' label"
  return 1
}

changed_paths() { # $1 BASE, $2 HEAD: files the branch changed since the merge base
  git diff --name-only "$1...$2"
}

# Planted git history: main moves a trusted file after a branch point.
git_self_test() {
  local d rc=0 g
  d=$(mktemp -d) || return 1
  g() { git -C "$d" -c user.name=t -c user.email=t@t -c commit.gpgsign=false "$@" >/dev/null 2>&1; }
  g init -q -b main && mkdir -p "$d/lean/comparator" "$d/lean/Challenge" &&
  echo a > "$d/lean/comparator/c.json" && echo a > "$d/README.md" && g add -A && g commit -qm base &&
  g branch stale && g branch real &&
  echo b > "$d/lean/comparator/c.json" && g commit -qam main-moves-trusted &&
  g checkout -q stale && echo b > "$d/README.md" && g commit -qam unrelated &&
  g checkout -q real && echo x > "$d/lean/Challenge/X.lean" && g add -A && g commit -qm trusted || { echo "self-test FAIL: fixture"; rm -rf "$d"; return 1; }
  (cd "$d" && changed_paths main stale | flag false) >/dev/null
  [ $? -eq 0 ] || { echo "self-test FAIL: stale branch flagged for a base-side lean/comparator change"; rc=1; }
  (cd "$d" && changed_paths main real | flag false) >/dev/null
  [ $? -eq 1 ] || { echo "self-test FAIL: branch-side lean/Challenge change not flagged"; rc=1; }
  (cd "$d" && git diff --name-only main stale | flag false) >/dev/null
  [ $? -eq 1 ] || { echo "self-test FAIL: fixture does not reproduce the two-dot false positive"; rc=1; }
  rm -rf "$d"
  return $rc
}

if [ "${1:-}" = --self-test ]; then
  bad=0
  t() { local want=$1 rev=$2; shift 2; printf '%s\n' "$@" | flag "$rev" >/dev/null; local got=$?
        [ "$got" = "$want" ] || { echo "self-test FAIL: [$*] reviewed=$rev want $want got $got"; bad=1; }; }
  t 0 false "crates/ordeal/src/lib.rs" "lean/Sound.lean"
  t 1 false "lean/Challenge/LratCheckSound.lean"
  t 1 false "lean/comparator/lrat_check_sound.json"
  t 1 false "README.md" "lean/CnfSpec.lean"
  t 1 false "lean/EchoSpec.lean"
  t 0 true  "lean/Challenge/LratCheckSound.lean"
  t 0 false "lean/ChallengeNotes.md" "lean/CnfSpecProof.lean"
  git_self_test || bad=1
  [ $bad -eq 0 ] && echo "self-test: 7/7 path cases and 3/3 git-history cases hold"
  exit $bad
fi

[ $# -eq 2 ] || { echo "usage: $0 BASE_SHA HEAD_SHA | --self-test" >&2; exit 2; }
changed=$(changed_paths "$1" "$2") || { echo "git diff $1...$2 failed (no merge base?)" >&2; exit 2; }
printf '%s\n' "$changed" | flag "${CHALLENGE_REVIEWED:-false}"
