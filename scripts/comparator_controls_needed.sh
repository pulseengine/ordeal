#!/usr/bin/env bash
# Decide whether the comparator planted controls (scripts/comparator_controls.sh)
# run in this CI event. They cost about 2.5 min, so a pull request runs them
# only when it touches what they exercise: the Lean tree, the comparator
# scripts, or the workflow that wires them. Every push to main runs them, so
# each commit that lands is covered.
#
#   scripts/comparator_controls_needed.sh EVENT [BASE_SHA HEAD_SHA]
#   scripts/comparator_controls_needed.sh --self-test
#
# Prints run=true|false (for $GITHUB_OUTPUT). Fails closed: an unknown event
# or a failed diff prints run=true.
set -uo pipefail

RELEVANT_RE='^(lean/|scripts/comparator_|\.github/workflows/ci\.yml$)'

decide() { # stdin: changed paths
  if grep -qE "$RELEVANT_RE"; then echo run=true; else echo run=false; fi
}

if [ "${1:-}" = --self-test ]; then
  bad=0
  t() { local want=$1; shift; local got; got=$(printf '%s\n' "$@" | decide)
        [ "$got" = "run=$want" ] || { echo "self-test FAIL: [$*] want run=$want got $got"; bad=1; }; }
  t true  "lean/Sound.lean"
  t true  "crates/ordeal/src/lib.rs" "lean/Challenge/LratCheckSound.lean"
  t true  "scripts/comparator_check.sh"
  t true  ".github/workflows/ci.yml"
  t false "crates/ordeal/src/lib.rs" "README.md"
  t false ".github/workflows/ci.yml.bak" "scripts/check_challenge_files.sh"
  t false ""
  [ $bad -eq 0 ] && echo "self-test: 7/7 cases hold"
  exit $bad
fi

case "${1:-}" in
  push) echo run=true ;;
  pull_request)
    [ $# -eq 3 ] || { echo "usage: $0 pull_request BASE_SHA HEAD_SHA" >&2; echo run=true; exit 0; }
    changed=$(git diff --name-only "$2" "$3") || { echo "git diff failed; running the controls" >&2; echo run=true; exit 0; }
    printf '%s\n' "$changed" | decide ;;
  *) echo "unknown event '${1:-}'; running the controls" >&2; echo run=true ;;
esac
