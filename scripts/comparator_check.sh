#!/usr/bin/env bash
# Comparator gate: every headline theorem's proof matches its trusted
# statement, uses only the permitted axioms, and is accepted by the Lean
# kernel (and nanoda, when the config enables it).
#
#   cd lean && bash ../scripts/comparator_check.sh
#
# The theorem list is DERIVED from lean/comparator/*.json, never typed here.
# Before comparator runs, the configs are checked against the tree:
#   - there is at least one config (an empty list must not pass);
#   - each config's challenge module is a file under Challenge/ that declares
#     every listed theorem, and its solution module exists;
#   - every listed theorem is pinned in AxiomCheck.lean (#print axioms);
#   - every Challenge/*.lean file is some config's challenge module, and every
#     theorem a challenge declares is listed in that config.
# So a new challenge cannot go unrun and a configured theorem cannot go
# unpinned. Needs comparator, lean4export and landrun (and nanoda_bin) on PATH.
set -uo pipefail

[ -d comparator ] && [ -d Challenge ] || { echo "run from lean/" >&2; exit 2; }
fail=0
err() { echo "::error::$1"; fail=1; }

# Comparator's config is flat JSON; read one field with jq.
command -v jq >/dev/null || { echo "jq is required" >&2; exit 2; }
shopt -s nullglob
cfgs=(comparator/*.json)
[ ${#cfgs[@]} -gt 0 ] || { err "no comparator configs under lean/comparator/"; exit 1; }

mod2file() { echo "${1//.//}.lean"; }
declared() { # theorem short names declared in a challenge file
  grep -oE '^theorem [A-Za-z_][A-Za-z0-9_'"'"']*' "$1" | awk '{print $2}' | sort -u; }

seen_challenges=""
for c in "${cfgs[@]}"; do
  ch=$(jq -r .challenge_module "$c"); so=$(jq -r .solution_module "$c")
  chf=$(mod2file "$ch"); sof=$(mod2file "$so")
  [ -f "$chf" ] || { err "$c: challenge module $ch has no file $chf"; continue; }
  case "$chf" in Challenge/*) ;; *) err "$c: challenge $chf is not under Challenge/";; esac
  [ -f "$sof" ] || err "$c: solution module $so has no file $sof"
  seen_challenges="$seen_challenges $chf"
  names=$(jq -r '.theorem_names[]' "$c")
  [ -n "$names" ] || err "$c: empty theorem_names"
  for full in $names; do
    short=${full##*.}
    declared "$chf" | grep -qx "$short" || err "$c: $full is not declared in $chf"
    grep -qE "^#print axioms $full\$" AxiomCheck.lean || err "$c: $full has no '#print axioms' pin in AxiomCheck.lean"
  done
  for short in $(declared "$chf"); do
    echo "$names" | grep -qE "(^|\.)$short\$" || err "$chf declares theorem $short, which $c does not list"
  done
  ax=$(jq -r '.permitted_axioms | sort | join(",")' "$c")
  [ "$ax" = "Classical.choice,Quot.sound,propext" ] || err "$c: permitted_axioms is [$ax], not exactly propext/Quot.sound/Classical.choice"
done
for f in Challenge/*.lean Challenge/**/*.lean; do
  case " $seen_challenges " in *" $f "*) ;; *) err "$f is no config's challenge module";; esac
done
[ $fail -eq 0 ] || { echo "comparator configs are inconsistent with the tree; not running comparator"; exit 1; }
echo "configs: ${#cfgs[@]}, all consistent with Challenge/ and AxiomCheck.lean"

for c in "${cfgs[@]}"; do
  s=$(date +%s)
  if lake env comparator "$c" > "${TMPDIR:-/tmp}/comparator-$(basename "$c" .json).log" 2>&1; then
    echo "ok: $(jq -r '.theorem_names|join(" ")' "$c") ($(( $(date +%s) - s ))s, nanoda=$(jq -r .enable_nanoda "$c"))"
  else
    err "comparator refused $c"; grep -v '^Exporting' "${TMPDIR:-/tmp}/comparator-$(basename "$c" .json).log" | tail -5
  fi
done
exit $fail
