#!/usr/bin/env bash
# Planted controls for the comparator gate (scripts/comparator_check.sh).
# Each mutant of the solution module Sound.lean must make comparator FAIL on
# lean/comparator/lrat_check_sound.json for its own reason, and the restored
# file must PASS.
#
#   cd lean && bash ../scripts/comparator_controls.sh
#
# Mutants (each must BUILD first, so the refusal comes from comparator, not
# from a broken elaboration):
#   weakened statement : the conclusion gains `∨ True`
#   extra axiom        : the proof term references a new `axiom`
#   mismatched name    : the solution theorem is renamed
#
# Sound.lean is restored from git after every mutant and on exit. Exit 1 if a
# mutant is accepted, is refused for the wrong reason, or does not build, or if
# the restored file is refused; exit 2 on a usage error.
set -uo pipefail

CFG=comparator/lrat_check_sound.json
F=Sound.lean
LOG="${TMPDIR:-/tmp}/comparator-control.log"
BLOG="${TMPDIR:-/tmp}/comparator-control-build.log"
[ -f "$CFG" ] && [ -f "$F" ] || { echo "run from lean/ (missing $CFG or $F)" >&2; exit 2; }
git diff --quiet -- "$F" || { echo "$F has local changes; refusing to mutate it" >&2; exit 2; }
trap 'git checkout -- "$F"' EXIT

ANCHOR='    unsat (cnf.val.map (fun c => c.val)) :=
  pure_check_sound _ _ (kernel_refines_pure cnf steps hfit h)'
grep -qF 'pure_check_sound _ _ (kernel_refines_pure cnf steps hfit h)' "$F" \
  || { echo "control anchor missing in $F" >&2; exit 2; }

fail=0
replace_body() { OLD="$ANCHOR" NEW="$1" perl -0pi -e 's/\Q$ENV{OLD}\E/$ENV{NEW}/ or die "anchor not found\n"' "$F"; }
must_build() {
  lake build Sound > "$BLOG" 2>&1 && return 0
  echo "FAIL: mutant '$1' does not build, so it tests nothing"; tail -3 "$BLOG"; fail=1; return 1
}
check_red() { # $1 = mutant name, $2 = regex the refusal must match
  local name=$1 want=$2
  if lake env comparator "$CFG" > "$LOG" 2>&1; then
    echo "FAIL: mutant '$name' was ACCEPTED by comparator"; fail=1
  elif grep -qE "$want" "$LOG"; then
    echo "ok: mutant '$name' refused: $(grep -E "$want" "$LOG" | head -1 | cut -c1-160)"
  else
    echo "FAIL: mutant '$name' refused for the wrong reason (want /$want/):"
    grep -v '^Exporting' "$LOG" | tail -3; fail=1
  fi
  git checkout -- "$F"
}

replace_body '    unsat (cnf.val.map (fun c => c.val)) ∨ True :=
  Or.inl (pure_check_sound _ _ (kernel_refines_pure cnf steps hfit h))'
must_build "weakened statement" && check_red "weakened statement" 'statement do not match'
git checkout -- "$F"

replace_body '    unsat (cnf.val.map (fun c => c.val)) :=
  (fun _ => pure_check_sound _ _ (kernel_refines_pure cnf steps hfit h)) ordeal_planted_axiom'
perl -0pi -e 's/^theorem lrat_check_sound\n/axiom ordeal_planted_axiom : True\n\ntheorem lrat_check_sound\n/m or die "anchor\n"' "$F"
must_build "extra axiom" && check_red "extra axiom" 'Illegal axiom detected'
git checkout -- "$F"

perl -0pi -e 's/^theorem lrat_check_sound\n/theorem lrat_check_sound_renamed\n/m or die "anchor\n"' "$F"
must_build "mismatched name" && check_red "mismatched name" 'lrat_check_sound not found'
git checkout -- "$F"

if lake env comparator "$CFG" > "$LOG" 2>&1; then echo "ok: restored Sound.lean accepted"
else echo "FAIL: restored Sound.lean refused"; grep -v '^Exporting' "$LOG" | tail -5; fail=1; fi
exit $fail
