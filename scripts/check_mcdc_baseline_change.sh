#!/usr/bin/env bash
# The MC/DC ratchet may only loosen for a stated cause.
#
#   scripts/check_mcdc_baseline_change.sh BASE_BASELINE HEAD_BASELINE
#
# Compares two versions of mcdc/baseline.txt (the merge base's and the PR's).
# A file whose uncovered conditions (gap + dead) rose, whose proved conditions
# fell, or which left the baseline is a LOOSENING. A loosening passes only if
#   (a) the "Measured with witness X" header names a different witness version
#       (an instrument change, e.g. 0.45.0 -> 0.46.0 removing witness#352's
#       over-claim), or
#   (b) the PR's baseline adds a "# reason:" line the base did not have.
# Otherwise it exits 1 and names each loosened file. Tightening never needs a
# reason. Exit 2 on a usage error or an unreadable/empty baseline, so a missing
# file can never pass as "nothing loosened".
set -uo pipefail

[ $# -eq 2 ] || { echo "usage: $0 BASE_BASELINE HEAD_BASELINE" >&2; exit 2; }
BASE=$1; HEAD=$2
for f in "$BASE" "$HEAD"; do
  [ -s "$f" ] || { echo "check_mcdc_baseline_change: missing or empty baseline: $f" >&2; exit 2; }
  grep -q '^src/' "$f" || { echo "check_mcdc_baseline_change: no file rows in $f" >&2; exit 2; }
done

wver() { sed -n 's/.*Measured with witness \([0-9][0-9.]*\).*/\1/p' "$1" | head -1; }
BV=$(wver "$BASE"); HV=$(wver "$HEAD")
[ -n "$BV" ] && [ -n "$HV" ] || { echo "check_mcdc_baseline_change: no 'Measured with witness X' header" >&2; exit 2; }

# Columns: file decisions not_full gap_conditions dead_conditions proved_conditions
loosened=$(awk '
  FNR == NR { if ($1 ~ /^src\//) { u[$1] = $4 + $5; p[$1] = $6 }; next }
  $1 ~ /^src\// { seen[$1] = 1
    if ($1 in u) {
      if ($4 + $5 > u[$1]) print $1 ": uncovered " u[$1] " -> " $4 + $5
      if ($6 < p[$1])      print $1 ": proved " p[$1] " -> " $6
    } }
  END { for (f in u) if (!(f in seen)) print f ": removed from the baseline" }
' "$BASE" "$HEAD")

if [ -z "$loosened" ]; then echo "OK: the MC/DC baseline did not loosen"; exit 0; fi
echo "$loosened" | sed 's/^/loosened: /'
if [ "$BV" != "$HV" ]; then
  echo "OK: loosening explained by the witness version change $BV -> $HV"; exit 0
fi
if comm -13 <(grep '^# reason:' "$BASE" | sort) <(grep '^# reason:' "$HEAD" | sort) | grep -q .; then
  echo "OK: loosening explained by a new '# reason:' line:"
  comm -13 <(grep '^# reason:' "$BASE" | sort) <(grep '^# reason:' "$HEAD" | sort)
  exit 0
fi
echo "FAIL: the MC/DC baseline loosened with neither a witness version change (still $HV) nor a new '# reason:' line"
exit 1
