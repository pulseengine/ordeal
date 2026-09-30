#!/usr/bin/env bash
# check_commit_trailers.sh RANGE — commit traceability gate (#188).
#
# Fails if, over the git revision RANGE (e.g. origin/main..HEAD):
#   * rivet reports an orphan commit, a broken or a malformed artifact ref;
#   * any commit carries `Trace: skip` together with an `Implements:` or
#     `Verifies:` trailer. rivet treats the whole commit as exempt then, so
#     the real trailers are silently cancelled (27 of 60 commits did this).
# `rivet commits --strict` is not used: it also fails on every artifact that
# no commit in the range covers, which is always true for a PR range.
set -euo pipefail
RANGE="${1:?usage: check_commit_trailers.sh <git-range>}"

json="$(rivet commits --range "$RANGE" --format json)"
python3 - "$json" <<'PYEOF'
import json, sys
s = json.loads(sys.argv[1])["summary"]
print(f"commits: linked={s['linked']} exempt={s['exempt']} orphans={s['orphans']} "
      f"broken_refs={s['broken_refs']} malformed_refs={s['malformed_refs']}")
bad = {k: s[k] for k in ("orphans", "broken_refs", "malformed_refs") if s[k]}
if bad:
    print(f"FAIL  {bad}", file=sys.stderr)
    sys.exit(1)
PYEOF

fail=0
while read -r sha; do
  body="$(git log -1 --format=%B "$sha")"
  if printf '%s\n' "$body" | grep -qE '^Trace:[[:space:]]*skip' \
     && printf '%s\n' "$body" | grep -qE '^(Implements|Verifies):'; then
    echo "FAIL  $(git log -1 --format='%h %s' "$sha"): 'Trace: skip' cancels its Implements/Verifies trailers"
    fail=1
  fi
done < <(git rev-list "$RANGE")
[ "$fail" -eq 0 ] || exit 1
echo "PASS  commit trailers over $RANGE"
