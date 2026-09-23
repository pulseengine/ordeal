#!/usr/bin/env bash
# check_verification_citations.sh — standing counter-measure for issue #141
# (rivet verification-citation rot: verified artifacts whose steps.run cited
# commands that ran ZERO tests but exited green, or named crates/features that
# no longer exist).
#
# STATIC check only — the cited commands are never executed. Two invariants:
#   1. Every `cargo test` steps.run in artifacts/verification.yaml that names
#      `-p <crate>` must reference a crate that exists in this workspace.
#   2. Every `cargo test` leg containing ` -- ` filter tokens has each token
#      checked against a test-name inventory generated ONCE (default feature
#      set) via:
#        cargo test -p ordeal --lib -- --list
#        cargo test -p ordeal-lrat -- --list
#        cargo test -p ordeal --test cli_baseline -- --list
#      A filter token matching zero inventory lines is exactly the class-1
#      defect of #141 (vacuous green) => exit 1.
# Legs mentioning --features or an external repo are SKIPped with a line, since
# the default-features inventory cannot vouch for them.
#
# Deliberately NOT wired into CI here — that wiring decision belongs to #138.

set -u

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
YAML="$ROOT/artifacts/verification.yaml"
TMPDIR_LOCAL="$(mktemp -d)"
trap 'rm -rf "$TMPDIR_LOCAL"' EXIT
RUNS="$TMPDIR_LOCAL/runs.txt"
INVENTORY="$TMPDIR_LOCAL/inventory.txt"

[ -f "$YAML" ] || { echo "FATAL: $YAML not found" >&2; exit 2; }

# --- 1. Extract every steps.run (python yaml preferred, sed fallback) --------
if python3 -c 'import yaml' 2>/dev/null; then
  python3 - "$YAML" >"$RUNS" <<'PYEOF'
import sys, yaml
with open(sys.argv[1]) as f:
    doc = yaml.safe_load(f)
for art in doc.get("artifacts", []):
    run = (art.get("fields") or {}).get("steps", {}).get("run")
    if run:
        print(f"{art.get('id', '?')}\t{run}")
PYEOF
else
  # Fallback: pair each `- id:` with the following `run:` line.
  awk '
    /^  - id: /       { id = $3 }
    /^        run: /  {
      line = $0
      sub(/^        run: /, "", line)
      gsub(/^"|"$/, "", line)
      print id "\t" line
    }
  ' "$YAML" >"$RUNS"
fi

[ -s "$RUNS" ] || { echo "FATAL: extracted zero steps.run entries" >&2; exit 2; }

# --- 2. Workspace crate list -------------------------------------------------
if CRATES="$(cd "$ROOT" && cargo metadata --no-deps --format-version 1 2>/dev/null \
    | python3 -c 'import json,sys; [print(p["name"]) for p in json.load(sys.stdin)["packages"]]' 2>/dev/null)" \
    && [ -n "$CRATES" ]; then
  :
else
  CRATES="$(grep -h '^name *= *"' "$ROOT"/crates/*/Cargo.toml | sed 's/.*"\(.*\)".*/\1/')"
fi

# --- 3. Test-name inventory, generated once (default feature set) ------------
{
  (cd "$ROOT" && cargo test -p ordeal --lib -- --list 2>/dev/null)
  (cd "$ROOT" && cargo test -p ordeal-lrat -- --list 2>/dev/null)
  (cd "$ROOT" && cargo test -p ordeal --test cli_baseline -- --list 2>/dev/null)
} | grep ': test$' >"$INVENTORY"

if ! [ -s "$INVENTORY" ]; then
  echo "FATAL: test inventory came back empty (build broken?)" >&2
  exit 2
fi
echo "inventory: $(wc -l <"$INVENTORY" | tr -d ' ') test names"

# --- 4. Check each cargo-test leg --------------------------------------------
fail=0
while IFS=$'\t' read -r id run; do
  # Split the command into legs on ';' and '&&'.
  echo "$run" | awk '{gsub(/&&|;/, "\n"); print}' | while IFS= read -r leg; do
    # Trim whitespace and env-var prefixes (FOO=bar cargo test ...).
    leg="$(echo "$leg" | sed 's/^ *//; s/ *$//; s/^\([A-Z_][A-Z0-9_]*=[^ ]* \)*//')"
    case "$leg" in
      "cargo test"*) ;;
      *)
        if echo "$leg" | grep -Eq 'pulseengine/|bazel'; then
          echo "SKIP  $id: external leg: $leg"
        fi
        continue
        ;;
    esac
    if echo "$leg" | grep -q -- '--features'; then
      echo "SKIP  $id: non-default features (inventory cannot vouch): $leg"
      continue
    fi
    # Invariant 1: -p <crate> exists in the workspace.
    crate="$(echo "$leg" | sed -n 's/.* -p \([^ ]*\).*/\1/p')"
    if [ -n "$crate" ] && ! printf '%s\n' "$CRATES" | grep -qx "$crate"; then
      echo "FAIL  $id: cites crate '$crate' not in workspace: $leg"
      echo fail >>"$TMPDIR_LOCAL/failed"
      continue
    fi
    # Invariant 2: every filter token after ' -- ' matches >=1 inventory line.
    case "$leg" in
      *" -- "*)
        tokens="$(echo "${leg#* -- }" | tr ' ' '\n' | grep -v '^-' | grep -v '^$' || true)"
        for tok in $tokens; do
          n="$(grep -cF -- "$tok" "$INVENTORY" || true)"
          if [ "${n:-0}" -eq 0 ]; then
            echo "FAIL  $id: filter token '$tok' matches ZERO tests in inventory: $leg"
            echo fail >>"$TMPDIR_LOCAL/failed"
          else
            echo "ok    $id: '$tok' -> $n test(s)"
          fi
        done
        ;;
    esac
  done
done <"$RUNS"

if [ -f "$TMPDIR_LOCAL/failed" ]; then
  echo "RESULT: FAIL — rotted citations found" >&2
  exit 1
fi
echo "RESULT: PASS — all cargo-test citations resolve against the workspace and test inventory"
exit 0
