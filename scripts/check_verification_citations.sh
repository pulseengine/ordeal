#!/usr/bin/env bash
# check_verification_citations.sh — standing counter-measure for issue #141
# (rivet verification-citation rot: verified artifacts whose steps.run cited
# commands that ran ZERO tests but exited green, or named crates, test
# targets or features that no longer exist).
#
# STATIC check only — the cited commands are never executed. For every
# `cargo test` leg of every `steps` run in artifacts/*.yaml:
#   1. `-p <crate>` names a workspace crate;
#   2. `--test <name>` names an existing integration-test target;
#   3. every test-name filter (positional before ` -- `, or after it) matches
#      >= 1 name in the default-features test inventory
#      (`cargo test --workspace -- --list`). A filter matching zero tests is
#      the class-1 defect of #141 (vacuous green) => exit 1.
# Legs with `--features` are reported as SKIP and counted: the default
# inventory cannot vouch for feature-gated test names.
#
# Issue #187: this script used to crash on string-shaped `steps` and still
# exit 0 (no pipefail), and only read verification.yaml. Any internal error
# now exits non-zero, never 0.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TMPDIR_LOCAL="$(mktemp -d)"
trap 'rm -rf "$TMPDIR_LOCAL"' EXIT
INVENTORY="$TMPDIR_LOCAL/inventory.txt"
META="$TMPDIR_LOCAL/metadata.json"

python3 -c 'import yaml' || { echo "FATAL: python3 with PyYAML is required" >&2; exit 2; }

(cd "$ROOT" && cargo metadata --no-deps --format-version 1) >"$META" \
  || { echo "FATAL: cargo metadata failed" >&2; exit 2; }

# Test-name inventory, generated once (default feature set, whole workspace).
(cd "$ROOT" && cargo test -q --workspace -- --list 2>/dev/null) \
  | { grep ': test$' || true; } >"$INVENTORY"
[ -s "$INVENTORY" ] || { echo "FATAL: test inventory came back empty (build broken?)" >&2; exit 2; }
echo "inventory: $(wc -l <"$INVENTORY" | tr -d ' ') test names"

python3 - "$ROOT" "$META" "$INVENTORY" <<'PYEOF'
import glob, json, os, re, shlex, sys
import yaml

root, meta_path, inv_path = sys.argv[1:4]
meta = json.load(open(meta_path))
crates = {p["name"] for p in meta["packages"]}
test_targets = {t["name"] for p in meta["packages"] for t in p["targets"] if "test" in t["kind"]}
inventory = [l.rsplit(": test", 1)[0] for l in open(inv_path).read().splitlines()]

# cargo options that consume the following token
CARGO_VALUE = {"-p", "--package", "--features", "-F", "--test", "--example", "--bin",
               "--bench", "--target", "-j", "--jobs", "--manifest-path", "--profile",
               "--color", "--target-dir", "-Z", "--exclude"}
# libtest options that consume the following token (the --skip value is not a
# filter that must match: skipping nothing is harmless)
HARNESS_VALUE = {"--test-threads", "--skip", "--format", "--color", "-Z", "--logfile"}

def runs():
    for path in sorted(glob.glob(os.path.join(root, "artifacts", "*.yaml"))):
        doc = yaml.safe_load(open(path)) or {}
        for art in doc.get("artifacts") or []:
            steps = (art.get("fields") or {}).get("steps")
            if isinstance(steps, dict):
                run = steps.get("run")
            elif isinstance(steps, str):
                run = steps[len("run:"):].strip() if steps.startswith("run:") else None
            elif steps is None:
                run = None
            else:
                raise TypeError(f"{art.get('id')}: unsupported steps shape {type(steps).__name__}")
            if run:
                yield os.path.basename(path), art.get("id", "?"), str(run)

fails = checked = skipped = 0
for fname, aid, run in runs():
    for leg in re.split(r"&&|;", run):
        leg = leg.strip()
        leg = re.sub(r"^(?:[A-Z_][A-Z0-9_]*=\S*\s+)*", "", leg)
        if not leg.startswith("cargo test"):
            continue
        toks = shlex.split(leg)[2:]
        if any(t in ("--features", "-F") or t.startswith("--features=") for t in toks):
            print(f"SKIP  {aid}: non-default features (inventory cannot vouch): {leg}")
            skipped += 1
            continue
        checked += 1
        filters, i, harness = [], 0, False
        while i < len(toks):
            t = toks[i]
            if t == "--" and not harness:
                harness = True
            elif not harness and t in CARGO_VALUE:
                v = toks[i + 1] if i + 1 < len(toks) else ""
                if t in ("-p", "--package") and v not in crates:
                    print(f"FAIL  {aid}: cites crate '{v}' not in workspace: {leg}"); fails += 1
                if t == "--test" and v not in test_targets:
                    print(f"FAIL  {aid}: cites test target '{v}' that does not exist: {leg}"); fails += 1
                i += 1
            elif harness and t in HARNESS_VALUE:
                i += 1
            elif not t.startswith("-"):
                filters.append(t)
            i += 1
        for tok in filters:
            n = sum(tok in name for name in inventory)
            if n == 0:
                print(f"FAIL  {aid}: filter '{tok}' matches ZERO tests in inventory: {leg}"); fails += 1
            else:
                print(f"ok    {aid}: '{tok}' -> {n} test(s)")

print(f"legs checked: {checked}, skipped (features): {skipped}")
if checked == 0:
    print("FATAL: zero cargo-test legs checked", file=sys.stderr); sys.exit(2)
if fails:
    print(f"RESULT: FAIL — {fails} rotted citation(s)", file=sys.stderr); sys.exit(1)
print("RESULT: PASS — all cargo-test citations resolve against the workspace and test inventory")
PYEOF
