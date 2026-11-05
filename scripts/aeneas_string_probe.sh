#!/usr/bin/env bash
# rivet: verifies VER-080
# Does a given Charon/Aeneas still turn String operations into axioms?
# (#282 / TR-080, docs/design/flattener-proof.md option A2.)
#
#   scripts/aeneas_string_probe.sh <charon> <aeneas>
#
# Translates lean/probe/string_names.rs (String names, ==, len, as_bytes)
# and lists the `^axiom` lines Aeneas emits. Prints BLOCKED when any String
# operation is an axiom (A2 would break the zero-axiom gate, so mirror.rs
# stays) and UNLOCKED when none is (re-open #282: the kernel could take
# String names directly). Exit 0 either way; exit 1 if a tool fails, so a
# broken toolchain is never read as an answer.
#
# Re-run on every Charon/Aeneas bump (lean/toolchain-pins.env). Prebuilt
# Aeneas release bundles (github.com/AeneasVerif/aeneas/releases) carry
# both binaries and a rust-toolchain file naming the nightly Charon needs
# (RUSTUP_TOOLCHAIN=<that nightly>, with rustc-dev).
set -uo pipefail
CHARON="${1:?usage: $0 <charon> <aeneas>}"; AENEAS="${2:?usage: $0 <charon> <aeneas>}"
cd "$(dirname "$0")/.."
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
"$CHARON" rustc --preset=aeneas --dest-file "$T/p.llbc" -- --crate-type=lib lean/probe/string_names.rs >"$T/charon.log" 2>&1 \
  || { echo "FAIL charon"; tail -5 "$T/charon.log"; exit 1; }
"$AENEAS" -backend lean "$T/p.llbc" -dest "$T/out" >"$T/aeneas.log" 2>&1 \
  || { echo "FAIL aeneas"; tail -5 "$T/aeneas.log"; exit 1; }
ls "$T"/out/*.lean >/dev/null 2>&1 || { echo "FAIL aeneas produced no Lean"; exit 1; }
# Sanity: the probe's own functions were translated (not a vacuous empty file).
grep -q "name_eq" "$T"/out/*.lean || { echo "FAIL name_eq missing from the translation"; exit 1; }
ax=$(grep -h '^axiom' "$T"/out/*.lean | sort -u)
echo "charon: $("$CHARON" version 2>&1 | head -1) | aeneas: $("$AENEAS" -version 2>&1 | head -1)"
echo "axioms:"; [ -n "$ax" ] && echo "$ax" | sed 's/^/  /'
if echo "$ax" | grep -q 'String'; then echo "BLOCKED: String operations are axioms"; else echo "UNLOCKED: no String axiom"; fi
