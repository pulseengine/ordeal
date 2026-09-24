#!/usr/bin/env bash
# rivet: verifies VER-040
# rivet: verifies VER-041
# Post-release verification of an ordeal release on the PUBLISHED bytes —
# release-execution step 6, made a script so the evidence for the
# asset-level requirements (TR-033 cosign sums, TR-039 static musl assets,
# TR-040 SBOM in the signed sums, TR-043 VEX) is reproducible by anyone:
#
#   scripts/verify_release.sh v0.21.0
#
# Every check prints PASS/FAIL; exits nonzero on any FAIL. Needs gh, cosign,
# shasum, python3, tar, curl, network. The darwin-arm64 execution checks run
# only on an arm64 mac; elsewhere they are reported as SKIP.
set -uo pipefail
TAG="${1:?usage: $0 vX.Y.Z}"; BARE="${TAG#v}"; REPO=pulseengine/ordeal
D="${TMPDIR:-/tmp}/ordeal-verify-$TAG"
rm -rf "$D"; mkdir -p "$D"; cd "$D"
fail=0; ok() { echo "PASS $1"; }; bad() { echo "FAIL $1"; fail=1; }; skip() { echo "SKIP $1"; }

gh release download "$TAG" --repo "$REPO" --clobber >/dev/null 2>&1 || bad "download"
echo "--- assets:"; ls -1

# 1. every archive + SBOM + VEX is listed in the sums, and the sums verify
for f in ordeal-$TAG-*.tar.gz ordeal-$BARE.cdx.json ordeal-$BARE.vex.json; do
  [ -f "$f" ] && grep -q " ./$f\$" SHA256SUMS.txt && ok "listed in SHA256SUMS: $f" || bad "not listed in SHA256SUMS: $f"
done
shasum -a 256 -c SHA256SUMS.txt >/dev/null 2>&1 && ok "shasum -c over all listed assets" || bad "shasum -c"
cosign verify-blob --certificate-identity-regexp "https://github.com/$REPO/.github/workflows/release.yml@.*" \
  --certificate-oidc-issuer 'https://token.actions.githubusercontent.com' \
  --bundle SHA256SUMS.txt.cosign.bundle SHA256SUMS.txt >/dev/null 2>&1 && ok "cosign verify-blob on SHA256SUMS" || bad "cosign"

# 2. six archives: 4 gnu/darwin + 2 musl
n=$(ls ordeal-$TAG-*.tar.gz 2>/dev/null | wc -l | tr -d ' '); [ "$n" = "6" ] && ok "6 platform archives ($n)" || bad "expected 6 archives, got $n"
for t in x86_64-unknown-linux-musl aarch64-unknown-linux-musl; do [ -f "ordeal-$TAG-$t.tar.gz" ] && ok "musl asset $t" || bad "musl asset $t missing"; done
mkdir -p musl && tar -xzf ordeal-$TAG-x86_64-unknown-linux-musl.tar.gz -C musl ordeal 2>/dev/null
python3 - musl/ordeal <<'ELF' && ok "x86_64 musl binary is static (ELF: no PT_INTERP, no DT_NEEDED)" || bad "musl binary not static (ELF parse)"
import struct,sys
b=open(sys.argv[1],'rb').read(); assert b[:4]==b'\x7fELF' and b[4]==2
phoff,shoff=struct.unpack_from('<QQ',b,0x20); phentsize,phnum,shentsize,shnum=struct.unpack_from('<HHHH',b,0x36)
ptypes=[struct.unpack_from('<I',b,phoff+i*phentsize)[0] for i in range(phnum)]
assert 3 not in ptypes, "PT_INTERP present"
needed=0
for i in range(shnum):
    st,off,sz,es=struct.unpack_from('<I',b,shoff+i*shentsize+4)[0],*struct.unpack_from('<QQ',b,shoff+i*shentsize+0x18),struct.unpack_from('<Q',b,shoff+i*shentsize+0x38)[0]
    if st==6:
        for j in range(sz//24):
            tag=struct.unpack_from('<q',b,off+j*24)[0]
            if tag==1: needed+=1
assert needed==0, f"DT_NEEDED={needed}"
ELF

# 3. the darwin binary solves and self-reports the tag (arm64 mac only)
if [ "$(uname -s)-$(uname -m)" = "Darwin-arm64" ]; then
mkdir -p mac && tar -xzf ordeal-$TAG-aarch64-apple-darwin.tar.gz -C mac ordeal
[ "$(mac/ordeal --version)" = "ordeal $BARE" ] && ok "published binary reports ordeal $BARE" || bad "version: $(mac/ordeal --version)"
printf '(set-logic QF_BV)\n(declare-const a (_ BitVec 8))\n(assert (distinct (bvurem a #x01) #x00))\n(check-sat)\n' > q.smt2
mac/ordeal check q.smt2 2>/dev/null | head -1 | grep -qx unsat && ok "published binary: certified unsat" || bad "unsat smoke"
J=$(mac/ordeal check q.smt2 --format json 2>/dev/null); python3 - "$J" <<'PY' && ok "--format json unsat carries cnf+lrat" || bad "json shape"
import json,sys; d=json.loads(sys.argv[1]); assert d["verdict"]=="unsat" and d["certificate"]["clauses"] and d["certificate"]["lrat"]
PY

else
  skip "darwin-arm64 execution checks (host is $(uname -s)-$(uname -m))"
fi

# 4. SBOM + VEX validity and bom-link consistency
python3 - "$BARE" <<'PY' && ok "SBOM/VEX: valid CycloneDX 1.5, VEX bom-links the SBOM, records db commit + asserted-at" || bad "SBOM/VEX consistency"
import json,sys
bare=sys.argv[1]
s=json.load(open(f"ordeal-{bare}.cdx.json")); v=json.load(open(f"ordeal-{bare}.vex.json"))
assert s["bomFormat"]=="CycloneDX" and v["bomFormat"]=="CycloneDX" and v["specVersion"]=="1.5"
props={p["name"]:p["value"] for p in v["metadata"]["properties"]}
serial=s["serialNumber"][len("urn:uuid:"):]
assert props["ordeal:sbom"]==f"urn:cdx:{serial}/{s.get('version',1)}", (props["ordeal:sbom"], serial)
assert len(props["advisory-db.commit"])==40 and props["asserted-at"].endswith("Z")
assert props["ordeal:shipped-closure"]==f"ordeal@{bare},ordeal-lrat@{bare}", props["ordeal:shipped-closure"]
print("VEX statements:", len(v["vulnerabilities"]), "| SBOM components:", [c["name"] for c in s.get("components",[])])
PY

# 5. release body composed from tag annotation + rivet note
gh release view "$TAG" --repo "$REPO" --json body -q .body > body.md
grep -q "## Falsification statement" body.md && grep -q "Release note (rivet, from the trace)" body.md && grep -q "## Functionalities provided" body.md && grep -q "Not covered by this note" body.md && ok "release body: falsification + rivet note sections present" || bad "release body composition"
grep -q "TR-038" body.md && ok "release body lists TR-038 (from the trace)" || bad "body lacks in-scope artifacts"

# 6. crates.io
for c in ordeal ordeal-lrat; do
  V=$(curl -s -H "User-Agent: ordeal-release-verify (release-verify)" "https://crates.io/api/v1/crates/$c" | python3 -c 'import json,sys; print(json.load(sys.stdin)["crate"]["max_version"])' 2>/dev/null)
  [ "$V" = "$BARE" ] && ok "crates.io $c = $V" || bad "crates.io $c = '$V' (want $BARE)"
done
echo "=== result: $([ $fail = 0 ] && echo ALL PASS || echo FAILURES PRESENT)"; exit $fail
