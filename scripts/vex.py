#!/usr/bin/env python3
# rivet: verifies VER-038
"""CycloneDX 1.5 VEX for ordeal releases (issue #146 / TR-043).

The VEX states, for the SHIPPED dependency closure only, which RustSec
advisories match and what they mean for ordeal. Decisions (maintainer,
2026-09-24): scope = shipped closure; weekly re-issue on the latest release
opens an issue for a human instead of publishing; `not_affected` is NEVER
generated.

Why "shipped closure": a release binary is built from `ordeal` + its normal
(non-dev) dependencies at default features. Cargo.lock also pins dev, bench,
fuzz and optional-feature crates that never reach a release artifact; an
advisory on one of those is not about the product, so it is not a VEX
statement. It is still recorded (as a property listing the ids) and gated
separately by `cargo deny` in CI, because those crates touch our build.

Judgements are HUMAN-AUTHORED in vex/judgements.json. A shipped-closure match
without a judgement is emitted as `in_triage` -- an honest state. The
generator never writes `not_affected` on its own: a justification such as
`code_not_reachable` is a claim about this source tree that only a person
can make, and a generated one would be a false statement signed into a
release.

Subcommands:
  generate   build the VEX document
  compare    exit 1 if two VEX documents make different statements
  self-test  exercise the rules above on synthetic inputs

Stdlib only: runs in the release job with no pip install.
"""

import argparse
import json
import re
import subprocess
import sys
import uuid

STATES = {
    "resolved",
    "resolved_with_pedigree",
    "exploitable",
    "in_triage",
    "false_positive",
    "not_affected",
}
JUSTIFICATIONS = {
    "code_not_present",
    "code_not_reachable",
    "requires_configuration",
    "requires_dependency",
    "requires_environment",
    "protected_by_compiler",
    "protected_at_runtime",
    "protected_at_perimeter",
    "protected_by_mitigating_control",
}


class VexError(Exception):
    pass


def shipped_closure():
    """(name, version) pairs a release binary is built from: ordeal's
    normal-edge dependency tree at default features (the same graph the
    CI dependency-freedom assertion checks)."""
    out = subprocess.run(
        ["cargo", "tree", "-p", "ordeal", "--edges", "normal", "--prefix", "none"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    closure = set()
    for line in out.splitlines():
        m = re.match(r"^(\S+) v(\S+)", line.strip())
        if m:
            closure.add((m.group(1), m.group(2)))
    if not closure:
        raise VexError("cargo tree returned an empty closure")
    return closure


def run_cargo_audit():
    # cargo audit exits nonzero when it finds vulnerabilities; the JSON is
    # still complete, so the exit code is not treated as failure here.
    p = subprocess.run(["cargo", "audit", "--json"], capture_output=True, text=True)
    try:
        return json.loads(p.stdout)
    except json.JSONDecodeError as e:
        raise VexError(f"cargo audit produced no JSON (exit {p.returncode}): {p.stderr[-400:]}") from e


def audit_matches(audit):
    """Every advisory match that states a vulnerability: `vulnerabilities`
    plus `unsound` warnings. `unmaintained` / `yanked` are not
    vulnerabilities (yanked crates are rejected by cargo-deny instead)."""
    found = []
    for v in audit.get("vulnerabilities", {}).get("list", []):
        found.append((v["advisory"], v["package"]))
    for w in audit.get("warnings", {}).get("unsound", []) or []:
        if w.get("advisory"):
            found.append((w["advisory"], w["package"]))
    return found


def load_judgements(path):
    if not path:
        return {}
    with open(path) as f:
        j = json.load(f)
    for adv_id, entry in j.items():
        state = entry.get("state")
        if state not in STATES:
            raise VexError(f"{adv_id}: state {state!r} is not a CycloneDX 1.5 analysis state")
        if state == "not_affected":
            if entry.get("justification") not in JUSTIFICATIONS:
                raise VexError(f"{adv_id}: not_affected requires a CycloneDX justification")
        if state in ("not_affected", "false_positive") and not entry.get("detail"):
            raise VexError(f"{adv_id}: {state} requires a human-written detail")
        if not entry.get("classified-by"):
            raise VexError(f"{adv_id}: every judgement records who made it (classified-by)")
    return j


def sbom_refs(sbom):
    """(name, version) -> bom-link for every component of the release SBOM."""
    serial = sbom["serialNumber"]
    if not serial.startswith("urn:uuid:"):
        raise VexError(f"SBOM serialNumber {serial!r} is not a urn:uuid")
    base = f"urn:cdx:{serial[len('urn:uuid:'):]}/{sbom.get('version', 1)}"
    refs = {}
    comps = list(sbom.get("components", []))
    root = sbom.get("metadata", {}).get("component")
    if root:
        comps.append(root)
    for c in comps:
        if "bom-ref" in c:
            refs[(c["name"], c.get("version"))] = f"{base}#{c['bom-ref']}"
    return base, refs


def build_vex(*, sbom, audit, closure, judgements, version, doc_version, asserted_at, serial=None):
    base, refs = sbom_refs(sbom)
    in_closure, outside = [], []
    for advisory, package in audit_matches(audit):
        key = (package["name"], package["version"])
        (in_closure if key in closure else outside).append((advisory, package))

    vulns = []
    for advisory, package in sorted(in_closure, key=lambda ap: (ap[0]["id"], ap[1]["name"])):
        key = (package["name"], package["version"])
        if key not in refs:
            raise VexError(f"{advisory['id']}: {key} is in the shipped closure but not in the SBOM")
        j = judgements.get(advisory["id"])
        analysis = {"state": "in_triage"}
        if j:
            analysis = {"state": j["state"]}
            for k in ("justification", "detail"):
                if j.get(k):
                    analysis[k] = j[k]
        vulns.append(
            {
                "id": advisory["id"],
                "source": {"name": "RustSec", "url": advisory.get("url") or f"https://rustsec.org/advisories/{advisory['id']}"},
                "description": advisory.get("title", ""),
                "affects": [{"ref": refs[key]}],
                "analysis": analysis,
            }
        )

    db_commit = audit.get("database", {}).get("last-commit")
    if not db_commit:
        raise VexError("audit JSON carries no advisory-db commit; refusing to assert without it")
    props = [
        {"name": "advisory-db.commit", "value": db_commit},
        {"name": "asserted-at", "value": asserted_at},
        {"name": "ordeal:vex-scope", "value": "shipped-closure"},
        {"name": "ordeal:shipped-closure", "value": ",".join(f"{n}@{v}" for n, v in sorted(closure))},
        {"name": "ordeal:sbom", "value": base},
        {
            "name": "ordeal:out-of-closure-advisories",
            "value": ",".join(sorted({a["id"] for a, _ in outside})) or "none",
        },
    ]
    return {
        "bomFormat": "CycloneDX",
        "specVersion": "1.5",
        "serialNumber": serial or f"urn:uuid:{uuid.uuid4()}",
        "version": doc_version,
        "metadata": {
            "timestamp": asserted_at,
            "component": {"type": "application", "name": "ordeal", "version": version},
            "properties": props,
        },
        "vulnerabilities": vulns,
    }


def statements(vex):
    """What a VEX document *says*: the comparison key for re-issue."""
    return sorted(
        (v["id"], v["analysis"]["state"], v["analysis"].get("justification", ""))
        for v in vex.get("vulnerabilities", [])
    )


def cmd_generate(a):
    with open(a.sbom) as f:
        sbom = json.load(f)
    if a.audit_json:
        with open(a.audit_json) as f:
            audit = json.load(f)
    else:
        audit = run_cargo_audit()
    vex = build_vex(
        sbom=sbom,
        audit=audit,
        closure=shipped_closure(),
        judgements=load_judgements(a.judgements),
        version=a.version,
        doc_version=a.doc_version,
        asserted_at=a.asserted_at,
    )
    with open(a.out, "w") as f:
        json.dump(vex, f, indent=2)
        f.write("\n")
    triage = [v["id"] for v in vex["vulnerabilities"] if v["analysis"]["state"] == "in_triage"]
    print(f"VEX written: {a.out} ({len(vex['vulnerabilities'])} statement(s); in_triage: {triage or 'none'})")


def cmd_compare(a):
    with open(a.old) as f:
        old = statements(json.load(f))
    with open(a.new) as f:
        new = statements(json.load(f))
    if old == new:
        print("VEX statements unchanged")
        return 0
    print("VEX statements CHANGED")
    print("  was:", old or "(none)")
    print("  now:", new or "(none)")
    return 1


def cmd_self_test(_a):
    sbom = {
        "serialNumber": "urn:uuid:00000000-0000-0000-0000-000000000001",
        "version": 1,
        "metadata": {"component": {"name": "ordeal", "version": "9.9.9", "bom-ref": "root"}},
        "components": [{"name": "dep", "version": "1.0.0", "bom-ref": "dep-ref"}],
    }

    def audit(*matches):
        return {
            "database": {"last-commit": "abc123"},
            "vulnerabilities": {
                "list": [
                    {"advisory": {"id": i, "title": "t", "url": "u"}, "package": {"name": n, "version": v}}
                    for i, n, v in matches
                ]
            },
        }

    closure = {("ordeal", "9.9.9"), ("dep", "1.0.0")}
    kw = dict(sbom=sbom, closure=closure, version="9.9.9", doc_version=1, asserted_at="2026-01-01T00:00:00Z", serial="urn:uuid:x")
    checks = []

    # 1. A shipped-closure match with no judgement is in_triage, never not_affected.
    v = build_vex(audit=audit(("RUSTSEC-1", "dep", "1.0.0")), judgements={}, **kw)
    checks.append(("untriaged match -> in_triage", v["vulnerabilities"][0]["analysis"] == {"state": "in_triage"}))
    checks.append(("bom-link points into the SBOM", v["vulnerabilities"][0]["affects"][0]["ref"] == "urn:cdx:00000000-0000-0000-0000-000000000001/1#dep-ref"))

    # 2. A human judgement is carried verbatim.
    j = {"RUSTSEC-1": {"state": "not_affected", "justification": "code_not_reachable", "detail": "only the X path is used", "classified-by": "maintainer"}}
    v = build_vex(audit=audit(("RUSTSEC-1", "dep", "1.0.0")), judgements=load_judgements_from(j), **kw)
    a0 = v["vulnerabilities"][0]["analysis"]
    checks.append(("human judgement carried", a0["state"] == "not_affected" and a0["justification"] == "code_not_reachable"))

    # 3. A match outside the shipped closure is not a statement about the product.
    v = build_vex(audit=audit(("RUSTSEC-2", "devdep", "3.0.0")), judgements={}, **kw)
    props = {p["name"]: p["value"] for p in v["metadata"]["properties"]}
    checks.append(("out-of-closure match excluded", v["vulnerabilities"] == []))
    checks.append(("out-of-closure match disclosed as a property", props["ordeal:out-of-closure-advisories"] == "RUSTSEC-2"))
    checks.append(("advisory-db commit recorded", props["advisory-db.commit"] == "abc123"))

    # 4. Invalid judgements are refused, not silently emitted.
    for bad, why in [
        ({"R": {"state": "fine", "classified-by": "m"}}, "unknown state"),
        ({"R": {"state": "not_affected", "detail": "d", "classified-by": "m"}}, "not_affected without justification"),
        ({"R": {"state": "not_affected", "justification": "code_not_reachable", "classified-by": "m"}}, "not_affected without detail"),
        ({"R": {"state": "in_triage"}}, "judgement without classified-by"),
    ]:
        try:
            load_judgements_from(bad)
            checks.append((f"refuses {why}", False))
        except VexError:
            checks.append((f"refuses {why}", True))

    # 5. No db commit -> refuse to assert.
    try:
        build_vex(audit={"vulnerabilities": {"list": []}}, judgements={}, **kw)
        checks.append(("refuses without db commit", False))
    except VexError:
        checks.append(("refuses without db commit", True))

    # 6. compare keys on statements, not on timestamps or serials.
    a1 = build_vex(audit=audit(), judgements={}, **kw)
    a2 = build_vex(audit=audit(), judgements={}, **{**kw, "asserted_at": "2027-01-01T00:00:00Z"})
    checks.append(("compare ignores the timestamp", statements(a1) == statements(a2)))
    b = build_vex(audit=audit(("RUSTSEC-1", "dep", "1.0.0")), judgements={}, **kw)
    checks.append(("compare sees a new match", statements(a1) != statements(b)))

    failed = [name for name, ok in checks if not ok]
    for name, ok in checks:
        print(("PASS " if ok else "FAIL ") + name)
    print(f"{len(checks) - len(failed)}/{len(checks)} self-test checks passed")
    return 1 if failed else 0


def load_judgements_from(obj):
    import tempfile

    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
        json.dump(obj, f)
        path = f.name
    return load_judgements(path)


def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = p.add_subparsers(dest="cmd", required=True)
    g = sub.add_parser("generate")
    g.add_argument("--sbom", required=True)
    g.add_argument("--out", required=True)
    g.add_argument("--version", required=True, help="ordeal version the VEX describes")
    g.add_argument("--doc-version", type=int, default=1, help="1 at release; +1 per re-issue")
    g.add_argument("--asserted-at", required=True, help="RFC 3339 UTC; pass $(date -u ...)")
    g.add_argument("--judgements", default="vex/judgements.json")
    g.add_argument("--audit-json", help="use a saved `cargo audit --json` instead of running it")
    c = sub.add_parser("compare")
    c.add_argument("old")
    c.add_argument("new")
    sub.add_parser("self-test")
    a = p.parse_args()
    try:
        if a.cmd == "generate":
            cmd_generate(a)
            return 0
        if a.cmd == "compare":
            return cmd_compare(a)
        return cmd_self_test(a)
    except VexError as e:
        print(f"vex: {e}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
