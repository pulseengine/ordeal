#!/usr/bin/env python3
# rivet: verifies VER-074
"""claim_check — gate ordeal's documentation claims against live evidence (TR-074).

A README is a claim about the system, the same species as a requirement.
`claims.yaml` (repo root) binds each load-bearing doc claim — what is proven,
by which theorem, what is trusted, every stated number, the badges — to
evidence a machine re-derives from the tree. The Test job runs this on every
change; drift between a claim and the source fails the build.

Adapted from the pulseengine-claude `claim-verification` reference
implementation (claim-check.py, skill v0.4.0). Stdlib + PyYAML only.

Usage:  scripts/claim_check.py [claims.yaml]     (default: ./claims.yaml)
        scripts/claim_check.py --self-test        (every predicate, both ways)
Exit:   0 = all claims hold · 1 = one or more drifted · 2 = usage / internal

Evidence predicates (all paths and globs resolve against the claims file's
directory, never the CWD — a glob that matches no file FAILS, so a predicate
can never green by measuring nothing):

  file-exists   path                       the proof / harness the claim rests on is present
  count-min     pattern glob min           PRESENCE: the pattern must appear >= min times
                                            (catches drift-to-absent: a theorem renamed away,
                                            a version bumped, a CI step deleted)
  count-max     pattern glob max           GROWTH: the pattern may appear <= max times
                                            (zero-sorry / zero-axiom claims: max 0)
  no-new        pattern glob recorded      alias of count-max with the ledger's recorded count
  verbatim      text                       the string is in the doc (whitespace-normalised:
                                            runs of spaces / newlines compare equal, so a
                                            sentence re-wrapped by an editor still matches
                                            and a sentence re-worded does not)
  set-equal     left right [waive]         two sets of names agree in BOTH directions; a side
                                            is {glob, name} (group 1 of each matching path) or
                                            {file, pattern [, after, before]} (group 1 of each
                                            match in the doc, optionally between two markers).
                                            An EMPTY side fails. `waive` is printed every run.
  count-equals  number set                 a number stated in prose == the size of a set on disk

Claim shape:
  - id: README-TRUSTED-BASE
    doc: README.md
    text: "…"              # optional; must appear in `doc` (normalised)
    epoch: "…"             # optional; what expires this claim even while its evidence
                           #   still passes (printed, so the reader sees the bound)
    evidence: [ {kind: …}, … ]
"""

import glob
import pathlib
import re
import sys

try:
    import yaml
except ImportError:  # pragma: no cover
    sys.exit("claim_check: needs PyYAML (python3 -m pip install pyyaml)")

_WS = re.compile(r"\s+")


def _norm(s):
    """Collapse every run of whitespace to one space (prose re-wraps freely)."""
    return _WS.sub(" ", s).strip()


def _globs(globs):
    return [globs] if isinstance(globs, str) else list(globs)


def _count(pattern, globs, root):
    rx = re.compile(pattern, re.M)
    total = 0
    matched_any = False
    for g in _globs(globs):
        for f in sorted(glob.glob(str(root / g), recursive=True)):
            p = pathlib.Path(f)
            if p.is_file():
                matched_any = True
                total += len(rx.findall(p.read_text(errors="ignore")))
    return total, matched_any


def _side(spec, root):
    """A set of names, from paths on disk or from a doc. Returns (names, error)."""
    if "glob" in spec:
        rx = re.compile(spec.get("name", r"([^/]+?)(?:\.[^/.]+)?$"))
        names = set()
        for f in glob.glob(str(root / spec["glob"]), recursive=True):
            rel = pathlib.Path(f).relative_to(root).as_posix()
            m = rx.search(rel)
            if m:
                names.add(m.group(1))
        return names, None if names else f"side matched NO paths: glob {spec['glob']!r}"
    if "file" in spec:
        p = root / spec["file"]
        if not p.exists():
            return set(), f"side file not found: {spec['file']}"
        text = p.read_text(errors="ignore")
        if spec.get("after"):
            i = text.find(spec["after"])
            if i < 0:
                return set(), f"section start {spec['after']!r} not found in {spec['file']}"
            text = text[i + len(spec["after"]):]
        if spec.get("before"):
            j = text.find(spec["before"])
            if j >= 0:
                text = text[:j]
        names = set(re.findall(spec["pattern"], text, re.M))
        return names, None if names else f"side pattern matched NOTHING in {spec['file']}"
    return set(), "side needs either glob or file"


def check_claim(c, root):
    fails = []
    doc_path = root / c["doc"]
    if not doc_path.exists():
        return [f"doc not found: {c['doc']}"]
    doc = doc_path.read_text(errors="ignore")
    doc_n = _norm(doc)

    text = c.get("text")
    if text and _norm(text) not in doc_n:
        fails.append(f'claim text not found in {c["doc"]}: "{_norm(text)}"')

    for ev in c.get("evidence", []):
        kind = ev.get("kind")
        if kind == "verbatim":
            s = ev.get("text", text)
            if not s:
                fails.append("verbatim predicate with no text")
            elif _norm(s) not in doc_n:
                fails.append(f'verbatim string absent from {c["doc"]}: "{_norm(s)}"')
        elif kind == "file-exists":
            if not (root / ev["path"]).exists():
                fails.append(f"evidence file missing: {ev['path']}")
        elif kind in ("count-max", "no-new"):
            limit = ev["max"] if kind == "count-max" else ev.get("recorded", 0)
            n, matched = _count(ev["pattern"], ev["glob"], root)
            if not matched:
                fails.append(f"predicate matched NO files (measures nothing): glob {ev['glob']}")
            elif n > limit:
                fails.append(
                    f"count grew: {n} > recorded max {limit}  [/{ev['pattern']}/ in {ev['glob']}]"
                    "  — change the claim, not the number"
                )
        elif kind == "count-min":
            n, matched = _count(ev["pattern"], ev["glob"], root)
            if not matched:
                fails.append(f"predicate matched NO files (measures nothing): glob {ev['glob']}")
            elif n < ev["min"]:
                fails.append(
                    f"claim evidence absent: {n} < required min {ev['min']}  "
                    f"[/{ev['pattern']}/ in {ev['glob']}]  — the doc asserts it; the source no longer carries it"
                )
        elif kind == "set-equal":
            left, el = _side(ev["left"], root)
            right, er = _side(ev["right"], root)
            for e in (el, er):
                if e:
                    fails.append(f"{e}  — an empty side compares nothing")
            if not (el or er):
                waived = set(ev.get("waive", []))
                for w in sorted(waived):
                    print(f"    waived (debt, printed every run): {w}")
                only_l = sorted(left - right - waived)
                only_r = sorted(right - left - waived)
                if only_l:
                    fails.append(f"in left but not right: {', '.join(only_l)}")
                if only_r:
                    fails.append(f"in right but not left: {', '.join(only_r)}")
        elif kind == "count-equals":
            names, es = _side(ev["set"], root)
            p = root / ev["number"]["file"]
            m = re.search(ev["number"]["pattern"], p.read_text(errors="ignore")) if p.exists() else None
            if es:
                fails.append(f"{es}  — an empty side compares nothing")
            elif not m:
                fails.append(
                    f"stated number not found: /{ev['number']['pattern']}/ in {ev['number']['file']}"
                )
            elif int(m.group(1)) != len(names):
                fails.append(
                    f"{ev['number']['file']} states {m.group(1)}, the source holds {len(names)}"
                )
        else:
            fails.append(f"unknown evidence kind: {kind!r}")
    return fails


def self_test():
    """Each predicate in BOTH directions over throwaway fixtures. A rule seen only
    to pass is indistinguishable from one that cannot fail."""
    import tempfile

    def run(files, ev, text=None):
        with tempfile.TemporaryDirectory() as d:
            root = pathlib.Path(d)
            for rel, body in files.items():
                (root / rel).parent.mkdir(parents=True, exist_ok=True)
                (root / rel).write_text(body)
            if not (root / "doc.md").exists():
                (root / "doc.md").write_text("x")
            claim = {"id": "T", "doc": "doc.md", "evidence": [ev]}
            if text is not None:
                claim["text"] = text
            return check_claim(claim, root)

    two = {"s/a/SKILL.md": "", "s/b/SKILL.md": ""}
    disk = {"glob": "s/*/SKILL.md", "name": r"s/([^/]+)/"}
    doc = lambda body: {**two, "doc.md": body}
    table = {"file": "doc.md", "pattern": r"^- `([a-z]+)`", "after": "## S", "before": "## E"}
    src = {"p/A.lean": "theorem a : True := trivial\n", "p/B.lean": "theorem b : True := by sorry\n"}
    cases = [
        # verbatim (whitespace-normalised)
        ("verbatim: present -> holds", {"doc.md": "the trusted base is X\n"},
         {"kind": "verbatim", "text": "the trusted base is X"}, False),
        ("verbatim: re-wrapped -> still holds", {"doc.md": "the trusted\n  base is X\n"},
         {"kind": "verbatim", "text": "the trusted base is X"}, False),
        ("verbatim: re-worded -> fails", {"doc.md": "the trusted base is Y\n"},
         {"kind": "verbatim", "text": "the trusted base is X"}, True),
        ("verbatim: empty text -> fails", {"doc.md": "anything"},
         {"kind": "verbatim", "text": ""}, True),
        ("claim text: absent -> fails", {"doc.md": "nothing"}, {"kind": "file-exists", "path": "doc.md"}, True),
        # file-exists
        ("file-exists: present -> holds", {"p/A.lean": ""}, {"kind": "file-exists", "path": "p/A.lean"}, False),
        ("file-exists: missing -> fails", {}, {"kind": "file-exists", "path": "p/A.lean"}, True),
        # count-min (presence)
        ("count-min: present -> holds", src,
         {"kind": "count-min", "pattern": r"^theorem a\b", "glob": "p/*.lean", "min": 1}, False),
        ("count-min: pattern vanished -> fails", src,
         {"kind": "count-min", "pattern": r"^theorem zzz\b", "glob": "p/*.lean", "min": 1}, True),
        ("count-min: glob matches no file -> fails", src,
         {"kind": "count-min", "pattern": r"^theorem a\b", "glob": "q/*.lean", "min": 1}, True),
        # count-max (growth)
        ("count-max: under -> holds", src,
         {"kind": "count-max", "pattern": r":= by sorry\b", "glob": "p/A.lean", "max": 0}, False),
        ("count-max: over -> fails", src,
         {"kind": "count-max", "pattern": r":= by sorry\b", "glob": "p/*.lean", "max": 0}, True),
        ("count-max: glob matches no file -> fails", src,
         {"kind": "count-max", "pattern": r"sorry", "glob": "q/*.lean", "max": 0}, True),
        ("no-new: over recorded -> fails", src,
         {"kind": "no-new", "pattern": r"sorry", "glob": "p/*.lean", "recorded": 0}, True),
        # set-equal
        ("set-equal: sets match -> holds", doc("## S\n- `a`\n- `b`\n## E\n"),
         {"kind": "set-equal", "left": disk, "right": table}, False),
        ("set-equal: doc lacks one -> fails", doc("## S\n- `a`\n## E\n"),
         {"kind": "set-equal", "left": disk, "right": table}, True),
        ("set-equal: doc lists a phantom -> fails", doc("## S\n- `a`\n- `b`\n- `c`\n## E\n"),
         {"kind": "set-equal", "left": disk, "right": table}, True),
        ("set-equal: empty doc side -> FAILS, not 0 mismatches", doc("## S\n## E\n"),
         {"kind": "set-equal", "left": disk, "right": table}, True),
        ("set-equal: empty disk side -> FAILS", {"doc.md": "## S\n- `a`\n## E\n"},
         {"kind": "set-equal", "left": disk, "right": table}, True),
        ("set-equal: empty doc side, differences waived -> still FAILS", doc("## S\n## E\n"),
         {"kind": "set-equal", "left": disk, "right": table, "waive": ["a", "b"]}, True),
        ("set-equal: empty disk side, differences waived -> still FAILS", {"doc.md": "## S\n- `a`\n## E\n"},
         {"kind": "set-equal", "left": disk, "right": table, "waive": ["a"]}, True),
        ("set-equal: waived name excluded", doc("## S\n- `a`\n## E\n"),
         {"kind": "set-equal", "left": disk, "right": table, "waive": ["b"]}, False),
        ("set-equal: section bounds respected", doc("- `z`\n## S\n- `a`\n- `b`\n## E\n- `y`\n"),
         {"kind": "set-equal", "left": disk, "right": table}, False),
        # count-equals
        ("count-equals: stated == actual -> holds", doc("# 2 custom skills"),
         {"kind": "count-equals", "number": {"file": "doc.md", "pattern": r"# (\d+) custom"}, "set": disk}, False),
        ("count-equals: stated != actual -> fails", doc("# 18 custom skills"),
         {"kind": "count-equals", "number": {"file": "doc.md", "pattern": r"# (\d+) custom"}, "set": disk}, True),
        ("count-equals: number missing -> fails", doc("no number here"),
         {"kind": "count-equals", "number": {"file": "doc.md", "pattern": r"# (\d+) custom"}, "set": disk}, True),
        ("count-equals: empty set -> fails", {"doc.md": "# 0 custom skills"},
         {"kind": "count-equals", "number": {"file": "doc.md", "pattern": r"# (\d+) custom"}, "set": disk}, True),
        ("unknown kind -> fails", {}, {"kind": "guess"}, True),
    ]
    bad = 0
    print("claim_check self-test")
    for name, files, ev, expect_fail in cases:
        text = "nothing-here" if name.startswith("claim text") else None
        got = bool(run(files, ev, text))
        ok = got == expect_fail
        bad += not ok
        print(f"  [{'ok  ' if ok else 'FAIL'}] {name}")
    print(f"  {len(cases) - bad}/{len(cases)} cases hold")
    return 1 if bad else 0


def main():
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    path = pathlib.Path(args[0] if args else "claims.yaml").resolve()
    if not path.exists():
        sys.exit(f"claim_check: {path} not found")
    root = path.parent
    data = yaml.safe_load(path.read_text()) or {}
    claims = data.get("claims", [])
    if not claims:
        print("claim_check: no claims declared — nothing to gate", file=sys.stderr)
        sys.exit(2)
    ids = [c.get("id") for c in claims]
    dup = sorted({i for i in ids if ids.count(i) > 1})
    if dup or None in ids:
        sys.exit(f"claim_check: duplicate or missing claim ids: {dup}")

    bad = 0
    for c in claims:
        fails = check_claim(c, root)
        if fails:
            bad += 1
            print(f"✗ {c['id']}  ({c['doc']})")
            for f in fails:
                print(f"    {f}")
        else:
            print(f"✓ {c['id']}")
        if c.get("epoch"):
            print(f"    epoch: {_norm(c['epoch'])}")

    print(f"\n{len(claims) - bad}/{len(claims)} claims hold.")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
