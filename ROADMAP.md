# Ordeal Roadmap

**The roadmap lives in the rivet graph, not in this file.** The delivery
phases P0–P5 are modeled as `FEAT-000`…`FEAT-015` in
[`artifacts/features.yaml`](artifacts/features.yaml) — all phases through P5
are **verified**, and every feature carries the release that shipped it
(`release:` field). This file is only a
pointer; a hand-maintained mirror of the phase tables went stale and was
retired (issue #140).

## Querying current status

```bash
# All roadmap features with their status and release:
rivet query '(has-tag "roadmap")'

# Anything not yet verified (empty = the whole graph is closed):
rivet query '(and (has-tag "roadmap") (not (= status "verified")))'

# One phase, e.g. P4:
rivet query '(has-tag "p4")'
```

`rivet release status` shows the release plan; `rivet verify` runs the
V-model gate.

## What's next

Post-P5 work is planned per release in rivet (`release:` field) and mirrored
to GitHub milestones. Current plan and readiness:

```bash
rivet release status v0.22.0      # the release in progress
rivet list --release backlog      # deliberately unscheduled (e.g. TR-032)
```

Open GitHub milestones: <https://github.com/pulseengine/ordeal/milestones>.

## Out of scope (permanent)

Quantifiers, floating-point, `Optimize`, and incremental push/pop solving are
**not** planned. Ordeal is a specialized decision procedure for a closed
fragment (loom #246), not a general SMT solver.
