# CLAUDE.md

See [AGENTS.md](AGENTS.md) for project instructions.

Additional Claude Code notes:

- Ordeal is a **certificate-checked** QF_BV SMT solver: the solver is
  **untrusted**, only the formally-verified LRAT checker is trusted. Never
  return an `Unsat` that the checker has not validated.
- The op set in `crates/ordeal/src/term.rs` is a **closed fragment** (loom
  #246). Do not add operations without a proven bit-blasting rule.
- `Solver::check` returning `Unknown` is **sound by construction** — callers
  treat `Unknown` conservatively (never optimize). Keep it that way until the
  real engine lands.
- Keep the default build **dependency-free**. Z3 lives behind the off-by-default
  `oracle` feature as a differential oracle / benchmark rival only.
- Use `rivet validate` after changing artifact YAML files.
- Commit messages require artifact trailers (Implements / Fixes / Verifies /
  Trace); use `Trace: skip` to opt out.
