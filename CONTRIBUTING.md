# Contributing to ordeal

Welcome! We're glad you're interested in contributing to ordeal — a pure-Rust,
certificate-checked QF_BV SMT solver for the PulseEngine toolchain.

## Development Setup

### Prerequisites

- Rust (stable toolchain — see `rust-toolchain.toml`)
- Cargo
- Git
- [Nix](https://nixos.org/download/) (optional — provides a ready-made dev
  shell via `flake.nix` / `direnv`)
- Z3 (optional — only needed for the `oracle` differential-checking feature)

### Getting Started

```bash
# Clone the repository
git clone https://github.com/pulseengine/ordeal.git
cd ordeal

# Build
cargo build --release

# Run all tests
cargo test --all
```

If you use Nix + direnv, `direnv allow` drops you into a shell with the pinned
Rust toolchain and Z3 already on `PATH`.

## Code Quality

### Formatting and Linting

```bash
# Format all code
cargo fmt

# Check formatting
cargo fmt --all -- --check

# Run clippy as CI does (default features, then the Z3-free optional ones)
cargo clippy --all-targets -- -D warnings
cargo clippy --all-targets --features ordeal/cert-bundle,ordeal/cadical -- -D warnings
# `--all-features` additionally lints the `oracle` feature and needs libz3

# The documentation claim gate (claims.yaml): every load-bearing doc claim
# bound to evidence re-derived from the tree
python3 scripts/claim_check.py
```

### Testing

```bash
# Run all tests (default build — no Z3 required)
cargo test --all

# Run the Z3 differential oracle (requires system Z3 / libz3-dev)
cargo test --all --features oracle
```

The default build is intentionally Z3-free: ordeal is a self-contained solver.
The optional `oracle` feature cross-checks ordeal's answers against Z3 and is
run as a non-blocking CI job.

The SMT-LIB parser differential (`oracle::front`, TR-087) hands every
repository `.smt2` file and 10^4 generated scripts to Z3's parser and to
ordeal's reader. Its echo leg (`oracle::echo`, #281 E1) prints the certified
echo of the same scripts and hands it to Z3's parser. Both run in one job,
`SMT-LIB parser differential (Z3)`, which is not `continue-on-error` and is
one of the required checks below, so a disagreement blocks the merge. Run
them locally with:

```bash
cargo test -p ordeal --features oracle --release --lib -- oracle::front::tests oracle::echo::tests --nocapture
```

## Pull Request Process

1. Fork the repository.
2. Create a feature branch: `git checkout -b feature/your-feature`.
3. Make your changes.
4. Ensure `cargo fmt`, `cargo clippy`, and `cargo test --all` pass.
5. Push to your fork and submit a pull request.
6. Ensure all CI checks pass. The checks branch protection requires on
   `main` (every other job in `.github/workflows/ci.yml` is advisory):

   - `Format`
   - `Clippy`
   - `Build (release)`
   - `Build (wasm32-wasip2)`
   - `Test`
   - `Reproducible build`
   - `Lean model + soundness proof`
   - `CaDiCaL backend (cadical feature)`
   - `SMT-LIB parser differential (Z3)`

   `claims.yaml` checks this list against the job names in `ci.yml`, so a
   job added to the workflow must be listed here or waived there.

## Commit Message Trailers

This repository uses [rivet](https://github.com/pulseengine/rivet) for artifact
traceability. Commit messages must carry a trailer linking the change to an
artifact:

- `Implements: <id>` — a new feature / requirement is implemented
- `Fixes: <id>` — a defect is fixed
- `Verifies: <id>` — a test or proof verifies a requirement
- `Trace: <id>` — general traceability reference

`rivet commit-msg-check` (wired into the pre-commit hooks) enforces this
locally; install the hooks with `pre-commit install --hook-type commit-msg`.

## Code Style

- Follow the Rust API guidelines.
- Use descriptive variable and function names.
- Add documentation comments for public APIs.
- Keep functions focused and small.
- Write tests for new functionality — a certificate-checked solver lives or
  dies by its test coverage.

## License

By contributing to ordeal, you agree that your contributions will be licensed
under the Apache License 2.0.
