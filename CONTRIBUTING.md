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

# Run clippy
cargo clippy --all-targets --all-features -- -D warnings
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

## Pull Request Process

1. Fork the repository.
2. Create a feature branch: `git checkout -b feature/your-feature`.
3. Make your changes.
4. Ensure `cargo fmt`, `cargo clippy`, and `cargo test --all` pass.
5. Push to your fork and submit a pull request.
6. Ensure all CI checks pass.

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
