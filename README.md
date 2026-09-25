<div align="center">

# Ordeal

<sup>A certificate-checked QF_BV SMT solver for the PulseEngine toolchain</sup>

&nbsp;

![Rust](https://img.shields.io/badge/Rust-CE422B?style=flat-square&logo=rust&logoColor=white&labelColor=1a1b27)
![License: Apache-2.0](https://img.shields.io/badge/License-Apache--2.0-blue?style=flat-square&labelColor=1a1b27)

&nbsp;

<h6>
  <a href="https://github.com/pulseengine/meld">Meld</a>
  &middot;
  <a href="https://github.com/pulseengine/loom">Loom</a>
  &middot;
  <a href="https://github.com/pulseengine/synth">Synth</a>
  &middot;
  <a href="https://github.com/pulseengine/ordeal">Ordeal</a>
  &middot;
  <a href="https://github.com/pulseengine/kiln">Kiln</a>
  &middot;
  <a href="https://github.com/pulseengine/sigil">Sigil</a>
</h6>

</div>

&nbsp;

Ordeal answers one kind of question: **are these two bit-vector computations
the same for every input?** It is the solver that
[loom](https://github.com/pulseengine/loom) and
[synth](https://github.com/pulseengine/synth) use to check that a WebAssembly
optimisation or an ARM lowering does not change behaviour.

What makes it different from asking Z3: **you don't have to trust ordeal's
answer.**

- **"Equivalent"** (UNSAT) comes with a proof certificate.
- **"Different"** (SAT) comes with a counterexample and a satisfying assignment.

Both are re-checked by a small checker whose soundness is machine-checked in
Lean 4. The solver itself is untrusted.

Pure Rust, no external dependencies, and it runs as a `wasm32-wasip2` component
as well as natively.

## Get ordeal

Pick the path that matches how you work:

| You are… | Use |
|---|---|
| Using the PulseEngine toolchain | the **varve** layer (below) |
| Calling it from Rust | `cargo add ordeal` |
| Wanting the command-line tool | `cargo install ordeal`, or a release binary |
| Building with Bazel | [rules_ordeal](https://github.com/pulseengine/rules_ordeal) |

**varve.** [varve](https://github.com/pulseengine/varve) installs the whole
PulseEngine toolchain as one pinned, signed layer. Ordeal is one of the tools
in it. With a `varve.toml` pinning a layer (see varve's
[Getting started](https://github.com/pulseengine/varve#getting-started)):

```sh
varve install && varve shim install   # then: . "$HOME/.varve/env"
ordeal --version                      # dispatched from the pinned layer
```

**Release binaries.** Each [release](https://github.com/pulseengine/ordeal/releases)
ships archives for Linux (glibc and static musl, x86_64 and aarch64) and macOS.
`SHA256SUMS.txt` is cosign-signed, and a CycloneDX SBOM and VEX are listed in it:

```sh
gh release download --repo pulseengine/ordeal -p 'ordeal-*-x86_64-unknown-linux-musl.tar.gz' -p 'SHA256SUMS.txt*'
cosign verify-blob --bundle SHA256SUMS.txt.cosign.bundle \
  --certificate-identity-regexp '^https://github\.com/pulseengine/ordeal/\.github/workflows/release\.yml@' \
  --certificate-oidc-issuer https://token.actions.githubusercontent.com SHA256SUMS.txt
sha256sum -c --ignore-missing SHA256SUMS.txt   # macOS: shasum -a 256 -c …
```

## Quick start

### Command line

Ordeal reads SMT-LIB2 (the QF_BV subset). Is `x + x` the same as `x << 1`?
Assert that they differ and ask. `unsat` means no difference exists:

```sh
$ printf '(declare-const x (_ BitVec 32))
(assert (distinct (bvadd x x) (bvshl x #x00000001)))
(check-sat)' | ordeal check -
unsat
; unsat certificate: 10 bytes of checker-validated LRAT
```

A satisfiable query prints the model:

```sh
$ echo '(declare-const x (_ BitVec 32))(assert (= x #x0000002a))(check-sat)' | ordeal check -
sat
((x #x0000002a))
```

`--format json` prints one JSON object per query. It carries the full evidence
for either answer:

- the CNF and LRAT proof for `unsat`;
- the satisfying assignment, with its bit map and hashes, for `sat`.

Anyone can re-check that object without trusting the ordeal binary.

### Rust

```rust
use ordeal::{BvTerm, CheckResult, Solver, Sort};

// Is x * 2 the same as x << 1 for every 32-bit x?
let x = || Box::new(BvTerm::Var { name: "x".into(), sort: Sort::new(32) });
let c = |v| Box::new(BvTerm::Const { value: v, sort: Sort::new(32) });

match Solver::prove_equiv(BvTerm::Mul(x(), c(2)), BvTerm::Shl(x(), c(1))) {
    CheckResult::Unsat(cert) => {
        // Equivalent. recheck() re-validates the proof with the trusted checker.
        cert.recheck().expect("certificate re-checks");
    }
    CheckResult::Sat(model) => println!("differ, e.g. at {:?}", model.assignments),
    CheckResult::Unknown => { /* no claim: never treat as equivalent */ }
}
```

The same program, runnable:
[`examples/quickstart.rs`](crates/ordeal/examples/quickstart.rs)
(`cargo run -p ordeal --example quickstart`). CI runs it on every change. For the SAT witness, resource-bounded checks and more patterns, see
[docs/consuming-ordeal.md](docs/consuming-ordeal.md).

## What it decides

A deliberately closed fragment of QF_BV, bit-widths 1 to 128 (SMT-LIB names):

- arithmetic: `bvadd bvsub bvmul bvudiv bvurem`, plus `bvneg bvsdiv bvsrem`
  (lowered into the core ops)
- bitwise: `bvand bvor bvxor bvnot`
- shifts and rotation: `bvshl bvlshr bvashr rotate_right rotate_left`
- structure: `extract concat zero_extend sign_extend ite`
- comparisons: `= distinct bvult bvule bvugt bvuge bvslt bvsle bvsgt bvsge`
- the Boolean connectives `not and or`

There is also a small preprocessed layer for byte arrays (`select`/`store`)
and uninterpreted pure calls.

Anything else is rejected as `unsupported`; ordeal never guesses. **Not
planned:** quantifiers, floating point, optimisation, incremental push/pop.
`Unknown` is always a possible answer (for example on a resource limit), and
callers must treat it as "no claim".

## Why you can trust an answer

```
formula → bit-blast → AIG → CNF → SAT solver ──unsat──▶ LRAT proof ─┐
                                              └──sat───▶ assignment ─┤
                                                                     ▼
                                                   ordeal-lrat checker (trusted)
```

Only `ordeal-lrat` is trusted. It is a small, dependency-free crate. The Rust
source is translated to Lean 4 with [Aeneas](https://github.com/AeneasVerif/aeneas)
and proven sound: an accepted proof means the formula really is unsatisfiable,
and an accepted assignment really satisfies it. The bit-blasting rules are
proven against Lean's `BitVec` semantics too. CI regenerates the Lean model
from the Rust source before every proof build, so the proof cannot drift from
the code.

A bug anywhere else can make ordeal fail to answer, but cannot make a wrong
answer pass the checker. Details and exact scope:
[docs/formal-verification.md](docs/formal-verification.md).

## Documentation

| | |
|---|---|
| [docs/consuming-ordeal.md](docs/consuming-ordeal.md) | Using ordeal from a tool: API patterns, SAT witness, SBOM/VEX |
| [ARCHITECTURE.md](ARCHITECTURE.md) | The pipeline and the trust boundary |
| [docs/formal-verification.md](docs/formal-verification.md) | What is proven, how, and what is not |
| [CHANGELOG.md](CHANGELOG.md) | What changed in each release |
| [ROADMAP.md](ROADMAP.md) | How the plan is tracked (rivet) |

**Building from source:**

```sh
cargo build && cargo test
cargo build --target wasm32-wasip2 --release   # the WebAssembly component
```

The Z3 cross-check used in development is behind the off-by-default `oracle`
feature.

## Part of PulseEngine

| Project | Role |
|---------|------|
| [**Loom**](https://github.com/pulseengine/loom) | WASM optimizer with SMT verification |
| [**Synth**](https://github.com/pulseengine/synth) | WASM-to-ARM AOT compiler with Rocq proofs |
| [**Ordeal**](https://github.com/pulseengine/ordeal) | Certificate-checked QF_BV SMT solver |
| [**Meld**](https://github.com/pulseengine/meld) | WASM Component Model static fuser |
| [**Kiln**](https://github.com/pulseengine/kiln) | WASM runtime for safety-critical systems |
| [**Sigil**](https://github.com/pulseengine/sigil) | Supply chain attestation and signing |
| [**varve**](https://github.com/pulseengine/varve) | Toolchain layer manager: pinned, signed bundles of the tools above |

## License

Apache-2.0. See [LICENSE](LICENSE).

---

<div align="center">

<sub>Part of <a href="https://github.com/pulseengine">PulseEngine</a> &mdash; WebAssembly toolchain for safety-critical systems</sub>

</div>
