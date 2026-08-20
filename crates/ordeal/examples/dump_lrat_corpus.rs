// rivet: verifies VER-033
//! TR-035 dual-mechanisation differential — the shared certificate corpus.
//!
//! Dumps a **deterministic** corpus of (DIMACS CNF, textual LRAT) pairs for
//! cross-checking ordeal's own formally-verified checker (`ordeal-lrat`,
//! Aeneas → Lean proven) against Lean core's *independently* verified LRAT
//! checker (`Std.Tactic.BVDecide.LRAT.check`, the absorbed leansat checker;
//! see `lean/DiffCheck.lean` for the consumer side). Any verdict disagreement
//! on this corpus localizes either an Aeneas translation-faithfulness gap or
//! a spec ambiguity between the two mechanisations.
//!
//! Two corpus halves, each recorded in `<outdir>/manifest.txt`:
//!
//! * `pristine/NNN.{cnf,lrat}` — certificates ordeal's checker **accepted**
//!   (they are exactly what `Solver::check` returned as `Unsat`; the dumper
//!   re-runs `ordeal_lrat::check` before writing). Expectation: `accept`.
//! * `mutated/NNN.{cnf,lrat}` — structural corruptions of pristine proofs
//!   (dropped hint, renumbered step id, negated clause literal, truncated
//!   final empty-clause step) that ordeal's checker **rejected** — asserted
//!   here before writing, so every manifest expectation is ground truth, not
//!   hope. Expectation: `reject`.
//!
//! Determinism: fixed seeds through the same xorshift64 generator pattern as
//! `oracle::gen_corpus` (ported here because the oracle module lives behind
//! the off-by-default `oracle` feature), no timestamps, no ambient
//! randomness. The same binary always writes byte-identical corpora.
//!
//! Run with: `cargo run -p ordeal --example dump_lrat_corpus -- <outdir>`

use ordeal::bmc_corpus;
use ordeal::{BoolTerm, BvTerm, CheckResult, Solver, Sort};
use std::fmt::Write as _;
use std::fs;
use std::path::Path;
use std::process::ExitCode;

// ─── Seeded query generation (the oracle::gen_corpus pattern) ───────────────

/// The variable widths the loom/synth fragment declares.
const WIDTHS: [u32; 3] = [8, 32, 64];

/// Maximum term depth for generated queries.
const MAX_DEPTH: u32 = 4;

/// Deterministic conflict budget per solve — bounds runtime without
/// introducing wall-clock nondeterminism (a deadline would).
const MAX_CONFLICTS: u64 = 30_000;

/// Size guards: keep the corpus CI-friendly for the Lean-side re-check.
const MAX_LRAT_BYTES: usize = 2_000_000;
const MAX_CNF_CLAUSES: usize = 60_000;

/// Corpus sizing.
const PRISTINE_TARGET: usize = 48;
const MUTATED_TARGET: usize = 16;

/// A tiny xorshift64 PRNG — local so the corpus needs no `rand` dependency
/// and stays byte-for-byte reproducible from the seed.
struct XorShift64 {
    state: u64,
}

impl XorShift64 {
    fn new(seed: u64) -> Self {
        Self {
            // xorshift has an all-zero fixed point; displace it.
            state: if seed == 0 {
                0x2545_F491_4F6C_DD1D
            } else {
                seed
            },
        }
    }

    fn next(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn width(&mut self) -> u32 {
        WIDTHS[self.below(WIDTHS.len() as u64) as usize]
    }
}

/// Generate a leaf of the requested width: a free variable from the pool
/// (when one of that width exists) or a constant.
fn gen_leaf(rng: &mut XorShift64, width: u32, vars: &[(String, u32)]) -> BvTerm {
    let candidates: Vec<&(String, u32)> = vars.iter().filter(|(_, w)| *w == width).collect();
    if !candidates.is_empty() && rng.below(2) == 0 {
        let (name, w) = candidates[rng.below(candidates.len() as u64) as usize];
        BvTerm::Var {
            name: name.clone(),
            sort: Sort::new(*w),
        }
    } else {
        BvTerm::Const {
            value: rng.next() as u128,
            sort: Sort::new(width),
        }
    }
}

/// Generate a well-sorted [`BvTerm`] of exactly `width` bits.
fn gen_bv(rng: &mut XorShift64, width: u32, depth: u32, vars: &[(String, u32)]) -> BvTerm {
    if depth == 0 {
        return gen_leaf(rng, width, vars);
    }
    let bin = |rng: &mut XorShift64| {
        let a = Box::new(gen_bv(rng, width, depth - 1, vars));
        let b = Box::new(gen_bv(rng, width, depth - 1, vars));
        (a, b)
    };
    match rng.below(17) {
        0 => {
            let (a, b) = bin(rng);
            BvTerm::Add(a, b)
        }
        1 => {
            let (a, b) = bin(rng);
            BvTerm::Sub(a, b)
        }
        2 => {
            let (a, b) = bin(rng);
            BvTerm::Mul(a, b)
        }
        3 => {
            let (a, b) = bin(rng);
            BvTerm::Udiv(a, b)
        }
        4 => {
            let (a, b) = bin(rng);
            BvTerm::And(a, b)
        }
        5 => {
            let (a, b) = bin(rng);
            BvTerm::Or(a, b)
        }
        6 => {
            let (a, b) = bin(rng);
            BvTerm::Xor(a, b)
        }
        7 => {
            let (a, b) = bin(rng);
            BvTerm::Shl(a, b)
        }
        8 => {
            let (a, b) = bin(rng);
            BvTerm::Lshr(a, b)
        }
        9 => {
            let (a, b) = bin(rng);
            BvTerm::Ashr(a, b)
        }
        10 => {
            let (a, b) = bin(rng);
            BvTerm::Rotr(a, b)
        }
        11 => {
            // Extract `width` bits out of a fragment width >= `width`.
            let sources: Vec<u32> = WIDTHS.iter().copied().filter(|w| *w >= width).collect();
            let src = sources[rng.below(sources.len() as u64) as usize];
            let lo = rng.below((src - width + 1) as u64) as u32;
            BvTerm::Extract {
                hi: lo + width - 1,
                lo,
                arg: Box::new(gen_bv(rng, src, depth - 1, vars)),
            }
        }
        12 if width == 64 => {
            // Concat splits 64 into two fragment-width halves.
            BvTerm::Concat(
                Box::new(gen_bv(rng, 32, depth - 1, vars)),
                Box::new(gen_bv(rng, 32, depth - 1, vars)),
            )
        }
        13 | 14 if width > 8 => {
            let sources: Vec<u32> = WIDTHS.iter().copied().filter(|w| *w < width).collect();
            let src = sources[rng.below(sources.len() as u64) as usize];
            let arg = Box::new(gen_bv(rng, src, depth - 1, vars));
            if rng.below(2) == 0 {
                BvTerm::ZeroExt {
                    by: width - src,
                    arg,
                }
            } else {
                BvTerm::SignExt {
                    by: width - src,
                    arg,
                }
            }
        }
        // bool→BV bridge: ite with a random condition and same-width branches.
        15 => BvTerm::Ite {
            cond: Box::new(gen_bool(rng, depth - 1, vars)),
            then_: Box::new(gen_bv(rng, width, depth - 1, vars)),
            else_: Box::new(gen_bv(rng, width, depth - 1, vars)),
        },
        16 => {
            let (a, b) = bin(rng);
            BvTerm::Urem(a, b)
        }
        // Structural op not expressible at this width — fall back to a leaf.
        _ => gen_leaf(rng, width, vars),
    }
}

/// Generate a well-sorted [`BoolTerm`] with terms of bounded depth.
fn gen_bool(rng: &mut XorShift64, depth: u32, vars: &[(String, u32)]) -> BoolTerm {
    let cmp = |rng: &mut XorShift64| {
        let w = rng.width();
        let a = Box::new(gen_bv(rng, w, depth.saturating_sub(1), vars));
        let b = Box::new(gen_bv(rng, w, depth.saturating_sub(1), vars));
        (a, b)
    };
    // At depth 0 only comparisons (the boolean "leaves") remain.
    let choices = if depth == 0 { 10 } else { 13 };
    match rng.below(choices) {
        0 => {
            let (a, b) = cmp(rng);
            BoolTerm::Eq(a, b)
        }
        1 => {
            let (a, b) = cmp(rng);
            BoolTerm::Ne(a, b)
        }
        2 => {
            let (a, b) = cmp(rng);
            BoolTerm::Ult(a, b)
        }
        3 => {
            let (a, b) = cmp(rng);
            BoolTerm::Ule(a, b)
        }
        4 => {
            let (a, b) = cmp(rng);
            BoolTerm::Ugt(a, b)
        }
        5 => {
            let (a, b) = cmp(rng);
            BoolTerm::Uge(a, b)
        }
        6 => {
            let (a, b) = cmp(rng);
            BoolTerm::Slt(a, b)
        }
        7 => {
            let (a, b) = cmp(rng);
            BoolTerm::Sle(a, b)
        }
        8 => {
            let (a, b) = cmp(rng);
            BoolTerm::Sgt(a, b)
        }
        9 => {
            let (a, b) = cmp(rng);
            BoolTerm::Sge(a, b)
        }
        10 => BoolTerm::Not(Box::new(gen_bool(rng, depth - 1, vars))),
        11 => BoolTerm::And(
            Box::new(gen_bool(rng, depth - 1, vars)),
            Box::new(gen_bool(rng, depth - 1, vars)),
        ),
        _ => BoolTerm::Or(
            Box::new(gen_bool(rng, depth - 1, vars)),
            Box::new(gen_bool(rng, depth - 1, vars)),
        ),
    }
}

/// One random query: a conjunction of 1–3 assertions over a few free
/// variables (widths 8/32/64 only), term depth bounded by [`MAX_DEPTH`].
fn gen_query(rng: &mut XorShift64) -> Vec<BoolTerm> {
    let n_vars = 2 + rng.below(2) as usize;
    let vars: Vec<(String, u32)> = (0..n_vars)
        .map(|i| (format!("v{i}"), rng.width()))
        .collect();
    let n_assertions = 1 + rng.below(3);
    (0..n_assertions)
        .map(|_| gen_bool(rng, MAX_DEPTH, &vars))
        .collect()
}

// ─── Crafted UNSAT families (negated identities of the closed fragment) ─────

fn var(name: &str, w: u32) -> BvTerm {
    BvTerm::Var {
        name: name.into(),
        sort: Sort::new(w),
    }
}

fn c(value: u128, w: u32) -> BvTerm {
    BvTerm::Const {
        value,
        sort: Sort::new(w),
    }
}

fn b(t: BvTerm) -> Box<BvTerm> {
    Box::new(t)
}

/// Negated bit-level identities: each is UNSAT for every width, so the
/// refutation exercises a whole op family end to end (blast → CNF → CDCL →
/// LRAT). Mul/Udiv families stay at the narrower widths to keep the
/// certificates CI-sized.
fn identity_queries() -> Vec<(String, Vec<BoolTerm>)> {
    let mut queries = Vec::new();
    for w in WIDTHS {
        let x = || var("x", w);
        let y = || var("y", w);
        // add commutes: x + y != y + x is UNSAT.
        queries.push((
            format!("add-comm-w{w}"),
            vec![BoolTerm::Ne(
                b(BvTerm::Add(b(x()), b(y()))),
                b(BvTerm::Add(b(y()), b(x()))),
            )],
        ));
        // xor cancels: (x ^ y) ^ y != x is UNSAT.
        queries.push((
            format!("xor-cancel-w{w}"),
            vec![BoolTerm::Ne(
                b(BvTerm::Xor(b(BvTerm::Xor(b(x()), b(y()))), b(y()))),
                b(x()),
            )],
        ));
        // absorption: (x & y) | x != x is UNSAT.
        queries.push((
            format!("absorb-w{w}"),
            vec![BoolTerm::Ne(
                b(BvTerm::Or(b(BvTerm::And(b(x()), b(y()))), b(x()))),
                b(x()),
            )],
        ));
        // x - x != 0 is UNSAT.
        queries.push((
            format!("sub-self-w{w}"),
            vec![BoolTerm::Ne(b(BvTerm::Sub(b(x()), b(x()))), b(c(0, w)))],
        ));
        // ult is irreflexive: x < x is UNSAT.
        queries.push((
            format!("ult-irrefl-w{w}"),
            vec![BoolTerm::Ult(b(x()), b(x()))],
        ));
        // ult is asymmetric: x < y ∧ y < x is UNSAT.
        queries.push((
            format!("ult-asym-w{w}"),
            vec![BoolTerm::Ult(b(x()), b(y())), BoolTerm::Ult(b(y()), b(x()))],
        ));
    }
    for w in [8u32, 32] {
        let x = || var("x", w);
        // mul by 2 is doubling: x * 2 != x + x is UNSAT.
        queries.push((
            format!("mul2-add-w{w}"),
            vec![BoolTerm::Ne(
                b(BvTerm::Mul(b(x()), b(c(2, w)))),
                b(BvTerm::Add(b(x()), b(x()))),
            )],
        ));
        // x / 1 != x is UNSAT.
        queries.push((
            format!("udiv-one-w{w}"),
            vec![BoolTerm::Ne(b(BvTerm::Udiv(b(x()), b(c(1, w)))), b(x()))],
        ));
    }
    // 64-bit split/reassemble: concat(x[63:32], x[31:0]) != x is UNSAT.
    let x64 = || var("x", 64);
    queries.push((
        "concat-extract-w64".to_string(),
        vec![BoolTerm::Ne(
            b(BvTerm::Concat(
                b(BvTerm::Extract {
                    hi: 63,
                    lo: 32,
                    arg: b(x64()),
                }),
                b(BvTerm::Extract {
                    hi: 31,
                    lo: 0,
                    arg: b(x64()),
                }),
            )),
            b(x64()),
        )],
    ));
    // zext roundtrip: (zext32(x8))[7:0] != x8 is UNSAT.
    let x8 = || var("x", 8);
    queries.push((
        "zext-extract-w8".to_string(),
        vec![BoolTerm::Ne(
            b(BvTerm::Extract {
                hi: 7,
                lo: 0,
                arg: b(BvTerm::ZeroExt {
                    by: 24,
                    arg: b(x8()),
                }),
            }),
            b(x8()),
        )],
    ));
    queries
}

/// 2–4 small BMC-shaped instances (TR-031 shapes, spar#350): correctly-sized
/// queue and correctly-ordered locks are UNSAT within the unrolled depth.
fn bmc_queries() -> Vec<(String, Vec<BoolTerm>)> {
    vec![
        ("bmc-queue-k6".to_string(), bmc_corpus::queue_overflow(6, 6)),
        ("bmc-queue-k9".to_string(), bmc_corpus::queue_overflow(9, 9)),
        (
            "bmc-deadlock-k4".to_string(),
            bmc_corpus::deadlock(4, false),
        ),
        (
            "bmc-deadlock-k5".to_string(),
            bmc_corpus::deadlock(5, false),
        ),
    ]
}

// ─── DIMACS / corpus writing ─────────────────────────────────────────────────

/// Render a clause list in DIMACS with the standard `p cnf` header.
fn to_dimacs(cnf: &[Vec<i32>]) -> String {
    let n_vars = cnf
        .iter()
        .flat_map(|cl| cl.iter())
        .map(|l| l.unsigned_abs())
        .max()
        .unwrap_or(0);
    let mut out = String::new();
    let _ = writeln!(out, "p cnf {n_vars} {}", cnf.len());
    for clause in cnf {
        for lit in clause {
            let _ = write!(out, "{lit} ");
        }
        out.push_str("0\n");
    }
    out
}

/// Guard the Lean-side faithfulness precondition: Lean core's
/// `CNF.convertLRAT` silently DROPS tautological clauses (its `filterMap`
/// returns `none` for them), which would shift every later clause id and
/// desynchronize the two checkers' id spaces. Ordeal's Tseitin encoding never
/// emits tautologies; a corpus entry violating that must fail loudly here
/// rather than manufacture a phantom disagreement downstream.
fn assert_no_tautology(label: &str, cnf: &[Vec<i32>]) {
    for (i, clause) in cnf.iter().enumerate() {
        for lit in clause {
            assert!(
                !clause.contains(&-lit),
                "{label}: CNF clause {i} is a tautology (contains {lit} and {})",
                -lit
            );
        }
    }
}

// ─── LRAT text mutation ──────────────────────────────────────────────────────

/// A parsed ordeal-emitted LRAT addition line: `<id> <lits>* 0 <hints>* 0`.
/// (Ordeal emits addition steps only — no deletion lines.)
struct AddLine {
    id: i64,
    lits: Vec<i64>,
    hints: Vec<i64>,
}

impl AddLine {
    fn parse(line: &str) -> Option<AddLine> {
        let tokens: Vec<i64> = line
            .split_whitespace()
            .map(|t| t.parse::<i64>().ok())
            .collect::<Option<Vec<i64>>>()?;
        let (&id, rest) = tokens.split_first()?;
        let z0 = rest.iter().position(|&t| t == 0)?;
        let (lits, tail) = rest.split_at(z0);
        let (&last, hints) = tail[1..].split_last()?;
        if last != 0 {
            return None;
        }
        Some(AddLine {
            id,
            lits: lits.to_vec(),
            hints: hints.to_vec(),
        })
    }

    fn render(&self) -> String {
        let mut out = String::new();
        let _ = write!(out, "{}", self.id);
        for lit in &self.lits {
            let _ = write!(out, " {lit}");
        }
        out.push_str(" 0");
        for hint in &self.hints {
            let _ = write!(out, " {hint}");
        }
        out.push_str(" 0");
        out
    }
}

/// Does the CNF contain a contradictory unit-clause pair `[l]` / `[-l]`?
///
/// TR-035 FINDING (kept out of the corpus by construction): the two verified
/// checkers disagree on hint-weakened certificates over such CNFs. Lean
/// core's `DefaultFormula.ofArray` PRELOADS every original unit clause into
/// its assignment vector, so with both `l` and `-l` preloaded, the first RUP
/// hint that touches that variable reduces to `encounteredBoth` →
/// `derivedEmpty` → the step is verified even though its own hint chain
/// never reaches a conflict. Ordeal's checker propagates ONLY through the
/// step's hints (units are not pre-propagated), so the same certificate is
/// rejected with `HintsExhausted`. Both verdicts are sound — the CNF really
/// is unsatisfiable, and rejection never claims otherwise — but "is this
/// hint chain a valid RUP justification" genuinely differs between the two
/// mechanisations. Hint-dropping mutations on such CNFs would therefore
/// manufacture a permanent, already-understood DISAGREE; the differential
/// documents the divergence (see lean/DiffCheck.lean, convention 5) and
/// excludes these sources from hint-weakening mutations instead.
fn has_contradictory_units(cnf: &[Vec<i32>]) -> bool {
    let units: Vec<i32> = cnf
        .iter()
        .filter(|cl| cl.len() == 1)
        .map(|cl| cl[0])
        .collect();
    units.iter().any(|&l| units.contains(&-l))
}

/// The structural corruptions of TR-035. Returns `None` when the kind
/// does not apply to this certificate (e.g. no line has enough hints).
fn mutate(lrat: &str, kind: usize) -> Option<(String, &'static str)> {
    let mut lines: Vec<AddLine> = lrat
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(AddLine::parse)
        .collect::<Option<Vec<AddLine>>>()?;
    if lines.is_empty() {
        return None;
    }
    let kind_name = match kind {
        // Drop the final hint of the final (empty-clause) step: unit
        // propagation runs out before the conflict.
        0 => {
            let last = lines.last_mut()?;
            if last.hints.is_empty() {
                return None;
            }
            last.hints.pop();
            "drop-final-hint"
        }
        // Renumber a step id: the first addition step claims an id 7 ahead
        // of the sequential one it must use.
        1 => {
            lines.first_mut()?.id += 7;
            "renumber-step-id"
        }
        // Negate a literal in an added clause: the first step whose clause
        // is nonempty asserts a different clause than the RUP hints justify.
        2 => {
            let line = lines.iter_mut().find(|l| !l.lits.is_empty())?;
            line.lits[0] = -line.lits[0];
            "negate-clause-literal"
        }
        // Truncate the final empty-clause step: the proof never derives ⊥.
        3 => {
            lines.pop();
            if lines.is_empty() {
                return None;
            }
            "truncate-empty-clause"
        }
        // Drop a middle hint of the longest hint chain: propagation misses
        // an assignment a later hint needs.
        4 => {
            let line = lines.iter_mut().max_by_key(|l| l.hints.len())?;
            if line.hints.len() < 3 {
                return None;
            }
            let mid = line.hints.len() / 2;
            line.hints.remove(mid);
            "drop-middle-hint"
        }
        _ => return None,
    };
    let mut out = String::new();
    for line in &lines {
        out.push_str(&line.render());
        out.push('\n');
    }
    if out == lrat {
        return None;
    }
    Some((out, kind_name))
}

// ─── Driver ──────────────────────────────────────────────────────────────────

struct PristineEntry {
    label: String,
    cnf: Vec<Vec<i32>>,
    lrat: String,
}

fn solve(label: &str, assertions: &[BoolTerm]) -> Option<PristineEntry> {
    let mut solver = Solver::new();
    for a in assertions {
        solver.assert(a.clone());
    }
    match solver.check_with_limit(MAX_CONFLICTS) {
        CheckResult::Unsat(cert) => {
            let lrat = cert
                .lrat_text()
                .expect("ordeal-emitted LRAT is always text")
                .to_string();
            if cert.lrat.len() > MAX_LRAT_BYTES || cert.cnf.len() > MAX_CNF_CLAUSES {
                eprintln!(
                    "  skip {label}: certificate too large for the CI corpus \
                     ({} LRAT bytes, {} clauses)",
                    cert.lrat.len(),
                    cert.cnf.len()
                );
                return None;
            }
            // Ground truth: the checker (not solver faith) accepts this pair.
            ordeal_lrat::check(&cert.cnf, &lrat)
                .expect("pristine certificate must pass ordeal-lrat");
            assert_no_tautology(label, &cert.cnf);
            Some(PristineEntry {
                label: label.to_string(),
                cnf: cert.cnf,
                lrat,
            })
        }
        _ => None,
    }
}

fn main() -> ExitCode {
    let Some(outdir) = std::env::args().nth(1) else {
        eprintln!("usage: dump_lrat_corpus <outdir>");
        return ExitCode::from(2);
    };
    let outdir = Path::new(&outdir);
    if outdir.exists() {
        fs::remove_dir_all(outdir).expect("clear stale corpus dir");
    }
    let pristine_dir = outdir.join("pristine");
    let mutated_dir = outdir.join("mutated");
    fs::create_dir_all(&pristine_dir).expect("create pristine dir");
    fs::create_dir_all(&mutated_dir).expect("create mutated dir");

    // 1. Solve: crafted identities, BMC shapes, then seeded random queries
    //    until the pristine target is met.
    let mut pristine: Vec<PristineEntry> = Vec::new();
    for (label, query) in identity_queries().into_iter().chain(bmc_queries()) {
        if let Some(entry) = solve(&label, &query) {
            pristine.push(entry);
        }
    }
    let crafted = pristine.len();

    let mut rng = XorShift64::new(0x7355_0035_C0DE_D1FF);
    let mut random_tried = 0usize;
    while pristine.len() < PRISTINE_TARGET && random_tried < 400 {
        random_tried += 1;
        let query = gen_query(&mut rng);
        let label = format!("rand-{random_tried:03}");
        if let Some(entry) = solve(&label, &query) {
            pristine.push(entry);
        }
    }
    assert!(
        pristine.len() >= 40,
        "corpus too small: only {} UNSAT certificates (need >= 40)",
        pristine.len()
    );

    // 2. Write the pristine half.
    let mut manifest = String::new();
    for (i, entry) in pristine.iter().enumerate() {
        let stem = format!("{i:03}");
        fs::write(
            pristine_dir.join(format!("{stem}.cnf")),
            to_dimacs(&entry.cnf),
        )
        .expect("write cnf");
        fs::write(pristine_dir.join(format!("{stem}.lrat")), &entry.lrat).expect("write lrat");
        let _ = writeln!(manifest, "pristine/{stem} accept");
    }

    // 3. Mutate: cycle the corruption kinds across pristine entries; every
    //    written mutant is asserted REJECTED by ordeal-lrat first.
    let mut written = 0usize;
    let mut still_valid = 0usize;
    let mut mutation_log: Vec<String> = Vec::new();
    'outer: for round in 0.. {
        let mut progressed = false;
        for (i, entry) in pristine.iter().enumerate() {
            if written >= MUTATED_TARGET {
                break 'outer;
            }
            let kind = (i + round) % 5;
            // Hint-weakening mutations (kinds 0 and 4) are excluded on CNFs
            // with a contradictory unit pair: Lean core's eager unit
            // preloading verifies such steps without their hints (see
            // `has_contradictory_units` — a documented tolerance divergence,
            // not a fixture).
            if matches!(kind, 0 | 4) && has_contradictory_units(&entry.cnf) {
                continue;
            }
            let Some((mutated, kind_name)) = mutate(&entry.lrat, kind) else {
                continue;
            };
            match ordeal_lrat::check(&entry.cnf, &mutated) {
                Err(err) => {
                    let stem = format!("{written:03}");
                    fs::write(
                        mutated_dir.join(format!("{stem}.cnf")),
                        to_dimacs(&entry.cnf),
                    )
                    .expect("write cnf");
                    fs::write(mutated_dir.join(format!("{stem}.lrat")), &mutated)
                        .expect("write lrat");
                    let _ = writeln!(manifest, "mutated/{stem} reject");
                    mutation_log.push(format!(
                        "  mutated/{stem}: {kind_name} of {} — ordeal rejects with {err:?}",
                        entry.label
                    ));
                    written += 1;
                    progressed = true;
                }
                Ok(()) => {
                    // The corruption accidentally produced another VALID
                    // proof (e.g. the dropped hint was redundant). It is not
                    // a rejection fixture; skip it — expectations stay ground
                    // truth.
                    still_valid += 1;
                }
            }
        }
        if !progressed {
            break;
        }
    }
    assert!(
        written >= 15,
        "only {written} mutated rejection fixtures (need >= 15)"
    );

    fs::write(outdir.join("manifest.txt"), &manifest).expect("write manifest");

    println!("TR-035 corpus written to {}", outdir.display());
    println!(
        "  pristine: {} (crafted {crafted}, bmc included, random {} of {random_tried} tried)",
        pristine.len(),
        pristine.len() - crafted
    );
    println!("  mutated:  {written} (mutations that stayed valid and were skipped: {still_valid})");
    for line in &mutation_log {
        println!("{line}");
    }
    ExitCode::SUCCESS
}
