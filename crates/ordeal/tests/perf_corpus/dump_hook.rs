//! REGENERATION TOOLING for tests/perf_corpus — not compiled by this
//! workspace (it is not a test target and no module includes it).
//!
//! How the synth/ and loom/ queries were taken (ordeal#283):
//!   1. `git worktree add --detach <dir> v<X.Y.Z>` at the ordeal version the
//!      consumer pins (synth: 0.36.1, loom: 0.34.0).
//!   2. Copy this file to `<dir>/crates/ordeal/src/dump_hook.rs`, add
//!      `#[doc(hidden)] pub mod dump_hook;` to lib.rs, and wrap the bodies of
//!      `Solver::check`, `check_with_limit` and `check_with_deadline` as
//!      `let p = crate::dump_hook::before(&self.assertions, "<entry>");
//!       let r = <original body>; crate::dump_hook::after(p, &r); r`.
//!   3. In a clone of the consumer at the manifest's commit, add
//!      `[patch.crates-io]` entries for ordeal (and ordeal-lrat,
//!      ordeal-cert) pointing at `<dir>/crates/...`.
//!   4. Run the command the manifest's `produced_by` names with
//!      `ORDEAL_DUMP_SMT2=<out>`; pick the query by its index; the `.meta`
//!      file next to it is the manifest's `consumer_api` block.
//!
//! Corpus dump hook (ordeal#283) — NOT part of any shipped ordeal.
//!
//! Applied to a scratch copy of the ordeal version a consumer pins, and
//! patched into that consumer with `[patch.crates-io]`. When
//! `ORDEAL_DUMP_SMT2=<dir>` is set, every `Solver::check`,
//! `check_with_limit` and `check_with_deadline` writes the asserted
//! conjunction as an SMT-LIB2 QF_BV script, `<dir>/q<pid>-<n>.smt2`, with a
//! header naming the calling thread (libtest names it after the test) and,
//! after the solve, the verdict and the API path's certificate sizes. The
//! perf gate later compares those sizes with what `smtlib::solve_str`
//! produces on the dumped text (fidelity check).
//!
//! The printer writes the term tree as is (the front end has no `let`), so
//! the re-parsed tree is the consumer's tree; ordeal hash-conses both the
//! same way. Rotations by a non-constant amount have no SMT-LIB spelling
//! and are refused (the dump is skipped and counted, never approximated).

use crate::{BoolTerm, BvTerm, CheckResult};
use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::sync::atomic::{AtomicUsize, Ordering};

static SEQ: AtomicUsize = AtomicUsize::new(0);

pub(crate) struct Pending {
    path: std::path::PathBuf,
    start: std::time::Instant,
}

fn sym(name: &str) -> String {
    let simple = name.chars().next().is_some_and(|c| !c.is_ascii_digit())
        && name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || "~!@$%^&*_-+=<>.?/".contains(c));
    if simple { name.to_string() } else { format!("|{name}|") }
}

/// Structural hash-consing printer: every compound node becomes one nullary
/// `define-fun` (`|nK|`), in dependency order, so the text is linear in the
/// DAG size (the consumer's term is a tree of `Box` clones that can be
/// exponentially larger). Leaves (variables, constants) stay inline.
struct Printer {
    vars: BTreeMap<String, u32>,
    memo: std::collections::HashMap<String, String>,
    defs: String,
}

impl Printer {
    fn intern(&mut self, sort: &str, body: String) -> String {
        if let Some(id) = self.memo.get(&body) {
            return id.clone();
        }
        let id = format!("|n{}|", self.memo.len());
        let _ = writeln!(self.defs, "(define-fun {id} () {sort} {body})");
        self.memo.insert(body, id.clone());
        id
    }

    fn bv(&mut self, t: &BvTerm) -> Result<(String, u32), String> {
        let (body, w) = match t {
            BvTerm::Const { value, sort } => return Ok((format!("(_ bv{value} {})", sort.width), sort.width)),
            BvTerm::Var { name, sort } => {
                if let Some(&w) = self.vars.get(name)
                    && w != sort.width
                {
                    return Err(format!("variable {name} at two widths"));
                }
                self.vars.insert(name.clone(), sort.width);
                return Ok((sym(name), sort.width));
            }
            BvTerm::Add(a, b) => self.bin("bvadd", a, b)?,
            BvTerm::Sub(a, b) => self.bin("bvsub", a, b)?,
            BvTerm::Mul(a, b) => self.bin("bvmul", a, b)?,
            BvTerm::Udiv(a, b) => self.bin("bvudiv", a, b)?,
            BvTerm::Urem(a, b) => self.bin("bvurem", a, b)?,
            BvTerm::And(a, b) => self.bin("bvand", a, b)?,
            BvTerm::Or(a, b) => self.bin("bvor", a, b)?,
            BvTerm::Xor(a, b) => self.bin("bvxor", a, b)?,
            BvTerm::Shl(a, b) => self.bin("bvshl", a, b)?,
            BvTerm::Lshr(a, b) => self.bin("bvlshr", a, b)?,
            BvTerm::Ashr(a, b) => self.bin("bvashr", a, b)?,
            BvTerm::Sdiv(a, b) => self.bin("bvsdiv", a, b)?,
            BvTerm::Srem(a, b) => self.bin("bvsrem", a, b)?,
            BvTerm::Concat(a, b) => {
                let (x, wa) = self.bv(a)?;
                let (y, wb) = self.bv(b)?;
                (format!("(concat {x} {y})"), wa + wb)
            }
            BvTerm::Rotr(a, k) | BvTerm::Rotl(a, k) => {
                let op = if matches!(t, BvTerm::Rotr(..)) { "rotate_right" } else { "rotate_left" };
                let BvTerm::Const { value, .. } = k.as_ref() else {
                    return Err(format!("{op} by a non-constant amount"));
                };
                let (x, w) = self.bv(a)?;
                if *value >= w as u128 {
                    // The front end reduces k mod w; the API term carries k.
                    return Err(format!("{op} amount {value} >= width {w}"));
                }
                (format!("((_ {op} {value}) {x})"), w)
            }
            BvTerm::Extract { hi, lo, arg } => (format!("((_ extract {hi} {lo}) {})", self.bv(arg)?.0), hi - lo + 1),
            BvTerm::ZeroExt { by, arg } => {
                let (x, w) = self.bv(arg)?;
                (format!("((_ zero_extend {by}) {x})"), w + by)
            }
            BvTerm::SignExt { by, arg } => {
                let (x, w) = self.bv(arg)?;
                (format!("((_ sign_extend {by}) {x})"), w + by)
            }
            BvTerm::Ite { cond, then_, else_ } => {
                let c = self.boolean(cond)?;
                let (a, w) = self.bv(then_)?;
                let (b, _) = self.bv(else_)?;
                (format!("(ite {c} {a} {b})"), w)
            }
            BvTerm::Not(a) => {
                let (x, w) = self.bv(a)?;
                (format!("(bvnot {x})"), w)
            }
            BvTerm::Neg(a) => {
                let (x, w) = self.bv(a)?;
                (format!("(bvneg {x})"), w)
            }
        };
        Ok((self.intern(&format!("(_ BitVec {w})"), body), w))
    }

    fn bin(&mut self, op: &str, a: &BvTerm, b: &BvTerm) -> Result<(String, u32), String> {
        let (x, w) = self.bv(a)?;
        let (y, _) = self.bv(b)?;
        Ok((format!("({op} {x} {y})"), w))
    }

    fn boolean(&mut self, t: &BoolTerm) -> Result<String, String> {
        let body = match t {
            BoolTerm::Eq(a, b) => self.bin("=", a, b)?.0,
            BoolTerm::Ne(a, b) => self.bin("distinct", a, b)?.0,
            BoolTerm::Ult(a, b) => self.bin("bvult", a, b)?.0,
            BoolTerm::Ule(a, b) => self.bin("bvule", a, b)?.0,
            BoolTerm::Ugt(a, b) => self.bin("bvugt", a, b)?.0,
            BoolTerm::Uge(a, b) => self.bin("bvuge", a, b)?.0,
            BoolTerm::Slt(a, b) => self.bin("bvslt", a, b)?.0,
            BoolTerm::Sle(a, b) => self.bin("bvsle", a, b)?.0,
            BoolTerm::Sgt(a, b) => self.bin("bvsgt", a, b)?.0,
            BoolTerm::Sge(a, b) => self.bin("bvsge", a, b)?.0,
            BoolTerm::Not(x) => format!("(not {})", self.boolean(x)?),
            BoolTerm::And(x, y) => {
                let x = self.boolean(x)?;
                let y = self.boolean(y)?;
                format!("(and {x} {y})")
            }
            BoolTerm::Or(x, y) => {
                let x = self.boolean(x)?;
                let y = self.boolean(y)?;
                format!("(or {x} {y})")
            }
        };
        Ok(self.intern("Bool", body))
    }
}

/// Print `assertions` as a QF_BV script: declarations, one nullary
/// `define-fun` per shared compound node, the asserts, `check-sat`.
pub fn to_script(assertions: &[BoolTerm]) -> Result<String, String> {
    let mut p = Printer { vars: BTreeMap::new(), memo: Default::default(), defs: String::new() };
    let mut asserts = String::new();
    for a in assertions {
        let id = p.boolean(a)?;
        let _ = writeln!(asserts, "(assert {id})");
    }
    let mut s = String::from("(set-logic QF_BV)\n");
    for (n, w) in &p.vars {
        let _ = writeln!(s, "(declare-fun {} () (_ BitVec {w}))", sym(n));
    }
    s.push_str(&p.defs);
    s.push_str(&asserts);
    s.push_str("(check-sat)\n");
    Ok(s)
}

pub(crate) fn before(assertions: &[BoolTerm], entry: &str) -> Option<Pending> {
    let dir = std::env::var_os("ORDEAL_DUMP_SMT2")?;
    let n = SEQ.fetch_add(1, Ordering::SeqCst);
    let thread = std::thread::current().name().unwrap_or("?").to_string();
    let path = std::path::Path::new(&dir).join(format!("q{}-{n:05}.smt2", std::process::id()));
    let text = match to_script(assertions) {
        Ok(t) => t,
        Err(e) => {
            let _ = std::fs::write(path.with_extension("skipped"), format!("; thread: {thread}\n; skipped: {e}\n"));
            return None;
        }
    };
    let head = format!("; thread: {thread}\n; entry: {entry}\n; assertions: {}\n", assertions.len());
    std::fs::write(&path, format!("{head}{text}")).ok()?;
    Some(Pending { path, start: std::time::Instant::now() })
}

pub(crate) fn after(p: Option<Pending>, r: &CheckResult) {
    let Some(p) = p else { return };
    let ms = p.start.elapsed().as_millis();
    let meta = match r {
        CheckResult::Unsat(c) => format!(
            "verdict=unsat cnf_clauses={} lrat_bytes={} lrat_lines={} api_ms={ms}\n",
            c.cnf.len(),
            c.lrat.len(),
            c.lrat.iter().filter(|&&b| b == b'\n').count()
        ),
        CheckResult::Sat(_) => format!("verdict=sat api_ms={ms}\n"),
        CheckResult::Unknown => format!("verdict=unknown api_ms={ms}\n"),
    };
    let _ = std::fs::write(p.path.with_extension("meta"), meta);
}
