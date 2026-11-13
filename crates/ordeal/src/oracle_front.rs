//! The Z3 parser differential, **front leg** (#281 phase E0, TR-087).
//!
//! `oracle::to_z3` translates ordeal's *own* trees, so the rest of the
//! oracle checks the engine, never the SMT-LIB reader. This leg reads text:
//! for a script `S`, Z3 parses `S` with its own parser
//! ([`z3::Solver::from_string`]) and ordeal's reader produces its tree
//! ([`crate::smtlib::read_script`]); ordeal's tree goes through
//! [`super::to_z3`], and for every assertion `k` Z3 decides
//! `A_Z3[k] xor A_ord[k]`. Unsat means the two readings of assertion `k`
//! agree under every interpretation of the declared names.
//!
//! # Names
//!
//! A bitvector name is linked by identity: ordeal's `Var { name: "x", w }`
//! becomes Z3's constant `x` of sort `(_ BitVec w)`, the same declaration the
//! parser made (a width the reader got wrong is a different constant, and
//! the xor then has a model). A quoted name that the reader keeps with its
//! bars (`|a b|`) denotes the SMT-LIB symbol `a b`, so the bars are stripped
//! here. A `Bool` name `b` is held by ordeal as a BV1 variable read as
//! `b = #b1` (`smtlib::Ctx::bool_decls`); Z3's `Bool` constant `b` and that
//! BV1 constant are different declarations, so every check asserts the
//! link `b ⇔ (b₁ = #b1)` (design note §2).
//!
//! # Outcome classes (design note §6)
//!
//! - **agree** — both read the script, the same number of assertions, every
//!   xor unsat;
//! - **disagree** — some xor has a model (or the counts differ, or Z3 cannot
//!   decide): a failure, reported with Z3's witness;
//! - **ordeal refuses / Z3 accepts** — incompleteness: counted and listed,
//!   not a failure (ordeal never answers on a script it refused);
//! - **Z3 refuses / ordeal accepts** — a failure unless the script is covered
//!   by an entry of [`Z3_REFUSES_ALLOW_LIST`], each with its reason;
//! - **both refuse** — counted, not compared.
//!
//! Z3 keeps reading after an `(error …)` and `from_string` then reports a
//! parser error for the whole script, so any error is "Z3 refuses".
//!
//! Not trusted, not on any verdict path: a differential, like the rest of
//! this module (`oracle.rs` header).

use super::{XorShift64, to_z3};
use crate::smtlib::{self, ScriptReading};
use crate::term::{BoolTerm, BvTerm, Sort};
use std::ffi::CStr;
use std::fmt::Write as _;
use z3::ast::Bool;
use z3::{Params, SatResult, Solver};

// ─── Z3's reading ────────────────────────────────────────────────────────────

/// What Z3's own SMT-LIB parser made of a script.
pub enum Z3Reading {
    /// Parsed without error: one Z3 assertion per `assert` command.
    Accepted(Vec<Bool>),
    /// Z3 reported an error (any `(error …)` while reading).
    Refused(String),
}

/// Parse `script` with Z3's parser (`Z3_solver_from_string`, which ignores
/// `check-sat`) and collect its assertions.
pub fn z3_read(script: &str) -> Z3Reading {
    if script.contains('\0') {
        return Z3Reading::Refused("NUL byte in script".into());
    }
    let solver = Solver::new();
    solver.from_string(script);
    let ctx = solver.get_context().get_z3_context();
    // SAFETY: `ctx` is the live thread-local context `solver` was created
    // in; both calls only read its error state. The safe `z3` crate clears
    // the error handler (`Z3_set_error_handler(ctx, None)`), so a parse
    // error sets this code instead of exiting the process.
    let code = unsafe { z3_sys::Z3_get_error_code(ctx) };
    if code != z3_sys::ErrorCode::Ok {
        // SAFETY: as above; Z3 returns a NUL-terminated string it owns.
        let msg = unsafe {
            let p = z3_sys::Z3_get_error_msg(ctx, code);
            if p.is_null() {
                String::new()
            } else {
                CStr::from_ptr(p).to_string_lossy().into_owned()
            }
        };
        return Z3Reading::Refused(format!("{code:?}: {msg}"));
    }
    Z3Reading::Accepted(solver.get_assertions())
}

// ─── Name linking ────────────────────────────────────────────────────────────

/// The SMT-LIB symbol an ordeal name denotes: `|s|` is the symbol `s`.
fn symbol_of(name: &str) -> &str {
    name.strip_prefix('|')
        .and_then(|n| n.strip_suffix('|'))
        .unwrap_or(name)
}

fn rename_bv(t: &BvTerm) -> BvTerm {
    let b = |x: &BvTerm| Box::new(rename_bv(x));
    match t {
        BvTerm::Var { name, sort } => BvTerm::Var {
            name: symbol_of(name).to_string(),
            sort: *sort,
        },
        BvTerm::Const { .. } => t.clone(),
        BvTerm::Add(x, y) => BvTerm::Add(b(x), b(y)),
        BvTerm::Sub(x, y) => BvTerm::Sub(b(x), b(y)),
        BvTerm::Mul(x, y) => BvTerm::Mul(b(x), b(y)),
        BvTerm::Udiv(x, y) => BvTerm::Udiv(b(x), b(y)),
        BvTerm::Urem(x, y) => BvTerm::Urem(b(x), b(y)),
        BvTerm::And(x, y) => BvTerm::And(b(x), b(y)),
        BvTerm::Or(x, y) => BvTerm::Or(b(x), b(y)),
        BvTerm::Xor(x, y) => BvTerm::Xor(b(x), b(y)),
        BvTerm::Shl(x, y) => BvTerm::Shl(b(x), b(y)),
        BvTerm::Lshr(x, y) => BvTerm::Lshr(b(x), b(y)),
        BvTerm::Ashr(x, y) => BvTerm::Ashr(b(x), b(y)),
        BvTerm::Rotr(x, y) => BvTerm::Rotr(b(x), b(y)),
        BvTerm::Rotl(x, y) => BvTerm::Rotl(b(x), b(y)),
        BvTerm::Sdiv(x, y) => BvTerm::Sdiv(b(x), b(y)),
        BvTerm::Srem(x, y) => BvTerm::Srem(b(x), b(y)),
        BvTerm::Concat(x, y) => BvTerm::Concat(b(x), b(y)),
        BvTerm::Not(x) => BvTerm::Not(b(x)),
        BvTerm::Neg(x) => BvTerm::Neg(b(x)),
        BvTerm::Extract { hi, lo, arg } => BvTerm::Extract {
            hi: *hi,
            lo: *lo,
            arg: b(arg),
        },
        BvTerm::ZeroExt { by, arg } => BvTerm::ZeroExt {
            by: *by,
            arg: b(arg),
        },
        BvTerm::SignExt { by, arg } => BvTerm::SignExt {
            by: *by,
            arg: b(arg),
        },
        BvTerm::Ite { cond, then_, else_ } => BvTerm::Ite {
            cond: Box::new(rename_bool(cond)),
            then_: b(then_),
            else_: b(else_),
        },
    }
}

fn rename_bool(t: &BoolTerm) -> BoolTerm {
    let v = |x: &BvTerm| Box::new(rename_bv(x));
    let p = |x: &BoolTerm| Box::new(rename_bool(x));
    match t {
        BoolTerm::Eq(a, b) => BoolTerm::Eq(v(a), v(b)),
        BoolTerm::Ne(a, b) => BoolTerm::Ne(v(a), v(b)),
        BoolTerm::Ult(a, b) => BoolTerm::Ult(v(a), v(b)),
        BoolTerm::Ule(a, b) => BoolTerm::Ule(v(a), v(b)),
        BoolTerm::Ugt(a, b) => BoolTerm::Ugt(v(a), v(b)),
        BoolTerm::Uge(a, b) => BoolTerm::Uge(v(a), v(b)),
        BoolTerm::Slt(a, b) => BoolTerm::Slt(v(a), v(b)),
        BoolTerm::Sle(a, b) => BoolTerm::Sle(v(a), v(b)),
        BoolTerm::Sgt(a, b) => BoolTerm::Sgt(v(a), v(b)),
        BoolTerm::Sge(a, b) => BoolTerm::Sge(v(a), v(b)),
        BoolTerm::Not(a) => BoolTerm::Not(p(a)),
        BoolTerm::And(a, b) => BoolTerm::And(p(a), p(b)),
        BoolTerm::Or(a, b) => BoolTerm::Or(p(a), p(b)),
    }
}

/// `b ⇔ (b₁ = #b1)` for every `Bool` name: Z3's `Bool` constant against the
/// BV1 variable ordeal holds it as.
fn bool_links(reading: &ScriptReading) -> Vec<Bool> {
    reading
        .bool_names
        .iter()
        .map(|n| {
            let s = symbol_of(n);
            let as_bv1 = to_z3(&BoolTerm::Eq(
                Box::new(BvTerm::Var {
                    name: s.to_string(),
                    sort: Sort::new(1),
                }),
                Box::new(BvTerm::Const {
                    value: 1,
                    sort: Sort::new(1),
                }),
            ));
            Bool::new_const(s).iff(&as_bv1)
        })
        .collect()
}

// ─── Outcome classes and the allow-list ──────────────────────────────────────

/// One script's outcome class (design note §6).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FrontClass {
    /// Every assertion agrees.
    Agree,
    /// A reading differs (with Z3's witness). Fails.
    Disagree,
    /// ordeal refuses a script Z3 accepts: incompleteness, listed only.
    OrdealRefuses,
    /// Z3 refuses a script ordeal accepts, not on the allow-list. Fails.
    Z3Refuses,
    /// Z3 refuses a script ordeal accepts, covered by an allow-list entry.
    Z3RefusesAllowed,
    /// Both refuse; not compared.
    BothRefuse,
}

/// One script's front-leg result.
#[derive(Clone, Debug)]
pub struct FrontResult {
    /// The class.
    pub class: FrontClass,
    /// Assertions compared (each an unsat xor) before the result was known.
    pub compared: usize,
    /// The witness, refusal message or allow-list entry, for the report.
    pub detail: String,
}

/// A reviewed exception to "Z3 refuses / ordeal accepts fails".
pub struct AllowEntry {
    /// Short id, printed in the tally.
    pub id: &'static str,
    /// Why the deviation is accepted.
    pub reason: &'static str,
    /// Whether the entry covers a script, judged on ordeal's reading.
    pub applies: fn(&ScriptReading) -> bool,
}

/// An identical redeclaration (same name, same sort) occurs in the reading.
fn has_identical_redeclaration(r: &ScriptReading) -> bool {
    let mut seen = std::collections::HashSet::new();
    r.declared.iter().any(|d| !seen.insert(d.clone()))
}

/// The reviewed allow-list of "Z3 refuses / ordeal accepts" deviations.
pub const Z3_REFUSES_ALLOW_LIST: &[AllowEntry] = &[AllowEntry {
    id: "identical-redeclaration-139",
    reason: "#139: an identical redeclaration (same name, same sort; `x` and \
             `|x|` are one name) is tolerated so concatenated logs read; \
             SMT-LIB and Z3 refuse it. It cannot change a verdict: the \
             second declaration names the same variable.",
    applies: has_identical_redeclaration,
}];

/// Per-check Z3 budget. The xors are near-identical formulas that Z3
/// mostly simplifies to `false`; a timeout is reported, never passed.
const CHECK_TIMEOUT_MS: u32 = 10_000;

/// Run the front leg on one script.
pub fn front_leg(script: &str) -> FrontResult {
    classify(z3_read(script), smtlib::read_script(script))
}

/// Classify one script from the two readings (split from [`front_leg`] so
/// the harness's own fixtures can feed it a reading directly).
fn classify(z3: Z3Reading, ord: Result<ScriptReading, smtlib::SmtError>) -> FrontResult {
    let result = |class, compared, detail: String| FrontResult {
        class,
        compared,
        detail,
    };
    // A width outside 1..=128 (#313): the reader answers `unknown` and holds
    // a placeholder for the assertion, which is not a reading of the text.
    // Incompleteness at worst (Z3 reads it), listed and not compared.
    if let Ok(r) = &ord
        && r.too_wide
    {
        return match z3 {
            Z3Reading::Accepted(_) => result(
                FrontClass::OrdealRefuses,
                0,
                "width above 128: answered unknown".into(),
            ),
            Z3Reading::Refused(z) => result(
                FrontClass::BothRefuse,
                0,
                format!("Z3: {z}; ordeal: width above 128"),
            ),
        };
    }
    let (z3_asserts, reading) = match (z3, ord) {
        (Z3Reading::Refused(z), Err(o)) => {
            return result(FrontClass::BothRefuse, 0, format!("Z3: {z}; ordeal: {o}"));
        }
        (Z3Reading::Accepted(_), Err(o)) => {
            return result(FrontClass::OrdealRefuses, 0, o.to_string());
        }
        (Z3Reading::Refused(z), Ok(reading)) => {
            return match Z3_REFUSES_ALLOW_LIST.iter().find(|e| (e.applies)(&reading)) {
                Some(e) => result(FrontClass::Z3RefusesAllowed, 0, e.id.to_string()),
                None => result(FrontClass::Z3Refuses, 0, z),
            };
        }
        (Z3Reading::Accepted(a), Ok(r)) => (a, r),
    };
    if z3_asserts.len() != reading.assertions.len() {
        return result(
            FrontClass::Disagree,
            0,
            format!(
                "assertion count: Z3 {} vs ordeal {}",
                z3_asserts.len(),
                reading.assertions.len()
            ),
        );
    }
    let links = bool_links(&reading);
    let mut params = Params::new();
    params.set_u32("timeout", CHECK_TIMEOUT_MS);
    for (k, (az, ao)) in z3_asserts.iter().zip(&reading.assertions).enumerate() {
        let ord = to_z3(&rename_bool(ao));
        let solver = Solver::new();
        solver.set_params(&params);
        for l in &links {
            solver.assert(l);
        }
        solver.assert(az.xor(&ord));
        match solver.check() {
            SatResult::Unsat => {}
            SatResult::Sat => {
                let model = solver
                    .get_model()
                    .map(|m| m.to_string())
                    .unwrap_or_default();
                return result(
                    FrontClass::Disagree,
                    k,
                    format!(
                        "assertion {k}: Z3 reads {az}, ordeal reads {ord}; witness: {}",
                        model.replace('\n', " ")
                    ),
                );
            }
            SatResult::Unknown => {
                return result(
                    FrontClass::Disagree,
                    k,
                    format!(
                        "assertion {k}: Z3 could not decide the xor ({})",
                        solver.get_reason_unknown().unwrap_or_default()
                    ),
                );
            }
        }
    }
    result(FrontClass::Agree, z3_asserts.len(), String::new())
}

// ─── The tally ───────────────────────────────────────────────────────────────

/// Counts of every class over a run, with the failing and listed scripts.
#[derive(Default, Debug)]
pub struct FrontTally {
    /// Scripts in each class.
    pub agree: usize,
    pub disagree: usize,
    pub ordeal_refuses: usize,
    pub z3_refuses: usize,
    pub z3_refuses_allowed: usize,
    pub both_refuse: usize,
    /// Assertions compared (unsat xors) over the run.
    pub assertions_compared: usize,
    /// `label: detail` of each failing script (disagree, Z3 refuses).
    pub failures: Vec<String>,
    /// `label: detail` of each listed, non-failing deviation.
    pub listed: Vec<String>,
}

impl FrontTally {
    /// Record one script's result under `label`.
    pub fn record(&mut self, label: &str, r: &FrontResult) {
        self.assertions_compared += r.compared;
        let line = format!("{label}: {}", r.detail);
        match r.class {
            FrontClass::Agree => self.agree += 1,
            FrontClass::Disagree => {
                self.disagree += 1;
                self.failures.push(format!("[disagree] {line}"));
            }
            FrontClass::Z3Refuses => {
                self.z3_refuses += 1;
                self.failures
                    .push(format!("[Z3 refuses / ordeal accepts] {line}"));
            }
            FrontClass::OrdealRefuses => {
                self.ordeal_refuses += 1;
                self.listed
                    .push(format!("[ordeal refuses / Z3 accepts] {line}"));
            }
            FrontClass::Z3RefusesAllowed => {
                self.z3_refuses_allowed += 1;
                self.listed
                    .push(format!("[Z3 refuses, allow-listed] {line}"));
            }
            FrontClass::BothRefuse => {
                self.both_refuse += 1;
                self.listed.push(format!("[both refuse] {line}"));
            }
        }
    }

    /// Scripts both sides read and compared (agree + disagree).
    pub fn compared(&self) -> usize {
        self.agree + self.disagree
    }

    /// The one-line tally printed on every run.
    pub fn summary(&self) -> String {
        format!(
            "front leg: {} scripts compared ({} assertions): agree {}, disagree {}, \
             ordeal-refuses/Z3-accepts {}, Z3-refuses/ordeal-accepts {}, \
             Z3-refuses allow-listed {}, both refuse {}",
            self.compared(),
            self.assertions_compared,
            self.agree,
            self.disagree,
            self.ordeal_refuses,
            self.z3_refuses,
            self.z3_refuses_allowed,
            self.both_refuse
        )
    }

    /// The full report: the summary, then every failure and listed script.
    pub fn report(&self) -> String {
        let mut s = self.summary();
        for f in &self.failures {
            let _ = write!(s, "\n  FAIL {f}");
        }
        for l in &self.listed {
            let _ = write!(s, "\n  list {l}");
        }
        s
    }

    /// Whether the run passes: something was compared, nothing failed.
    pub fn passes(&self) -> bool {
        self.compared() > 0 && self.failures.is_empty()
    }
}

/// Run the front leg over labelled scripts.
pub fn run_front_leg<'a>(scripts: impl IntoIterator<Item = (String, &'a str)>) -> FrontTally {
    let mut tally = FrontTally::default();
    for (label, script) in scripts {
        tally.record(&label, &front_leg(script));
    }
    tally
}

// ─── The seeded SMT-LIB text generator ───────────────────────────────────────

/// Bitvector widths the generator declares: odd and non-power-of-two widths
/// on purpose (the #182 class), and small ones so `rotate_*` amounts reach
/// `k >= 2^w`.
const GEN_WIDTHS: &[u32] = &[1, 3, 4, 5, 7, 8, 12, 16];

/// One generated script in this many declares a reserved word (#315).
const RESERVED_DECL_ONE_IN: u64 = 25;

/// The comment that marks such a script, so a run can tell the scripts the
/// reader must refuse from the ones it must read.
pub const RESERVED_DECL_MARK: &str = "; reserved-word declaration";

/// Reserved words and theory symbols the generator declares, bare or quoted.
const RESERVED_DECL_WORDS: &[&str] = &[
    "let",
    "_",
    "!",
    "as",
    "par",
    "forall",
    "exists",
    "match",
    "NUMERAL",
    "DECIMAL",
    "STRING",
    "BINARY",
    "HEXADECIMAL",
    "assert",
    "check-sat",
    "ite",
    "distinct",
    "concat",
    "bvadd",
    "bvult",
    "true",
    "Bool",
    "extract",
];

struct TextGen {
    rng: XorShift64,
    /// (base symbol, width, simple?) — a simple symbol may be spelled bare
    /// or quoted at each use; any other is always quoted.
    vars: Vec<(String, u32, bool)>,
    /// (base symbol, simple?).
    bools: Vec<(String, bool)>,
}

impl TextGen {
    fn below(&mut self, n: u64) -> u64 {
        self.rng.below(n)
    }

    fn pick<'s, T>(&mut self, xs: &'s [T]) -> &'s T {
        &xs[self.below(xs.len() as u64) as usize]
    }

    fn spell(&mut self, base: &str, simple: bool) -> String {
        if simple && self.below(2) == 0 {
            base.to_string()
        } else {
            format!("|{base}|")
        }
    }

    /// A literal of width `w` in one of the three forms; `(_ bvN W)` with a
    /// value that may be `>= 2^W` (SMT-LIB reduces it mod `2^W`).
    fn literal(&mut self, w: u32) -> String {
        let v = self.rng.next() as u128;
        let masked = if w >= 128 { v } else { v & ((1u128 << w) - 1) };
        match self.below(3) {
            0 if w.is_multiple_of(4) => format!("#x{:0width$x}", masked, width = (w / 4) as usize),
            0 | 1 => format!("#b{:0width$b}", masked, width = w as usize),
            _ => {
                let n = if self.below(2) == 0 {
                    masked
                } else {
                    // >= 2^W: a multiple of 2^W added on top.
                    masked + ((self.below(5) as u128 + 1) << w.min(64))
                };
                format!("(_ bv{n} {w})")
            }
        }
    }

    fn var_of_width(&mut self, w: u32) -> Option<String> {
        let cands: Vec<(String, bool)> = self
            .vars
            .iter()
            .filter(|v| v.1 == w)
            .map(|v| (v.0.clone(), v.2))
            .collect();
        if cands.is_empty() {
            return None;
        }
        let (b, s) = cands[self.below(cands.len() as u64) as usize].clone();
        Some(self.spell(&b, s))
    }

    fn leaf(&mut self, w: u32) -> String {
        if self.below(3) != 0
            && let Some(v) = self.var_of_width(w)
        {
            return v;
        }
        // Reach a declared var of another width through extract/extend.
        if self.below(2) == 0 && !self.vars.is_empty() {
            let i = self.below(self.vars.len() as u64) as usize;
            let (b, vw, s) = self.vars[i].clone();
            let v = self.spell(&b, s);
            if vw > w {
                let lo = self.below((vw - w + 1) as u64) as u32;
                return format!("((_ extract {} {lo}) {v})", lo + w - 1);
            }
            if vw < w {
                let op = if self.below(2) == 0 {
                    "zero_extend"
                } else {
                    "sign_extend"
                };
                return format!("((_ {op} {}) {v})", w - vw);
            }
            return v;
        }
        self.literal(w)
    }

    fn args(&mut self, w: u32, d: u32, lo: u64, hi: u64) -> String {
        let n = lo + self.below(hi - lo + 1);
        (0..n).map(|_| self.bv(w, d)).collect::<Vec<_>>().join(" ")
    }

    fn bv(&mut self, w: u32, d: u32) -> String {
        if d == 0 || self.below(4) == 0 {
            return self.leaf(w);
        }
        let d = d - 1;
        match self.below(9) {
            0 => {
                let op = *self.pick(&["bvadd", "bvmul", "bvand", "bvor", "bvxor"]);
                format!("({op} {})", self.args(w, d, 2, 4))
            }
            1 => {
                let op = *self.pick(&[
                    "bvsub", "bvudiv", "bvurem", "bvshl", "bvlshr", "bvashr", "bvsdiv", "bvsrem",
                ]);
                format!("({op} {} {})", self.bv(w, d), self.bv(w, d))
            }
            2 => {
                let op = *self.pick(&["bvnot", "bvneg"]);
                format!("({op} {})", self.bv(w, d))
            }
            3 if w >= 2 => {
                // n-ary concat: split w into 2..=3 positive parts.
                let a = 1 + self.below((w - 1) as u64) as u32;
                let rest = w - a;
                if rest >= 2 && self.below(2) == 0 {
                    let b = 1 + self.below((rest - 1) as u64) as u32;
                    format!(
                        "(concat {} {} {})",
                        self.bv(a, d),
                        self.bv(b, d),
                        self.bv(rest - b, d)
                    )
                } else {
                    format!("(concat {} {})", self.bv(a, d), self.bv(rest, d))
                }
            }
            4 => {
                let extra = self.below(5) as u32;
                let lo = self.below(extra as u64 + 1) as u32;
                format!(
                    "((_ extract {} {lo}) {})",
                    lo + w - 1,
                    self.bv(w + extra, d)
                )
            }
            5 if w >= 2 => {
                let k = 1 + self.below((w - 1) as u64) as u32;
                let op = *self.pick(&["zero_extend", "sign_extend"]);
                format!("((_ {op} {k}) {})", self.bv(w - k, d))
            }
            6 | 7 => {
                // k >= w often; k >= 2^w at small widths.
                let span = if w <= 8 {
                    (1u64 << w) * 3
                } else {
                    4 * w as u64
                };
                let k = self.below(span + 1);
                let op = *self.pick(&["rotate_left", "rotate_right"]);
                format!("((_ {op} {k}) {})", self.bv(w, d))
            }
            _ => format!(
                "(ite {} {} {})",
                self.boolean(d),
                self.bv(w, d),
                self.bv(w, d)
            ),
        }
    }

    fn width(&mut self) -> u32 {
        *self.pick(GEN_WIDTHS)
    }

    fn boolean(&mut self, d: u32) -> String {
        let leafy = d == 0 || self.below(5) == 0;
        let choice = if leafy {
            self.below(4)
        } else {
            4 + self.below(9)
        };
        let dd = d.saturating_sub(1);
        match choice {
            0 => self.pick(&["true", "false"]).to_string(),
            1 if !self.bools.is_empty() => {
                let i = self.below(self.bools.len() as u64) as usize;
                let (b, s) = self.bools[i].clone();
                self.spell(&b, s)
            }
            1..=3 => {
                let w = self.width();
                let op = *self.pick(&[
                    "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
                ]);
                format!("({op} {} {})", self.bv(w, dd), self.bv(w, dd))
            }
            4 => {
                let w = self.width();
                format!("(= {})", self.args(w, dd, 2, 4))
            }
            5 => {
                let w = self.width();
                format!("(distinct {})", self.args(w, dd, 2, 4))
            }
            6 => format!("(not {})", self.boolean(dd)),
            7 => {
                let op = *self.pick(&["and", "or"]);
                format!("({op} {})", self.bools_n(dd, 2, 4))
            }
            8 => format!("(=> {})", self.bools_n(dd, 2, 4)),
            9 => format!("(= {})", self.bools_n(dd, 2, 3)),
            // `distinct` and `ite` at sort Bool (#312).
            11 => format!("(distinct {})", self.bools_n(dd, 2, 4)),
            12 => format!(
                "(ite {} {} {})",
                self.boolean(dd),
                self.boolean(dd),
                self.boolean(dd)
            ),
            _ => {
                let w = self.width();
                let op = *self.pick(&["bvslt", "bvsle", "bvsgt", "bvsge"]);
                format!("({op} {} {})", self.bv(w, dd), self.bv(w, dd))
            }
        }
    }

    fn bools_n(&mut self, d: u32, lo: u64, hi: u64) -> String {
        let n = lo + self.below(hi - lo + 1);
        (0..n)
            .map(|_| self.boolean(d))
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// A `set-info` whose value is a string literal holding what a naive
    /// tokenizer breaks on: `)`, `(`, `;` and the `""` escape (#311).
    fn set_info(&mut self) -> &'static str {
        self.pick(&[
            "(set-info :source \"a ) b\")\n",
            "(set-info :notes \"a;b\")\n",
            "(set-info :source \"say \"\"hi\"\" ( now\")\n",
            "(set-info :source \"\")\n",
            "(set-info :source \"x ) ; ( y\")(set-info :status unknown)\n",
            "(set-info :smt-lib-version 2.6)\n",
            "(set-option :print-success false)\n",
        ])
    }

    fn comment(&mut self) -> &'static str {
        self.pick(&[
            "; a comment ( with an unbalanced paren\n",
            "; |not a symbol| #x00 (assert false)\n",
            ";; double\n",
            "",
            "",
        ])
    }

    fn script(&mut self) -> String {
        let mut s = String::new();
        s.push_str(self.comment());
        if self.below(4) != 0 {
            s.push_str("(set-logic QF_BV)\n");
        }
        if self.below(3) == 0 {
            s.push_str(self.set_info());
        }
        self.vars.clear();
        self.bools.clear();
        let nv = 2 + self.below(3);
        for i in 0..nv {
            let w = self.width();
            let (base, simple) = match self.below(5) {
                0 => (format!("v {i}"), false),
                1 => (format!("{i}v"), false),
                2 => (format!("v#{i}"), false),
                _ => (format!("v{i}"), true),
            };
            let name = self.spell(&base, simple);
            if self.below(2) == 0 {
                let _ = writeln!(s, "(declare-const {name} (_ BitVec {w}))");
            } else {
                let _ = writeln!(s, "(declare-fun {name} () (_ BitVec {w}))");
            }
            s.push_str(self.comment());
            self.vars.push((base, w, simple));
        }
        // A declaration of a reserved word or theory symbol (#315): the
        // reader refuses it. Z3 accepts some (`|let|`) and refuses others, so
        // such a script is "ordeal refuses" or "both refuse", never compared;
        // the marker lets the run account for every script not compared.
        if self.below(RESERVED_DECL_ONE_IN) == 0 {
            let word = *self.pick(RESERVED_DECL_WORDS);
            let name = self.spell(word, true);
            let w = self.width();
            let _ = writeln!(
                s,
                "(declare-fun {name} () (_ BitVec {w})) {RESERVED_DECL_MARK}"
            );
        }
        let nb = self.below(3);
        for i in 0..nb {
            let (base, simple) = if self.below(3) == 0 {
                (format!("p {i}"), false)
            } else {
                (format!("p{i}"), true)
            };
            let name = self.spell(&base, simple);
            if self.below(2) == 0 {
                let _ = writeln!(s, "(declare-const {name} Bool)");
            } else {
                let _ = writeln!(s, "(declare-fun {name} () Bool)");
            }
            self.bools.push((base, simple));
        }
        let na = 1 + self.below(3);
        for _ in 0..na {
            let b = self.boolean(3);
            let _ = write!(s, "(assert {b})");
            if self.below(3) == 0 {
                s.push_str(" ; trailing comment");
            }
            s.push('\n');
        }
        s.push_str("(check-sat)\n");
        s
    }
}

/// A seeded, reproducible generator of SMT-LIB **text** in the syntax the
/// reader desugars (#281 E0): n-ary `bvadd`… and `concat`, chained `=`,
/// n-ary `distinct`, `=>`, `Bool` constants by `declare-const` and nullary
/// `declare-fun`, `true` / `false`, `=` over booleans, `rotate_*` with
/// `k >= w` (and `k >= 2^w` at small widths), all three literal forms with
/// `(_ bvN W)` values `>= 2^W`, quoted symbols (simple ones spelled both
/// ways, non-simple ones always quoted), comments, `set-info` / `set-option`
/// string literals holding `)` `(` `;` and `""` (#311), `distinct` and `ite`
/// at sort Bool (#312), and, in one script in 25, a declaration of a reserved
/// word (#315, marked by [`RESERVED_DECL_MARK`]). [`super::gen_corpus`]
/// prints nothing, so it cannot reach this syntax.
pub fn gen_smtlib_text(seed: u64, n: usize) -> Vec<String> {
    let mut g = TextGen {
        rng: XorShift64::new(seed),
        vars: Vec::new(),
        bools: Vec::new(),
    };
    (0..n).map(|_| g.script()).collect()
}

#[cfg(test)]
mod tests {
    //! The front leg's gate (VER-087). Run alone with
    //! `cargo test -p ordeal --features oracle --release --lib oracle::front::tests`
    //! (CI job "SMT-LIB parser differential", blocking).

    use super::*;
    use crate::smtlib::{Mutation, mutation};
    use std::path::{Path, PathBuf};
    use std::time::Instant;

    /// Generated scripts per CI run: 10^4 take ~21 s in release with Z3
    /// 5.1.0 on an Apple-silicon Mac (measured 2026-11-05). The 10^5 run
    /// (another seed) is `front_leg_agrees_on_1e5_generated_scripts`,
    /// `#[ignore]`d here and run by `.github/workflows/nightly-exhaustive.yml`
    /// (design note §6).
    const GEN_COUNT: usize = 10_000;
    const GEN_SEED: u64 = 0x0281_E0F0;

    /// Every `.smt2` file under `dir`, skipping build output and hidden dirs.
    fn smt2_files(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for e in entries.flatten() {
            let p = e.path();
            let name = e.file_name().to_string_lossy().into_owned();
            if p.is_dir() {
                if !name.starts_with('.') && name != "target" && name != "node_modules" {
                    smt2_files(&p, out);
                }
            } else if name.ends_with(".smt2") {
                out.push(p);
            }
        }
    }

    /// Disarms the mutation when dropped, so a failing control cannot leak
    /// an armed mutation into the next test on this thread.
    struct Armed;
    impl Armed {
        fn arm(m: Mutation) -> Self {
            mutation::arm(m);
            Armed
        }
    }
    impl Drop for Armed {
        fn drop(&mut self) {
            mutation::disarm();
        }
    }

    // rivet: verifies VER-087
    #[test]
    fn front_leg_agrees_on_every_repository_smt2_file() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let mut files = Vec::new();
        smt2_files(&root, &mut files);
        files.sort();
        // 27 when written (design note §6): 10 differential fixtures, 3 Verus
        // fixtures, 2 evidence/certs, 12 fuzz seeds.
        assert!(files.len() >= 27, "found only {} .smt2 files", files.len());
        let mut scripts = Vec::new();
        for f in &files {
            let text = std::fs::read_to_string(f).expect("readable .smt2");
            let rel = f.strip_prefix(&root).unwrap_or(f).display().to_string();
            // A Verus log is fed as the obligation `ordeal verus` reads.
            if crate::verus::is_bitvector_query(&text) {
                let ob = crate::verus::extract(&text).expect("Verus fixture extracts");
                scripts.push((format!("{rel} (verus::extract)"), ob.script));
            } else {
                scripts.push((rel, text));
            }
        }
        let t = Instant::now();
        let tally = run_front_leg(scripts.iter().map(|(l, s)| (l.clone(), s.as_str())));
        eprintln!(
            "{} files, {:.2?}\n{}",
            files.len(),
            t.elapsed(),
            tally.report()
        );
        assert!(tally.passes(), "{}", tally.report());
    }

    fn generated_run(seed: u64, n: usize) {
        let t = Instant::now();
        let scripts = gen_smtlib_text(seed, n);
        let tally = run_front_leg(
            scripts
                .iter()
                .enumerate()
                .map(|(i, s)| (format!("gen#{i}"), s.as_str())),
        );
        eprintln!(
            "{n} generated scripts (seed {seed:#x}), {:.2?}\n{}",
            t.elapsed(),
            tally.report()
        );
        assert!(tally.passes(), "{}", tally.report());
        // The generator emits only scripts both sides should read, except
        // the marked reserved-word declarations (#315), which the reader
        // refuses: every script not compared is exactly one of those.
        let reserved = scripts
            .iter()
            .filter(|s| s.contains(RESERVED_DECL_MARK))
            .count();
        assert_eq!(tally.compared() + reserved, n, "{}", tally.report());
        assert_eq!(
            tally.ordeal_refuses + tally.both_refuse,
            reserved,
            "{}",
            tally.report()
        );
        assert!(reserved > 0 || n < 100, "no reserved-word script in {n}");
    }

    // rivet: verifies VER-087
    #[test]
    fn front_leg_agrees_on_generated_scripts() {
        generated_run(GEN_SEED, GEN_COUNT);
    }

    /// The 10^5 run, another seed: nightly only (nightly-exhaustive.yml).
    #[test]
    #[ignore = "10^5 scripts, minutes: nightly-exhaustive.yml"]
    fn front_leg_agrees_on_1e5_generated_scripts() {
        generated_run(0x0281_E0F1, 100_000);
    }

    /// The generator reaches every piece of syntax it is there for.
    // rivet: verifies VER-087
    #[test]
    fn generator_covers_the_desugared_syntax() {
        let all = gen_smtlib_text(GEN_SEED, 2_000).concat();
        for needle in [
            "(bvadd ",
            "(concat ",
            "(distinct ",
            "(=> ",
            "(= ",
            " Bool)",
            "declare-fun",
            "true",
            "false",
            "rotate_left",
            "rotate_right",
            "#x",
            "#b",
            "(_ bv",
            "|v ",
            "|v#",
            "(ite ",
            "; trailing",
            "zero_extend",
            "sign_extend",
            "(extract",
            // #311: string literals in set-info / set-option
            "(set-info :source \"a ) b\")",
            "(set-info :notes \"a;b\")",
            "\"say \"\"hi\"\" ( now\"",
            // #312: Bool distinct and Bool ite, as an assert's own head or
            // an operand of a Bool connective (a bitvector term cannot be)
            "(assert (ite ",
            "(not (ite ",
            "(distinct true",
            "(distinct false",
            "(distinct (not ",
            // #315
            RESERVED_DECL_MARK,
        ] {
            let needle = needle.replace("(extract", "(_ extract");
            assert!(all.contains(&needle), "generator never emits {needle:?}");
        }
        // A rotate amount >= 2^w at a non-power-of-two width (the RotlNoMod
        // control needs one): e.g. `rotate_left 9` on a 3-bit operand.
        let mut big = false;
        for s in gen_smtlib_text(GEN_SEED, 2_000) {
            if s.contains(RESERVED_DECL_MARK) {
                continue; // the reader refuses these on purpose (#315)
            }
            let r = smtlib::read_script(&s).expect("generated scripts read");
            big |= r.declared.iter().any(|d| d.1 == 3 || d.1 == 5);
        }
        assert!(big);
    }

    /// Each front-end negative control (design note §6) turns the leg red,
    /// and the same scripts agree again once it is disarmed.
    // rivet: verifies VER-087
    #[test]
    fn every_front_negative_control_turns_the_leg_red() {
        let scripts = gen_smtlib_text(GEN_SEED, 1_000);
        for m in [
            Mutation::SltAsUlt,
            Mutation::RotlNoMod,
            Mutation::ChainEqDropLast,
            Mutation::ImpliesLeftAssoc,
        ] {
            let armed = Armed::arm(m);
            let red: Vec<usize> = scripts
                .iter()
                .enumerate()
                .filter(|(_, s)| front_leg(s).class == FrontClass::Disagree)
                .map(|(i, _)| i)
                .collect();
            drop(armed);
            eprintln!(
                "control {m:?}: {} of {} scripts disagree",
                red.len(),
                scripts.len()
            );
            assert!(!red.is_empty(), "control {m:?} did not turn the leg red");
            for i in red {
                assert_eq!(
                    front_leg(&scripts[i]).class,
                    FrontClass::Agree,
                    "gen#{i} still disagrees with {m:?} disarmed"
                );
            }
        }
    }

    /// One fixture per outcome class, for the harness itself.
    // rivet: verifies VER-087
    #[test]
    fn harness_classifies_one_fixture_per_outcome_class() {
        let agree = "(declare-const x (_ BitVec 8))(declare-const |p q| Bool)\
                     (assert (=> |p q| (= x #x01) (bvslt x #x02)))(check-sat)";
        let r = front_leg(agree);
        assert_eq!((r.class, r.compared), (FrontClass::Agree, 1), "{r:?}");

        // disagree: the real reader with bvslt mistranslated; Z3's witness
        // is reported.
        let slt = "(declare-const x (_ BitVec 8))(assert (bvslt x #x00))(check-sat)";
        let r = {
            let _a = Armed::arm(Mutation::SltAsUlt);
            front_leg(slt)
        };
        assert_eq!(r.class, FrontClass::Disagree, "{r:?}");
        assert!(
            r.detail.contains("witness") && r.detail.contains('x'),
            "{r:?}"
        );
        // and a reading with the wrong number of assertions.
        let mut short = smtlib::read_script(agree).expect("reads");
        short.assertions.clear();
        let r = classify(z3_read(agree), Ok(short));
        assert_eq!(r.class, FrontClass::Disagree, "{r:?}");

        // #315: a reserved word declared as a quoted symbol. Z3 5.1.0
        // accepts `|let|`; ordeal refuses it (SMT-LIB 2.6 section 3.1). That
        // is incompleteness, listed and never a failure: the run passes.
        let reserved = "(declare-fun |let| () (_ BitVec 8))(assert (= |let| #x01))(check-sat)";
        let r = front_leg(reserved);
        assert_eq!(r.class, FrontClass::OrdealRefuses, "{r:?}");
        let mut t = FrontTally::default();
        t.record("reserved", &r);
        t.record("agree", &front_leg(agree));
        assert!(t.passes(), "{}", t.report());
        assert!(t.listed.iter().any(|l| l.contains("reserved")));
        assert!(t.failures.is_empty());

        // #313: a width above 128 is read as `unknown` with a placeholder
        // assertion, so it is listed as incompleteness, never compared (and
        // never a "disagree" on the placeholder).
        let wide = "(declare-const x (_ BitVec 8))\
                    (assert (= ((_ extract 7 0) (_ bv5 136)) x))(check-sat)";
        assert!(smtlib::read_script(wide).expect("reads").too_wide);
        let r = front_leg(wide);
        assert_eq!(r.class, FrontClass::OrdealRefuses, "{r:?}");
        assert!(r.detail.contains("width above 128"), "{r:?}");

        // ordeal refuses / Z3 accepts: an uninterpreted function.
        let uf = "(declare-fun f ((_ BitVec 8)) (_ BitVec 8))(declare-const x (_ BitVec 8))\
                  (assert (= (f x) x))(check-sat)";
        assert_eq!(front_leg(uf).class, FrontClass::OrdealRefuses);

        // Z3 refuses / ordeal accepts, not allow-listed: fails.
        let r = classify(
            Z3Reading::Refused("synthetic".into()),
            smtlib::read_script(agree),
        );
        assert_eq!(r.class, FrontClass::Z3Refuses, "{r:?}");
        let mut t = FrontTally::default();
        t.record("synthetic", &r);
        t.record("agree", &front_leg(agree));
        assert!(!t.passes(), "a Z3 refusal must fail the run");

        // Z3 refuses / ordeal accepts, allow-listed (#139): `x` and `|x|`
        // declared twice at the same sort.
        let redecl = "(declare-const x (_ BitVec 8))(declare-const |x| (_ BitVec 8))\
                      (assert (= x #x01))(check-sat)";
        let r = front_leg(redecl);
        assert_eq!(r.class, FrontClass::Z3RefusesAllowed, "{r:?}");
        assert_eq!(r.detail, "identical-redeclaration-139");

        // both refuse.
        assert_eq!(front_leg("(assert (= x").class, FrontClass::BothRefuse);

        // No vacuous pass: a run that compared nothing fails.
        let mut empty = FrontTally::default();
        empty.record("uf", &front_leg(uf));
        assert!(!empty.passes());
    }
}
