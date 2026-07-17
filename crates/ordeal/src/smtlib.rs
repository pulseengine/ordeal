//! A minimal **QF_BV** SMT-LIB2 front end (FEAT-006 / loom field-report #34).
//!
//! The production interface to `ordeal` is the Rust API (`Solver` / `BvTerm` /
//! `BoolTerm`): loom and synth embed the crate in-process. This module adds a
//! small textual reader on top of that API so the solver can be driven
//! standalone — for ad-hoc queries, regression corpora, and a differential
//! harness against Z3 — without a parser-crate dependency (the default build
//! stays dependency-free and `wasm32-wasip2`-clean; this module is pure `std`
//! and does no I/O — the CLI in `main.rs` owns stdin/files/exit codes).
//!
//! # Supported subset
//!
//! This is a **QF_BV-only** reader. Anything outside the subset is reported as
//! [`SmtError::Unsupported`] rather than silently mis-handled — the solver is
//! certificate-checked and must never guess at a construct it did not model.
//!
//! - **Commands:** `set-logic` (accepted/ignored), `declare-const` /
//!   `declare-fun name () (_ BitVec N)`, `assert`, `check-sat`, `get-model`,
//!   `get-value` (accepted, prints the model), `exit`; `set-info` /
//!   `set-option` are ignored.
//! - **Literals:** `(_ bvN W)`, `#xHEX`, `#bBIN` → [`BvTerm::Const`]; a
//!   declared name → [`BvTerm::Var`].
//! - **Bitvector ops:** `bvadd bvsub bvmul bvand bvor bvxor` (n-ary,
//!   left-folded) and `concat` (n-ary); `bvudiv bvshl bvlshr bvashr` (binary);
//!   `bvnot bvneg` (unary) and `bvurem bvsdiv bvsrem` (binary) via
//!   [`crate::lowering`]; `((_ extract hi lo) x)`, `((_ zero_extend k) x)`,
//!   `((_ sign_extend k) x)`, `((_ rotate_left k) x)`,
//!   `((_ rotate_right k) x)`, and `(ite c a b)` → [`BvTerm::Ite`].
//! - **Predicates:** `= distinct bvult bvule bvugt bvuge bvslt bvsle bvsgt
//!   bvsge` and the boolean connectives `not and or` (n-ary `and`/`or`).
//!
//! # The rotate-amount mismatch
//!
//! SMT-LIB's `rotate_left` / `rotate_right` take a **constant** rotate amount
//! `k` baked into the operator symbol, but the closed core only has
//! [`BvTerm::Rotr`], which rotates by a **term** amount. We bridge this by
//! materializing `k` as a same-width [`BvTerm::Const`]:
//! `((_ rotate_right k) x)` becomes `Rotr(x, Const{k, width(x)})`, and
//! `((_ rotate_left k) x)` goes through [`crate::lowering::bvrotl`] (which is
//! `Rotr(x, 0 - k)` — exact for the power-of-two target widths 8/32/64). No new
//! operator enters the closed fragment.

use crate::eval::bv_sort;
use crate::lowering;
use crate::{BoolTerm, BvTerm, CheckResult, Solver, Sort};
use std::collections::{HashMap, HashSet};

/// Why reading or solving an SMT-LIB2 script failed.
///
/// The CLI maps every variant to a non-zero exit; the solver never proceeds on
/// a construct it could not faithfully translate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SmtError {
    /// The s-expression syntax was malformed (unbalanced parens, empty
    /// command, unknown symbol, bad literal, …).
    Parse(String),
    /// A well-formed construct outside the supported QF_BV subset.
    Unsupported(String),
    /// A construct the reader accepted but the solver rejected as ill-formed
    /// (e.g. an operand-width mismatch surfaced while sizing a term).
    Solver(String),
}

impl std::fmt::Display for SmtError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SmtError::Parse(m) => write!(f, "parse error: {m}"),
            SmtError::Unsupported(m) => write!(f, "unsupported: {m}"),
            SmtError::Solver(m) => write!(f, "solver error: {m}"),
        }
    }
}

impl std::error::Error for SmtError {}

/// The result of reading and solving a script.
#[derive(Clone, Debug)]
pub struct Outcome {
    /// The verdict of the (last) `check-sat`, or `None` if the script had none.
    pub result: Option<CheckResult>,
    /// Declared bitvector variables, in declaration order (name, width). Used
    /// to print a full model on `sat`.
    pub declared: Vec<(String, u32)>,
}

// ─── S-expression front end ──────────────────────────────────────────────────

/// A parsed s-expression: either an atom (symbol/literal) or a nested list.
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

/// Borrow an atom's text, if `s` is an atom.
fn as_atom(s: &Sexp) -> Option<&str> {
    match s {
        Sexp::Atom(a) => Some(a.as_str()),
        Sexp::List(_) => None,
    }
}

/// Split raw source into s-expression tokens: `(`, `)`, `|quoted|` symbols, and
/// bare atoms. Whitespace separates; `;` starts a line comment.
fn tokenize(src: &str) -> Vec<String> {
    let mut toks = Vec::new();
    let mut chars = src.chars().peekable();
    while let Some(&c) = chars.peek() {
        match c {
            c if c.is_whitespace() => {
                chars.next();
            }
            ';' => {
                // Line comment: consume through the newline.
                for c in chars.by_ref() {
                    if c == '\n' {
                        break;
                    }
                }
            }
            '(' | ')' => {
                chars.next();
                toks.push(c.to_string());
            }
            '|' => {
                // A `|...|` quoted symbol keeps its bars so it stays a single
                // atom even if it contains spaces.
                chars.next();
                let mut s = String::from("|");
                for c in chars.by_ref() {
                    s.push(c);
                    if c == '|' {
                        break;
                    }
                }
                toks.push(s);
            }
            _ => {
                // A bare atom runs until whitespace, a paren, or a comment.
                let mut s = String::new();
                while let Some(&c) = chars.peek() {
                    if c.is_whitespace() || c == '(' || c == ')' || c == ';' {
                        break;
                    }
                    s.push(c);
                    chars.next();
                }
                toks.push(s);
            }
        }
    }
    toks
}

/// Parse a whole token stream into the sequence of top-level s-expressions
/// (one per command).
fn parse_sexps(toks: &[String]) -> Result<Vec<Sexp>, SmtError> {
    let mut pos = 0;
    let mut out = Vec::new();
    while pos < toks.len() {
        let (s, next) = parse_one(toks, pos)?;
        out.push(s);
        pos = next;
    }
    Ok(out)
}

/// Parse a single s-expression starting at `pos`, returning it and the index
/// just past it.
fn parse_one(toks: &[String], pos: usize) -> Result<(Sexp, usize), SmtError> {
    let tok = toks
        .get(pos)
        .ok_or_else(|| SmtError::Parse("unexpected end of input".into()))?;
    match tok.as_str() {
        "(" => {
            let mut items = Vec::new();
            let mut p = pos + 1;
            loop {
                match toks.get(p) {
                    None => return Err(SmtError::Parse("unclosed '('".into())),
                    Some(t) if t == ")" => return Ok((Sexp::List(items), p + 1)),
                    Some(_) => {
                        let (s, next) = parse_one(toks, p)?;
                        items.push(s);
                        p = next;
                    }
                }
            }
        }
        ")" => Err(SmtError::Parse("unexpected ')'".into())),
        _ => Ok((Sexp::Atom(tok.clone()), pos + 1)),
    }
}

// ─── Interpretation ──────────────────────────────────────────────────────────

/// Reader state: the declared variables (name → bit width) accumulated so far.
struct Ctx {
    decls: HashMap<String, u32>,
    /// Names declared with the `Bool` sort (TR-029).
    ///
    /// The core has no boolean variable — [`BoolTerm`] is built from
    /// comparisons, so there is nothing to bind a free `Bool` to. A `Bool`
    /// declaration therefore becomes a **BV1 variable**, and a use of that
    /// name in boolean position becomes `name = #b1`. This mirrors how the
    /// reader already encodes the `true`/`false` literals (as trivial
    /// equalities) and keeps the fragment closed: no new operation, no
    /// `term.rs` change.
    ///
    /// Verus emits exactly this shape for every `by (bit_vector)` obligation
    /// — `(declare-const %%location_label%%0 Bool)` guarding the goal.
    bool_decls: HashSet<String>,
}

impl Ctx {
    /// Compute a term's bit width via the crate's sort-checker, mapping a
    /// sort error to [`SmtError::Solver`]. Used where a rule needs the width
    /// (the rotate-amount constant, the lowering helpers).
    fn width_of(t: &BvTerm) -> Result<u32, SmtError> {
        bv_sort(t)
            .map(|s| s.width)
            .map_err(|e| SmtError::Solver(format!("ill-sorted subterm: {e:?}")))
    }

    /// Whether an s-expression is boolean-shaped, so `=` can tell `iff` from
    /// bitvector equality. Structural on purpose: the core has no boolean
    /// sort to consult, and a `Bool`-declared name is the only atom that can
    /// be a boolean leaf.
    fn is_bool_sexp(&self, s: &Sexp) -> bool {
        match s {
            Sexp::Atom(a) => a == "true" || a == "false" || self.bool_decls.contains(a.as_str()),
            Sexp::List(items) => matches!(
                items.first().and_then(as_atom),
                Some(
                    "and"
                        | "or"
                        | "not"
                        | "=>"
                        | "="
                        | "distinct"
                        | "bvult"
                        | "bvule"
                        | "bvugt"
                        | "bvuge"
                        | "bvslt"
                        | "bvsle"
                        | "bvsgt"
                        | "bvsge"
                )
            ),
        }
    }

    /// Parse a bitvector-sorted term.
    fn parse_bv(&self, s: &Sexp) -> Result<BvTerm, SmtError> {
        match s {
            Sexp::Atom(a) => self.parse_bv_atom(a),
            Sexp::List(items) => {
                let head = items
                    .first()
                    .ok_or_else(|| SmtError::Parse("empty term list".into()))?;
                match head {
                    // `(_ bvN W)` indexed constant.
                    Sexp::Atom(a) if a == "_" => parse_indexed_const(items),
                    // `((_ op ...) args...)` indexed operator application.
                    Sexp::List(_) => self.parse_indexed_app(items),
                    // `(op args...)` ordinary operator.
                    Sexp::Atom(op) => self.parse_bv_op(op, &items[1..]),
                }
            }
        }
    }

    /// Parse an atomic bitvector term: a `#x`/`#b` literal or a declared name.
    fn parse_bv_atom(&self, a: &str) -> Result<BvTerm, SmtError> {
        if let Some(hex) = a.strip_prefix("#x") {
            if hex.is_empty() || !hex.chars().all(|c| c.is_ascii_hexdigit()) {
                return Err(SmtError::Parse(format!("bad hex literal '{a}'")));
            }
            let width = (hex.len() as u32) * 4;
            let value = u128::from_str_radix(hex, 16)
                .map_err(|_| SmtError::Parse(format!("hex literal too wide: '{a}'")))?;
            return Ok(const_bv(value, width));
        }
        if let Some(bin) = a.strip_prefix("#b") {
            if bin.is_empty() || !bin.chars().all(|c| c == '0' || c == '1') {
                return Err(SmtError::Parse(format!("bad binary literal '{a}'")));
            }
            let width = bin.len() as u32;
            let value = u128::from_str_radix(bin, 2)
                .map_err(|_| SmtError::Parse(format!("binary literal too wide: '{a}'")))?;
            return Ok(const_bv(value, width));
        }
        match self.decls.get(a) {
            Some(&width) => Ok(BvTerm::Var {
                name: a.to_string(),
                sort: Sort::new(width),
            }),
            None => Err(SmtError::Parse(format!("unknown symbol '{a}'"))),
        }
    }

    /// Parse an ordinary (non-indexed) bitvector operator application.
    fn parse_bv_op(&self, op: &str, args: &[Sexp]) -> Result<BvTerm, SmtError> {
        match op {
            // n-ary, left-associative core ops.
            "bvadd" => self.fold_bv(op, args, |a, b| BvTerm::Add(Box::new(a), Box::new(b))),
            "bvsub" => self.fold_bv(op, args, |a, b| BvTerm::Sub(Box::new(a), Box::new(b))),
            "bvmul" => self.fold_bv(op, args, |a, b| BvTerm::Mul(Box::new(a), Box::new(b))),
            "bvand" => self.fold_bv(op, args, |a, b| BvTerm::And(Box::new(a), Box::new(b))),
            "bvor" => self.fold_bv(op, args, |a, b| BvTerm::Or(Box::new(a), Box::new(b))),
            "bvxor" => self.fold_bv(op, args, |a, b| BvTerm::Xor(Box::new(a), Box::new(b))),
            "concat" => self.fold_bv(op, args, |a, b| BvTerm::Concat(Box::new(a), Box::new(b))),

            // Binary core ops.
            "bvudiv" => {
                let (a, b) = self.two_bv(op, args)?;
                Ok(BvTerm::Udiv(Box::new(a), Box::new(b)))
            }
            "bvshl" => {
                let (a, b) = self.two_bv(op, args)?;
                Ok(BvTerm::Shl(Box::new(a), Box::new(b)))
            }
            "bvlshr" => {
                let (a, b) = self.two_bv(op, args)?;
                Ok(BvTerm::Lshr(Box::new(a), Box::new(b)))
            }
            "bvashr" => {
                let (a, b) = self.two_bv(op, args)?;
                Ok(BvTerm::Ashr(Box::new(a), Box::new(b)))
            }

            // Derived ops, lowered onto the closed core (crate::lowering).
            "bvnot" => {
                let x = self.one_bv(op, args)?;
                let w = Self::width_of(&x)?;
                Ok(lowering::bvnot(x, w))
            }
            "bvneg" => {
                let x = self.one_bv(op, args)?;
                let w = Self::width_of(&x)?;
                Ok(lowering::bvneg(x, w))
            }
            "bvurem" => {
                let (a, b) = self.two_bv(op, args)?;
                let w = Self::width_of(&a)?;
                Ok(lowering::bvurem(a, b, w))
            }
            "bvsdiv" => {
                let (a, b) = self.two_bv(op, args)?;
                let w = Self::width_of(&a)?;
                Ok(lowering::bvsdiv(a, b, w))
            }
            "bvsrem" => {
                let (a, b) = self.two_bv(op, args)?;
                let w = Self::width_of(&a)?;
                Ok(lowering::bvsrem(a, b, w))
            }

            // The bool→BV bridge.
            "ite" => {
                if args.len() != 3 {
                    return Err(SmtError::Parse(format!(
                        "ite takes 3 args, got {}",
                        args.len()
                    )));
                }
                let cond = self.parse_bool(&args[0])?;
                let then_ = self.parse_bv(&args[1])?;
                let else_ = self.parse_bv(&args[2])?;
                Ok(BvTerm::Ite {
                    cond: Box::new(cond),
                    then_: Box::new(then_),
                    else_: Box::new(else_),
                })
            }

            other => Err(SmtError::Unsupported(format!(
                "bitvector operator '{other}'"
            ))),
        }
    }

    /// Parse an indexed operator application `((_ op ...) args...)`.
    fn parse_indexed_app(&self, items: &[Sexp]) -> Result<BvTerm, SmtError> {
        let Sexp::List(op) = &items[0] else {
            return Err(SmtError::Parse("expected indexed operator".into()));
        };
        // op = [_ , name, index, ...]
        if op.first().and_then(as_atom) != Some("_") {
            return Err(SmtError::Unsupported("non-'_' indexed operator".into()));
        }
        let name = op
            .get(1)
            .and_then(as_atom)
            .ok_or_else(|| SmtError::Parse("missing indexed operator name".into()))?;
        let idx = |n: usize| -> Result<u32, SmtError> {
            op.get(n)
                .and_then(as_atom)
                .and_then(|s| s.parse::<u32>().ok())
                .ok_or_else(|| SmtError::Parse(format!("bad index {n} on '{name}'")))
        };
        let arg = |this: &Self| -> Result<BvTerm, SmtError> {
            if items.len() != 2 {
                return Err(SmtError::Parse(format!("'{name}' takes 1 argument")));
            }
            this.parse_bv(&items[1])
        };
        match name {
            "extract" => {
                let (hi, lo) = (idx(2)?, idx(3)?);
                Ok(BvTerm::Extract {
                    hi,
                    lo,
                    arg: Box::new(arg(self)?),
                })
            }
            "zero_extend" => Ok(BvTerm::ZeroExt {
                by: idx(2)?,
                arg: Box::new(arg(self)?),
            }),
            "sign_extend" => Ok(BvTerm::SignExt {
                by: idx(2)?,
                arg: Box::new(arg(self)?),
            }),
            "rotate_right" => {
                // SMT-LIB's amount is a CONSTANT k; the core Rotr rotates by a
                // term, so materialize k as a same-width constant.
                let k = idx(2)?;
                let x = arg(self)?;
                let w = Self::width_of(&x)?;
                Ok(BvTerm::Rotr(Box::new(x), Box::new(const_bv(k as u128, w))))
            }
            "rotate_left" => {
                // rotate_left k == rotr by (-k); lowering::bvrotl builds exactly
                // that (exact for the power-of-two widths 8/32/64).
                let k = idx(2)?;
                let x = arg(self)?;
                let w = Self::width_of(&x)?;
                Ok(lowering::bvrotl(x, const_bv(k as u128, w), w))
            }
            other => Err(SmtError::Unsupported(format!("indexed operator '{other}'"))),
        }
    }

    /// Parse a boolean-sorted term (a predicate or a connective).
    fn parse_bool(&self, s: &Sexp) -> Result<BoolTerm, SmtError> {
        match s {
            Sexp::Atom(a) => match a.as_str() {
                // No boolean literal exists in the core; encode via a trivial
                // equality so `true`/`false` still round-trip.
                "true" => Ok(BoolTerm::Eq(
                    Box::new(const_bv(0, 1)),
                    Box::new(const_bv(0, 1)),
                )),
                "false" => Ok(BoolTerm::Eq(
                    Box::new(const_bv(0, 1)),
                    Box::new(const_bv(1, 1)),
                )),
                // A `Bool`-declared name reads as `name = #b1` (see
                // `Ctx::bool_decls`). Verus guards every by(bit_vector) goal
                // with `(declare-const %%location_label%%N Bool)`.
                name if self.bool_decls.contains(name) => Ok(BoolTerm::Eq(
                    Box::new(BvTerm::Var {
                        name: name.to_string(),
                        sort: Sort::new(1),
                    }),
                    Box::new(const_bv(1, 1)),
                )),
                other => Err(SmtError::Unsupported(format!("boolean atom '{other}'"))),
            },
            Sexp::List(items) => {
                let op = items
                    .first()
                    .and_then(as_atom)
                    .ok_or_else(|| SmtError::Parse("bad predicate".into()))?;
                let args = &items[1..];
                match op {
                    // SMT-LIB `=` is polymorphic. On bitvectors it is the
                    // core's Eq; on BOOLEANS it is `iff`, which is how Verus
                    // encodes `<==>` — and gale's mpu.rs power-of-two lemma is
                    // a biconditional, so this is not a corner case.
                    "=" if args.iter().all(|a| self.is_bool_sexp(a)) => {
                        if args.len() < 2 {
                            return Err(SmtError::Parse("'=' needs two arguments".into()));
                        }
                        let terms = args
                            .iter()
                            .map(|a| self.parse_bool(a))
                            .collect::<Result<Vec<_>, _>>()?;
                        // Chain, as SMT-LIB does: (= a b c) == (and (= a b) (= b c)).
                        let mut acc: Option<BoolTerm> = None;
                        for w in terms.windows(2) {
                            let e = iff(&w[0], &w[1]);
                            acc = Some(match acc {
                                None => e,
                                Some(p) => BoolTerm::And(Box::new(p), Box::new(e)),
                            });
                        }
                        Ok(acc.expect("len >= 2"))
                    }
                    "=" => self.chain_eq(args),
                    // SMT-LIB `=>` is n-ary and RIGHT-associative:
                    // (=> a b c) == (=> a (=> b c)). Expressed with the core's
                    // existing Not/Or — no new operation enters the fragment.
                    "=>" => {
                        if args.is_empty() {
                            return Err(SmtError::Parse("'=>' needs arguments".into()));
                        }
                        let mut terms = args
                            .iter()
                            .map(|a| self.parse_bool(a))
                            .collect::<Result<Vec<_>, _>>()?;
                        let mut acc = terms.pop().expect("non-empty");
                        while let Some(p) = terms.pop() {
                            acc = BoolTerm::Or(Box::new(BoolTerm::Not(Box::new(p))), Box::new(acc));
                        }
                        Ok(acc)
                    }
                    "distinct" => self.all_distinct(args),
                    "bvult" => self.cmp(args, BoolTerm::Ult),
                    "bvule" => self.cmp(args, BoolTerm::Ule),
                    "bvugt" => self.cmp(args, BoolTerm::Ugt),
                    "bvuge" => self.cmp(args, BoolTerm::Uge),
                    "bvslt" => self.cmp(args, BoolTerm::Slt),
                    "bvsle" => self.cmp(args, BoolTerm::Sle),
                    "bvsgt" => self.cmp(args, BoolTerm::Sgt),
                    "bvsge" => self.cmp(args, BoolTerm::Sge),
                    "not" => {
                        if args.len() != 1 {
                            return Err(SmtError::Parse("not takes 1 arg".into()));
                        }
                        Ok(BoolTerm::Not(Box::new(self.parse_bool(&args[0])?)))
                    }
                    "and" => {
                        self.fold_bool("and", args, |a, b| BoolTerm::And(Box::new(a), Box::new(b)))
                    }
                    "or" => {
                        self.fold_bool("or", args, |a, b| BoolTerm::Or(Box::new(a), Box::new(b)))
                    }
                    other => Err(SmtError::Unsupported(format!("predicate '{other}'"))),
                }
            }
        }
    }

    /// `(= a b c ...)` → conjunction of consecutive equalities.
    fn chain_eq(&self, args: &[Sexp]) -> Result<BoolTerm, SmtError> {
        let bvs = self.parse_bv_list(args)?;
        if bvs.len() < 2 {
            return Err(SmtError::Parse("'=' needs at least 2 arguments".into()));
        }
        let eq = |a: &BvTerm, b: &BvTerm| BoolTerm::Eq(Box::new(a.clone()), Box::new(b.clone()));
        let mut acc = eq(&bvs[0], &bvs[1]);
        for pair in bvs.windows(2).skip(1) {
            acc = BoolTerm::And(Box::new(acc), Box::new(eq(&pair[0], &pair[1])));
        }
        Ok(acc)
    }

    /// `(distinct a b c ...)` → conjunction of all pairwise disequalities.
    fn all_distinct(&self, args: &[Sexp]) -> Result<BoolTerm, SmtError> {
        let bvs = self.parse_bv_list(args)?;
        if bvs.len() < 2 {
            return Err(SmtError::Parse(
                "'distinct' needs at least 2 arguments".into(),
            ));
        }
        let mut acc: Option<BoolTerm> = None;
        for i in 0..bvs.len() {
            for j in (i + 1)..bvs.len() {
                let ne = BoolTerm::Ne(Box::new(bvs[i].clone()), Box::new(bvs[j].clone()));
                acc = Some(match acc {
                    None => ne,
                    Some(prev) => BoolTerm::And(Box::new(prev), Box::new(ne)),
                });
            }
        }
        Ok(acc.expect("len >= 2 guarantees at least one pair"))
    }

    /// A binary bitvector comparison predicate.
    fn cmp(
        &self,
        args: &[Sexp],
        f: impl Fn(Box<BvTerm>, Box<BvTerm>) -> BoolTerm,
    ) -> Result<BoolTerm, SmtError> {
        let (a, b) = self.two_bv("comparison", args)?;
        Ok(f(Box::new(a), Box::new(b)))
    }

    /// Parse every argument as a bitvector term.
    fn parse_bv_list(&self, args: &[Sexp]) -> Result<Vec<BvTerm>, SmtError> {
        args.iter().map(|a| self.parse_bv(a)).collect()
    }

    /// Fold `>=1` bitvector arguments left-associatively with `f`.
    fn fold_bv(
        &self,
        op: &str,
        args: &[Sexp],
        f: impl Fn(BvTerm, BvTerm) -> BvTerm,
    ) -> Result<BvTerm, SmtError> {
        let mut it = self.parse_bv_list(args)?.into_iter();
        let mut acc = it
            .next()
            .ok_or_else(|| SmtError::Parse(format!("'{op}' needs at least 1 argument")))?;
        for next in it {
            acc = f(acc, next);
        }
        Ok(acc)
    }

    /// Fold `>=1` boolean arguments left-associatively with `f`.
    fn fold_bool(
        &self,
        op: &str,
        args: &[Sexp],
        f: impl Fn(BoolTerm, BoolTerm) -> BoolTerm,
    ) -> Result<BoolTerm, SmtError> {
        let mut acc: Option<BoolTerm> = None;
        for a in args {
            let t = self.parse_bool(a)?;
            acc = Some(match acc {
                None => t,
                Some(prev) => f(prev, t),
            });
        }
        acc.ok_or_else(|| SmtError::Parse(format!("'{op}' needs at least 1 argument")))
    }

    /// Parse exactly one bitvector argument.
    fn one_bv(&self, op: &str, args: &[Sexp]) -> Result<BvTerm, SmtError> {
        if args.len() != 1 {
            return Err(SmtError::Parse(format!(
                "'{op}' takes 1 argument, got {}",
                args.len()
            )));
        }
        self.parse_bv(&args[0])
    }

    /// Parse exactly two bitvector arguments.
    fn two_bv(&self, op: &str, args: &[Sexp]) -> Result<(BvTerm, BvTerm), SmtError> {
        if args.len() != 2 {
            return Err(SmtError::Parse(format!(
                "'{op}' takes 2 arguments, got {}",
                args.len()
            )));
        }
        Ok((self.parse_bv(&args[0])?, self.parse_bv(&args[1])?))
    }
}

/// Build a `width`-bit constant.
fn const_bv(value: u128, width: u32) -> BvTerm {
    BvTerm::Const {
        value,
        sort: Sort::new(width),
    }
}

/// Parse a `(_ bvN W)` indexed constant.
fn parse_indexed_const(items: &[Sexp]) -> Result<BvTerm, SmtError> {
    // items = [_ , bvN, W]
    let name = items
        .get(1)
        .and_then(as_atom)
        .ok_or_else(|| SmtError::Parse("bad '(_ bvN W)' constant".into()))?;
    let digits = name
        .strip_prefix("bv")
        .ok_or_else(|| SmtError::Unsupported(format!("indexed identifier '(_ {name} ...)'")))?;
    let value = digits
        .parse::<u128>()
        .map_err(|_| SmtError::Parse(format!("bad bitvector constant '{name}'")))?;
    let width = items
        .get(2)
        .and_then(as_atom)
        .and_then(|s| s.parse::<u32>().ok())
        .ok_or_else(|| SmtError::Parse("missing width in '(_ bvN W)'".into()))?;
    Ok(const_bv(value, width))
}

/// Parse a `(_ BitVec N)` sort, returning its width.
fn parse_sort(s: &Sexp) -> Result<u32, SmtError> {
    if let Sexp::List(items) = s
        && items.len() == 3
        && as_atom(&items[0]) == Some("_")
        && as_atom(&items[1]) == Some("BitVec")
    {
        return as_atom(&items[2])
            .and_then(|w| w.parse::<u32>().ok())
            .ok_or_else(|| SmtError::Parse("bad BitVec width".into()));
    }
    // `Bool` is admitted as a 1-bit variable (see `Ctx::bool_decls`): the core
    // has no boolean variable, so a `Bool` declaration becomes a BV1 whose
    // boolean reading is `name = #b1`. Verus guards every `by (bit_vector)`
    // goal with one, so refusing it would reject the real VCs outright.
    if as_atom(s) == Some("Bool") {
        return Ok(1);
    }
    Err(SmtError::Unsupported("non-BitVec sort".into()))
}

/// Read an SMT-LIB2 QF_BV script, execute its commands, and return the
/// [`Outcome`] (the `check-sat` verdict plus the declared variables).
///
/// This performs no I/O: it takes the whole script as a string and is safe to
/// call on any target (the CLI wraps it with stdin/file reading and exit
/// codes). Any construct outside the supported subset yields an [`SmtError`].
pub fn solve_str(input: &str) -> Result<Outcome, SmtError> {
    let toks = tokenize(input);
    let sexps = parse_sexps(&toks)?;

    let mut ctx = Ctx {
        decls: HashMap::new(),
        bool_decls: HashSet::new(),
    };
    let mut declared: Vec<(String, u32)> = Vec::new();
    let mut solver = Solver::new();
    let mut result: Option<CheckResult> = None;

    for s in &sexps {
        let items = match s {
            Sexp::List(items) if !items.is_empty() => items,
            _ => return Err(SmtError::Parse("expected a command list".into())),
        };
        let cmd = as_atom(&items[0]).ok_or_else(|| SmtError::Parse("bad command head".into()))?;
        match cmd {
            // Accepted / ignored preamble.
            "set-logic" | "set-info" | "set-option" => {}

            "declare-const" => {
                // (declare-const name (_ BitVec N))  |  (declare-const name Bool)
                let name = decl_name(items, 1)?;
                let sort = item(items, 2, "declare-const")?;
                let width = parse_sort(sort)?;
                if as_atom(sort) == Some("Bool") {
                    ctx.bool_decls.insert(name.clone());
                }
                ctx.decls.insert(name.clone(), width);
                declared.push((name, width));
            }
            "declare-fun" => {
                // (declare-fun name () (_ BitVec N)) — only nullary funcs.
                let name = decl_name(items, 1)?;
                match item(items, 2, "declare-fun")? {
                    Sexp::List(p) if p.is_empty() => {}
                    _ => {
                        return Err(SmtError::Unsupported(
                            "declare-fun with parameters (uninterpreted function)".into(),
                        ));
                    }
                }
                let width = parse_sort(item(items, 3, "declare-fun")?)?;
                ctx.decls.insert(name.clone(), width);
                declared.push((name, width));
            }
            "assert" => {
                let term = ctx.parse_bool(item(items, 1, "assert")?)?;
                solver.assert(term);
            }
            "check-sat" => {
                result = Some(solver.check());
            }
            // Model queries: accepted; the CLI prints the model on `sat`.
            "get-model" | "get-value" => {}
            "exit" => break,

            // Everything else is out of scope — never silently ignored.
            "push" | "pop" | "reset" | "reset-assertions" | "get-assertions" | "get-unsat-core"
            | "get-proof" => {
                return Err(SmtError::Unsupported(format!("command '{cmd}'")));
            }
            other => return Err(SmtError::Unsupported(format!("command '{other}'"))),
        }
    }

    Ok(Outcome { result, declared })
}

/// Fetch command argument `n`, or a parse error naming the command.
fn item<'a>(items: &'a [Sexp], n: usize, cmd: &str) -> Result<&'a Sexp, SmtError> {
    items
        .get(n)
        .ok_or_else(|| SmtError::Parse(format!("'{cmd}' is missing an argument")))
}

/// Read a declaration's name atom.
fn decl_name(items: &[Sexp], n: usize) -> Result<String, SmtError> {
    as_atom(item(items, n, "declaration")?)
        .map(str::to_string)
        .ok_or_else(|| SmtError::Parse("declaration name must be a symbol".into()))
}

/// `a <-> b`, expressed with the core's Not/Or/And — no new operation.
/// Mirrors `trap::iff`; SMT-LIB spells it `=` over Bool, Verus spells it `<==>`.
fn iff(a: &BoolTerm, b: &BoolTerm) -> BoolTerm {
    BoolTerm::And(
        Box::new(BoolTerm::Or(
            Box::new(BoolTerm::Not(Box::new(a.clone()))),
            Box::new(b.clone()),
        )),
        Box::new(BoolTerm::Or(
            Box::new(BoolTerm::Not(Box::new(b.clone()))),
            Box::new(a.clone()),
        )),
    )
}

#[cfg(test)]
mod tests {
    // ── TR-029: the Verus VC dialect (issue #65) ─────────────────────────
    //
    // Verus emits `(declare-const %%location_label%%N Bool)` + `(=> label goal)`
    // around EVERY `by (bit_vector)` obligation. Without both, its VCs are
    // rejected outright — which is the whole gap between "gale hand-transcribes
    // 64 obligations" and "the obligation Verus actually checked is discharged
    // with a re-checkable certificate".

    #[test]
    fn bool_declared_const_reads_as_bv1_equality() {
        // The core has no boolean variable, so a Bool decl becomes BV1 and its
        // boolean use is `name = #b1`. Satisfiable: pick label = 1.
        let src = "(set-logic QF_BV)(declare-const p Bool)(assert p)(check-sat)";
        match solve_str(src).unwrap().result.unwrap() {
            CheckResult::Sat(_) => {}
            other => panic!("a free Bool must be satisfiable, got {other:?}"),
        }
    }

    #[test]
    fn bool_const_is_falsifiable_too() {
        // Not vacuous: `p AND NOT p` must be UNSAT.
        let src = "(set-logic QF_BV)(declare-const p Bool)(assert p)(assert (not p))(check-sat)";
        match solve_str(src).unwrap().result.unwrap() {
            CheckResult::Unsat(_) => {}
            other => panic!("p AND NOT p must be UNSAT, got {other:?}"),
        }
    }

    #[test]
    fn implication_is_right_associative() {
        // (=> a b c) == (=> a (=> b c)). With a=1, b=1, c=0 the formula is
        // false, so asserting it alongside those values must be UNSAT.
        let src = "(set-logic QF_BV)\
                   (declare-const a Bool)(declare-const b Bool)(declare-const c Bool)\
                   (assert a)(assert b)(assert (not c))(assert (=> a b c))(check-sat)";
        match solve_str(src).unwrap().result.unwrap() {
            CheckResult::Unsat(_) => {}
            other => panic!("(=> a b c) with a,b true and c false must be UNSAT, got {other:?}"),
        }
        // And it is satisfiable when the chain is respected.
        let ok = "(set-logic QF_BV)\
                  (declare-const a Bool)(declare-const b Bool)(declare-const c Bool)\
                  (assert (=> a b c))(check-sat)";
        match solve_str(ok).unwrap().result.unwrap() {
            CheckResult::Sat(_) => {}
            other => panic!("(=> a b c) alone must be satisfiable, got {other:?}"),
        }
    }

    /// THE #65 test: a REAL Verus VC, emitted by verus 0.2026.02.15.61aa1bf
    /// (sha256-identical to the toolchain rules_verus pins, i.e. the exact
    /// binary gale verifies with) for gale's `cpu_mask.rs:179` obligation.
    ///
    /// This is not a hand-written approximation of the dialect — it is the
    /// bit-blast sub-query Verus itself sent to Z3, and it must discharge to a
    /// checker-validated UNSAT. gale's hand-transcription of the same lemma
    /// (`proofs/ordeal-bv/cpu_mask_pot.smt2`) also returns unsat, which is the
    /// cross-check that the automated path agrees with the human one.
    #[test]
    fn real_verus_by_bit_vector_vc_discharges() {
        let src = include_str!("../tests/fixtures/verus_gale_cpu_mask_slice.smt2");
        match solve_str(src).unwrap().result.unwrap() {
            CheckResult::Unsat(cert) => {
                cert.recheck()
                    .expect("Verus's own VC must yield a re-checkable certificate");
            }
            other => panic!("Verus's cpu_mask by(bit_vector) VC must be UNSAT, got {other:?}"),
        }
    }

    use super::*;
    use crate::Model;

    /// Solve a script and return its verdict, panicking on any reader error.
    fn verdict(src: &str) -> CheckResult {
        solve_str(src)
            .unwrap_or_else(|e| panic!("reader error: {e}"))
            .result
            .expect("script had a (check-sat)")
    }

    /// Look a variable's model value up by name.
    fn model_of(m: &Model, name: &str) -> Option<u128> {
        m.assignments
            .iter()
            .find(|(k, _)| k == name)
            .map(|(_, v)| *v)
    }

    #[test]
    fn add_zero_identity_negation_is_unsat() {
        // x + 0 == x always holds, so its negation is UNSAT.
        let src = "
            (set-logic QF_BV)
            (declare-const x (_ BitVec 8))
            (assert (not (= (bvadd x #x00) x)))
            (check-sat)";
        assert!(matches!(verdict(src), CheckResult::Unsat(_)));
    }

    #[test]
    fn equality_to_constant_is_sat_with_model() {
        let src = "
            (declare-const x (_ BitVec 32))
            (assert (= x #x0000002a))
            (check-sat)
            (get-model)";
        let out = solve_str(src).unwrap();
        assert_eq!(out.declared, vec![("x".to_string(), 32)]);
        match out.result {
            Some(CheckResult::Sat(m)) => assert_eq!(model_of(&m, "x"), Some(0x2a)),
            other => panic!("expected sat with x=0x2a, got {other:?}"),
        }
    }

    #[test]
    fn udiv_by_zero_equivalence_is_unsat() {
        // bvudiv by zero is all-ones for every x, so `x udiv 0 == 0xff` is
        // valid and its negation UNSAT.
        let src = "
            (declare-const x (_ BitVec 8))
            (assert (not (= (bvudiv x #x00) #xff)))
            (check-sat)";
        assert!(matches!(verdict(src), CheckResult::Unsat(_)));
    }

    #[test]
    fn signed_and_unsigned_compare_disagree() {
        // 0x80 is unsigned 128 (> 0x7f) but signed -128 (< 0x7f): a witness
        // that bvult and bvslt disagree.
        let src = "
            (declare-const x (_ BitVec 8))
            (assert (bvult #x7f x))
            (assert (bvslt x #x7f))
            (check-sat)
            (get-value (x))";
        match verdict(src) {
            CheckResult::Sat(m) => assert_eq!(model_of(&m, "x"), Some(0x80)),
            other => panic!("expected sat with x=0x80, got {other:?}"),
        }
    }

    #[test]
    fn ite_selects_branch() {
        // (ite (x < 10) 1 0) == 1  is satisfiable exactly when x < 10.
        let src = "
            (declare-const x (_ BitVec 8))
            (assert (= (ite (bvult x #x0a) #x01 #x00) #x01))
            (check-sat)";
        match verdict(src) {
            CheckResult::Sat(m) => assert!(model_of(&m, "x").unwrap() < 0x0a),
            other => panic!("expected sat, got {other:?}"),
        }
    }

    #[test]
    fn bvsdiv_signed_division() {
        // -2 / 2 == -1  (0xfe sdiv 0x02 == 0xff over 8 bits).
        let src = "
            (declare-const x (_ BitVec 8))
            (assert (= x #xfe))
            (assert (= (bvsdiv x #x02) #xff))
            (check-sat)";
        match verdict(src) {
            CheckResult::Sat(m) => assert_eq!(model_of(&m, "x"), Some(0xfe)),
            other => panic!("expected sat, got {other:?}"),
        }
    }

    #[test]
    fn rotate_left_constant_amount() {
        // rotate_left 1 of 0b1000_0001 (0x81) == 0b0000_0011 (0x03).
        let src = "
            (declare-const x (_ BitVec 8))
            (assert (= ((_ rotate_left 1) #x81) x))
            (check-sat)
            (get-model)";
        match verdict(src) {
            CheckResult::Sat(m) => assert_eq!(model_of(&m, "x"), Some(0x03)),
            other => panic!("expected sat with x=0x03, got {other:?}"),
        }
    }

    #[test]
    fn rotate_right_constant_amount() {
        // rotate_right 1 of 0x81 (1000_0001) == 1100_0000 (0xc0).
        let src = "
            (declare-const x (_ BitVec 8))
            (assert (= ((_ rotate_right 1) #x81) x))
            (check-sat)";
        match verdict(src) {
            CheckResult::Sat(m) => assert_eq!(model_of(&m, "x"), Some(0xc0)),
            other => panic!("expected sat with x=0xc0, got {other:?}"),
        }
    }

    #[test]
    fn zero_extend_and_concat() {
        // zero_extend 8 of 0xff (8-bit) == 0x00ff (16-bit).
        let src = "
            (declare-const x (_ BitVec 8))
            (assert (= x #xff))
            (assert (= ((_ zero_extend 8) x) #x00ff))
            (check-sat)";
        assert!(matches!(verdict(src), CheckResult::Sat(_)));
    }

    #[test]
    fn declare_fun_nullary_is_accepted() {
        let src = "
            (declare-fun y () (_ BitVec 16))
            (assert (= y #x00ff))
            (check-sat)
            (get-model)";
        match verdict(src) {
            CheckResult::Sat(m) => assert_eq!(model_of(&m, "y"), Some(0xff)),
            other => panic!("expected sat, got {other:?}"),
        }
    }

    #[test]
    fn unsupported_operator_is_rejected() {
        let src = "
            (declare-const x (_ BitVec 8))
            (assert (= (bvfoo x x) #x00))
            (check-sat)";
        assert!(matches!(solve_str(src), Err(SmtError::Unsupported(_))));
    }

    #[test]
    fn unsupported_command_is_rejected() {
        let src = "(push 1)(check-sat)";
        assert!(matches!(solve_str(src), Err(SmtError::Unsupported(_))));
    }

    #[test]
    fn parse_error_on_unbalanced_parens() {
        let src = "(declare-const x (_ BitVec 8)) (assert (= x #x00)";
        assert!(matches!(solve_str(src), Err(SmtError::Parse(_))));
    }

    #[test]
    fn unknown_symbol_is_a_parse_error() {
        // `y` is never declared.
        let src = "
            (declare-const x (_ BitVec 8))
            (assert (= x y))
            (check-sat)";
        assert!(matches!(solve_str(src), Err(SmtError::Parse(_))));
    }
}
