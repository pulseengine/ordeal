//! The performance and proof-size regression gate (#283, TR-081): shared
//! harness for `tests/perf_gate.rs` (fast self-tests, default run) and
//! `tests/perf_gate_corpus.rs` (the real-corpus run, release build, its own
//! CI job).
//!
//! The corpus lives in `tests/perf_corpus/`: `manifest.json` names every
//! query with its provenance and expected verdict, `budgets.json` publishes
//! the budgets the gate holds each query to. The two must name the same
//! set of queries, in both directions, and a run over zero queries fails.
//!
//! Proof size is deterministic, so it is pinned: the CNF clause count and
//! the LRAT byte and line counts must EQUAL the published budget. Larger is
//! a regression; smaller is an improvement whose budget must be lowered, so
//! the slack cannot later hide a regression. Wall-clock time is noisy on
//! shared runners, so it gets headroom ([`TIME_FACTOR`], [`TIME_FLOOR_MS`]).
//!
//! Every verdict is certificate-checked twice: the solver returns `Unsat`
//! only after the trusted crate validated it, and the gate re-runs the
//! trusted checker on the returned certificate (`Certificate::recheck`). A
//! `Sat` is re-confirmed by a witness the trusted crate re-checks
//! (`SatCertificate::recheck`). `Unknown` always fails.
//!
//! Test-only knobs (environment, read here and nowhere in the solver):
//! - `ORDEAL_PERF_GATE_BUDGETS=PATH`: read budgets from PATH instead.
//! - `ORDEAL_PERF_GATE_ONLY=ID[,ID..]`: run only these queries (planted
//!   controls; the set agreement is still checked over the whole corpus).
//! - `ORDEAL_PERF_GATE_SLOWDOWN=N`: solve each query N times inside its
//!   timed region (an injected N-fold slowdown).
//! - `ORDEAL_PERF_GATE_INFLATE_LRAT=N`: add N bytes to each measured LRAT
//!   size (an injected proof-size regression).
//! - `ORDEAL_PERF_GATE_SUGGEST=1`: also print a budgets.json computed from
//!   this run under the published policy.

#![allow(dead_code)] // each test target uses a different part

use ordeal::{BoolTerm, BvTerm, CheckResult, Solver, Sort, WitnessCheckResult};
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};
use std::time::Instant;

/// Time budget = max(measured x TIME_FACTOR, measured + TIME_FLOOR_MS),
/// rounded up to 100 ms, from a release-build measurement.
pub const TIME_FACTOR: u64 = 5;
/// See [`TIME_FACTOR`].
pub const TIME_FLOOR_MS: u64 = 500;
/// A query faster than this is re-run and timed by its fastest run.
const RERUN_BELOW_MS: f64 = 2000.0;
const RERUNS: usize = 3;

pub fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/perf_corpus")
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Unsat,
    Sat,
    Unknown,
}

impl Verdict {
    fn parse(s: &str) -> Result<Self, String> {
        match s {
            "unsat" => Ok(Verdict::Unsat),
            "sat" => Ok(Verdict::Sat),
            other => Err(format!(
                "expected verdict must be sat or unsat, got {other:?}"
            )),
        }
    }
    pub fn as_str(self) -> &'static str {
        match self {
            Verdict::Unsat => "unsat",
            Verdict::Sat => "sat",
            Verdict::Unknown => "unknown",
        }
    }
}

#[derive(Clone, Debug)]
pub enum Driver {
    /// The `ordeal check` path: `smtlib::solve_str_with_witness`.
    Smtlib,
    /// The `ordeal verus` path: `verus::extract`, then `smtlib::solve_str`.
    Verus,
    /// The in-process API path loom and synth use: the file's nullary
    /// `define-fun` DAG is expanded to the consumer's term tree, asserted,
    /// and `Solver::check` decides it.
    ApiDag,
    /// A generator from `ordeal::bmc_corpus` (synthetic spar stand-in).
    Bmc {
        generator: String,
        k: usize,
        arg: u64,
    },
}

#[derive(Clone, Debug)]
pub struct Entry {
    pub id: String,
    pub consumer: String,
    pub real: bool,
    pub file: Option<PathBuf>,
    pub sha256: Option<String>,
    pub driver: Driver,
    pub expect: Verdict,
}

#[derive(Clone, Debug)]
pub struct Manifest {
    pub entries: Vec<Entry>,
    pub uncovered: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Budget {
    pub time_ms: u64,
    pub cnf_clauses: u64,
    pub lrat_bytes: Option<u64>,
    pub lrat_lines: Option<u64>,
}

#[derive(Clone, Debug)]
pub struct Measurement {
    pub verdict: Verdict,
    pub time_ms: f64,
    pub cnf_clauses: u64,
    pub lrat_bytes: Option<u64>,
    pub lrat_lines: Option<u64>,
}

fn str_field<'a>(v: &'a Value, k: &str, ctx: &str) -> Result<&'a str, String> {
    v.get(k)
        .and_then(Value::as_str)
        .filter(|s| !s.trim().is_empty())
        .ok_or_else(|| format!("{ctx}: missing or empty string field {k:?}"))
}

fn u64_field(v: &Value, k: &str, ctx: &str) -> Result<u64, String> {
    v.get(k)
        .and_then(Value::as_u64)
        .ok_or_else(|| format!("{ctx}: missing integer field {k:?}"))
}

fn opt_u64(v: &Value, k: &str, ctx: &str) -> Result<Option<u64>, String> {
    match v.get(k) {
        None | Some(Value::Null) => Ok(None),
        Some(x) => x
            .as_u64()
            .map(Some)
            .ok_or_else(|| format!("{ctx}: field {k:?} is neither an integer nor null")),
    }
}

/// Read and validate `manifest.json`: every entry carries provenance, a
/// real entry names a repository, a full commit SHA, its source and how it
/// was produced, and every file's SHA-256 matches its bytes.
pub fn load_manifest(dir: &Path) -> Result<Manifest, String> {
    let text = std::fs::read_to_string(dir.join("manifest.json"))
        .map_err(|e| format!("manifest.json: {e}"))?;
    let v: Value = serde_json::from_str(&text).map_err(|e| format!("manifest.json: {e}"))?;
    if v.get("schema").and_then(Value::as_str) != Some("ordeal-perf-corpus/v1") {
        return Err("manifest.json: schema must be ordeal-perf-corpus/v1".into());
    }
    let mut entries = Vec::new();
    let mut ids = BTreeSet::new();
    for q in v
        .get("queries")
        .and_then(Value::as_array)
        .ok_or("manifest.json: no queries array")?
    {
        let id = str_field(q, "id", "query")?.to_string();
        let ctx = format!("manifest {id}");
        if !ids.insert(id.clone()) {
            return Err(format!("{ctx}: duplicate id"));
        }
        let consumer = str_field(q, "consumer", &ctx)?.to_string();
        let real = q
            .get("real")
            .and_then(Value::as_bool)
            .ok_or(format!("{ctx}: missing bool real"))?;
        let expect =
            Verdict::parse(str_field(q, "expect", &ctx)?).map_err(|e| format!("{ctx}: {e}"))?;
        let p = q
            .get("provenance")
            .ok_or(format!("{ctx}: missing provenance"))?;
        str_field(p, "produced_by", &ctx)?;
        if real {
            let repo = str_field(p, "repo", &ctx)?;
            if repo != format!("pulseengine/{consumer}") {
                return Err(format!(
                    "{ctx}: real query from {repo}, consumer {consumer}"
                ));
            }
            let sha = str_field(p, "commit", &ctx)?;
            if sha.len() != 40 || !sha.bytes().all(|b| b.is_ascii_hexdigit()) {
                return Err(format!(
                    "{ctx}: commit must be a full 40-hex SHA, got {sha:?}"
                ));
            }
            str_field(p, "source", &ctx)?;
        } else if p.get("synthetic").and_then(Value::as_str).is_none() {
            return Err(format!(
                "{ctx}: a non-real query must say why in provenance.synthetic"
            ));
        }
        let driver = match str_field(q, "driver", &ctx)? {
            "smtlib" => Driver::Smtlib,
            "verus" => Driver::Verus,
            "api-dag" => Driver::ApiDag,
            "bmc" => {
                let b = q
                    .get("bmc")
                    .ok_or(format!("{ctx}: bmc driver needs a bmc object"))?;
                Driver::Bmc {
                    generator: str_field(b, "generator", &ctx)?.to_string(),
                    k: u64_field(b, "k", &ctx)? as usize,
                    arg: u64_field(b, "arg", &ctx)?,
                }
            }
            other => return Err(format!("{ctx}: unknown driver {other:?}")),
        };
        let (file, sha256) = match q.get("file").and_then(Value::as_str) {
            Some(f) => {
                let path = dir.join(f);
                let bytes = std::fs::read(&path).map_err(|e| format!("{ctx}: {f}: {e}"))?;
                let want = str_field(q, "sha256", &ctx)?;
                let got = ordeal::sha256::sha256_hex(&bytes);
                if got != want {
                    return Err(format!("{ctx}: {f} sha256 {got} != manifest {want}"));
                }
                (Some(path), Some(want.to_string()))
            }
            None if matches!(driver, Driver::Bmc { .. }) => (None, None),
            None => return Err(format!("{ctx}: driver needs a file")),
        };
        entries.push(Entry {
            id,
            consumer,
            real,
            file,
            sha256,
            driver,
            expect,
        });
    }
    let uncovered = v
        .get("consumers_not_covered")
        .and_then(Value::as_array)
        .map(|a| {
            a.iter()
                .filter_map(|c| c.get("repo").and_then(Value::as_str).map(str::to_string))
                .collect()
        })
        .unwrap_or_default();
    Ok(Manifest { entries, uncovered })
}

/// Read a budgets file (`ordeal-perf-budgets/v1`).
pub fn load_budgets(path: &Path) -> Result<BTreeMap<String, Budget>, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    parse_budgets(&text)
}

pub fn parse_budgets(text: &str) -> Result<BTreeMap<String, Budget>, String> {
    let v: Value = serde_json::from_str(text).map_err(|e| format!("budgets: {e}"))?;
    if v.get("schema").and_then(Value::as_str) != Some("ordeal-perf-budgets/v1") {
        return Err("budgets: schema must be ordeal-perf-budgets/v1".into());
    }
    let mut out = BTreeMap::new();
    for (id, b) in v
        .get("queries")
        .and_then(Value::as_object)
        .ok_or("budgets: no queries object")?
    {
        let ctx = format!("budget {id}");
        let budget = Budget {
            time_ms: u64_field(b, "time_ms", &ctx)?,
            cnf_clauses: u64_field(b, "cnf_clauses", &ctx)?,
            lrat_bytes: opt_u64(b, "lrat_bytes", &ctx)?,
            lrat_lines: opt_u64(b, "lrat_lines", &ctx)?,
        };
        if budget.time_ms == 0 {
            return Err(format!("{ctx}: time_ms must be positive"));
        }
        out.insert(id.clone(), budget);
    }
    Ok(out)
}

/// The manifest and the budgets name the same queries, in both directions,
/// and there is at least one.
pub fn set_agreement(entries: &[Entry], budgets: &BTreeMap<String, Budget>) -> Vec<String> {
    let m: BTreeSet<&str> = entries.iter().map(|e| e.id.as_str()).collect();
    let b: BTreeSet<&str> = budgets.keys().map(String::as_str).collect();
    let mut errs = Vec::new();
    if m.is_empty() {
        errs.push("the corpus is empty: 0 queries is not a pass".to_string());
    }
    for id in m.difference(&b) {
        errs.push(format!("{id}: in manifest.json but has no budget"));
    }
    for id in b.difference(&m) {
        errs.push(format!("{id}: has a budget but is not in manifest.json"));
    }
    errs
}

/// Compare one measurement to its budget and expected verdict.
pub fn judge(entry: &Entry, budget: &Budget, m: &Measurement) -> Vec<String> {
    let id = &entry.id;
    let mut errs = Vec::new();
    if m.verdict != entry.expect {
        errs.push(format!(
            "{id}: verdict {} but the manifest expects {}",
            m.verdict.as_str(),
            entry.expect.as_str()
        ));
    }
    if m.time_ms > budget.time_ms as f64 {
        errs.push(format!(
            "{id}: time {:.0} ms exceeds the budget of {} ms",
            m.time_ms, budget.time_ms
        ));
    }
    let pinned = |what: &str, got: Option<u64>, want: Option<u64>, errs: &mut Vec<String>| {
        if got == want {
            return;
        }
        match (got, want) {
            (Some(g), Some(w)) if g > w => {
                errs.push(format!("{id}: {what} {g} exceeds the budget {w} (+{})", g - w))
            }
            (Some(g), Some(w)) => errs.push(format!(
                "{id}: {what} {g} is below the budget {w} (-{}): an improvement; lower the budget to {g}",
                w - g
            )),
            (g, w) => errs.push(format!("{id}: {what} {g:?} but the budget says {w:?}")),
        }
    };
    pinned(
        "cnf_clauses",
        Some(m.cnf_clauses),
        Some(budget.cnf_clauses),
        &mut errs,
    );
    pinned("lrat_bytes", m.lrat_bytes, budget.lrat_bytes, &mut errs);
    pinned("lrat_lines", m.lrat_lines, budget.lrat_lines, &mut errs);
    errs
}

/// The time budget the published policy gives a measured time.
pub fn time_budget(measured_ms: f64) -> u64 {
    let t = measured_ms.ceil() as u64;
    let b = (t * TIME_FACTOR).max(t + TIME_FLOOR_MS);
    b.div_ceil(100) * 100
}

// ─── Drivers ────────────────────────────────────────────────────────────────

/// What one solve produced, before the gate's own re-checks.
enum Solved {
    Unsat(ordeal::Certificate),
    Sat,
    Unknown,
}

/// The prepared input: parsing/expansion that is the consumer's own cost
/// (building its terms) stays outside the timed region.
enum Prepared {
    Script(String),
    Terms(Vec<BoolTerm>),
}

fn prepare(entry: &Entry) -> Result<Prepared, String> {
    let text = || {
        std::fs::read_to_string(entry.file.as_ref().expect("file-backed driver"))
            .map_err(|e| format!("{}: {e}", entry.id))
    };
    match &entry.driver {
        Driver::Smtlib => Ok(Prepared::Script(text()?)),
        Driver::Verus => {
            let ob =
                ordeal::verus::extract(&text()?).map_err(|e| format!("{}: {e:?}", entry.id))?;
            Ok(Prepared::Script(ob.script))
        }
        Driver::ApiDag => Ok(Prepared::Terms(
            read_dag(&text()?).map_err(|e| format!("{}: {e}", entry.id))?,
        )),
        Driver::Bmc { generator, k, arg } => match generator.as_str() {
            "queue_overflow" => Ok(Prepared::Terms(ordeal::bmc_corpus::queue_overflow(
                *k, *arg as u8,
            ))),
            "deadlock" => Ok(Prepared::Terms(ordeal::bmc_corpus::deadlock(*k, *arg != 0))),
            g => Err(format!("{}: unknown bmc generator {g:?}", entry.id)),
        },
    }
}

/// The timed region: exactly the call the consumer makes.
fn solve(entry: &Entry, p: &Prepared) -> Result<Solved, String> {
    match (p, &entry.driver) {
        (Prepared::Script(s), Driver::Smtlib) => {
            match ordeal::smtlib::solve_str_with_witness(s)
                .map_err(|e| format!("{}: {e:?}", entry.id))?
                .0
            {
                Some(WitnessCheckResult::Unsat(c)) => Ok(Solved::Unsat(c)),
                Some(WitnessCheckResult::Sat(w)) => {
                    w.recheck().map_err(|e| {
                        format!("{}: Sat witness failed its re-check: {e:?}", entry.id)
                    })?;
                    Ok(Solved::Sat)
                }
                _ => Ok(Solved::Unknown),
            }
        }
        (Prepared::Script(s), _) => {
            match ordeal::smtlib::solve_str(s)
                .map_err(|e| format!("{}: {e:?}", entry.id))?
                .result
            {
                Some(CheckResult::Unsat(c)) => Ok(Solved::Unsat(c)),
                Some(CheckResult::Sat(_)) => Ok(Solved::Sat),
                _ => Ok(Solved::Unknown),
            }
        }
        (Prepared::Terms(ts), _) => {
            let mut s = Solver::new();
            for t in ts {
                s.assert(t.clone());
            }
            match s.check() {
                CheckResult::Unsat(c) => Ok(Solved::Unsat(c)),
                CheckResult::Sat(_) => Ok(Solved::Sat),
                CheckResult::Unknown => Ok(Solved::Unknown),
            }
        }
    }
}

/// A `Sat` from a path that returns a bare model is re-confirmed outside
/// the timed region by a witness the trusted crate re-checks.
fn confirm_sat(entry: &Entry, p: &Prepared) -> Result<(), String> {
    let r = match p {
        Prepared::Script(s) => ordeal::smtlib::solve_str_with_witness(s)
            .map_err(|e| format!("{}: {e:?}", entry.id))?
            .0
            .unwrap_or(WitnessCheckResult::Unknown),
        Prepared::Terms(ts) => {
            let mut s = Solver::new();
            for t in ts {
                s.assert(t.clone());
            }
            s.check_with_witness()
        }
    };
    match r {
        WitnessCheckResult::Sat(w) => w
            .recheck()
            .map_err(|e| format!("{}: Sat witness failed its re-check: {e:?}", entry.id)),
        _ => Err(format!(
            "{}: Sat was not re-confirmed by a checked witness",
            entry.id
        )),
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Injection {
    /// Solve this many times inside the timed region (>= 1).
    pub slowdown: u32,
    /// Bytes added to each measured LRAT size.
    pub inflate_lrat: u64,
}

impl Injection {
    pub fn from_env() -> Self {
        let num = |k: &str| std::env::var(k).ok().and_then(|v| v.parse::<u64>().ok());
        Injection {
            slowdown: num("ORDEAL_PERF_GATE_SLOWDOWN").unwrap_or(1).max(1) as u32,
            inflate_lrat: num("ORDEAL_PERF_GATE_INFLATE_LRAT").unwrap_or(0),
        }
    }
}

/// Run one query: time it (fastest of [`RERUNS`] when it is quick), demand
/// the same proof on every run, re-check every verdict.
pub fn measure(entry: &Entry, inj: Injection) -> Result<Measurement, String> {
    let prepared = prepare(entry)?;
    let mut best = f64::INFINITY;
    let mut seen: Option<(Verdict, u64, Option<u64>, Option<u64>)> = None;
    let mut runs = 0;
    loop {
        let start = Instant::now();
        let mut solved = solve(entry, &prepared)?;
        for _ in 1..inj.slowdown {
            solved = solve(entry, &prepared)?;
        }
        let ms = start.elapsed().as_secs_f64() * 1000.0;
        best = best.min(ms);
        runs += 1;
        let shape = match &solved {
            Solved::Unsat(c) => {
                c.recheck().map_err(|e| {
                    format!("{}: Unsat certificate failed its re-check: {e}", entry.id)
                })?;
                let lines = c.lrat.iter().filter(|&&b| b == b'\n').count() as u64;
                (
                    Verdict::Unsat,
                    c.cnf.len() as u64,
                    Some(c.lrat.len() as u64),
                    Some(lines),
                )
            }
            Solved::Sat => {
                confirm_sat(entry, &prepared)?;
                (Verdict::Sat, sat_cnf_clauses(&prepared, entry)?, None, None)
            }
            Solved::Unknown => (Verdict::Unknown, 0, None, None),
        };
        match &seen {
            None => seen = Some(shape),
            Some(prev) if *prev != shape => {
                return Err(format!(
                    "{}: nondeterministic result across runs: {prev:?} then {shape:?}",
                    entry.id
                ));
            }
            Some(_) => {}
        }
        if runs >= RERUNS || best >= RERUN_BELOW_MS {
            break;
        }
    }
    let (verdict, cnf_clauses, lrat_bytes, lrat_lines) = seen.expect("ran at least once");
    Ok(Measurement {
        verdict,
        time_ms: best,
        cnf_clauses,
        lrat_bytes: lrat_bytes.map(|b| b + inj.inflate_lrat),
        lrat_lines,
    })
}

/// The CNF a `Sat` verdict's witness satisfies, for the clause-count pin.
fn sat_cnf_clauses(p: &Prepared, entry: &Entry) -> Result<u64, String> {
    let r = match p {
        Prepared::Script(s) => ordeal::smtlib::solve_str_with_witness(s)
            .map_err(|e| format!("{}: {e:?}", entry.id))?
            .0
            .unwrap_or(WitnessCheckResult::Unknown),
        Prepared::Terms(ts) => {
            let mut s = Solver::new();
            for t in ts {
                s.assert(t.clone());
            }
            s.check_with_witness()
        }
    };
    match r {
        WitnessCheckResult::Sat(w) => Ok(w.cnf.len() as u64),
        _ => Err(format!("{}: Sat witness missing", entry.id)),
    }
}

// ─── The nullary define-fun DAG reader (api-dag driver) ─────────────────────
//
// Untrusted test code. It reads exactly what the corpus dump hook prints
// (declare-fun, nullary define-fun, assert, check-sat) and rebuilds the
// consumer's term TREE by cloning each defined node at every use, so the
// solver sees the same terms the consumer asserted. The manifest records
// the consumer's own API-path CNF and LRAT sizes next to each query, which
// is how the reader's fidelity was checked when the corpus was taken.

#[derive(Clone, Debug)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

fn tokenize(s: &str) -> Result<Vec<String>, String> {
    let mut out = Vec::new();
    let mut it = s.chars().peekable();
    while let Some(c) = it.next() {
        match c {
            ';' => {
                for c in it.by_ref() {
                    if c == '\n' {
                        break;
                    }
                }
            }
            '(' | ')' => out.push(c.to_string()),
            '|' => {
                let mut t = String::from("|");
                loop {
                    match it.next() {
                        Some('|') => break,
                        Some(c) => t.push(c),
                        None => return Err("unterminated |symbol|".into()),
                    }
                }
                t.push('|');
                out.push(t);
            }
            c if c.is_whitespace() => {}
            c => {
                let mut t = c.to_string();
                while let Some(&n) = it.peek() {
                    if n.is_whitespace() || n == '(' || n == ')' {
                        break;
                    }
                    t.push(n);
                    it.next();
                }
                out.push(t);
            }
        }
    }
    Ok(out)
}

fn parse_sexps(tokens: &[String]) -> Result<Vec<Sexp>, String> {
    let mut stack: Vec<Vec<Sexp>> = vec![Vec::new()];
    for t in tokens {
        match t.as_str() {
            "(" => stack.push(Vec::new()),
            ")" => {
                let done = stack.pop().ok_or("unbalanced )")?;
                stack
                    .last_mut()
                    .ok_or("unbalanced )")?
                    .push(Sexp::List(done));
            }
            _ => stack.last_mut().expect("root").push(Sexp::Atom(t.clone())),
        }
    }
    if stack.len() != 1 {
        return Err("unbalanced (".into());
    }
    Ok(stack.pop().expect("root"))
}

fn unbar(s: &str) -> &str {
    s.strip_prefix('|')
        .and_then(|t| t.strip_suffix('|'))
        .unwrap_or(s)
}

#[derive(Clone)]
enum Def {
    Bv(BvTerm, u32),
    Bool(BoolTerm),
}

struct Reader {
    vars: HashMap<String, u32>,
    defs: HashMap<String, Def>,
}

fn num(s: &Sexp) -> Result<u128, String> {
    match s {
        Sexp::Atom(a) => a.parse().map_err(|_| format!("not a numeral: {a}")),
        _ => Err("expected a numeral".into()),
    }
}

impl Reader {
    fn bv(&self, s: &Sexp) -> Result<(BvTerm, u32), String> {
        match s {
            Sexp::Atom(a) => {
                let name = unbar(a);
                if let Some(&w) = self.vars.get(name) {
                    return Ok((
                        BvTerm::Var {
                            name: name.to_string(),
                            sort: Sort::new(w),
                        },
                        w,
                    ));
                }
                match self.defs.get(name) {
                    Some(Def::Bv(t, w)) => Ok((t.clone(), *w)),
                    _ => Err(format!("unknown bitvector symbol {a}")),
                }
            }
            Sexp::List(items) => {
                let head = items.first().ok_or("empty term")?;
                if let Sexp::Atom(h) = head
                    && h == "_"
                {
                    // (_ bvV W)
                    let Some(Sexp::Atom(v)) = items.get(1) else {
                        return Err("bad literal".into());
                    };
                    let value = v
                        .strip_prefix("bv")
                        .ok_or("bad literal")?
                        .parse::<u128>()
                        .map_err(|e| e.to_string())?;
                    let w = num(items.get(2).ok_or("bad literal")?)? as u32;
                    return Ok((
                        BvTerm::Const {
                            value,
                            sort: Sort::new(w),
                        },
                        w,
                    ));
                }
                if let Sexp::List(idx) = head {
                    // ((_ op k [l]) x)
                    let op = match idx.get(1) {
                        Some(Sexp::Atom(o)) => o.as_str(),
                        _ => return Err("bad indexed operator".into()),
                    };
                    let (x, w) = self.bv(items.get(1).ok_or("indexed op needs an argument")?)?;
                    let k = num(idx.get(2).ok_or("indexed op needs an index")?)? as u32;
                    let arg = Box::new(x);
                    return Ok(match op {
                        "extract" => {
                            let lo = num(idx.get(3).ok_or("extract needs lo")?)? as u32;
                            (BvTerm::Extract { hi: k, lo, arg }, k - lo + 1)
                        }
                        "zero_extend" => (BvTerm::ZeroExt { by: k, arg }, w + k),
                        "sign_extend" => (BvTerm::SignExt { by: k, arg }, w + k),
                        "rotate_left" | "rotate_right" => {
                            let amt = Box::new(BvTerm::Const {
                                value: k as u128,
                                sort: Sort::new(w),
                            });
                            if op == "rotate_left" {
                                (BvTerm::Rotl(arg, amt), w)
                            } else {
                                (BvTerm::Rotr(arg, amt), w)
                            }
                        }
                        other => return Err(format!("unsupported indexed operator {other}")),
                    });
                }
                let Sexp::Atom(op) = head else { unreachable!() };
                let arg = |i: usize| {
                    self.bv(items
                        .get(i)
                        .ok_or_else(|| format!("{op}: missing argument"))?)
                };
                if op == "ite" {
                    let c = self.boolean(items.get(1).ok_or("ite: missing condition")?)?;
                    let (a, w) = arg(2)?;
                    let (b, _) = arg(3)?;
                    return Ok((
                        BvTerm::Ite {
                            cond: Box::new(c),
                            then_: Box::new(a),
                            else_: Box::new(b),
                        },
                        w,
                    ));
                }
                if op == "bvnot" || op == "bvneg" {
                    let (a, w) = arg(1)?;
                    let a = Box::new(a);
                    return Ok((
                        if op == "bvnot" {
                            BvTerm::Not(a)
                        } else {
                            BvTerm::Neg(a)
                        },
                        w,
                    ));
                }
                if items.len() != 3 {
                    return Err(format!("{op}: expected two arguments"));
                }
                let (a, wa) = arg(1)?;
                let (b, wb) = arg(2)?;
                let (a, b) = (Box::new(a), Box::new(b));
                Ok(match op.as_str() {
                    "bvadd" => (BvTerm::Add(a, b), wa),
                    "bvsub" => (BvTerm::Sub(a, b), wa),
                    "bvmul" => (BvTerm::Mul(a, b), wa),
                    "bvudiv" => (BvTerm::Udiv(a, b), wa),
                    "bvurem" => (BvTerm::Urem(a, b), wa),
                    "bvsdiv" => (BvTerm::Sdiv(a, b), wa),
                    "bvsrem" => (BvTerm::Srem(a, b), wa),
                    "bvand" => (BvTerm::And(a, b), wa),
                    "bvor" => (BvTerm::Or(a, b), wa),
                    "bvxor" => (BvTerm::Xor(a, b), wa),
                    "bvshl" => (BvTerm::Shl(a, b), wa),
                    "bvlshr" => (BvTerm::Lshr(a, b), wa),
                    "bvashr" => (BvTerm::Ashr(a, b), wa),
                    "concat" => (BvTerm::Concat(a, b), wa + wb),
                    other => return Err(format!("unsupported bitvector operator {other}")),
                })
            }
        }
    }

    fn boolean(&self, s: &Sexp) -> Result<BoolTerm, String> {
        match s {
            Sexp::Atom(a) => match self.defs.get(unbar(a)) {
                Some(Def::Bool(t)) => Ok(t.clone()),
                _ => Err(format!("unknown boolean symbol {a}")),
            },
            Sexp::List(items) => {
                let Some(Sexp::Atom(op)) = items.first() else {
                    return Err("bad boolean term".into());
                };
                let b = |i: usize| -> Result<Box<BoolTerm>, String> {
                    Ok(Box::new(
                        self.boolean(
                            items
                                .get(i)
                                .ok_or_else(|| format!("{op}: missing argument"))?,
                        )?,
                    ))
                };
                match op.as_str() {
                    "not" => return Ok(BoolTerm::Not(b(1)?)),
                    "and" => return Ok(BoolTerm::And(b(1)?, b(2)?)),
                    "or" => return Ok(BoolTerm::Or(b(1)?, b(2)?)),
                    _ => {}
                }
                let x = Box::new(
                    self.bv(items.get(1).ok_or("comparison: missing argument")?)?
                        .0,
                );
                let y = Box::new(
                    self.bv(items.get(2).ok_or("comparison: missing argument")?)?
                        .0,
                );
                Ok(match op.as_str() {
                    "=" => BoolTerm::Eq(x, y),
                    "distinct" => BoolTerm::Ne(x, y),
                    "bvult" => BoolTerm::Ult(x, y),
                    "bvule" => BoolTerm::Ule(x, y),
                    "bvugt" => BoolTerm::Ugt(x, y),
                    "bvuge" => BoolTerm::Uge(x, y),
                    "bvslt" => BoolTerm::Slt(x, y),
                    "bvsle" => BoolTerm::Sle(x, y),
                    "bvsgt" => BoolTerm::Sgt(x, y),
                    "bvsge" => BoolTerm::Sge(x, y),
                    other => return Err(format!("unsupported predicate {other}")),
                })
            }
        }
    }
}

fn sort_width(s: &Sexp) -> Result<Option<u32>, String> {
    match s {
        Sexp::Atom(a) if a == "Bool" => Ok(None),
        Sexp::List(items) if items.len() == 3 => match (&items[0], &items[1]) {
            (Sexp::Atom(u), Sexp::Atom(b)) if u == "_" && b == "BitVec" => {
                Ok(Some(num(&items[2])? as u32))
            }
            _ => Err("bad sort".into()),
        },
        _ => Err("bad sort".into()),
    }
}

/// Read a dump-hook script into the asserted terms, in order.
pub fn read_dag(text: &str) -> Result<Vec<BoolTerm>, String> {
    let mut r = Reader {
        vars: HashMap::new(),
        defs: HashMap::new(),
    };
    let mut asserts = Vec::new();
    let mut check_sat = 0;
    for cmd in parse_sexps(&tokenize(text)?)? {
        let Sexp::List(items) = cmd else {
            return Err("top level atom".into());
        };
        let Some(Sexp::Atom(head)) = items.first() else {
            return Err("bad command".into());
        };
        let name = |i: usize| match items.get(i) {
            Some(Sexp::Atom(n)) => Ok(unbar(n).to_string()),
            _ => Err(format!("{head}: missing name")),
        };
        let empty_params = |i: usize| matches!(items.get(i), Some(Sexp::List(p)) if p.is_empty());
        match head.as_str() {
            "set-logic" => {}
            "declare-fun" => {
                if !empty_params(2) {
                    return Err("declare-fun with parameters".into());
                }
                let w = sort_width(items.get(3).ok_or("declare-fun: no sort")?)?
                    .ok_or("declare-fun: only bitvector constants")?;
                r.vars.insert(name(1)?, w);
            }
            "define-fun" => {
                if !empty_params(2) {
                    return Err("define-fun with parameters".into());
                }
                let n = name(1)?;
                let body = items.get(4).ok_or("define-fun: no body")?;
                let def = match sort_width(items.get(3).ok_or("define-fun: no sort")?)? {
                    Some(w) => {
                        let (t, got) = r.bv(body)?;
                        if got != w {
                            return Err(format!("{n}: declared width {w}, body width {got}"));
                        }
                        Def::Bv(t, w)
                    }
                    None => Def::Bool(r.boolean(body)?),
                };
                r.defs.insert(n, def);
            }
            "assert" => asserts.push(r.boolean(items.get(1).ok_or("assert: no term")?)?),
            "check-sat" => check_sat += 1,
            other => return Err(format!("unsupported command {other}")),
        }
    }
    if check_sat != 1 || asserts.is_empty() {
        return Err(format!(
            "expected one check-sat after >= 1 assert, got {check_sat} / {}",
            asserts.len()
        ));
    }
    Ok(asserts)
}
