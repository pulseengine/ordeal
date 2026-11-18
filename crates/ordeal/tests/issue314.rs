// rivet: verifies VER-096
//! Issue #314 (TR-096): `bvudiv` / `bvurem` by a constant power of two.
//!
//! The restoring divider emits, for every remainder bit below the divisor's
//! set bit, the mux `ge ? r : r`. Up to v0.37.0 the compaction kept all
//! `k * (w - k)` of them and the CDCL search did not finish at 128 bits.
//! Since v0.38.0 the trusted `blast_kernel::compact` folds them away
//! (`mux_fold`, requested by a hint and checked), and the query is decided
//! in milliseconds. This file holds:
//!
//! - the regression: `udiv` and `urem` at several widths and `k`, decided
//!   `Unsat` with a certificate that re-checks, inside a time bound;
//! - the control: the SAME queries lowered without the fold (the v0.37.0
//!   lowering, rebuilt here from the public API) run into the deadline;
//! - the odd-width guard: the checker certifies the CNF, not the query, so
//!   a fold that changed a value would give a certified wrong `Unsat` —
//!   every near-miss of the identity must stay `Sat` with a model that the
//!   evaluator confirms;
//! - the bundles: one written by the v0.37.0 release binary is still
//!   accepted by this build's `ordeal-recheck`, and the bundle this build
//!   writes for the same script is tagged `ordeal-dag/v3`.

use ordeal::blast_kernel as k;
use ordeal::cnf::CnfFormula;
use ordeal::dag::{DagBuilder, fold_hints, mux_fold_requests, strash_hints};
use ordeal::query::{QUERY_ENCODING_V3, TermCheckResult};
use ordeal::sat::{SatResult, SatSolver};
use ordeal::{BoolTerm, BvTerm, Solver, Sort};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{Duration, Instant};

const ORDEAL: &str = env!("CARGO_BIN_EXE_ordeal");

/// Wall-clock bound on ONE certified decision (lowering, search, proof,
/// every trusted gate), in a debug build. Measured: at most 0.9 s
/// (`w = 128, k = 64`, debug, 2026-11-18); without the fold the same query
/// does not finish in 60 s in a release build.
const DECISION_BOUND: Duration = Duration::from_secs(20);

/// The deadline of the control: what the SAT core gets on the CNF lowered
/// WITHOUT the fold. Twenty times what the folded CNF needs for search at
/// the control's sizes in a debug build.
const CONTROL_DEADLINE: Duration = Duration::from_millis(1500);

fn var(name: &str, w: u32) -> BvTerm {
    BvTerm::Var {
        name: name.into(),
        sort: Sort::new(w),
    }
}

fn konst(value: u128, w: u32) -> BvTerm {
    BvTerm::Const {
        value,
        sort: Sort::new(w),
    }
}

/// The shift-and-mask spelling of `x udiv 2^j` (`urem = false`):
/// `zero_extend_j(x[w-1:j])`, or of `x urem 2^j`:
/// `zero_extend_(w-j)(x[j-1:0])`. `1 <= j < w`.
fn shifted(urem: bool, x: BvTerm, w: u32, j: u32) -> BvTerm {
    if urem {
        BvTerm::ZeroExt {
            by: w - j,
            arg: Box::new(BvTerm::Extract {
                hi: j - 1,
                lo: 0,
                arg: Box::new(x),
            }),
        }
    } else {
        BvTerm::ZeroExt {
            by: j,
            arg: Box::new(BvTerm::Extract {
                hi: w - 1,
                lo: j,
                arg: Box::new(x),
            }),
        }
    }
}

/// `x op 2^k != shifted_j(x)`: UNSAT exactly when `j == k` (the identity),
/// satisfiable for every other `j`.
fn query(urem: bool, w: u32, k: u32, j: u32) -> BoolTerm {
    let x = var("x", w);
    let d = konst(1u128 << k, w);
    let lhs = if urem {
        BvTerm::Urem(Box::new(x.clone()), Box::new(d))
    } else {
        BvTerm::Udiv(Box::new(x.clone()), Box::new(d))
    };
    BoolTerm::Ne(Box::new(lhs), Box::new(shifted(urem, x, w, j)))
}

fn op(urem: bool) -> &'static str {
    if urem { "urem" } else { "udiv" }
}

/// The production lowering re-run through the public API (as
/// `Solver::lower_with` runs it: canonicalize, hash-consed DAG, proven
/// `encode`, hints, proven `compact`, proven `tseitin`), with the fold
/// hints (`fold = true`, production) or without them (the v0.37.0
/// lowering). Returns the CNF and how many gates the fold removed.
fn lower(q: &BoolTerm, fold: bool) -> (CnfFormula, usize) {
    let mut builder = DagBuilder::new(true);
    builder
        .assert_root(&ordeal::canon::canonicalize_bool(q))
        .expect("well-sorted");
    let dag = builder.finish();
    let mut raw = k::aig_new();
    let (_, outs) = k::encode(&mut raw, &dag.nodes, &dag.bits, &dag.roots);
    let hints = if fold {
        fold_hints(&raw)
    } else {
        strash_hints(&raw)
    };
    let (aig, map) = k::compact(&raw, &hints);
    let outs = k::map_word(&map, &outs);
    let clauses = k::tseitin(&aig, &outs);
    (
        CnfFormula {
            num_vars: aig.nodes.len() as u32,
            clauses,
        },
        mux_fold_requests(&hints),
    )
}

/// The built-in SAT core on `cnf` under a deadline: `Some(true)` = UNSAT,
/// `Some(false)` = SAT, `None` = the deadline passed.
fn search(cnf: &CnfFormula, deadline: Duration) -> (Option<bool>, Duration) {
    let mut sat = SatSolver::new();
    let t0 = Instant::now();
    let r = sat.solve_with_deadline(cnf, Instant::now() + deadline);
    (r.map(|v| matches!(v, SatResult::Unsat)), t0.elapsed())
}

/// `(w, k)`: the #314 repro (128, 64), its neighbours, the widths loom and
/// synth use, and the odd widths 3 / 5 / 12 / 24.
const CASES: [(u32, u32); 14] = [
    (128, 64),
    (128, 1),
    (128, 127),
    (64, 32),
    (64, 7),
    (32, 16),
    (32, 31),
    (16, 8),
    (8, 4),
    (3, 1),
    (5, 2),
    (12, 7),
    (24, 11),
    (24, 23),
];

/// The regression. Every case, `udiv` and `urem`: `Unsat`, the certificate
/// re-checks through the trusted crate, the fold fired `k * (w - k)` times
/// (for `urem` too: the same divider), the query block is tagged
/// `ordeal-dag/v3`, and the decision took less than [`DECISION_BOUND`].
#[test]
fn pow2_division_is_certified_unsat_inside_the_bound() {
    for (w, kk) in CASES {
        for urem in [false, true] {
            let what = format!("{} w={w} k={kk}", op(urem));
            let q = query(urem, w, kk, kk);
            let mut s = Solver::new();
            s.assert(q.clone());
            let t0 = Instant::now();
            let r = s.check_with_term();
            let took = t0.elapsed();
            let TermCheckResult::Unsat(cert) = r else {
                panic!("{what}: expected a certified Unsat, got {r:?} after {took:?}");
            };
            assert!(
                took < DECISION_BOUND,
                "{what}: decided, but in {took:?} (bound {DECISION_BOUND:?})"
            );
            cert.recheck()
                .unwrap_or_else(|e| panic!("{what}: the certificate must re-check: {e}"));
            let fired = mux_fold_requests(&cert.query.query.hints);
            assert_eq!(fired, (kk * (w - kk)) as usize, "{what}: fold count");
            assert_eq!(cert.query.query.encoding(), QUERY_ENCODING_V3, "{what}");
            // The certificate's CNF is the one this file's `lower` builds.
            assert_eq!(
                cert.query.certificate.cnf,
                lower(&q, true).0.clauses,
                "{what}"
            );
        }
    }
}

/// The control: the fold is what decides them. Lowered WITHOUT the fold —
/// the lowering of every release up to v0.37.0 — the SAT core runs into
/// [`CONTROL_DEADLINE`] on these queries; lowered with it, the same core
/// refutes them well inside the same deadline. If this test fails because
/// the first leg finished, the search got better and #314's time bound no
/// longer measures the fold: pick harder sizes, do not delete the control.
#[test]
fn without_the_fold_the_search_runs_into_the_deadline() {
    for (urem, w, kk) in [(false, 64u32, 32u32), (true, 64, 32), (false, 128, 64)] {
        let what = format!("{} w={w} k={kk}", op(urem));
        let q = query(urem, w, kk, kk);
        let (legacy, none) = lower(&q, false);
        assert_eq!(none, 0, "{what}: the v0.37.0 hints request no fold");
        let (folded, fired) = lower(&q, true);
        assert_eq!(fired, (kk * (w - kk)) as usize, "{what}");
        assert!(
            folded.clauses.len() < legacy.clauses.len(),
            "{what}: the fold removes clauses"
        );
        let (old, t_old) = search(&legacy, CONTROL_DEADLINE);
        assert_eq!(
            old, None,
            "{what}: WITHOUT the fold the search finished in {t_old:?} — the control is spent"
        );
        let (new, t_new) = search(&folded, CONTROL_DEADLINE);
        assert_eq!(
            new,
            Some(true),
            "{what}: WITH the fold the search must refute it inside the deadline ({t_new:?})"
        );
    }
}

/// The odd-width guard. `x op 2^k != shifted_j(x)` is satisfiable for
/// every `j != k`; a fold that changed the divider's value could turn one
/// of these into a certified wrong `Unsat` (the checker certifies the CNF
/// the trusted crate derived, and the fold is in that derivation). At
/// widths 3, 5, 12 and 24, every `k` and every `j`: `Unsat` exactly on the
/// diagonal, and off it a model under which the evaluator — which shares
/// no code with the lowering — finds the two sides different.
#[test]
fn near_misses_of_the_identity_stay_sat_at_odd_widths() {
    let (mut unsat, mut sat, mut fired) = (0u32, 0u32, 0usize);
    for w in [3u32, 5, 12, 24] {
        // Width 24 would be 2 * 23 * 23 queries; sample its diagonals.
        let ks: Vec<u32> = if w == 24 {
            vec![1, 7, 12, 23]
        } else {
            (1..w).collect()
        };
        for &kk in &ks {
            for j in 1..w {
                if w == 24 && j.abs_diff(kk) > 2 {
                    continue;
                }
                for urem in [false, true] {
                    let what = format!("{} w={w} k={kk} j={j}", op(urem));
                    let q = query(urem, w, kk, j);
                    let mut s = Solver::new();
                    s.assert(q.clone());
                    match s.check_with_term() {
                        TermCheckResult::Unsat(cert) => {
                            assert_eq!(j, kk, "{what}: Unsat off the diagonal is WRONG");
                            cert.recheck().expect("re-checks");
                            fired += mux_fold_requests(&cert.query.query.hints);
                            unsat += 1;
                        }
                        TermCheckResult::Sat(cert) => {
                            assert_ne!(j, kk, "{what}: the identity must be Unsat");
                            cert.recheck().expect("re-checks");
                            fired += mux_fold_requests(&cert.query.query.hints);
                            let env: ordeal::eval::Env = cert
                                .query
                                .witness
                                .model
                                .assignments
                                .iter()
                                .cloned()
                                .collect();
                            assert_eq!(
                                ordeal::eval::eval_bool(&q, &env),
                                Ok(true),
                                "{what}: the model must satisfy the query under the evaluator"
                            );
                            sat += 1;
                        }
                        TermCheckResult::Unknown => panic!("{what}: Unknown"),
                    }
                }
            }
        }
    }
    // Both verdicts and the fold itself were exercised.
    assert!(unsat >= 40 && sat >= 200, "unsat {unsat}, sat {sat}");
    assert!(fired > 1000, "the fold fired {fired} times");
}

// ── The bundles ───────────────────────────────────────────────────────────

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/issue314")
        .join(name)
}

/// The real `ordeal-recheck`, the sibling of the `ordeal` binary; built
/// here when a narrower `cargo test -p ordeal` left it out. Never skips.
fn recheck_bin() -> PathBuf {
    let ordeal = Path::new(ORDEAL);
    let profile_dir = ordeal.parent().expect("target profile dir");
    let exe = profile_dir.join(format!("ordeal-recheck{}", std::env::consts::EXE_SUFFIX));
    if !exe.exists() {
        let mut cmd = Command::new(env!("CARGO"));
        cmd.args(["build", "-p", "ordeal-recheck", "--manifest-path"])
            .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../Cargo.toml"))
            .arg("--target-dir")
            .arg(profile_dir.parent().expect("target dir"));
        if profile_dir.file_name().and_then(|n| n.to_str()) == Some("release") {
            cmd.arg("--release");
        }
        let st = cmd.status().expect("run cargo build -p ordeal-recheck");
        assert!(st.success(), "cargo build -p ordeal-recheck failed");
    }
    assert!(
        exe.exists(),
        "ordeal-recheck not found at {}",
        exe.display()
    );
    exe
}

fn recheck(file: &Path) -> Output {
    Command::new(recheck_bin())
        .arg(file)
        .output()
        .expect("run ordeal-recheck")
}

/// The text between `"key":"` and the next `"` — enough to read a string
/// field of a bundle without a JSON dependency (the default build has none).
fn string_field<'a>(json: &'a str, after: &str, key: &str) -> &'a str {
    let from = json
        .find(after)
        .unwrap_or_else(|| panic!("{after} not found"));
    let pat = format!("\"{key}\":\"");
    let at = json[from..]
        .find(&pat)
        .unwrap_or_else(|| panic!("{key} not found after {after}"))
        + from
        + pat.len();
    let end = json[at..].find('"').expect("closing quote") + at;
    &json[at..end]
}

/// Old bundles still re-check, and new ones say what they need.
///
/// `tests/fixtures/issue314/*.v0.37.0.cert.json` were written by the
/// v0.37.0 release binary (`ordeal check FILE --cert-out`) for the two
/// `.smt2` scripts beside them. Their hints never request the fold, so
/// this build's trusted crate compacts them exactly as v0.37.0 did and
/// re-derives the CNF they carry: `ordeal-recheck` accepts them, tag
/// `ordeal-dag/v1` and all. The bundle THIS build writes for the same
/// script is a different certificate — the fold fires, so the CNF is
/// smaller — tagged `ordeal-dag/v3` with `min_version` 0.38.0, and it
/// re-checks too. Retagging it `ordeal-dag/v1` is refused at parse.
#[test]
fn a_v0_37_bundle_still_rechecks_and_a_new_one_is_tagged_v3() {
    let scratch =
        PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!("issue314-{}", std::process::id()));
    std::fs::create_dir_all(&scratch).unwrap();
    for name in ["udiv_pow2_w8_k4", "urem_pow2_w12_k5"] {
        // The v0.37.0 bundle, as committed.
        let old_path = fixture(&format!("{name}.v0.37.0.cert.json"));
        let old = std::fs::read_to_string(&old_path).expect("the committed fixture");
        assert!(
            old.contains("\"version\":\"0.37.0\""),
            "{name}: written by 0.37.0"
        );
        assert_eq!(
            string_field(&old, "\"query\":", "encoding"),
            "ordeal-dag/v1"
        );
        assert!(
            !old.contains("18446744073709551615"),
            "{name}: a v0.37.0 bundle carries no fold hint"
        );
        let o = recheck(&old_path);
        assert_eq!(
            o.status.code(),
            Some(0),
            "{name}: the v0.37.0 bundle must still be accepted: {} {}",
            String::from_utf8_lossy(&o.stdout),
            String::from_utf8_lossy(&o.stderr)
        );
        assert!(String::from_utf8_lossy(&o.stdout).contains("accepted (ordeal-cert/v3, unsat)"));

        // This build's bundle for the same script.
        let new_path = scratch.join(format!("{name}.cert.json"));
        let o = Command::new(ORDEAL)
            .args(["check", fixture(&format!("{name}.smt2")).to_str().unwrap()])
            .args(["--cert-out", new_path.to_str().unwrap()])
            .output()
            .expect("run ordeal");
        assert_eq!(o.status.code(), Some(0), "{name}");
        let new = std::fs::read_to_string(&new_path).expect("the bundle was written");
        assert_eq!(
            string_field(&new, "\"query\":", "encoding"),
            "ordeal-dag/v3"
        );
        assert_eq!(string_field(&new, "\"recheck\":", "min_version"), "0.38.0");
        assert!(new.contains("18446744073709551615"), "{name}: fold hints");
        assert!(
            new.len() < old.len(),
            "{name}: the folded certificate is smaller"
        );
        let o = recheck(&new_path);
        assert_eq!(o.status.code(), Some(0), "{name}: the new bundle re-checks");

        // The same bundle claiming the old tag is a lie about the lowering.
        let lied_path = scratch.join(format!("{name}.lied.cert.json"));
        std::fs::write(
            &lied_path,
            new.replacen(
                "\"encoding\":\"ordeal-dag/v3\"",
                "\"encoding\":\"ordeal-dag/v1\"",
                1,
            ),
        )
        .unwrap();
        let o = recheck(&lied_path);
        assert_eq!(o.status.code(), Some(1), "{name}: a v1 tag with fold hints");
        let said = format!(
            "{}{}",
            String::from_utf8_lossy(&o.stdout),
            String::from_utf8_lossy(&o.stderr)
        );
        assert!(said.contains("mux-fold hint"), "{name}: {said}");
    }
    let _ = std::fs::remove_dir_all(&scratch);
}

// ── Measurement ───────────────────────────────────────────────────────────

/// The #314 timing table (a measurement, release build):
///
///   cargo test -p ordeal --release --test issue314 timings -- --ignored --nocapture
///
/// Per query: the v0.37.0 lowering's clause count and SAT-core time under
/// `U314_DEADLINE_MS` (default 60000; `deadline` = it passed), then this
/// build's fold count, clause count, SAT-core time and the time of the
/// whole certified decision (`check_with_term`, every trusted gate).
#[test]
#[ignore = "measurement, not a check: prints the #314 before/after timings"]
fn timings() {
    let deadline = Duration::from_millis(
        std::env::var("U314_DEADLINE_MS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(60_000),
    );
    println!(
        "\n| query | clauses v0.37 | search v0.37 | fires | clauses | search | certified decision |"
    );
    println!("|---|---:|---:|---:|---:|---:|---:|");
    let ms = |d: Duration| format!("{:.1} ms", d.as_secs_f64() * 1e3);
    for (w, kk) in CASES {
        for urem in [false, true] {
            let q = query(urem, w, kk, kk);
            let (legacy, _) = lower(&q, false);
            let (old, t_old) = search(&legacy, deadline);
            let (folded, fired) = lower(&q, true);
            let (new, t_new) = search(&folded, deadline);
            assert_eq!(new, Some(true));
            let mut s = Solver::new();
            s.assert(q);
            let t0 = Instant::now();
            let r = s.check_with_term();
            let t_all = t0.elapsed();
            assert!(matches!(r, TermCheckResult::Unsat(_)));
            println!(
                "| {} w={w} k={kk} | {} | {} | {fired} | {} | {} | {} |",
                op(urem),
                legacy.clauses.len(),
                match old {
                    Some(true) => ms(t_old),
                    Some(false) => "SAT (!)".to_string(),
                    None => format!("deadline ({} s)", deadline.as_secs()),
                },
                folded.clauses.len(),
                ms(t_new),
                ms(t_all)
            );
        }
    }
}
