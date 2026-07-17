//! Verus VC ingestion: lift `by (bit_vector)` obligations out of a Verus SMT
//! log so the obligation **Verus actually checked** is discharged with a
//! re-checkable certificate (TR-023 / FEAT-009, issue #65).
//!
//! # Why this exists
//!
//! A consumer like gale discharges its `by (bit_vector)` leaves through Verus →
//! **unchecked Z3**, and cites "Verus SMT/Z3" as ASIL-D evidence. The obvious
//! workaround — hand-transcribing each lemma into an `.smt2` file — makes the
//! certificate prove *the transcription*, not the obligation. Across ~64 leaves
//! that transcription gap is the whole risk. Reading Verus's own emitted query
//! closes it: the bytes checked here are the bytes Verus sent to Z3.
//!
//! # What Verus emits
//!
//! With `--log-all` (or `--log smt`), Verus writes one file per **spun-off**
//! query, and says *why* it spun it off:
//!
//! ```text
//! ;; MODULE 'root module'
//! ;; cpu_mask.rs:179:9: 179:15 (#0)
//! ;; query spun off because: bitvector      <-- the discriminator
//! ...prelude (Fuel, Poly, ~85 quantified vstd axioms)...
//! ;; cpu_mask.rs:179:9: 179:15 (#0)
//! (set-option :tactic.default_tactic sat)   <-- Z3 switched to bit-blasting
//! (set-option :smt.ematching false)         <-- so the prelude goes inert
//! (declare-const cpu_id! (_ BitVec 32))
//! (assert (bvult cpu_id! ((_ zero_extend 26) (_ bv32 6))))
//! (declare-const %%location_label%%0 Bool)
//! (assert (not (=> %%location_label%%0 ...)))
//! (check-sat)
//! ```
//!
//! The bit-blast block references only its own constants; the prelude's
//! quantifiers are inert for it (`ematching` is off). Notably it contains **no
//! `let` and no `define-fun`** — measured against verus 0.2026.02.15.61aa1bf,
//! the release `rules_verus` pins.
//!
//! # Why slicing is sound
//!
//! [`extract`] takes a **contiguous tail** of the query, so the assertions it
//! keeps are a *subset* of the ones Verus sent. Dropping assertions only makes
//! `UNSAT` **harder** to reach (fewer constraints ⇒ more models), so:
//!
//! > a sliced query that is UNSAT ⇒ the obligation Verus posed holds.
//!
//! A mis-slice can therefore lose a proof (reporting `Sat`/`Unknown`, which a
//! caller must treat conservatively) but can never manufacture one. Any symbol
//! the goal needs but the slice dropped surfaces as an undeclared-symbol parse
//! error rather than a silently different problem.

use std::fmt;

/// Verus's own marker for a query it split out for bit-vector reasoning.
/// Semantic, and emitted by Verus itself — not a guess about Z3 tactics.
const BITVECTOR_MARKER: &str = ";; query spun off because: bitvector";

/// Verus switches Z3 into bit-blasting mode immediately before the block.
const BITBLAST_MARKER: &str = "tactic.default_tactic sat";

/// Why a Verus log could not be turned into a QF_BV obligation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerusError {
    /// The log is not a `by (bit_vector)` query (no spin-off marker). The
    /// caller is pointed at a prelude dump (`root.smt2`) or an ordinary
    /// query, whose full encoding is quantified and outside the fragment.
    NotBitVector,
    /// The spin-off marker is present but the bit-blast block is not, so the
    /// file's shape is not the one this reader was built against.
    NoBitBlastBlock,
    /// The block never reaches a `(check-sat)`.
    NoCheckSat,
}

impl fmt::Display for VerusError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VerusError::NotBitVector => write!(
                f,
                "not a `by (bit_vector)` query: no `{BITVECTOR_MARKER}` marker \
                 (a Verus prelude dump such as root.smt2, or an ordinary \
                 quantified query, is outside the QF_BV fragment)"
            ),
            VerusError::NoBitBlastBlock => write!(
                f,
                "bitvector query has no `{BITBLAST_MARKER}` block — unexpected Verus log shape"
            ),
            VerusError::NoCheckSat => write!(f, "bitvector block has no `(check-sat)`"),
        }
    }
}

impl std::error::Error for VerusError {}

/// One `by (bit_vector)` obligation lifted from a Verus log.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BvObligation {
    /// The source location Verus recorded (e.g. `cpu_mask.rs:179:9: 179:15`),
    /// so a verdict or certificate can be attributed to the lemma it proves.
    pub location: Option<String>,
    /// A self-contained QF_BV script ready for [`crate::smtlib::solve_str`].
    pub script: String,
}

/// Lift the `by (bit_vector)` obligation out of one Verus query log.
///
/// Returns [`VerusError::NotBitVector`] unless Verus itself marked the query as
/// spun off for bitvector reasoning — this reader never *assumes* a log is
/// QF_BV, because the surrounding Verus encoding is quantified and would be
/// silently wrong to treat as the fragment.
pub fn extract(log: &str) -> Result<BvObligation, VerusError> {
    if !log.contains(BITVECTOR_MARKER) {
        return Err(VerusError::NotBitVector);
    }
    let lines: Vec<&str> = log.lines().collect();

    // The bit-blast block is the LAST such marker: Verus emits the prelude
    // first, then reconfigures Z3 immediately before the goal.
    let start = lines
        .iter()
        .rposition(|l| l.contains(BITBLAST_MARKER))
        .ok_or(VerusError::NoBitBlastBlock)?;
    let end = lines[start..]
        .iter()
        .position(|l| l.trim() == "(check-sat)")
        .map(|i| start + i)
        .ok_or(VerusError::NoCheckSat)?;

    // The nearest preceding `;; <file>:<line>:<col>` comment names the lemma.
    let location = lines[..start]
        .iter()
        .rev()
        .find(|l| l.starts_with(";; ") && l.contains(".rs:"))
        .map(|l| l.trim_start_matches(";; ").trim().to_string());

    // Keep the block verbatim minus solver-configuration noise, which carries
    // no semantics: `set-option` tunes Z3, `get-info` asks for statistics.
    let mut out = String::from("(set-logic QF_BV)\n");
    for line in &lines[start..=end] {
        let t = line.trim_start();
        if t.starts_with("(set-option") || t.starts_with("(get-info") {
            continue;
        }
        out.push_str(line);
        out.push('\n');
    }
    Ok(BvObligation {
        location,
        script: out,
    })
}

/// Whether a log is a `by (bit_vector)` query at all — lets a caller skip the
/// prelude dumps in a `--log-all` directory without treating them as errors.
pub fn is_bitvector_query(log: &str) -> bool {
    log.contains(BITVECTOR_MARKER)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// gale's OWN `cpu_mask.rs` obligation, as logged by verus
    /// 0.2026.02.15.61aa1bf (the release `rules_verus` pins, sha256-identical
    /// to the binary gale verifies with) during a real verification of gale's
    /// crate — 1159 verified, 0 errors. Not a reproduction: this is the query
    /// gale's ASIL-D evidence currently rests on, sent to unchecked Z3.
    const REAL_LOG: &str = include_str!("../tests/fixtures/verus_gale_cpu_mask_raw.smt2");

    /// gale's `mpu.rs:98` `is_power_of_two` obligation — a BICONDITIONAL, so
    /// it carries the boolean `=` (`<==>`) idiom, and 240 prelude quantifiers
    /// for the slicer to keep out.
    const REAL_MPU_LOG: &str = include_str!("../tests/fixtures/verus_gale_mpu_pow2_raw.smt2");

    #[test]
    fn extracts_the_bitvector_block_from_a_real_verus_log() {
        let o = extract(REAL_LOG).expect("real Verus log must yield an obligation");
        assert!(
            o.script.starts_with("(set-logic QF_BV)"),
            "slice must be a standalone QF_BV script"
        );
        assert!(
            o.script.contains("(check-sat)"),
            "slice must end in check-sat"
        );
        assert!(
            o.script.contains("%%location_label%%0"),
            "slice must carry the real goal, got: {}",
            &o.script[..200.min(o.script.len())]
        );
    }

    /// The slice must NOT drag in the prelude: ~85 quantified vstd axioms sit
    /// above the block, and a `forall` would put the query outside the closed
    /// fragment (the reader would reject it, so this failing means the
    /// boundary is wrong, not that the solver is).
    #[test]
    fn slice_excludes_the_quantified_prelude() {
        let o = extract(REAL_LOG).unwrap();
        assert!(
            REAL_LOG.contains("forall"),
            "fixture should contain the prelude's quantifiers"
        );
        assert!(
            !o.script.contains("forall"),
            "the slice must not contain quantifiers"
        );
        assert!(
            !o.script.contains("declare-datatypes") && !o.script.contains("declare-sort"),
            "the slice must not contain the prelude's sorts/datatypes"
        );
    }

    /// Solver configuration carries no semantics and must not reach the reader.
    #[test]
    fn slice_drops_solver_configuration() {
        let o = extract(REAL_LOG).unwrap();
        assert!(!o.script.contains("set-option"));
        assert!(!o.script.contains("get-info"));
    }

    #[test]
    fn reports_the_source_location() {
        let o = extract(REAL_LOG).unwrap();
        let loc = o.location.expect("Verus records a source location");
        assert!(
            loc.contains(".rs:"),
            "expected a file:line location, got {loc}"
        );
    }

    /// A prelude dump (`root.smt2`) or an ordinary query is quantified and is
    /// NOT QF_BV. Refusing it is the point: silently slicing one would hand
    /// the solver a problem it cannot faithfully model.
    #[test]
    fn refuses_a_log_that_is_not_a_bitvector_query() {
        let ordinary = "(declare-const x Int)\n(assert (forall ((y Int)) (> y 0)))\n(check-sat)\n";
        assert_eq!(extract(ordinary), Err(VerusError::NotBitVector));
        assert!(!is_bitvector_query(ordinary));
        assert!(is_bitvector_query(REAL_LOG));
    }

    #[test]
    fn marked_but_malformed_logs_error_rather_than_guess() {
        let no_block = format!("{BITVECTOR_MARKER}\n(assert true)\n(check-sat)\n");
        assert_eq!(extract(&no_block), Err(VerusError::NoBitBlastBlock));

        let no_check = format!("{BITVECTOR_MARKER}\n(set-option :{BITBLAST_MARKER})\n(assert x)\n");
        assert_eq!(extract(&no_check), Err(VerusError::NoCheckSat));
    }

    /// gale's `mpu.rs:98` biconditional — the `<==>` idiom, which Verus emits
    /// as `=` over BOOLEAN operands. This is the obligation that exposed the
    /// gap: before boolean `=` was supported the reader died with
    /// `unsupported: bitvector operator 'and'`.
    #[test]
    fn gale_mpu_biconditional_discharges() {
        let o = extract(REAL_MPU_LOG).expect("gale's mpu obligation must lift");
        assert!(
            !o.script.contains("forall"),
            "240 prelude quantifiers must stay out of the slice"
        );
        let outcome = crate::smtlib::solve_str(&o.script).expect("slice must parse");
        match outcome.result.expect("has check-sat") {
            crate::CheckResult::Unsat(cert) => {
                cert.recheck().expect("certificate must re-check");
            }
            other => panic!("gale mpu.rs:98 is_power_of_two must be UNSAT, got {other:?}"),
        }
    }

    /// End-to-end: the lifted obligation discharges to a checker-validated
    /// UNSAT. This is #65's whole claim — the obligation Verus checked, now
    /// backed by a certificate anyone can re-validate.
    #[test]
    fn lifted_obligation_discharges_with_a_recheckable_certificate() {
        let o = extract(REAL_LOG).unwrap();
        let outcome = crate::smtlib::solve_str(&o.script).expect("slice must parse");
        match outcome.result.expect("script has a check-sat") {
            crate::CheckResult::Unsat(cert) => {
                cert.recheck().expect("certificate must re-check");
            }
            other => panic!("gale's cpu_mask obligation must be UNSAT, got {other:?}"),
        }
    }
}
