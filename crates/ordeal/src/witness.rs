//! The independently re-checkable SAT witness (TR-038 / #133, design in
//! docs/design/sat-witness.md) — the SAT twin of [`Certificate`].
//!
//! Always compiled (no feature gate, no dependencies): the witness is a
//! plain data structure plus the trusted recheck, and since #162 / TR-045
//! the shipped CLI emits it on every `sat` verdict (`--format json`), so
//! both verdict directions are evidence at the command line, not only in
//! the API. The `ordeal-cert/v1` JSON envelope (serde) stays behind the
//! `cert-bundle` feature in [`crate::cert_bundle`]; the canonical texts and
//! content hashes it embeds are computed HERE so the CLI's witness block
//! and the API's bundle are byte-for-byte the same witness.

use crate::sha256::sha256_hex;
use crate::solver::{Certificate, Model};

/// The result of [`crate::Solver::check_with_witness`] (TR-038): like
/// [`crate::CheckResult`] but `Sat` carries an independently
/// re-checkable [`SatCertificate`] instead of a bare model.
#[derive(Clone, Debug)]
pub enum WitnessCheckResult {
    /// Satisfiable, with a witness the trusted crate already validated.
    Sat(SatCertificate),
    /// Unsatisfiable, with the LRAT certificate the checker validated.
    Unsat(Certificate),
    /// No claim (identical semantics to [`crate::CheckResult::Unknown`]).
    Unknown,
}

/// The `witness.encoding` value: `assignment` is a `0`/`1` string whose
/// first character is DIMACS variable 1 (LSB-first per model variable in
/// the bit map). Readers reject any other encoding.
pub const WITNESS_ENCODING: &str = "bitstring-lsb-var1";

/// An independently re-checkable SAT verdict — the SAT twin of
/// [`Certificate`] (TR-038 / #133, docs/design/sat-witness.md): the
/// model, the CNF it satisfies, the FULL satisfying assignment (inputs
/// and Tseitin auxiliaries), and the map from each model variable's bits
/// to signed CNF literals. [`SatCertificate::recheck`] re-establishes
/// the verdict via the trusted `ordeal-lrat` crate with zero solver
/// trust: every clause is checked satisfied, and every advertised model
/// binding is checked consistent with the assignment.
#[derive(Clone, Debug)]
pub struct SatCertificate {
    /// The decoded model (what a consumer reads).
    pub model: Model,
    /// The CNF the assignment satisfies (same clauses an Unsat would
    /// have refuted — the term↔CNF gap is carried by the blaster proofs
    /// in both directions).
    pub cnf: Vec<Vec<i32>>,
    /// `assignment[i]` is the value of DIMACS variable `i + 1`.
    pub assignment: Vec<bool>,
    /// Per model variable: (name, width, LSB-first signed CNF literals —
    /// a negative literal means the bit is that variable's complement).
    pub bit_map: Vec<(String, u32, Vec<i32>)>,
}

/// Why a SAT witness recheck failed.
#[derive(Debug)]
pub enum SatRecheckError {
    /// The trusted kernel rejected the witness (unsatisfied clause,
    /// range error, or a binding/assignment disagreement).
    Witness(ordeal_lrat::SatWitnessError),
    /// A model binding has no bit-map entry — the advertised model is
    /// not covered by the witness.
    UnmappedBinding(String),
    /// A binding's width disagrees with its bit-map entry.
    WidthMismatch(String),
}

impl std::fmt::Display for SatRecheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SatRecheckError::Witness(e) => write!(f, "witness rejected: {e:?}"),
            SatRecheckError::UnmappedBinding(n) => {
                write!(f, "model binding '{n}' has no bit-map entry")
            }
            SatRecheckError::WidthMismatch(n) => {
                write!(f, "model binding '{n}' width disagrees with its bit map")
            }
        }
    }
}

impl std::error::Error for SatRecheckError {}

impl SatCertificate {
    /// Re-establish `Sat` independently of the solver: the trusted crate
    /// checks every clause satisfied and every model binding consistent.
    pub fn recheck(&self) -> Result<(), SatRecheckError> {
        ordeal_lrat::check_sat(&self.cnf, &self.assignment).map_err(SatRecheckError::Witness)?;
        for (name, value) in &self.model.assignments {
            let Some((_, width, bits)) = self.bit_map.iter().find(|(n, _, _)| n == name) else {
                return Err(SatRecheckError::UnmappedBinding(name.clone()));
            };
            if bits.len() != *width as usize {
                return Err(SatRecheckError::WidthMismatch(name.clone()));
            }
            ordeal_lrat::check_binding(&self.assignment, bits, *value)
                .map_err(SatRecheckError::Witness)?;
        }
        Ok(())
    }

    /// The witness assignment as a `0`/`1` string, `assignment[0]` first
    /// (variable 1) — the [`WITNESS_ENCODING`] text.
    #[must_use]
    pub fn assignment_bitstring(&self) -> String {
        assignment_bitstring(&self.assignment)
    }

    /// `sha256(assignment_bitstring)` — the bundle's `assignment_sha256`
    /// (rivet: `witness-sha256`).
    #[must_use]
    pub fn assignment_sha256(&self) -> String {
        sha256_hex(self.assignment_bitstring().as_bytes())
    }

    /// `sha256(canonical bit-map text)` — the bundle's `bit_map_sha256`
    /// (rivet: `bit-map-sha256`).
    #[must_use]
    pub fn bit_map_sha256(&self) -> String {
        sha256_hex(bit_map_canonical_text(&self.bit_map).as_bytes())
    }

    /// `sha256(DIMACS clause text)` — the bundle's `problem_sha256`
    /// (rivet: `cnf-sha256`), over the same canonical text as UNSAT.
    #[must_use]
    pub fn problem_sha256(&self) -> String {
        sha256_hex(cnf_text(&self.cnf).as_bytes())
    }
}

/// The witness assignment as a `0`/`1` string, `assignment[0]` first
/// (variable 1). Stable and diff-friendly for hashing.
pub(crate) fn assignment_bitstring(assignment: &[bool]) -> String {
    let mut s = String::with_capacity(assignment.len());
    for &b in assignment {
        s.push(if b { '1' } else { '0' });
    }
    s
}

/// Canonical text of the bit map for hashing: `name width l1 l2 …\n` per
/// entry, in-order.
pub(crate) fn bit_map_canonical_text(bit_map: &[(String, u32, Vec<i32>)]) -> String {
    let mut s = String::new();
    for (name, width, bits) in bit_map {
        s.push_str(name);
        s.push(' ');
        s.push_str(&width.to_string());
        for b in bits {
            s.push(' ');
            s.push_str(&b.to_string());
        }
        s.push('\n');
    }
    s
}

/// Canonical text form of the CNF for hashing and the `problem` block:
/// DIMACS clause lines (`lit* 0`), one per clause, `\n`-separated.
pub(crate) fn cnf_text(cnf: &[Vec<i32>]) -> String {
    let mut s = String::new();
    for clause in cnf {
        for lit in clause {
            s.push_str(&lit.to_string());
            s.push(' ');
        }
        s.push_str("0\n");
    }
    s
}
