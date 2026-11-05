//! The v1 certificate pair and the model type (TR-075: extracted from
//! `ordeal::solver`, which re-exports them unchanged). [`Certificate`] is
//! the CNF + LRAT pair; [`Certificate::recheck`] runs the trusted
//! `ordeal_lrat::check` over it, exactly as the solver does before it
//! returns `Unsat`.

/// A machine-checkable UNSAT certificate — a **self-contained, portable proof
/// object**.
///
/// The solver (untrusted) emits an LRAT proof; the `ordeal-lrat` checker
/// (the only trusted component) validated exactly these bytes against
/// [`cnf`](Certificate::cnf) before this value was constructed. Because the
/// certificate carries *both halves* — the DIMACS CNF and the LRAT refutation —
/// a consumer can re-establish the UNSAT verdict **with zero trust in ordeal**
/// by calling [`recheck`](Certificate::recheck) (or running `ordeal_lrat::check`
/// directly). That independent re-check is the whole point: an UNSAT is
/// believable because *you* can validate the proof, not because the solver says
/// so. This is what a translation validator (synth) needs to turn a proof-less
/// solver verdict into checkable evidence.
#[derive(Clone, Debug, Default)]
pub struct Certificate {
    /// The checker-validated textual LRAT proof bytes.
    pub lrat: Vec<u8>,
    /// The exact DIMACS CNF clause set the LRAT proof refutes — the other half
    /// of the checkable pair. Together with [`lrat`](Certificate::lrat) it is a
    /// complete, independently-verifiable proof of unsatisfiability.
    pub cnf: Vec<Vec<i32>>,
}

/// Why an independent [`Certificate::recheck`] could not confirm the proof.
#[derive(Debug)]
pub enum CertificateError {
    /// The LRAT bytes were not valid UTF-8 (only possible for a hand-built
    /// certificate; ones ordeal emits are always text).
    NotText,
    /// The trusted `ordeal-lrat` checker rejected the LRAT proof against the
    /// carried CNF.
    Rejected(ordeal_lrat::CheckError),
}

impl std::fmt::Display for CertificateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CertificateError::NotText => write!(f, "LRAT certificate is not valid UTF-8"),
            CertificateError::Rejected(e) => write!(f, "checker rejected certificate: {e:?}"),
        }
    }
}

impl std::error::Error for CertificateError {}

impl Certificate {
    /// The LRAT proof as text, if the bytes are valid UTF-8 (ordeal-emitted
    /// certificates always are).
    pub fn lrat_text(&self) -> Option<&str> {
        std::str::from_utf8(&self.lrat).ok()
    }

    /// Independently re-validate this certificate with the trusted `ordeal-lrat`
    /// checker — the *same* check ordeal ran internally before returning
    /// `Unsat`, reproducible by any consumer with no faith in the (untrusted)
    /// solver. `Ok(())` ⟺ the LRAT proof refutes [`cnf`](Certificate::cnf), so
    /// the conjunction really is unsatisfiable.
    pub fn recheck(&self) -> Result<(), CertificateError> {
        let text = self.lrat_text().ok_or(CertificateError::NotText)?;
        ordeal_lrat::check(&self.cnf, text).map_err(CertificateError::Rejected)
    }
}

/// A satisfying assignment (counterexample) for a SAT query.
///
/// Each entry binds a variable name to the concrete bitvector value (as a
/// `u128`, zero-extended for widths below 128) that witnesses satisfiability.
#[derive(Clone, Debug, Default)]
pub struct Model {
    /// Variable-name → value assignments.
    pub assignments: Vec<(String, u128)>,
}
