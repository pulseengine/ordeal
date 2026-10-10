//! The certificate-carried query (issue #192 phase 4, `ordeal-cert/v2`):
//! the term DAG the solver lowered, kept next to the certificate so that a
//! consumer re-checks the QUERY, not a CNF it has to take on faith.
//!
//! Since phase 3 the solver lowers every query through the proven
//! `blast_kernel::encode` / `compact` / `tseitin` (now in the trusted
//! `ordeal-lrat` crate). A v1 certificate carries the CNF those produced
//! plus the LRAT proof; `recheck()` proves the CNF unsatisfiable, and the
//! step from the query to the CNF is the solver's word. A
//! [`QueryCertificate`] carries, in addition, the lowered query itself —
//! the [`QueryDag`]: the `DagNode` list, its constant table, the asserted
//! roots and the compaction hints — and its `recheck()` calls
//! `ordeal_lrat::check_query`, which re-runs the proven lowering over the
//! DAG inside the trusted crate and checks the LRAT proof against the CNF
//! *it* produced (`kernel.spec.check_query_sound`, `lean/QueryCheck.lean`:
//! accepted ⟹ no assignment to the DAG's variables makes every root
//! true). What stays untrusted is the untrusted `dag.rs` builder's choice of
//! DAG for the assertions, canon, lowering of derived ops, the sliver and
//! the front ends (`docs/formal-verification.md`).
//!
//! Always compiled (no feature gate, no dependencies): like the SAT witness
//! this is plain data plus the trusted recheck; the `ordeal-cert/v2` JSON
//! envelope (serde) is behind the `cert-bundle` feature in
//! [`crate::cert_bundle`], and the CLI emits the same block with
//! `--with-query`. The canonical text and the content hash are computed
//! HERE so the CLI's block and the API's bundle are byte-for-byte the same
//! query.

use crate::blast_kernel as k;
use crate::sha256::sha256_hex;
use crate::solver::Certificate;
use crate::witness::SatCertificate;

/// The `query.encoding` value of a DAG over the phase-3 node kinds: a
/// `DagNode` list (`[op, args…]` per node, operands as indices of earlier
/// nodes), a `0`/`1` constant table, root indices and compaction hints.
/// Since #192 phase 5 a DAG that uses one of the five derived-op node kinds
/// (`bvnot`, `neg`, `rotl`, `sdiv`, `srem`) is tagged [`QUERY_ENCODING_V2`]
/// instead, so a v0.27.0 reader refuses it rather than misreading it; a DAG
/// without them keeps this tag, and v0.27.0 readers keep reading it.
/// [`QueryDag::encoding`] picks the tag; readers accept both and reject any
/// other.
pub const QUERY_ENCODING: &str = "ordeal-dag/v1";

/// The `query.encoding` value of a DAG that uses a derived-op node kind
/// (`ordeal-dag/v1` plus `bvnot`, `neg`, `rotl`, `sdiv`, `srem`; #192
/// phase 5). Readers from v0.28.0 on.
pub const QUERY_ENCODING_V2: &str = "ordeal-dag/v2";

/// Is `encoding` one this reader decodes?
pub fn encoding_supported(encoding: &str) -> bool {
    encoding == QUERY_ENCODING || encoding == QUERY_ENCODING_V2
}

/// The lowered query: exactly the inputs the proven lowering (and the
/// trusted re-check) consumes.
#[derive(Clone, Default, PartialEq, Eq)]
pub struct QueryDag {
    /// The term DAG, topologically ordered (every operand is an earlier
    /// node) — the closed `term.rs` fragment.
    pub nodes: Vec<k::DagNode>,
    /// The constant table the `Const(s, w)` nodes slice, LSB first.
    pub bits: Vec<bool>,
    /// The asserted boolean nodes (one per assertion).
    pub roots: Vec<usize>,
    /// The structural-hashing hints the solver compacted with (untrusted
    /// advice: `compact` checks each one; a wrong hint costs a duplicate
    /// gate, never a wrong value). Carried so the re-encoded CNF is the
    /// CNF the proof refutes, gate for gate.
    pub hints: Vec<usize>,
}

impl std::fmt::Debug for QueryDag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("QueryDag")
            .field("nodes", &self.nodes.len())
            .field("bits", &self.bits.len())
            .field("roots", &self.roots)
            .field("hints", &self.hints.len())
            .field("sha256", &self.sha256())
            .finish()
    }
}

/// A node as its `[op, args…]` spelling: the operator mnemonic and its
/// integer arguments in the order the constructor takes them
/// (`Var(w)` → `("var", [w])`, `Const(s, w)` → `("const", [s, w])`,
/// `Extract(hi, lo, a)` → `("extract", [hi, lo, a])`, `ZeroExt(a, by)` →
/// `("zero_ext", [a, by])`, `Ite(c, t, e)` → `("ite", [c, t, e])`, binary
/// ops → `(op, [a, b])`, `Not(a)` → `("not", [a])`).
pub fn node_op(node: &k::DagNode) -> (&'static str, Vec<usize>) {
    use k::DagNode as N;
    match *node {
        N::Var(w) => ("var", vec![w]),
        N::Const(s, w) => ("const", vec![s, w]),
        N::Add(a, b) => ("add", vec![a, b]),
        N::Sub(a, b) => ("sub", vec![a, b]),
        N::Mul(a, b) => ("mul", vec![a, b]),
        N::Udiv(a, b) => ("udiv", vec![a, b]),
        N::Urem(a, b) => ("urem", vec![a, b]),
        N::And(a, b) => ("and", vec![a, b]),
        N::Or(a, b) => ("or", vec![a, b]),
        N::Xor(a, b) => ("xor", vec![a, b]),
        N::Shl(a, b) => ("shl", vec![a, b]),
        N::Lshr(a, b) => ("lshr", vec![a, b]),
        N::Ashr(a, b) => ("ashr", vec![a, b]),
        N::Rotr(a, b) => ("rotr", vec![a, b]),
        N::Extract(hi, lo, a) => ("extract", vec![hi, lo, a]),
        N::Concat(a, b) => ("concat", vec![a, b]),
        N::ZeroExt(a, by) => ("zero_ext", vec![a, by]),
        N::SignExt(a, by) => ("sign_ext", vec![a, by]),
        N::Ite(c, t, e) => ("ite", vec![c, t, e]),
        N::Eq(a, b) => ("eq", vec![a, b]),
        N::Ne(a, b) => ("ne", vec![a, b]),
        N::Ult(a, b) => ("ult", vec![a, b]),
        N::Ule(a, b) => ("ule", vec![a, b]),
        N::Ugt(a, b) => ("ugt", vec![a, b]),
        N::Uge(a, b) => ("uge", vec![a, b]),
        N::Slt(a, b) => ("slt", vec![a, b]),
        N::Sle(a, b) => ("sle", vec![a, b]),
        N::Sgt(a, b) => ("sgt", vec![a, b]),
        N::Sge(a, b) => ("sge", vec![a, b]),
        N::Not(a) => ("not", vec![a]),
        N::BoolAnd(a, b) => ("bool_and", vec![a, b]),
        N::BoolOr(a, b) => ("bool_or", vec![a, b]),
        N::BvNot(a) => ("bvnot", vec![a]),
        N::Neg(a) => ("neg", vec![a]),
        N::Rotl(a, b) => ("rotl", vec![a, b]),
        N::Sdiv(a, b) => ("sdiv", vec![a, b]),
        N::Srem(a, b) => ("srem", vec![a, b]),
    }
}

/// Is this one of the five derived-op node kinds of #192 phase 5 (the ones
/// `ordeal-dag/v1` cannot express)?
pub fn node_is_derived(node: &k::DagNode) -> bool {
    use k::DagNode as N;
    matches!(
        node,
        N::BvNot(_) | N::Neg(_) | N::Rotl(_, _) | N::Sdiv(_, _) | N::Srem(_, _)
    )
}

/// The inverse of [`node_op`]: `None` for an unknown mnemonic or a wrong
/// argument count (a reader reports that as malformed; well-formedness of
/// the operands is the trusted `dag_wf`'s job, not the reader's).
pub fn node_from_op(op: &str, args: &[usize]) -> Option<k::DagNode> {
    use k::DagNode as N;
    let one = || if args.len() == 1 { Some(args[0]) } else { None };
    let two = || {
        if args.len() == 2 {
            Some((args[0], args[1]))
        } else {
            None
        }
    };
    let three = || {
        if args.len() == 3 {
            Some((args[0], args[1], args[2]))
        } else {
            None
        }
    };
    Some(match op {
        "var" => N::Var(one()?),
        "const" => {
            let (s, w) = two()?;
            N::Const(s, w)
        }
        "add" => {
            let (a, b) = two()?;
            N::Add(a, b)
        }
        "sub" => {
            let (a, b) = two()?;
            N::Sub(a, b)
        }
        "mul" => {
            let (a, b) = two()?;
            N::Mul(a, b)
        }
        "udiv" => {
            let (a, b) = two()?;
            N::Udiv(a, b)
        }
        "urem" => {
            let (a, b) = two()?;
            N::Urem(a, b)
        }
        "and" => {
            let (a, b) = two()?;
            N::And(a, b)
        }
        "or" => {
            let (a, b) = two()?;
            N::Or(a, b)
        }
        "xor" => {
            let (a, b) = two()?;
            N::Xor(a, b)
        }
        "shl" => {
            let (a, b) = two()?;
            N::Shl(a, b)
        }
        "lshr" => {
            let (a, b) = two()?;
            N::Lshr(a, b)
        }
        "ashr" => {
            let (a, b) = two()?;
            N::Ashr(a, b)
        }
        "rotr" => {
            let (a, b) = two()?;
            N::Rotr(a, b)
        }
        "extract" => {
            let (hi, lo, a) = three()?;
            N::Extract(hi, lo, a)
        }
        "concat" => {
            let (a, b) = two()?;
            N::Concat(a, b)
        }
        "zero_ext" => {
            let (a, by) = two()?;
            N::ZeroExt(a, by)
        }
        "sign_ext" => {
            let (a, by) = two()?;
            N::SignExt(a, by)
        }
        "ite" => {
            let (c, t, e) = three()?;
            N::Ite(c, t, e)
        }
        "eq" => {
            let (a, b) = two()?;
            N::Eq(a, b)
        }
        "ne" => {
            let (a, b) = two()?;
            N::Ne(a, b)
        }
        "ult" => {
            let (a, b) = two()?;
            N::Ult(a, b)
        }
        "ule" => {
            let (a, b) = two()?;
            N::Ule(a, b)
        }
        "ugt" => {
            let (a, b) = two()?;
            N::Ugt(a, b)
        }
        "uge" => {
            let (a, b) = two()?;
            N::Uge(a, b)
        }
        "slt" => {
            let (a, b) = two()?;
            N::Slt(a, b)
        }
        "sle" => {
            let (a, b) = two()?;
            N::Sle(a, b)
        }
        "sgt" => {
            let (a, b) = two()?;
            N::Sgt(a, b)
        }
        "sge" => {
            let (a, b) = two()?;
            N::Sge(a, b)
        }
        "not" => N::Not(one()?),
        "bool_and" => {
            let (a, b) = two()?;
            N::BoolAnd(a, b)
        }
        "bool_or" => {
            let (a, b) = two()?;
            N::BoolOr(a, b)
        }
        "bvnot" => N::BvNot(one()?),
        "neg" => N::Neg(one()?),
        "rotl" => {
            let (a, b) = two()?;
            N::Rotl(a, b)
        }
        "sdiv" => {
            let (a, b) = two()?;
            N::Sdiv(a, b)
        }
        "srem" => {
            let (a, b) = two()?;
            N::Srem(a, b)
        }
        _ => return None,
    })
}

/// The constant table as a `0`/`1` string, `bits[0]` first.
pub fn bits_string(bits: &[bool]) -> String {
    let mut s = String::with_capacity(bits.len());
    for &b in bits {
        s.push(if b { '1' } else { '0' });
    }
    s
}

/// Parse a `0`/`1` string back into a constant table; `None` on any other
/// character.
pub fn bits_from_string(s: &str) -> Option<Vec<bool>> {
    let mut out = Vec::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '0' => out.push(false),
            '1' => out.push(true),
            _ => return None,
        }
    }
    Some(out)
}

fn push_usizes(s: &mut String, xs: &[usize]) {
    for x in xs {
        s.push(' ');
        s.push_str(&x.to_string());
    }
}

impl QueryDag {
    /// Does the DAG use one of the derived-op node kinds of #192 phase 5?
    #[must_use]
    pub fn has_derived(&self) -> bool {
        self.nodes.iter().any(node_is_derived)
    }

    /// The encoding tag this DAG is emitted under: the lowest one that can
    /// express it — [`QUERY_ENCODING`] (`ordeal-dag/v1`, readable by
    /// v0.27.0) unless a derived-op node is present, then
    /// [`QUERY_ENCODING_V2`].
    #[must_use]
    pub fn encoding(&self) -> &'static str {
        if self.has_derived() {
            QUERY_ENCODING_V2
        } else {
            QUERY_ENCODING
        }
    }

    /// The canonical text the content hash covers (stable, diff-friendly):
    /// the encoding tag ([`QueryDag::encoding`]), `nodes <n>`, one `<op>
    /// <args…>` line per node, then `bits <bitstring>`, `roots <r…>` and
    /// `hints <h…>`.
    pub fn canonical_text(&self) -> String {
        self.canonical_text_tagged(self.encoding())
    }

    /// [`QueryDag::canonical_text`] under an explicit encoding tag — what a
    /// reader hashes to verify a block that DECLARES its tag (a v1-tagged
    /// block hashes with the v1 tag even on a reader that would emit v2).
    pub fn canonical_text_tagged(&self, encoding: &str) -> String {
        let mut s = String::new();
        s.push_str(encoding);
        s.push('\n');
        s.push_str("nodes ");
        s.push_str(&self.nodes.len().to_string());
        s.push('\n');
        for n in &self.nodes {
            let (op, args) = node_op(n);
            s.push_str(op);
            push_usizes(&mut s, &args);
            s.push('\n');
        }
        s.push_str("bits ");
        s.push_str(&bits_string(&self.bits));
        s.push('\n');
        s.push_str("roots");
        push_usizes(&mut s, &self.roots);
        s.push('\n');
        s.push_str("hints");
        push_usizes(&mut s, &self.hints);
        s.push('\n');
        s
    }

    /// `sha256(canonical_text)` — the bundle's `query.sha256` (rivet:
    /// `query-sha256`). Integrity only: the verdict rests on the recheck.
    #[must_use]
    pub fn sha256(&self) -> String {
        sha256_hex(self.canonical_text().as_bytes())
    }

    /// [`QueryDag::sha256`] under an explicit encoding tag (see
    /// [`QueryDag::canonical_text_tagged`]).
    #[must_use]
    pub fn sha256_tagged(&self, encoding: &str) -> String {
        sha256_hex(self.canonical_text_tagged(encoding).as_bytes())
    }
}

/// A certificate together with the query it certifies (issue #192 phase
/// 4): the v1 pair (`certificate.cnf`, `certificate.lrat`) plus the lowered
/// [`QueryDag`]. [`QueryCertificate::recheck`] is the stronger re-check:
/// the trusted crate re-encodes the DAG itself and checks the proof
/// against the CNF *it* produced, so an accepted re-check proves the DAG
/// unsatisfiable — `kernel.spec.check_query_sound`.
#[derive(Clone, Debug)]
pub struct QueryCertificate {
    /// The v1 pair: the CNF the solver produced from the DAG, and the LRAT
    /// proof the checker validated against it. `certificate.recheck()` is
    /// the v1 (CNF-level) re-check, still available.
    pub certificate: Certificate,
    /// The lowered query the CNF was encoded from.
    pub query: QueryDag,
}

/// Why a [`QueryCertificate::recheck`] could not confirm the proof.
#[derive(Debug)]
pub enum QueryRecheckError {
    /// The LRAT bytes were not valid UTF-8 (only possible for a hand-built
    /// certificate).
    NotText,
    /// The trusted crate rejected: the DAG is malformed or too large, or
    /// the proof does not refute the CNF re-encoded from it.
    Rejected(ordeal_lrat::QueryCheckError),
    /// The trusted re-encoding of the DAG is not the CNF the certificate
    /// carries — the bundle is internally inconsistent (a v1 reader would
    /// be checking a different formula than the query's).
    CnfMismatch,
}

impl std::fmt::Display for QueryRecheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QueryRecheckError::NotText => write!(f, "LRAT certificate is not valid UTF-8"),
            QueryRecheckError::Rejected(e) => write!(f, "trusted query re-check rejected: {e}"),
            QueryRecheckError::CnfMismatch => write!(
                f,
                "the CNF re-encoded from the query differs from the carried CNF"
            ),
        }
    }
}

impl std::error::Error for QueryRecheckError {}

impl QueryCertificate {
    /// Re-establish the verdict at the QUERY level, with zero trust in the
    /// solver: `ordeal_lrat::check_query` checks the DAG well-formed
    /// (`dag_wf`), re-runs the proven lowering over it, and checks the LRAT
    /// proof against the CNF it produced. `Ok(())` ⟹ no assignment to the
    /// DAG's variables makes every root true (`check_query_sound`). The
    /// re-encoded CNF must also equal `certificate.cnf`, so the v1 pair a
    /// bundle carries for older readers is the query's CNF and not another.
    pub fn recheck(&self) -> Result<(), QueryRecheckError> {
        let text = self
            .certificate
            .lrat_text()
            .ok_or(QueryRecheckError::NotText)?;
        let q = &self.query;
        let cnf = ordeal_lrat::check_query(&q.nodes, &q.bits, &q.roots, &q.hints, text)
            .map_err(QueryRecheckError::Rejected)?;
        if cnf != self.certificate.cnf {
            return Err(QueryRecheckError::CnfMismatch);
        }
        Ok(())
    }
}

/// The result of [`crate::Solver::check_with_query`]: like
/// [`crate::witness::WitnessCheckResult`] but `Unsat` carries a
/// [`QueryCertificate`] — the certificate with the lowered query — whose
/// trusted re-check passed before it was returned.
#[derive(Clone, Debug)]
pub enum QueryCheckResult {
    /// Unsatisfiable, with the certificate and the query it refutes; the
    /// trusted `check_query` accepted it before return.
    Unsat(QueryCertificate),
    /// Satisfiable, with a witness the trusted crate already validated.
    Sat(SatCertificate),
    /// No claim (identical semantics to [`crate::CheckResult::Unknown`]).
    Unknown,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BoolTerm, BvTerm, Solver, Sort};

    fn var(name: &str, w: u32) -> BvTerm {
        BvTerm::Var {
            name: name.into(),
            sort: Sort::new(w),
        }
    }

    fn konst(v: u128, w: u32) -> BvTerm {
        BvTerm::Const {
            value: v,
            sort: Sort::new(w),
        }
    }

    /// `x + 5 == 3` and `x - 7 != 3 - 7 - 5 + ... `: an UNSAT query whose
    /// refutation depends on the constants — `(x + 5 = 3) ∧ (x ≠ 254)` at
    /// width 8 (x = 254 is the only solution of the first conjunct).
    fn unsat_query() -> Solver {
        let mut s = Solver::new();
        s.assert(BoolTerm::Eq(
            Box::new(BvTerm::Add(Box::new(var("x", 8)), Box::new(konst(5, 8)))),
            Box::new(konst(3, 8)),
        ));
        s.assert(BoolTerm::Ne(Box::new(var("x", 8)), Box::new(konst(254, 8))));
        s
    }

    fn unsat_cert() -> QueryCertificate {
        match unsat_query().check_with_query() {
            QueryCheckResult::Unsat(c) => c,
            other => panic!("expected Unsat, got {other:?}"),
        }
    }

    // rivet: verifies VER-062
    #[test]
    fn query_certificate_rechecks_through_the_trusted_crate() {
        let cert = unsat_cert();
        cert.recheck().expect("fresh query certificate re-checks");
        // The v1 pair inside is the usual checker-validated one.
        cert.certificate.recheck().expect("v1 pair re-checks");
        assert!(!cert.query.nodes.is_empty());
        assert_eq!(cert.query.roots.len(), 2);
        // Deterministic: same query, same bytes, same hash.
        assert_eq!(cert.query.sha256(), unsat_cert().query.sha256());
    }

    // rivet: verifies VER-062
    /// The phase-4 acceptance criterion (#192): flipping ONE constant bit
    /// of the query fails the recheck although the CNF and the proof are
    /// untouched — the trusted crate re-encodes the DAG it is given, and
    /// the proof no longer refutes (or the CNF no longer matches) that.
    #[test]
    fn flipping_one_constant_bit_fails_the_recheck_with_cnf_and_proof_untouched() {
        let mut cert = unsat_cert();
        let (cnf, lrat) = (cert.certificate.cnf.clone(), cert.certificate.lrat.clone());
        let mut rejected = 0;
        for i in 0..cert.query.bits.len() {
            cert.query.bits[i] = !cert.query.bits[i];
            let r = cert.recheck();
            assert_eq!(cert.certificate.cnf, cnf, "CNF must be untouched");
            assert_eq!(cert.certificate.lrat, lrat, "proof must be untouched");
            if r.is_err() {
                rejected += 1;
            }
            cert.query.bits[i] = !cert.query.bits[i];
        }
        // Every constant bit of this query influences its refutation.
        assert_eq!(
            rejected,
            cert.query.bits.len(),
            "every single-bit flip must be rejected"
        );
        cert.recheck().expect("restored query re-checks again");
    }

    // rivet: verifies VER-062
    /// Tampering with the DAG structure (not just a constant) is caught the
    /// same way; a malformed DAG is rejected by `dag_wf` before any
    /// encoding.
    #[test]
    fn structural_tampering_and_malformed_dags_are_rejected() {
        let mut cert = unsat_cert();
        // Swap the two roots' meaning: assert the negation of the first.
        let first_root = cert.query.roots[0];
        cert.query.nodes.push(k::DagNode::Not(first_root));
        let not_node = cert.query.nodes.len() - 1;
        cert.query.roots[0] = not_node;
        assert!(cert.recheck().is_err(), "negated root must not re-check");

        // A malformed DAG: an operand that is not an earlier node.
        let mut cert = unsat_cert();
        cert.query.nodes[0] = k::DagNode::Add(usize::MAX, 0);
        match cert.recheck() {
            Err(QueryRecheckError::Rejected(ordeal_lrat::QueryCheckError::Query(
                ordeal_lrat::QueryError::NodeNotWellFormed { node: 0 },
            ))) => {}
            other => panic!("expected NodeNotWellFormed at node 0, got {other:?}"),
        }
        // A root that is not boolean.
        let mut cert = unsat_cert();
        let var_node = cert
            .query
            .nodes
            .iter()
            .position(|n| matches!(n, k::DagNode::Var(_)))
            .expect("the query has a variable");
        cert.query.roots[0] = var_node;
        match cert.recheck() {
            Err(QueryRecheckError::Rejected(ordeal_lrat::QueryCheckError::Query(
                ordeal_lrat::QueryError::BadRoot { root: 0 },
            ))) => {}
            other => panic!("expected BadRoot 0, got {other:?}"),
        }
    }

    // rivet: verifies VER-062
    /// Wrong hints never make a wrong verdict: they change the gate
    /// sharing, so the re-encoded CNF is a different (equisatisfiable) CNF
    /// and the carried pair no longer matches it — `CnfMismatch`, not an
    /// accept of a formula the proof does not refute.
    #[test]
    fn hints_are_advice_not_trust() {
        let mut cert = unsat_cert();
        cert.query.hints = (0..cert.query.hints.len()).collect(); // share nothing
        match cert.recheck() {
            Err(QueryRecheckError::CnfMismatch | QueryRecheckError::Rejected(_)) => {}
            other => panic!("expected a rejection, got {other:?}"),
        }
    }

    // rivet: verifies VER-062
    /// `node_op` / `node_from_op` round-trip every constructor, and the
    /// canonical text pins the spelling.
    #[test]
    fn node_spelling_round_trips() {
        use k::DagNode as N;
        let all = [
            N::Var(8),
            N::Const(3, 8),
            N::Add(0, 1),
            N::Sub(0, 1),
            N::Mul(0, 1),
            N::Udiv(0, 1),
            N::Urem(0, 1),
            N::And(0, 1),
            N::Or(0, 1),
            N::Xor(0, 1),
            N::Shl(0, 1),
            N::Lshr(0, 1),
            N::Ashr(0, 1),
            N::Rotr(0, 1),
            N::Extract(7, 2, 0),
            N::Concat(0, 1),
            N::ZeroExt(0, 4),
            N::SignExt(0, 4),
            N::Ite(2, 0, 1),
            N::Eq(0, 1),
            N::Ne(0, 1),
            N::Ult(0, 1),
            N::Ule(0, 1),
            N::Ugt(0, 1),
            N::Uge(0, 1),
            N::Slt(0, 1),
            N::Sle(0, 1),
            N::Sgt(0, 1),
            N::Sge(0, 1),
            N::Not(2),
            N::BoolAnd(2, 3),
            N::BoolOr(2, 3),
            N::BvNot(0),
            N::Neg(0),
            N::Rotl(0, 1),
            N::Sdiv(0, 1),
            N::Srem(0, 1),
        ];
        for n in all {
            let (op, args) = node_op(&n);
            assert!(node_from_op(op, &args) == Some(n), "{op}");
            assert!(node_from_op(op, &[]).is_none(), "{op}: wrong arity");
        }
        assert!(node_from_op("bvfoo", &[0, 1]).is_none());
        let q = QueryDag {
            nodes: vec![N::Var(2), N::Const(0, 2), N::Eq(0, 1)],
            bits: vec![true, false],
            roots: vec![2],
            hints: vec![0, 1, 2],
        };
        assert_eq!(q.encoding(), QUERY_ENCODING);
        assert!(!q.has_derived());
        assert_eq!(
            q.canonical_text(),
            "ordeal-dag/v1\nnodes 3\nvar 2\nconst 0 2\neq 0 1\nbits 10\nroots 2\nhints 0 1 2\n"
        );
        assert_eq!(bits_from_string("10"), Some(vec![true, false]));
        assert_eq!(bits_from_string("1x"), None);
        // #192 phase 5: a derived-op node lifts the tag to ordeal-dag/v2,
        // and the hash follows the tag it is computed under.
        let q2 = QueryDag {
            nodes: vec![N::Var(2), N::Var(2), N::Sdiv(0, 1), N::Neg(2), N::Eq(2, 3)],
            bits: vec![],
            roots: vec![4],
            hints: vec![],
        };
        assert!(q2.has_derived());
        assert_eq!(q2.encoding(), QUERY_ENCODING_V2);
        assert_eq!(
            q2.canonical_text(),
            "ordeal-dag/v2\nnodes 5\nvar 2\nvar 2\nsdiv 0 1\nneg 2\neq 2 3\nbits \nroots 4\nhints\n"
        );
        assert_eq!(q2.sha256(), q2.sha256_tagged(QUERY_ENCODING_V2));
        assert_ne!(q2.sha256(), q2.sha256_tagged(QUERY_ENCODING));
        assert!(encoding_supported(QUERY_ENCODING) && encoding_supported(QUERY_ENCODING_V2));
        assert!(!encoding_supported("ordeal-dag/v3"));
    }

    /// #192 phase 5: a query whose refutation rests on `bvsdiv`'s semantics,
    /// as `check_with_query` lowers it — the DAG carries an `Sdiv` node
    /// (not its rewrite), the trusted crate re-checks it, and the block is
    /// tagged `ordeal-dag/v2`.
    fn sdiv_query_certificate() -> QueryCertificate {
        // `(a sdiv b) ≠ rewrite(a sdiv b)` at width 8: UNSAT only because
        // the node IS signed division (the rewrite's sign-mask construction
        // over `bvudiv`).
        let a = var("a", 8);
        let b = var("b", 8);
        let sdiv = BvTerm::Sdiv(Box::new(a.clone()), Box::new(b.clone()));
        let twin = crate::lowering::expand_bv(&sdiv).expect("sorted");
        let mut s = Solver::new();
        s.assert(BoolTerm::Ne(Box::new(sdiv), Box::new(twin)));
        match s.check_with_query() {
            QueryCheckResult::Unsat(c) => c,
            other => panic!("expected Unsat, got {other:?}"),
        }
    }

    // rivet: verifies VER-064
    /// The derived op reaches the certificate as ITS OWN node: the query
    /// block of an `(a sdiv b) ≠ rewrite(a sdiv b)` refutation holds an
    /// `Sdiv` node next to the rewrite's `Udiv`, is tagged `ordeal-dag/v2`,
    /// and re-checks through the trusted crate.
    #[test]
    fn derived_op_is_carried_as_its_own_node_and_rechecks() {
        let cert = sdiv_query_certificate();
        cert.recheck()
            .expect("the trusted crate re-encodes the Sdiv node");
        assert!(cert.query.has_derived());
        assert_eq!(cert.query.encoding(), QUERY_ENCODING_V2);
        let kinds: Vec<&str> = cert.query.nodes.iter().map(|n| node_op(n).0).collect();
        assert!(
            kinds.contains(&"sdiv"),
            "the query block carries the operation: {kinds:?}"
        );
        assert!(
            kinds.contains(&"udiv"),
            "the rewritten twin is next to it: {kinds:?}"
        );
        assert!(
            cert.query.canonical_text().starts_with("ordeal-dag/v2\n"),
            "the hash covers the v2 tag"
        );
    }

    // rivet: verifies VER-064
    /// The phase-5 negative control: change the `Sdiv` node of that
    /// certificate to `Udiv` (same operands, hash recomputed so integrity
    /// passes) with the CNF and the proof untouched — the recheck FAILS,
    /// because the trusted crate re-encodes `udiv` and the carried proof
    /// no longer refutes (nor matches) that CNF. The semantics differ (a
    /// negative dividend), so this is not a formatting accident.
    #[test]
    fn sdiv_node_swapped_to_udiv_fails_the_recheck() {
        let mut cert = sdiv_query_certificate();
        let (cnf, lrat) = (cert.certificate.cnf.clone(), cert.certificate.lrat.clone());
        let i = cert
            .query
            .nodes
            .iter()
            .position(|n| matches!(n, k::DagNode::Sdiv(_, _)))
            .expect("an Sdiv node");
        let k::DagNode::Sdiv(a, b) = cert.query.nodes[i] else {
            unreachable!()
        };
        cert.query.nodes[i] = k::DagNode::Udiv(a, b);
        assert!(!cert.query.has_derived(), "no derived node is left");
        assert_eq!(
            cert.query.encoding(),
            QUERY_ENCODING,
            "tag follows the content"
        );
        let r = cert.recheck();
        assert_eq!(cert.certificate.cnf, cnf, "CNF must be untouched");
        assert_eq!(cert.certificate.lrat, lrat, "proof must be untouched");
        assert!(r.is_err(), "Sdiv → Udiv must fail the recheck: {r:?}");
        // …and the CNF-level (v1) recheck of the untouched pair still passes:
        // exactly the gap the query re-check closes.
        cert.certificate.recheck().expect("v1 pair re-checks");
        // The other direction too: a derived node forged INTO the twin's
        // `udiv` (hash recomputed) does not re-check either.
        let mut cert = sdiv_query_certificate();
        let j = cert
            .query
            .nodes
            .iter()
            .position(|n| matches!(n, k::DagNode::Udiv(_, _)))
            .expect("the rewrite's Udiv node");
        let k::DagNode::Udiv(a, b) = cert.query.nodes[j] else {
            unreachable!()
        };
        cert.query.nodes[j] = k::DagNode::Srem(a, b);
        assert!(cert.recheck().is_err(), "Udiv → Srem must fail the recheck");
    }

    // rivet: verifies VER-062
    /// `check_with_query` agrees with `check` / `check_with_witness` on
    /// every verdict direction, and a SAT query comes back with the usual
    /// witness.
    #[test]
    fn check_with_query_matches_the_other_entries() {
        let s = unsat_query();
        assert!(matches!(s.check(), crate::CheckResult::Unsat(_)));
        assert!(matches!(s.check_with_query(), QueryCheckResult::Unsat(_)));
        let mut sat = Solver::new();
        sat.assert(BoolTerm::Eq(
            Box::new(BvTerm::Urem(Box::new(var("a", 8)), Box::new(konst(5, 8)))),
            Box::new(konst(3, 8)),
        ));
        match sat.check_with_query() {
            QueryCheckResult::Sat(w) => w.recheck().expect("witness re-checks"),
            other => panic!("expected Sat, got {other:?}"),
        }
        let empty = Solver::new();
        assert!(matches!(empty.check_with_query(), QueryCheckResult::Sat(_)));
    }
}
