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
//!
//! Since TR-075 the data types and their trusted re-checks live in the
//! solver-free `ordeal-cert` crate (`ordeal_cert::query`), re-exported
//! here unchanged; what stays is solver-side: the `*CheckResult` verdict
//! types and the constructors that flatten the caller's trees
//! ([`QueryTermFlatten`]).

pub use ordeal_cert::query::*;

use crate::blast_kernel as k;
use ordeal_lrat::ExtNode;

/// The result of [`crate::Solver::check_with_query`]: like
/// [`crate::witness::WitnessCheckResult`] but both decided verdicts carry
/// the lowered query — `Unsat` a [`QueryCertificate`], `Sat` (since #192
/// phase 6) a [`QuerySatCertificate`] — whose trusted re-check passed
/// before it was returned.
#[derive(Clone, Debug)]
pub enum QueryCheckResult {
    /// Unsatisfiable, with the certificate and the query it refutes; the
    /// trusted `check_query` accepted it before return.
    Unsat(QueryCertificate),
    /// Satisfiable, with the witness, the query and the input assignment
    /// that satisfies it; the trusted `check_query_model` accepted it
    /// before return (`.witness` is the v1 [`SatCertificate`]).
    Sat(QuerySatCertificate),
    /// No claim (identical semantics to [`crate::CheckResult::Unknown`]).
    Unknown,
}

/// Why [`QueryTerm::flatten_sliver`] could not build the blocks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SliverFlattenError {
    /// The trusted flattener refused the extended trees.
    Flat(ordeal_lrat::FlatError),
    /// A kernel name is not UTF-8 (impossible for a name that came from a
    /// `String`).
    Names,
    /// The lowered core is ill-sorted.
    Core(crate::eval::EvalError),
}

impl From<crate::eval::EvalError> for SliverFlattenError {
    fn from(e: crate::eval::EvalError) -> Self {
        SliverFlattenError::Core(e)
    }
}
/// The solver-side constructors of a [`QueryTerm`]: they flatten the
/// caller's `term.rs` / sliver trees through the trusted flattener and map
/// the result onto the lowered DAG, so they need the solver's term types
/// and DAG builder and stay in `ordeal` when the data type moved to
/// `ordeal-cert` (TR-075). Until v0.35.0 these were inherent associated
/// functions; with this trait in scope (`use ordeal::query::QueryTermFlatten`)
/// the `QueryTerm::flatten(..)` / `QueryTerm::flatten_sliver(..)` call
/// syntax is unchanged.
pub trait QueryTermFlatten: Sized {
    /// See [`QueryTerm::flatten_sliver`](QueryTermFlatten::flatten_sliver).
    fn flatten_sliver(
        assertions: &[crate::sliver::ExtBoolTerm],
        trace: &crate::sliver::SliverTrace,
        query: &QueryDag,
        query_vars: &[(String, u32, usize)],
    ) -> Result<(QueryTerm, SliverBlock), SliverFlattenError>;

    /// See [`QueryTerm::flatten`](QueryTermFlatten::flatten).
    fn flatten(
        assertions: &[crate::term::BoolTerm],
        query: &QueryDag,
        query_vars: &[(String, u32, usize)],
    ) -> Result<QueryTerm, ordeal_lrat::FlatError>;
}

impl QueryTermFlatten for QueryTerm {
    /// Flatten a SLIVER query's lowered core (TR-072): the hash-consed
    /// `DagBuilder` over the lowered assertions, then — as non-root
    /// witness nodes — the lowered index of every read and the lowered
    /// arguments of every call, which is where the read and call tables
    /// point; the extended query's map onto this core (a variable by name,
    /// a constant by value, a closed operator as the operator over its
    /// operands' images, a `select` or a call by its lowered term); and
    /// the map onto the solver's DAG (`dag::term_map`) as for a core
    /// query. Every map and table is untrusted advice the trusted checks
    /// verify. Fails only on an ill-sorted term.
    fn flatten_sliver(
        assertions: &[crate::sliver::ExtBoolTerm],
        trace: &crate::sliver::SliverTrace,
        query: &QueryDag,
        query_vars: &[(String, u32, usize)],
    ) -> Result<(QueryTerm, SliverBlock), SliverFlattenError> {
        use crate::dag::{DagBuilder, NO_IMAGE};
        use crate::term::{BvTerm, Sort};
        // TR-073: the extended query is the TRUSTED flattener's output over
        // the kernel's copy of the trees; the lowering's own walk
        // (`trace.ext`, the differential twin) only supplies the lowered
        // images, indexed by node — a disagreement between the two walks
        // is a `check_sliver_lowering` rejection, never a wrong verdict.
        let flat = ordeal_lrat::flatten_tree(&crate::mirror::of_ext_bools(assertions))
            .map_err(SliverFlattenError::Flat)?;
        let kernel_ext = crate::mirror::ext_query(&flat).ok_or(SliverFlattenError::Names)?;
        debug_assert!(
            kernel_ext == trace.ext,
            "the kernel's flattening and the lowering's walk disagree — ordeal bug"
        );
        let consts = crate::mirror::const_table(&flat);
        let ext = &kernel_ext;
        let lowered = &trace.lowered;
        let mut builder = DagBuilder::new(true);
        for a in &lowered.assertions {
            builder.assert_root(a)?;
        }
        let var = |name: &str, width: u32| BvTerm::Var {
            name: name.to_string(),
            sort: Sort::new(width),
        };
        let mut reads = Vec::with_capacity(3 * lowered.read_sites.len());
        for (name, array, index) in &lowered.read_sites {
            let v = builder.bv(&var(name, 8))?;
            let x = builder.bv(index)?;
            let aid = ext
                .arrays
                .iter()
                .position(|a| a == array)
                .unwrap_or(NO_IMAGE);
            reads.extend([v, aid, x]);
        }
        let mut calls = Vec::with_capacity(4 * lowered.calls.len());
        let mut cargs = Vec::new();
        for (name, func, args, sort) in &lowered.calls {
            let v = builder.bv(&var(name, sort.width))?;
            let fid = ext
                .funcs
                .iter()
                .position(|(f, _)| f == func)
                .unwrap_or(NO_IMAGE);
            let s = cargs.len();
            for a in args {
                cargs.push(builder.bv(a)?);
            }
            calls.extend([v, fid, s, args.len()]);
        }
        let name_of: std::collections::HashMap<usize, (&str, u32)> = ext
            .vars
            .iter()
            .map(|(name, width, node)| (*node, (name.as_str(), *width)))
            .collect();
        let mut map: Vec<usize> = Vec::with_capacity(ext.nodes.len());
        for (i, n) in ext.nodes.iter().enumerate() {
            let image = match n {
                ExtNode::Core(k::DagNode::Var(_)) => match name_of.get(&i) {
                    Some((name, width)) => builder.bv(&var(name, *width))?,
                    None => NO_IMAGE,
                },
                // #262: the kernel's constant for this node, MASKED — the
                // value the lowered core carries (`sliver::masked_bv`), so
                // the lookup hits the core's node; the raw value's bits
                // above the width mean nothing to the core.
                ExtNode::Core(k::DagNode::Const(_, _)) => match consts.get(&i) {
                    Some(&(value, w)) => builder.bv(&BvTerm::Const {
                        value: crate::eval::mask_to(value, w),
                        sort: Sort::new(w),
                    })?,
                    None => NO_IMAGE,
                },
                ExtNode::Core(nd) => {
                    let at = |a: usize| map.get(a).copied().filter(|&m| m != NO_IMAGE);
                    match crate::dag::map_operands(nd, at) {
                        Some(mapped) => builder.intern_node(mapped).unwrap_or(NO_IMAGE),
                        None => NO_IMAGE,
                    }
                }
                ExtNode::Select(..) | ExtNode::Call(..) => match &trace.images[i] {
                    Some(t) => builder.bv(t)?,
                    None => NO_IMAGE,
                },
            };
            map.push(image);
        }
        let dag = builder.finish();
        let term_map =
            crate::dag::term_map(&dag, &query.nodes, &query.bits, &query.roots, query_vars);
        let term = QueryTerm {
            nodes: dag.nodes,
            bits: dag.bits,
            roots: dag.roots,
            vars: dag.vars,
            map: term_map,
            shared: true,
        };
        let block = SliverBlock {
            ext: kernel_ext,
            map,
            reads,
            calls,
            cargs,
        };
        Ok((term, block))
    }
    /// Flatten `assertions` with the TRUSTED flattener (TR-073:
    /// `ordeal_lrat::flatten_tree` over the kernel's copy of the trees,
    /// `crate::mirror`; the `nodes` / `bits` / `roots` / `vars` of the
    /// term are the kernel's output, verbatim — `dag::flatten` is its
    /// differential twin) and map the result onto the lowered `query`
    /// (`query_vars`: the lowered DAG's `(name, width, Var node)` map).
    /// Fails only on a term the kernel refuses (ill-sorted, or one name at
    /// two widths).
    fn flatten(
        assertions: &[crate::term::BoolTerm],
        query: &QueryDag,
        query_vars: &[(String, u32, usize)],
    ) -> Result<QueryTerm, ordeal_lrat::FlatError> {
        let flat = ordeal_lrat::flatten_tree(&crate::mirror::of_bools(assertions))?;
        let nodes = ordeal_lrat::project_core(&flat.nodes)?;
        let vars = crate::mirror::var_table(&flat).ok_or(ordeal_lrat::FlatError::NameWidth)?;
        let term = crate::dag::Dag {
            nodes,
            bits: flat.bits,
            roots: flat.roots,
            vars,
        };
        let map = crate::dag::term_map(&term, &query.nodes, &query.bits, &query.roots, query_vars);
        Ok(QueryTerm {
            nodes: term.nodes,
            bits: term.bits,
            roots: term.roots,
            vars: term.vars,
            map,
            shared: false,
        })
    }
}

/// The result of [`crate::Solver::check_with_term`]: like
/// [`QueryCheckResult`] but both decided verdicts also carry the term the
/// query was lowered from — `Unsat` a [`TermCertificate`], `Sat` a
/// [`TermSatCertificate`] — whose trusted re-check (term-to-DAG
/// correspondence included) passed before it was returned.
#[derive(Clone, Debug)]
pub enum TermCheckResult {
    /// Unsatisfiable: the certificate, the query it refutes and the term;
    /// `check_term_dag` and `check_query` accepted before return.
    Unsat(TermCertificate),
    /// Satisfiable: the witness, the query, the inputs and the term;
    /// `check_term_dag`, `check_query_model` and the binding checks
    /// accepted before return.
    Sat(TermSatCertificate),
    /// No claim (identical semantics to [`crate::CheckResult::Unknown`]).
    Unknown,
}

/// The result of [`crate::Solver::check_sliver_with_term`]: both decided
/// verdicts carry the extended query and its correspondence to the
/// lowered core, whose trusted re-check passed before it was returned.
#[derive(Clone, Debug)]
pub enum SliverCheckResult {
    /// Unsatisfiable under every array and UF interpretation.
    Unsat(SliverCertificate),
    /// Satisfiable, with the extended model.
    Sat(SliverSatCertificate),
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
    /// witness (inside the query-carrying certificate since phase 6).
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
            QueryCheckResult::Sat(w) => {
                w.witness.recheck().expect("v1 witness re-checks");
                w.recheck().expect("query-level model re-checks");
            }
            other => panic!("expected Sat, got {other:?}"),
        }
        let empty = Solver::new();
        match empty.check_with_query() {
            QueryCheckResult::Sat(w) => {
                assert!(w.query.nodes.is_empty() && w.inputs.bits.is_empty());
                w.recheck().expect("the empty query re-checks vacuously");
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    // ── #192 phase 6: the SAT direction at the query level ─────────────

    /// `(a + b = 9) ∧ (a < b) ∧ (a * 2 = b)` at width 8 — a two-variable
    /// SAT query with arithmetic, so the input assignment has two `Var`
    /// nodes to map, and a UNIQUE model (`3a = 9` mod 256 ⟹ `a = 3`,
    /// `b = 6`), so every single input-bit flip is a non-model.
    fn sat_query_certificate() -> QuerySatCertificate {
        let mut s = Solver::new();
        s.assert(BoolTerm::Eq(
            Box::new(BvTerm::Add(Box::new(var("a", 8)), Box::new(var("b", 8)))),
            Box::new(konst(9, 8)),
        ));
        s.assert(BoolTerm::Ult(Box::new(var("a", 8)), Box::new(var("b", 8))));
        s.assert(BoolTerm::Eq(
            Box::new(BvTerm::Mul(Box::new(var("a", 8)), Box::new(konst(2, 8)))),
            Box::new(var("b", 8)),
        ));
        match s.check_with_query() {
            QueryCheckResult::Sat(c) => c,
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    // rivet: verifies VER-065
    /// The positive path: a real SAT query comes back with a certificate
    /// the trusted `check_query_model` accepts; the inputs are the model's
    /// bits at each variable's `Var` node (LSB first), the model is the
    /// expected one, and the block is deterministic.
    #[test]
    fn query_sat_certificate_rechecks_through_the_trusted_crate() {
        let cert = sat_query_certificate();
        cert.recheck().expect("fresh SAT certificate re-checks");
        ordeal_lrat::check_query_model(
            &cert.query.nodes,
            &cert.query.bits,
            &cert.query.roots,
            &cert.inputs.bits,
        )
        .expect("the trusted crate alone accepts the inputs");
        assert_eq!(cert.query.roots.len(), 3);
        assert_eq!(cert.inputs.vars.len(), 2);
        assert_eq!(cert.inputs.bits.len(), 16);
        let value = |name: &str| {
            cert.witness
                .model
                .assignments
                .iter()
                .find(|(n, _)| n == name)
                .map(|(_, v)| *v)
                .expect(name)
        };
        assert_eq!((value("a"), value("b")), (3, 6));
        // The inputs ARE the model: for each var, the bits at its node's
        // offset spell its value LSB first.
        let mut nin = 0;
        for (i, n) in cert.query.nodes.iter().enumerate() {
            if let k::DagNode::Var(w) = *n {
                let (name, width, _) = cert
                    .inputs
                    .vars
                    .iter()
                    .find(|(_, _, node)| *node == i)
                    .expect("every Var node is a model variable");
                assert_eq!(*width as usize, w);
                let v: u128 = (0..w)
                    .map(|j| u128::from(cert.inputs.bits[nin + j]) << j)
                    .sum();
                assert_eq!(v, value(name), "{name}");
                nin += w;
            }
        }
        assert_eq!(nin, 16);
        assert_eq!(
            cert.inputs.sha256(),
            sat_query_certificate().inputs.sha256()
        );
        assert!(
            cert.inputs
                .canonical_text()
                .starts_with("ordeal-inputs/v1\nbits ")
        );
    }

    // rivet: verifies VER-065
    /// The phase-6 negative controls: with the v1 witness UNTOUCHED (same
    /// CNF, assignment, bit map — it keeps re-checking), (1) one flipped
    /// input bit fails the trusted check; (2) a negated root fails it with
    /// the inputs untouched too; (3) a constant bit of the query flipped
    /// fails it; (4) a `vars` entry pointing at the wrong node fails the
    /// consistency check. The CNF-level witness cannot see any of these —
    /// exactly the gap the query-level check closes.
    #[test]
    fn tampering_the_inputs_or_the_query_fails_the_model_recheck() {
        let cert = sat_query_certificate();
        let (cnf, assignment) = (cert.witness.cnf.clone(), cert.witness.assignment.clone());
        // (1) Every single input bit matters here: a = 3, b = 6 is the
        // unique model (a + 2a = 9, a < 2a), so each flip is rejected.
        let mut rejected = 0;
        for i in 0..cert.inputs.bits.len() {
            let mut t = cert.clone();
            t.inputs.bits[i] = !t.inputs.bits[i];
            let direct = ordeal_lrat::check_query_model(
                &t.query.nodes,
                &t.query.bits,
                &t.query.roots,
                &t.inputs.bits,
            );
            assert!(
                matches!(direct, Err(ordeal_lrat::ModelError::RootFalse { .. })),
                "bit {i}: {direct:?}"
            );
            assert!(t.witness.recheck().is_ok(), "the v1 witness is untouched");
            assert!(t.recheck().is_err(), "bit {i}");
            rejected += 1;
        }
        assert_eq!(rejected, 16);
        // (2) The negated root.
        let mut t = cert.clone();
        let root = t.query.roots[0];
        t.query.nodes.push(k::DagNode::Not(root));
        t.query.roots[0] = t.query.nodes.len() - 1;
        t.inputs
            .check_consistent(&t.query, &t.witness.model)
            .expect("the model is still the inputs");
        match t.recheck() {
            Err(QueryModelRecheckError::Rejected(ordeal_lrat::ModelError::RootFalse {
                root: 0,
            })) => {}
            other => panic!("expected RootFalse at root 0, got {other:?}"),
        }
        // (3) A flipped constant bit (the `9`, the `2`: every constant bit
        // of this query is load-bearing).
        let mut rejected = 0;
        for i in 0..cert.query.bits.len() {
            let mut t = cert.clone();
            t.query.bits[i] = !t.query.bits[i];
            if t.recheck().is_err() {
                rejected += 1;
            }
            assert_eq!(t.witness.cnf, cnf);
            assert_eq!(t.witness.assignment, assignment);
        }
        assert_eq!(
            rejected,
            cert.query.bits.len(),
            "every constant bit flip is rejected"
        );
        // (4) A model variable mapped to the other variable's node.
        let mut t = cert.clone();
        let (na, nb) = (t.inputs.vars[0].2, t.inputs.vars[1].2);
        t.inputs.vars[0].2 = nb;
        t.inputs.vars[1].2 = na;
        assert!(matches!(
            t.recheck(),
            Err(QueryModelRecheckError::InputMismatch(_))
        ));
        // (5) A malformed query and a short assignment are the trusted
        // crate's own rejections (the malformed node is a non-`Var`, so
        // the untrusted var map stays intact and the trusted `dag_wf` is
        // what rejects).
        let mut t = cert.clone();
        let j = t
            .query
            .nodes
            .iter()
            .position(|n| !matches!(n, k::DagNode::Var(_)))
            .expect("a non-Var node");
        t.query.nodes[j] = k::DagNode::Add(usize::MAX, 0);
        match t.recheck() {
            Err(QueryModelRecheckError::Rejected(ordeal_lrat::ModelError::Query(
                ordeal_lrat::QueryError::NodeNotWellFormed { node },
            ))) if node == j => {}
            other => panic!("expected NodeNotWellFormed at node {j}, got {other:?}"),
        }
        let mut t = cert;
        t.inputs.bits.pop();
        assert!(matches!(
            t.recheck(),
            Err(QueryModelRecheckError::UnmappedVariable(_))
                | Err(QueryModelRecheckError::Rejected(
                    ordeal_lrat::ModelError::ModelTooShort { .. }
                ))
        ));
    }
}
