//! #192 phase 7 (TR-069): the term certificates at the API level — the
//! positive controls, one negative control per risk of the trusted
//! `check_term_dag` (a tampered map, two term variables aliased to one DAG
//! variable, a wrong fold, a term that asks a different question), and the
//! degradation of a rejected certificate to `Unknown`.

use crate::blast_kernel as k;
use crate::query::{
    TermCertificate, TermCheckResult, TermModelRecheckError, TermRecheckError, TermSatCertificate,
};
use crate::{BoolTerm, BvTerm, Solver, Sort};
use ordeal_lrat::TermError;

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

fn b<T>(t: T) -> Box<T> {
    Box::new(t)
}

/// An UNSAT query that exercises every rewrite the trusted check admits:
/// `a * b ≠ b * a` (a commutative swap and hash-consing), `x + 2 * 3 > x +
/// 6` (a constant fold, a mirror, and the two sums hash-consed once the
/// fold is in), `(a sdiv 1) ≠ a` (a derived operator as its own node).
fn rewrite_heavy_unsat() -> Solver {
    let mut s = Solver::new();
    s.assert(BoolTerm::Ne(
        b(BvTerm::Mul(b(var("a", 8)), b(var("b", 8)))),
        b(BvTerm::Mul(b(var("b", 8)), b(var("a", 8)))),
    ));
    s.assert(BoolTerm::Ugt(
        b(BvTerm::Add(
            b(var("x", 8)),
            b(BvTerm::Mul(b(konst(2, 8)), b(konst(3, 8)))),
        )),
        b(BvTerm::Add(b(var("x", 8)), b(konst(6, 8)))),
    ));
    s.assert(BoolTerm::Ne(
        b(BvTerm::Sdiv(b(var("a", 8)), b(konst(1, 8)))),
        b(var("a", 8)),
    ));
    s
}

fn unsat_term_cert() -> TermCertificate {
    match rewrite_heavy_unsat().check_with_term() {
        TermCheckResult::Unsat(c) => c,
        other => panic!("expected Unsat, got {other:?}"),
    }
}

/// `a + b = 9 ∧ b > a ∧ a * 2 = b`: the unique model `a = 3, b = 6`, with a
/// mirror (`b > a`) and a swap (`a * 2` becomes `2 * a`) on the way.
fn sat_term_cert() -> TermSatCertificate {
    let mut s = Solver::new();
    s.assert(BoolTerm::Eq(
        b(BvTerm::Add(b(var("a", 8)), b(var("b", 8)))),
        b(konst(9, 8)),
    ));
    s.assert(BoolTerm::Ugt(b(var("b", 8)), b(var("a", 8))));
    s.assert(BoolTerm::Eq(
        b(BvTerm::Mul(b(var("a", 8)), b(konst(2, 8)))),
        b(var("b", 8)),
    ));
    match s.check_with_term() {
        TermCheckResult::Sat(c) => c,
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// The term node of a variable, by name.
fn term_var_node(cert_vars: &[(String, u32, usize)], name: &str) -> usize {
    cert_vars
        .iter()
        .find(|(n, _, _)| n == name)
        .map(|(_, _, node)| *node)
        .expect(name)
}

// rivet: verifies VER-069
/// The positive control: a rewrite-heavy UNSAT query gets `Unsat` through
/// the trusted term check; the term block is the un-canonicalized
/// question (more nodes than the DAG, the folded constant's children with
/// no image, the derived operator as its own node), and the trusted crate
/// alone accepts the term, the map and the DAG.
#[test]
fn term_certificate_rechecks_through_the_trusted_crate() {
    let cert = unsat_term_cert();
    cert.recheck().expect("fresh term certificate re-checks");
    let t = &cert.term;
    let q = &cert.query.query;
    assert_eq!(
        ordeal_lrat::check_term_dag(
            &t.nodes, &t.bits, &t.roots, &t.map, &q.nodes, &q.bits, &q.roots
        ),
        Ok(()),
        "the trusted crate alone accepts the correspondence"
    );
    cert.query
        .recheck()
        .expect("the v2 certificate inside re-checks");
    assert_eq!(t.roots.len(), 3);
    assert_eq!(t.map.len(), t.nodes.len());
    assert!(
        t.nodes.len() > q.nodes.len(),
        "the term is the question as asked: {} nodes against the DAG's {}",
        t.nodes.len(),
        q.nodes.len()
    );
    assert!(
        t.map.contains(&crate::dag::NO_IMAGE),
        "the folded constant's children have no image"
    );
    assert!(
        t.nodes.iter().any(|n| matches!(n, k::DagNode::Sdiv(_, _))),
        "the derived operator is a node of the term"
    );
    // Both `a * b` and `b * a` map to the one hash-consed DAG `bvmul`
    // node (the third product, `2 * 3`, maps to the folded constant).
    let muls: Vec<usize> = t
        .nodes
        .iter()
        .enumerate()
        .filter(|(_, n)| matches!(n, k::DagNode::Mul(_, _)))
        .map(|(i, _)| t.map[i])
        .filter(|&m| m != crate::dag::NO_IMAGE && matches!(q.nodes[m], k::DagNode::Mul(_, _)))
        .collect();
    assert!(
        muls.len() == 2 && muls[0] == muls[1],
        "the two products share one DAG node: {muls:?}"
    );
    assert!(t.canonical_text().starts_with("ordeal-term/v1\nnodes "));
    assert_eq!(
        t.sha256(),
        unsat_term_cert().term.sha256(),
        "deterministic hash"
    );
    assert_eq!(t.vars.len(), 3);
}

// rivet: verifies VER-069
/// The SAT positive control: the unique model is bound to the TERM's
/// variables through the map by the proven `var_offset` /
/// `check_input_value`, and the trusted crate alone accepts every step.
#[test]
fn term_sat_certificate_rechecks_and_binds_the_model() {
    let cert = sat_term_cert();
    cert.recheck()
        .expect("fresh SAT term certificate re-checks");
    let t = &cert.term;
    let q = &cert.query.query;
    assert_eq!(
        ordeal_lrat::check_term_dag(
            &t.nodes, &t.bits, &t.roots, &t.map, &q.nodes, &q.bits, &q.roots
        ),
        Ok(())
    );
    let model = &cert.query.witness.model.assignments;
    assert_eq!(
        model,
        &vec![("a".to_string(), 3u128), ("b".to_string(), 6u128)]
    );
    for (name, value) in model {
        let node = term_var_node(&t.vars, name);
        let image = t.map[node];
        assert_ne!(image, crate::dag::NO_IMAGE);
        let offset = ordeal_lrat::var_offset(&q.nodes, image).expect("offset");
        assert!(
            ordeal_lrat::check_input_value(&cert.query.inputs.bits, offset, 8, *value),
            "{name} = {value} is the input bits at its image's offset"
        );
        assert!(!ordeal_lrat::check_input_value(
            &cert.query.inputs.bits,
            offset,
            8,
            *value + 1
        ));
    }
}

// rivet: verifies VER-069
/// One negative control per risk, with the v2 certificate (CNF, proof,
/// query) UNTOUCHED and still re-checking: a tampered map entry, two term
/// variables aliased to one DAG variable, a wrong fold, and a term that
/// asks a different question are each rejected by the trusted check.
#[test]
fn tampering_the_map_the_var_map_or_a_fold_fails_the_term_recheck() {
    let fresh = unsat_term_cert();
    let t = &fresh.term;
    let is_op = |n: &k::DagNode| !matches!(n, k::DagNode::Var(_) | k::DagNode::Const(_, _));
    // (1) A tampered map: an operator pointed at a different DAG node.
    let i = (0..t.nodes.len())
        .find(|&i| is_op(&t.nodes[i]) && t.map[i] != crate::dag::NO_IMAGE)
        .expect("a mapped operator");
    let mut cert = fresh.clone();
    cert.term.map[i] = (cert.term.map[i] + 1) % fresh.query.query.nodes.len();
    assert!(
        matches!(cert.recheck(), Err(TermRecheckError::Term(_))),
        "a tampered map entry is rejected: {:?}",
        cert.recheck()
    );
    cert.query
        .recheck()
        .expect("the v2 certificate is untouched");
    // (2) Aliasing: `b` mapped onto `a`'s DAG variable. A refutation of
    // the more constrained DAG says nothing about the term, so this is the
    // one check whose omission would be unsound.
    let mut cert = fresh.clone();
    let a = term_var_node(&cert.term.vars, "a");
    let bn = term_var_node(&cert.term.vars, "b");
    cert.term.map[bn] = cert.term.map[a];
    assert!(
        matches!(
            cert.recheck(),
            Err(TermRecheckError::Term(TermError::VarMismatch { .. }))
        ),
        "{:?}",
        cert.recheck()
    );
    cert.query
        .recheck()
        .expect("the v2 certificate is untouched");
    // (3) A wrong fold: the term says `2 + 3`, the DAG's constant is 6.
    let mut cert = fresh.clone();
    let mul = (0..t.nodes.len())
        .find(|&i| {
            matches!(t.nodes[i], k::DagNode::Mul(_, _))
                && t.map[i] != crate::dag::NO_IMAGE
                && matches!(fresh.query.query.nodes[t.map[i]], k::DagNode::Const(_, _))
        })
        .expect("the folded product");
    let (x, y) = match t.nodes[mul] {
        k::DagNode::Mul(x, y) => (x, y),
        _ => unreachable!(),
    };
    cert.term.nodes[mul] = k::DagNode::Add(x, y);
    assert!(
        matches!(
            cert.recheck(),
            Err(TermRecheckError::Term(TermError::FoldMismatch { .. }))
        ),
        "{:?}",
        cert.recheck()
    );
    cert.query
        .recheck()
        .expect("the v2 certificate is untouched");
    // (4) A different question: `(a sdiv 1) = a` instead of `≠` — the same
    // DAG would be a certified wrong answer about it.
    let mut cert = fresh.clone();
    let ne = (0..t.nodes.len())
        .find(|&i| {
            matches!(t.nodes[i], k::DagNode::Ne(_, _))
                && t.map[i] != crate::dag::NO_IMAGE
                && matches!(fresh.query.query.nodes[t.map[i]], k::DagNode::Ne(_, _))
        })
        .expect("a mapped disequality");
    let (x, y) = match t.nodes[ne] {
        k::DagNode::Ne(x, y) => (x, y),
        _ => unreachable!(),
    };
    cert.term.nodes[ne] = k::DagNode::Eq(x, y);
    assert!(
        matches!(
            cert.recheck(),
            Err(TermRecheckError::Term(TermError::NodeMismatch { .. }))
        ),
        "{:?}",
        cert.recheck()
    );
    cert.query
        .recheck()
        .expect("the v2 certificate is untouched");
    // (5) On `sat`: the term's variable map swapped — the model's `a` is
    // then checked against `b`'s bits and the proven binding rejects it.
    let fresh_sat = sat_term_cert();
    let mut cert = fresh_sat.clone();
    let a = cert
        .term
        .vars
        .iter()
        .position(|(n, _, _)| n == "a")
        .expect("a");
    let bn = cert
        .term
        .vars
        .iter()
        .position(|(n, _, _)| n == "b")
        .expect("b");
    let (na, nb) = (cert.term.vars[a].2, cert.term.vars[bn].2);
    cert.term.vars[a].2 = nb;
    cert.term.vars[bn].2 = na;
    assert!(
        matches!(cert.recheck(), Err(TermModelRecheckError::Binding(_))),
        "{:?}",
        cert.recheck()
    );
    cert.query
        .recheck()
        .expect("the v2 SAT certificate is untouched");
    // And the aliasing control on `sat` too.
    let mut cert = fresh_sat.clone();
    cert.term.map[nb] = cert.term.map[na];
    assert!(matches!(
        cert.recheck(),
        Err(TermModelRecheckError::Term(TermError::VarMismatch { .. }))
    ));
}

// rivet: verifies VER-069
/// The gates degrade a rejected certificate to `Unknown`, never to a
/// verdict about the wrong term.
#[test]
fn a_rejected_term_map_degrades_to_unknown_not_a_verdict() {
    let mut cert = unsat_term_cert();
    assert!(matches!(
        Solver::term_verdict(cert.clone()),
        TermCheckResult::Unsat(_)
    ));
    let a = term_var_node(&cert.term.vars, "a");
    let bn = term_var_node(&cert.term.vars, "b");
    cert.term.map[bn] = cert.term.map[a];
    assert!(matches!(
        Solver::term_verdict(cert),
        TermCheckResult::Unknown
    ));
    let mut cert = sat_term_cert();
    assert!(matches!(
        Solver::term_sat_verdict(cert.clone()),
        TermCheckResult::Sat(_)
    ));
    let i = cert
        .term
        .nodes
        .iter()
        .position(|n| matches!(n, k::DagNode::Ugt(_, _)))
        .expect("the mirrored comparison");
    cert.term.map[i] = crate::dag::NO_IMAGE;
    assert!(matches!(
        Solver::term_sat_verdict(cert),
        TermCheckResult::Unknown
    ));
}

// rivet: verifies VER-069
/// `check_with_term` decides exactly what `check_with_query` decides, on
/// both verdicts and on the empty query.
#[test]
fn check_with_term_matches_check_with_query() {
    use crate::query::QueryCheckResult;
    let empty = Solver::new();
    assert!(matches!(empty.check_with_term(), TermCheckResult::Sat(_)));
    let s = rewrite_heavy_unsat();
    match (s.check_with_query(), s.check_with_term()) {
        (QueryCheckResult::Unsat(q), TermCheckResult::Unsat(t)) => {
            assert!(q.query == t.query.query);
            assert_eq!(q.certificate.cnf, t.query.certificate.cnf);
        }
        (q, t) => panic!("verdicts differ: {q:?} vs {t:?}"),
    }
    let sat = sat_term_cert();
    assert_eq!(sat.query.witness.model.assignments.len(), 2);
}
