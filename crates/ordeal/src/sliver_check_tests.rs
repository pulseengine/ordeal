//! TR-072: the proven sliver at the API level — the positive controls
//! (every sliver entry point rests on `check_sliver_lowering`; the
//! extended certificate re-checks; the consumer's re-flattening agrees;
//! the SAT pullback satisfies the extended query), one negative control
//! per risk of the trusted check (a tampered ext block, a wrong read
//! share, the #247 capture shape, a lowering that forgets a congruence
//! clause), each degrading every entry point to `Unknown`.

use crate::query::SliverCheckResult;
use crate::sliver::{self, ArrayTerm, ExtBoolTerm, ExtBvTerm, ExtOp, eval_ext_bool};
use crate::solver::tamper::{self, Tamper};
use crate::{BoolTerm, BvTerm, CheckResult, Solver, Sort};

fn v8(name: &str) -> ExtBvTerm {
    ExtBvTerm::Core(BvTerm::Var {
        name: name.into(),
        sort: Sort::new(8),
    })
}

fn v32(name: &str) -> ExtBvTerm {
    ExtBvTerm::Core(BvTerm::Var {
        name: name.into(),
        sort: Sort::new(32),
    })
}

fn c8(v: u128) -> ExtBvTerm {
    ExtBvTerm::Core(BvTerm::Const {
        value: v,
        sort: Sort::new(8),
    })
}

fn c32(v: u128) -> ExtBvTerm {
    ExtBvTerm::Core(BvTerm::Const {
        value: v,
        sort: Sort::new(32),
    })
}

fn add32(a: ExtBvTerm, b: ExtBvTerm) -> ExtBvTerm {
    ExtBvTerm::Op(Box::new(ExtOp::Add(a, b)))
}

fn arr(name: &str) -> ArrayTerm {
    ArrayTerm::Var { name: name.into() }
}

fn store(a: ArrayTerm, i: ExtBvTerm, v: ExtBvTerm) -> ArrayTerm {
    ArrayTerm::Store {
        array: Box::new(a),
        index: Box::new(i),
        value: Box::new(v),
    }
}

fn sel(a: ArrayTerm, i: ExtBvTerm) -> ExtBvTerm {
    ExtBvTerm::Select {
        array: Box::new(a),
        index: Box::new(i),
    }
}

fn call(name: &str, args: Vec<ExtBvTerm>) -> ExtBvTerm {
    ExtBvTerm::PureCall {
        name: name.into(),
        args,
        sort: Sort::new(8),
    }
}

/// loom's shape: two bytes stored at `base + 0` and `base + 1`, the first
/// read back — `mem[base+1 := v1][base+0 := v0][base + 0] ≠ v0`, UNSAT
/// (a symbolic read-over-write mux, two reads of one array through the
/// chain's base, a congruence root).
fn loom_unsat() -> Vec<ExtBoolTerm> {
    let base = || v32("base");
    let m = store(
        store(arr("mem"), add32(base(), c32(1)), v8("v1")),
        add32(base(), c32(0)),
        v8("v0"),
    );
    vec![ExtBoolTerm::Ne(sel(m, add32(base(), c32(0))), v8("v0"))]
}

/// `a[i] ≠ a[j] ∧ a[i] = f(x) ∧ f(y) = 7`: SAT with `i ≠ j`; two reads of
/// one array (one congruence root) and two call sites (one more).
fn mixed_sat() -> Vec<ExtBoolTerm> {
    vec![
        ExtBoolTerm::Ne(sel(arr("a"), v32("i")), sel(arr("a"), v32("j"))),
        ExtBoolTerm::Eq(sel(arr("a"), v32("i")), call("f", vec![v8("x")])),
        ExtBoolTerm::Eq(call("f", vec![v8("y")]), c8(7)),
    ]
}

/// `x = y ∧ f(x) ≠ f(y)`: UNSAT by Ackermann congruence alone.
fn uf_unsat() -> Vec<ExtBoolTerm> {
    vec![
        ExtBoolTerm::Eq(v8("x"), v8("y")),
        ExtBoolTerm::Ne(call("f", vec![v8("x")]), call("f", vec![v8("y")])),
    ]
}

fn unsat_cert(q: &[ExtBoolTerm]) -> crate::query::SliverCertificate {
    match Solver::from_sliver(q)
        .expect("in the sliver")
        .check_sliver_with_term()
    {
        SliverCheckResult::Unsat(c) => c,
        other => panic!("expected Unsat, got {other:?}"),
    }
}

fn sat_cert(q: &[ExtBoolTerm]) -> crate::query::SliverSatCertificate {
    match Solver::from_sliver(q)
        .expect("in the sliver")
        .check_sliver_with_term()
    {
        SliverCheckResult::Sat(c) => c,
        other => panic!("expected Sat, got {other:?}"),
    }
}

// rivet: verifies VER-072
/// The positive control, UNSAT: the extended certificate re-checks; the
/// trusted crate alone accepts the ext block against the lowered core;
/// the core is the hash-consed lowering (`ordeal-term/v2`); the ext block
/// is what the consumer's re-flattening of the question yields, hash for
/// hash.
#[test]
fn sliver_certificate_rechecks_through_the_trusted_crate() {
    for q in [loom_unsat(), uf_unsat()] {
        let cert = unsat_cert(&q);
        cert.recheck()
            .expect("fresh extended certificate re-checks");
        assert_eq!(cert.sliver.check(&cert.term.term), Ok(()));
        assert!(cert.term.term.shared);
        assert_eq!(cert.term.term.encoding(), crate::query::TERM_ENCODING_V2);
        let again = sliver::flatten_ext(&q).expect("in the sliver");
        assert!(
            again == cert.sliver.ext,
            "the consumer's flattening is the block's"
        );
        let mut block2 = cert.sliver.clone();
        block2.ext = again;
        assert_eq!(block2.sha256(), cert.sliver.sha256());
        // The v3 certificate inside is about the lowered core and re-checks
        // on its own.
        cert.term
            .recheck()
            .expect("the term certificate inside re-checks");
    }
}

// rivet: verifies VER-072
/// The positive control, SAT: the extended certificate re-checks, and the
/// pullback model — arrays at every read's index value, the function at
/// every call's argument values — satisfies every extended assertion
/// under the untrusted evaluator (the statement of
/// `check_sliver_model_sound`, observed).
#[test]
fn sliver_sat_certificate_pulls_back_to_an_extended_model() {
    let q = mixed_sat();
    let cert = sat_cert(&q);
    cert.recheck()
        .expect("fresh extended SAT certificate re-checks");
    assert_eq!(cert.sliver.check(&cert.term.term), Ok(()));
    for a in &q {
        assert!(
            eval_ext_bool(a, &cert.model).expect("evaluates"),
            "the pullback model satisfies {a:?}"
        );
    }
    assert!(cert.model.arrays.contains_key("a"));
    assert!(cert.model.calls.keys().any(|(f, _)| f == "f"));
    // Two reads, two call sites: one congruence root each, after the
    // three asserted roots.
    assert_eq!(cert.sliver.reads.len(), 6);
    assert_eq!(cert.sliver.calls.len(), 8);
    assert_eq!(cert.term.term.roots.len(), 5);
}

// rivet: verifies VER-072
/// Every entry point of a sliver solver — and the one-shots — rests on
/// the sliver check: a tampered ext block (the first select's image
/// moved) degrades `check`, both bounded twins, `check_with_query`,
/// `check_with_term`, `check_sliver_with_term` and the one-shots to
/// `Unknown`, on UNSAT and on SAT.
#[test]
fn a_tampered_ext_block_degrades_every_entry_point_to_unknown() {
    for q in [loom_unsat(), mixed_sat()] {
        let s = Solver::from_sliver(&q).expect("in the sliver");
        let _armed = tamper::arm(Tamper::ExtMap);
        assert!(matches!(s.check(), CheckResult::Unknown));
        assert!(matches!(
            s.check_with_deadline(60_000),
            CheckResult::Unknown
        ));
        assert!(matches!(
            s.check_with_limit(1_000_000),
            CheckResult::Unknown
        ));
        assert!(matches!(
            s.check_with_query(),
            crate::query::QueryCheckResult::Unknown
        ));
        assert!(matches!(
            s.check_with_term(),
            crate::query::TermCheckResult::Unknown
        ));
        assert!(matches!(
            s.check_sliver_with_term(),
            SliverCheckResult::Unknown
        ));
        assert!(matches!(Solver::check_sliver(&q), CheckResult::Unknown));
        assert!(matches!(
            Solver::check_sliver_with_deadline(&q, 60_000),
            CheckResult::Unknown
        ));
        assert!(matches!(
            Solver::check_sliver_with_limit(&q, 1_000_000),
            CheckResult::Unknown
        ));
    }
    // Disarmed, the same solvers decide.
    assert!(matches!(
        Solver::check_sliver(&loom_unsat()),
        CheckResult::Unsat(_)
    ));
    assert!(matches!(
        Solver::check_sliver(&mixed_sat()),
        CheckResult::Sat(_)
    ));
}

// rivet: verifies VER-072
/// A wrong read share — the second read entry claiming the first's
/// variable — is rejected by the table check: `Unknown` on UNSAT and SAT
/// (queries with two reads of one array).
#[test]
fn a_wrong_read_share_degrades_to_unknown() {
    let two_reads_unsat = vec![
        ExtBoolTerm::Ne(sel(arr("a"), v32("i")), sel(arr("a"), v32("j"))),
        ExtBoolTerm::Eq(v32("i"), v32("j")),
    ];
    assert!(matches!(
        Solver::check_sliver(&two_reads_unsat),
        CheckResult::Unsat(_)
    ));
    for q in [two_reads_unsat, mixed_sat()] {
        let s = Solver::from_sliver(&q).expect("in the sliver");
        let _armed = tamper::arm(Tamper::ReadShare);
        assert!(matches!(s.check(), CheckResult::Unknown));
        assert!(matches!(
            s.check_sliver_with_term(),
            SliverCheckResult::Unknown
        ));
    }
}

// rivet: verifies VER-072
/// The #247 shape, re-established by the trusted check itself: the read
/// table registering the query variable `v` as a read variable (two
/// classes on one node) is rejected, so a lowering that aliased a fresh
/// variable to a query variable could never be certified — whatever the
/// Rust renaming does.
#[test]
fn the_capture_shape_is_rejected_by_the_class_partition() {
    // `v ≠ a[i]`: `v` is the first extended variable, BV8 like a read.
    let q = vec![ExtBoolTerm::Ne(v8("v"), sel(arr("a"), v32("i")))];
    let s = Solver::from_sliver(&q).expect("in the sliver");
    assert!(matches!(s.check(), CheckResult::Sat(_)));
    let _armed = tamper::arm(Tamper::CaptureName);
    assert!(matches!(s.check(), CheckResult::Unknown));
    assert!(matches!(
        s.check_sliver_with_term(),
        SliverCheckResult::Unknown
    ));
    // And the kernel's own verdict on the tampered block is the class
    // error, not a side effect elsewhere.
    drop(_armed);
    let cert = sat_cert(&q);
    let mut block = cert.sliver.clone();
    let (_, _, node) = block.ext.vars[0].clone();
    block.reads[0] = block.map[node];
    assert_eq!(
        block.check(&cert.term.term),
        Err(ordeal_lrat::SliverCheckError::VarClass { node })
    );
}

// rivet: verifies VER-072
/// A lowering that forgets a congruence clause: the core, the DAG and the
/// CNF all agree on it (the solver would answer), and only the trusted
/// check's root count catches it — `Unknown` from every entry point. The
/// control is potent: with the forgetful lowering `a[i] ≠ a[j] ∧ i = j`
/// is engine-SAT (the spurious model of TR-028), which the check refuses
/// to certify.
#[test]
fn a_forgotten_congruence_clause_degrades_to_unknown() {
    let q = vec![
        ExtBoolTerm::Ne(sel(arr("a"), v32("i")), sel(arr("a"), v32("j"))),
        ExtBoolTerm::Eq(v32("i"), v32("j")),
    ];
    assert!(matches!(Solver::check_sliver(&q), CheckResult::Unsat(_)));
    let _armed = sliver::hooks::drop_last_congruence();
    let forgetful = sliver::lower(&q).expect("in the sliver");
    assert_eq!(forgetful.len(), 2, "the congruence clause is gone");
    let mut core = Solver::new();
    for a in forgetful {
        core.assert(a);
    }
    assert!(
        matches!(core.check(), CheckResult::Sat(_)),
        "without the clause the core is satisfiable — the spurious model"
    );
    let s = Solver::from_sliver(&q).expect("in the sliver");
    assert!(matches!(s.check(), CheckResult::Unknown));
    assert!(matches!(
        s.check_with_deadline(60_000),
        CheckResult::Unknown
    ));
    assert!(matches!(
        s.check_sliver_with_term(),
        SliverCheckResult::Unknown
    ));
    assert!(matches!(Solver::check_sliver(&q), CheckResult::Unknown));
}

// rivet: verifies VER-072
/// A later `assert` on a sliver solver joins the extended query: the gate
/// still sees the whole question and decides it.
#[test]
fn assert_after_from_sliver_keeps_the_gate_whole() {
    let q = vec![ExtBoolTerm::Eq(sel(arr("a"), v32("i")), c8(3))];
    let mut s = Solver::from_sliver(&q).expect("in the sliver");
    assert!(s.is_sliver());
    assert!(matches!(s.check(), CheckResult::Sat(_)));
    s.assert(BoolTerm::Ne(
        Box::new(BvTerm::Var {
            name: "i".into(),
            sort: Sort::new(32),
        }),
        Box::new(BvTerm::Var {
            name: "i".into(),
            sort: Sort::new(32),
        }),
    ));
    assert_eq!(s.num_assertions(), 2);
    assert!(matches!(s.check(), CheckResult::Unsat(_)));
    assert!(matches!(
        s.check_sliver_with_term(),
        SliverCheckResult::Unsat(_)
    ));
}

// rivet: verifies VER-072
/// The edges: an empty extended query is satisfiable with an empty block;
/// a core solver has no extended certificate to give.
#[test]
fn empty_extended_query_and_core_solver_edges() {
    let s = Solver::from_sliver(&[]).expect("in the sliver");
    assert!(matches!(s.check(), CheckResult::Sat(_)));
    assert!(matches!(
        s.check_sliver_with_term(),
        SliverCheckResult::Sat(_)
    ));
    let mut core = Solver::new();
    core.assert(BoolTerm::Eq(
        Box::new(BvTerm::Var {
            name: "x".into(),
            sort: Sort::new(8),
        }),
        Box::new(BvTerm::Const {
            value: 1,
            sort: Sort::new(8),
        }),
    ));
    assert!(!core.is_sliver());
    assert!(matches!(core.check(), CheckResult::Sat(_)));
    assert!(matches!(
        core.check_sliver_with_term(),
        SliverCheckResult::Unknown
    ));
}
