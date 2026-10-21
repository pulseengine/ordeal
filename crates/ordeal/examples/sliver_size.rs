//! TR-072 certificate size: the `ordeal-cert/v4` bundle of the loom-shaped
//! 6-pair obligation (24 reads of one array, 276 congruence roots) and of
//! smaller ones, block by block, next to the v3 bundle of the same
//! lowered core. Needs `--features cert-bundle`.

use ordeal::sliver::{ArrayTerm, ExtBoolTerm, ExtBvTerm, ExtOp};
use ordeal::{BvTerm, SliverCheckResult, Solver, Sort};

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

fn c32(v: u128) -> ExtBvTerm {
    ExtBvTerm::Core(BvTerm::Const {
        value: v,
        sort: Sort::new(32),
    })
}

fn add32(a: ExtBvTerm, b: ExtBvTerm) -> ExtBvTerm {
    ExtBvTerm::Op(Box::new(ExtOp::Add(a, b)))
}

fn sel(a: ArrayTerm, i: ExtBvTerm) -> ExtBvTerm {
    ExtBvTerm::Select {
        array: Box::new(a),
        index: Box::new(i),
    }
}

fn store(a: ArrayTerm, i: ExtBvTerm, v: ExtBvTerm) -> ArrayTerm {
    ArrayTerm::Store {
        array: Box::new(a),
        index: Box::new(i),
        value: Box::new(v),
    }
}

fn all_unsat(n: usize) -> Vec<ExtBoolTerm> {
    let chain = || {
        (0..4 * n).fold(ArrayTerm::Var { name: "mem".into() }, |acc, k| {
            store(acc, add32(v32("b"), c32(k as u128)), v8(&format!("v{k}")))
        })
    };
    let mut or_ne: Option<ExtBoolTerm> = None;
    for k in 0..4 * n {
        let ne = ExtBoolTerm::Ne(
            sel(chain(), add32(v32("b"), c32(k as u128))),
            v8(&format!("v{k}")),
        );
        or_ne = Some(match or_ne {
            None => ne,
            Some(p) => ExtBoolTerm::Or(Box::new(p), Box::new(ne)),
        });
    }
    vec![or_ne.unwrap()]
}

fn main() {
    let attests = ordeal::cert_bundle::Attests {
        kind: "translation_validation".into(),
        claim: "loom-shaped memory obligation".into(),
        standards: vec![],
    };
    println!(
        "pairs\treads\troots\text_nodes\tv3_bytes\tv4_bytes\text_block_bytes\tcheck_ms\tsolve_ms"
    );
    for n in [1usize, 2, 4, 6] {
        let q = all_unsat(n);
        let t0 = std::time::Instant::now();
        let s = Solver::from_sliver(&q).expect("in the sliver");
        let cert = match s.check_sliver_with_term() {
            SliverCheckResult::Unsat(c) => c,
            other => panic!("expected Unsat, got {other:?}"),
        };
        let solve_ms = t0.elapsed().as_millis();
        let t1 = std::time::Instant::now();
        cert.sliver
            .check(&cert.term.term)
            .expect("the trusted sliver check accepts");
        let check_ms = t1.elapsed().as_micros() as f64 / 1000.0;
        let v3 = cert.term.to_cert_v3(&attests);
        let v4 = cert.to_cert_v4(&attests);
        let v: serde_json::Value = serde_json::from_str(&v4).unwrap();
        let ext_bytes = v["ext"].to_string().len();
        println!(
            "{n}\t{}\t{}\t{}\t{}\t{}\t{}\t{check_ms:.3}\t{solve_ms}",
            cert.sliver.reads.len() / 3,
            cert.term.term.roots.len(),
            cert.sliver.ext.nodes.len(),
            v3.len(),
            v4.len(),
            ext_bytes
        );
    }
}
