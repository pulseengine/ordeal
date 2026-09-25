use ordeal::{BvTerm, CheckResult, Solver, Sort};

fn main() {
    // Is x * 2 the same as x << 1 for every 32-bit x?
    let x = || {
        Box::new(BvTerm::Var {
            name: "x".into(),
            sort: Sort::new(32),
        })
    };
    let c = |v| {
        Box::new(BvTerm::Const {
            value: v,
            sort: Sort::new(32),
        })
    };

    let lhs = BvTerm::Mul(x(), c(2));
    let rhs = BvTerm::Shl(x(), c(1));

    match Solver::prove_equiv(lhs, rhs) {
        // Equivalent. The certificate carries the CNF and the LRAT proof;
        // recheck() re-validates it with the trusted checker, zero trust in the solver.
        CheckResult::Unsat(cert) => {
            cert.recheck().expect("certificate re-checks");
            println!("equivalent (certificate re-checked)");
        }
        // Not equivalent: the model is a counterexample.
        CheckResult::Sat(model) => println!("differ, e.g. at {:?}", model.assignments),
        // No claim — never treat Unknown as "equivalent".
        CheckResult::Unknown => println!("unknown"),
    }
}
