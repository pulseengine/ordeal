//! CNF representation and the Tseitin encoder (DES-003).
//!
//! Literals are DIMACS-style nonzero `i32`s: positive means the variable is
//! asserted true, negative means false. Variables are numbered from 1.
//!
//! [`tseitin`] lowers an [`Aig`] to an equisatisfiable CNF in linear size:
//! CNF variable `v+1` corresponds to AIG variable `v` (the +1 skips DIMACS
//! variable 0), three clauses per AND gate, the constant node pinned false,
//! and one unit clause per asserted output literal.

use crate::aig::{Aig, Lit};

/// A DIMACS-style CNF literal (nonzero; sign is polarity).
pub type CnfLit = i32;

/// A clause: a disjunction of literals.
pub type Clause = Vec<CnfLit>;

/// A CNF formula.
#[derive(Clone, Debug, Default)]
pub struct CnfFormula {
    /// Highest variable index in use (variables are 1..=num_vars).
    pub num_vars: u32,
    /// The clause database.
    pub clauses: Vec<Clause>,
}

impl CnfFormula {
    /// Evaluate under a full assignment (`assignment[v-1]` is variable `v`).
    /// Used by tests and the model self-check, not the solving path.
    pub fn eval(&self, assignment: &[bool]) -> bool {
        self.clauses.iter().all(|clause| {
            clause.iter().any(|&l| {
                let v = assignment[(l.unsigned_abs() - 1) as usize];
                if l > 0 { v } else { !v }
            })
        })
    }
}

/// The AIG-variable → CNF-variable correspondence produced by [`tseitin`].
#[derive(Clone, Debug)]
pub struct TseitinMap;

impl TseitinMap {
    /// CNF literal corresponding to an AIG literal.
    pub fn cnf_lit(&self, lit: Lit) -> CnfLit {
        let var = (lit.var() + 1) as CnfLit;
        if lit.is_complement() { -var } else { var }
    }
}

/// Tseitin-transform the AIG, asserting every literal in `outputs`.
///
/// Returns an equisatisfiable CNF: it is satisfiable iff some input
/// assignment makes all `outputs` true.
pub fn tseitin(aig: &Aig, outputs: &[Lit]) -> (CnfFormula, TseitinMap) {
    let map = TseitinMap;
    let mut clauses: Vec<Clause> = Vec::with_capacity(3 * aig.num_ands() as usize + 1);
    // Constant node (AIG var 0) is false: CNF var 1 is false.
    clauses.push(vec![-1]);
    // Three clauses per AND gate o = a & b:
    //   (¬o ∨ a) (¬o ∨ b) (o ∨ ¬a ∨ ¬b)
    for (var, a, b) in aig.and_gates() {
        let o = (var + 1) as CnfLit;
        let (la, lb) = (map.cnf_lit(a), map.cnf_lit(b));
        clauses.push(vec![-o, la]);
        clauses.push(vec![-o, lb]);
        clauses.push(vec![o, -la, -lb]);
    }
    for &out in outputs {
        clauses.push(vec![map.cnf_lit(out)]);
    }
    (
        CnfFormula {
            num_vars: aig.num_vars(),
            clauses,
        },
        map,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aig::word_input;

    /// Brute-force satisfiability of a CNF (≤ 24 vars) — test-only oracle.
    fn brute_sat(f: &CnfFormula) -> bool {
        let n = f.num_vars as usize;
        assert!(n <= 24);
        (0u32..1 << n).any(|bits| {
            let assignment: Vec<bool> = (0..n).map(|i| bits >> i & 1 == 1).collect();
            f.eval(&assignment)
        })
    }

    #[test]
    fn tseitin_is_equisatisfiable_on_random_circuits() {
        // Deterministic xorshift for reproducibility.
        let mut s: u64 = 0x9E3779B97F4A7C15;
        let mut next = move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        for round in 0..30 {
            let mut g = Aig::new();
            let inputs = word_input(&mut g, 5);
            // Build a random circuit over the inputs.
            let mut pool: Vec<Lit> = inputs.clone();
            // Cap the arena so the brute-force oracle (≤ 24 vars) stays feasible:
            // an xor costs 3 gates, so grow while there is headroom for one.
            while g.num_vars() < 21 {
                let a = pool[(next() % pool.len() as u64) as usize];
                let b = pool[(next() % pool.len() as u64) as usize];
                let lit = match next() % 3 {
                    0 => g.and(a, b),
                    1 => g.or(a, b),
                    _ => g.xor(a, b),
                };
                pool.push(if next() % 2 == 0 { lit } else { lit.not() });
            }
            let out = *pool.last().unwrap();

            // Semantic truth: does some input assignment make `out` true?
            let sem_sat = (0u32..32).any(|bits| {
                let iv: Vec<bool> = (0..5).map(|i| bits >> i & 1 == 1).collect();
                let vals = g.simulate(&iv);
                g.lit_value(&vals, out)
            });

            let (cnf, _) = tseitin(&g, &[out]);
            assert_eq!(
                brute_sat(&cnf),
                sem_sat,
                "round {round}: Tseitin must be equisatisfiable"
            );
            // Linear size: 1 const + 3 per gate + 1 output unit.
            assert_eq!(cnf.clauses.len(), 2 + 3 * g.num_ands() as usize);
        }
    }

    #[test]
    fn constant_outputs() {
        let g = Aig::new();
        let (cnf_true, _) = tseitin(&g, &[Lit::TRUE]);
        assert!(brute_sat(&cnf_true));
        let (cnf_false, _) = tseitin(&g, &[Lit::FALSE]);
        assert!(!brute_sat(&cnf_false));
    }

    #[test]
    fn conflicting_outputs_are_unsat() {
        let mut g = Aig::new();
        let x = g.input();
        let (cnf, _) = tseitin(&g, &[x, x.not()]);
        assert!(!brute_sat(&cnf));
    }
}
