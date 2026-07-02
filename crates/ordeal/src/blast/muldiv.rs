//! Multiplication and unsigned division (DES-008): shift-add partial
//! products; restoring long division with the SMT-LIB divide-by-zero case
//! (divisor = 0 ⇒ all-ones quotient) merged via a divisor-is-zero mux.

use crate::aig::{Aig, Word};

/// `bvmul` — truncated shift-add partial-product sum.
pub fn blast_mul(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    let _ = (aig, a, b);
    unimplemented!("DES-008 lands in wave 1")
}

/// `bvudiv` — restoring division; divisor 0 yields all-ones.
pub fn blast_udiv(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    let _ = (aig, a, b);
    unimplemented!("DES-008 lands in wave 1")
}
