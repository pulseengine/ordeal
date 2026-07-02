//! Shifts and rotate (DES-007): barrel shifter with SMT-LIB out-of-range
//! semantics; bvrotr rotates by amount mod width.

use crate::aig::{Aig, Word};

/// `bvshl` — zero when the shift amount is ≥ width.
pub fn blast_shl(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    let _ = (aig, a, b);
    unimplemented!("DES-007 lands in wave 1")
}

/// `bvlshr` — zero when the shift amount is ≥ width.
pub fn blast_lshr(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    let _ = (aig, a, b);
    unimplemented!("DES-007 lands in wave 1")
}

/// `bvashr` — sign-fills; all sign bits when the amount is ≥ width.
pub fn blast_ashr(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    let _ = (aig, a, b);
    unimplemented!("DES-007 lands in wave 1")
}

/// `bvrotr` — rotate right by amount mod width.
pub fn blast_rotr(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    let _ = (aig, a, b);
    unimplemented!("DES-007 lands in wave 1")
}
