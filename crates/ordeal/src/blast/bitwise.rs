//! Bitwise ops and (dis)equality (DES-005): bvand, bvor, bvxor, eq, ne.

use crate::aig::{Aig, Lit, Word};

/// `bvand` — per-bit AND.
pub fn blast_and(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    let _ = (aig, a, b);
    unimplemented!("DES-005 lands in wave 1")
}

/// `bvor` — per-bit OR.
pub fn blast_or(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    let _ = (aig, a, b);
    unimplemented!("DES-005 lands in wave 1")
}

/// `bvxor` — per-bit XOR.
pub fn blast_xor(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    let _ = (aig, a, b);
    unimplemented!("DES-005 lands in wave 1")
}

/// `=` — conjunction of per-bit XNORs.
pub fn blast_eq(aig: &mut Aig, a: &Word, b: &Word) -> Lit {
    let _ = (aig, a, b);
    unimplemented!("DES-005 lands in wave 1")
}

/// `distinct` — negation of equality.
pub fn blast_ne(aig: &mut Aig, a: &Word, b: &Word) -> Lit {
    let _ = (aig, a, b);
    unimplemented!("DES-005 lands in wave 1")
}
