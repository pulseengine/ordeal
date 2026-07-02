//! Add/sub and the eight ordered comparisons (DES-006).

use crate::aig::{Aig, Lit, Word};

/// `bvadd` — ripple-carry adder.
pub fn blast_add(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    let _ = (aig, a, b);
    unimplemented!("DES-006 lands in wave 1")
}

/// `bvsub` — add of two's complement (invert + carry-in 1).
pub fn blast_sub(aig: &mut Aig, a: &Word, b: &Word) -> Word {
    let _ = (aig, a, b);
    unimplemented!("DES-006 lands in wave 1")
}

/// `bvult` — unsigned less-than via the subtraction borrow chain.
pub fn blast_ult(aig: &mut Aig, a: &Word, b: &Word) -> Lit {
    let _ = (aig, a, b);
    unimplemented!("DES-006 lands in wave 1")
}

/// `bvule`.
pub fn blast_ule(aig: &mut Aig, a: &Word, b: &Word) -> Lit {
    let _ = (aig, a, b);
    unimplemented!("DES-006 lands in wave 1")
}

/// `bvugt`.
pub fn blast_ugt(aig: &mut Aig, a: &Word, b: &Word) -> Lit {
    let _ = (aig, a, b);
    unimplemented!("DES-006 lands in wave 1")
}

/// `bvuge`.
pub fn blast_uge(aig: &mut Aig, a: &Word, b: &Word) -> Lit {
    let _ = (aig, a, b);
    unimplemented!("DES-006 lands in wave 1")
}

/// `bvslt` — signed: unsigned compare with sign bits flipped.
pub fn blast_slt(aig: &mut Aig, a: &Word, b: &Word) -> Lit {
    let _ = (aig, a, b);
    unimplemented!("DES-006 lands in wave 1")
}

/// `bvsle`.
pub fn blast_sle(aig: &mut Aig, a: &Word, b: &Word) -> Lit {
    let _ = (aig, a, b);
    unimplemented!("DES-006 lands in wave 1")
}

/// `bvsgt`.
pub fn blast_sgt(aig: &mut Aig, a: &Word, b: &Word) -> Lit {
    let _ = (aig, a, b);
    unimplemented!("DES-006 lands in wave 1")
}

/// `bvsge`.
pub fn blast_sge(aig: &mut Aig, a: &Word, b: &Word) -> Lit {
    let _ = (aig, a, b);
    unimplemented!("DES-006 lands in wave 1")
}
