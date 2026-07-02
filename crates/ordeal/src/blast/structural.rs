//! Structural ops (DES-009): extract, concat, zero_ext, sign_ext.
//! Pure word plumbing — no gates.

use crate::aig::Word;

/// `extract[hi:lo]` (inclusive) — slice of the LSB-first word.
pub fn blast_extract(a: &Word, hi: u32, lo: u32) -> Word {
    let _ = (a, hi, lo);
    unimplemented!("DES-009 lands in wave 1")
}

/// `concat` — SMT-LIB: the FIRST operand becomes the high bits.
pub fn blast_concat(hi_part: &Word, lo_part: &Word) -> Word {
    let _ = (hi_part, lo_part);
    unimplemented!("DES-009 lands in wave 1")
}

/// `zero_ext` — append `by` FALSE literals above the MSB.
pub fn blast_zero_ext(a: &Word, by: u32) -> Word {
    let _ = (a, by);
    unimplemented!("DES-009 lands in wave 1")
}

/// `sign_ext` — replicate the sign literal `by` times.
pub fn blast_sign_ext(a: &Word, by: u32) -> Word {
    let _ = (a, by);
    unimplemented!("DES-009 lands in wave 1")
}
