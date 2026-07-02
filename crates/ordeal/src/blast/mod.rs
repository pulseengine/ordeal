//! Bit-blasting rules: each QF_BV operation lowered to AIG gates
//! (DES-005..DES-009), one module per op family.
//!
//! Words are LSB-first [`Word`](crate::aig::Word)s. Every rule is verified
//! against the concrete evaluator (DES-001): exhaustively at width 8,
//! randomized at widths 32/64. A rule that has not passed its UV measure is
//! not enabled in the pipeline (the P1 kill criterion).

pub mod arith;
pub mod bitwise;
pub mod muldiv;
pub mod shift;
pub mod structural;
