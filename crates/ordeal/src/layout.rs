//! Byte-layout helpers (TR-021): split a bitvector into little-endian bytes and
//! reassemble it, as pure `extract`/`concat` compositions over the closed
//! fragment — no new operations.
//!
//! These are the primitive the wire-codec and ABI-layout consumers asked for:
//! relay's CCSDS/MAVLink/NID encode-decode round-trips (`relay#265`), spar's
//! AADL↔WIT↔canonical-ABI field packing (`spar#327`, spar#319), and kiln's
//! `extend`/`wrap` conversions. Paired with [`crate::Solver::prove_equiv`] they
//! turn "does this codec round-trip?" and "does this record encode that layout?"
//! into a certificate-checked QF_BV query.
//!
//! Byte 0 is the **least significant** byte, matching `to_le_bytes` on Rust's
//! integers and the little-endian wire formats these consumers use.

use crate::term::BvTerm;

/// Split `x` into its little-endian bytes: index 0 is the least-significant
/// byte, index `width/8 - 1` the most significant. Each byte is an 8-bit
/// `extract`.
///
/// `width` must be a multiple of 8 (8/16/32/64 in the validated fragment); a
/// non-multiple would leave a partial byte and is rejected.
pub fn to_le_bytes(x: &BvTerm, width: u32) -> Vec<BvTerm> {
    assert!(
        width > 0 && width.is_multiple_of(8),
        "to_le_bytes: width {width} is not a positive multiple of 8"
    );
    (0..width / 8)
        .map(|i| BvTerm::Extract {
            hi: 8 * i + 7,
            lo: 8 * i,
            arg: Box::new(x.clone()),
        })
        .collect()
}

/// Reassemble a bitvector from little-endian bytes: `bytes[0]` is the
/// least-significant byte. The result is `8 * bytes.len()` bits wide.
///
/// Inverse of [`to_le_bytes`]: `from_le_bytes(&to_le_bytes(x, w))` is
/// equivalent to `x` for every `x` (see the round-trip tests).
pub fn from_le_bytes(bytes: &[BvTerm]) -> BvTerm {
    // `Concat(hi, lo)` places `hi` above `lo`, so fold from the least
    // significant byte upward.
    let mut it = bytes.iter();
    let mut acc = it
        .next()
        .expect("from_le_bytes: needs at least one byte")
        .clone();
    for higher in it {
        acc = BvTerm::Concat(Box::new(higher.clone()), Box::new(acc));
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::{Env, bv_sort, eval_bv};
    use crate::solver::{CheckResult, Solver};
    use crate::term::Sort;

    fn v(name: &str, w: u32) -> BvTerm {
        BvTerm::Var {
            name: name.into(),
            sort: Sort::new(w),
        }
    }

    #[test]
    fn to_le_bytes_extracts_each_byte_least_significant_first() {
        let w = 32;
        let x = v("x", w);
        let bytes = to_le_bytes(&x, w);
        assert_eq!(bytes.len(), 4);
        for (i, byte) in bytes.iter().enumerate() {
            assert_eq!(bv_sort(byte).unwrap().width, 8, "each byte is 8 bits");
            let mut env = Env::new();
            env.insert("x".into(), 0xDEAD_BEEF);
            let expected = (0xDEAD_BEEFu128 >> (8 * i)) & 0xFF;
            assert_eq!(eval_bv(byte, &env).unwrap(), expected, "byte {i}");
        }
    }

    #[test]
    fn round_trip_evaluates_identically_at_every_width() {
        for w in [8u32, 16, 32, 64] {
            let x = v("x", w);
            let rebuilt = from_le_bytes(&to_le_bytes(&x, w));
            assert_eq!(bv_sort(&rebuilt).unwrap().width, w, "width preserved");
            for val in [0u128, 1, 0xFF, 0x1234, 0xDEAD_BEEF, u64::MAX as u128] {
                let masked = if w >= 128 {
                    val
                } else {
                    val & ((1u128 << w) - 1)
                };
                let mut env = Env::new();
                env.insert("x".into(), masked);
                assert_eq!(
                    eval_bv(&rebuilt, &env).unwrap(),
                    masked,
                    "round-trip w{w} value {masked:#x}"
                );
            }
        }
    }

    #[test]
    fn round_trip_is_certificate_checked_equivalent() {
        // The consumer-facing shape: prove the codec round-trip for ALL inputs
        // with a re-checkable certificate, not just sampled values.
        for w in [16u32, 32] {
            let x = v("x", w);
            let rebuilt = from_le_bytes(&to_le_bytes(&x, w));
            match Solver::prove_equiv(x, rebuilt) {
                CheckResult::Unsat(cert) => {
                    cert.recheck()
                        .expect("round-trip certificate must re-check");
                }
                other => panic!("le-bytes round-trip must be proven at w{w}, got {other:?}"),
            }
        }
    }

    #[test]
    fn a_wrong_byte_order_is_caught_with_a_counterexample() {
        // Guard the oracle: reversing the bytes must NOT prove equivalent.
        let w = 32;
        let x = v("x", w);
        let mut bytes = to_le_bytes(&x, w);
        bytes.reverse(); // big-endian reassembly — wrong
        match Solver::prove_equiv(x, from_le_bytes(&bytes)) {
            CheckResult::Sat(_) => {}
            other => panic!("byte-swapped reassembly must be Sat, got {other:?}"),
        }
    }
}
