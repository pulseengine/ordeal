// rivet: verifies VER-042
//! The in-tree SHA-256 (`ordeal::sha256`, #162 / TR-045) checked against an
//! INDEPENDENT implementation (the `sha2` crate, a dev-dependency that never
//! ships) on every length 0..=200 — the 55/56/63/64-byte cases that decide
//! whether padding needs a second block all lie in this range. Lives as an
//! integration test so the library's own unit tests stay dependency-free
//! (Bazel's `rust_test` compiles those without Cargo dev-dependencies).

use sha2::Digest;

fn hex_of(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

#[test]
fn matches_sha2_across_padding_boundaries() {
    let mut x: u64 = 0x9e37_79b9_7f4a_7c15;
    for len in 0..=200usize {
        let mut buf = Vec::with_capacity(len);
        for _ in 0..len {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            buf.push((x & 0xff) as u8);
        }
        let expect = hex_of(&sha2::Sha256::digest(&buf));
        assert_eq!(ordeal::sha256::sha256_hex(&buf), expect, "len {len}");
    }
}

/// The hex spelling every `ordeal-cert/v1` hash uses is exactly what an
/// independent SHA-256 produces over the same canonical bytes (the CLI
/// baseline test checks this on real output; this pins the primitive).
#[test]
fn hex_spelling_matches_sha2() {
    for input in [&b""[..], b"abc", b"0110", b"a 8 -3 4 5 6 7 8 9 10\n"] {
        assert_eq!(
            ordeal::sha256::sha256_hex(input),
            hex_of(&sha2::Sha256::digest(input))
        );
    }
}
