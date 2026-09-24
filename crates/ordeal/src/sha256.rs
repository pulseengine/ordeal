//! SHA-256 (FIPS 180-4), in-tree and dependency-free (#162 / TR-045).
//!
//! Why hand-rolled: the `ordeal-cert/v1` witness block carries two content
//! hashes (`assignment_sha256`, `bit_map_sha256`) that rivet reads as
//! `witness-sha256` / `bit-map-sha256`, and the shipped `ordeal` binary is
//! the DEFAULT build — dependency-free by CI-asserted policy (the SBOM's
//! component set is exactly `ordeal-lrat`). Pulling `sha2` into the release
//! closure was one of the four options on #162; the user chose this one.
//!
//! Trust note: these hashes are **integrity** only — they let a reader
//! detect a bundle that was edited in transit. They carry no part of the
//! soundness argument: SAT is re-established by `ordeal_lrat::check_sat` /
//! `check_binding` over the plain clauses and assignment, UNSAT by the
//! verified LRAT checker. A wrong hash here can only make a valid bundle
//! be REJECTED, never make an invalid one accepted. Tested against the
//! FIPS known-answer vectors and, in `cargo test`, differentially against
//! the `sha2` crate (a dev-dependency — it never ships).

const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

const H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// Process one 64-byte block into the running state.
fn compress(state: &mut [u32; 8], block: &[u8]) {
    debug_assert_eq!(block.len(), 64);
    let mut w = [0u32; 64];
    for (t, word) in w.iter_mut().enumerate().take(16) {
        *word = u32::from_be_bytes([
            block[4 * t],
            block[4 * t + 1],
            block[4 * t + 2],
            block[4 * t + 3],
        ]);
    }
    for t in 16..64 {
        let s0 = w[t - 15].rotate_right(7) ^ w[t - 15].rotate_right(18) ^ (w[t - 15] >> 3);
        let s1 = w[t - 2].rotate_right(17) ^ w[t - 2].rotate_right(19) ^ (w[t - 2] >> 10);
        w[t] = w[t - 16]
            .wrapping_add(s0)
            .wrapping_add(w[t - 7])
            .wrapping_add(s1);
    }
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;
    for t in 0..64 {
        let big_s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let ch = (e & f) ^ (!e & g);
        let t1 = h
            .wrapping_add(big_s1)
            .wrapping_add(ch)
            .wrapping_add(K[t])
            .wrapping_add(w[t]);
        let big_s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        let maj = (a & b) ^ (a & c) ^ (b & c);
        let t2 = big_s0.wrapping_add(maj);
        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
    }
    for (s, v) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
        *s = s.wrapping_add(v);
    }
}

/// The SHA-256 digest of `bytes`.
#[must_use]
pub fn sha256(bytes: &[u8]) -> [u8; 32] {
    let mut state = H0;
    let mut chunks = bytes.chunks_exact(64);
    for block in &mut chunks {
        compress(&mut state, block);
    }
    // Padding: 0x80, zeros to 56 mod 64, then the bit length big-endian.
    let rem = chunks.remainder();
    let mut tail = [0u8; 128];
    tail[..rem.len()].copy_from_slice(rem);
    tail[rem.len()] = 0x80;
    let tail_len = if rem.len() < 56 { 64 } else { 128 };
    let bit_len = (bytes.len() as u64).wrapping_mul(8);
    tail[tail_len - 8..tail_len].copy_from_slice(&bit_len.to_be_bytes());
    for block in tail[..tail_len].chunks_exact(64) {
        compress(&mut state, block);
    }
    let mut out = [0u8; 32];
    for (i, word) in state.iter().enumerate() {
        out[4 * i..4 * i + 4].copy_from_slice(&word.to_be_bytes());
    }
    out
}

/// The SHA-256 digest of `bytes` as 64 lowercase hex characters — the
/// spelling every `ordeal-cert/v1` content hash uses.
#[must_use]
pub fn sha256_hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(64);
    for b in sha256(bytes) {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

// rivet: verifies VER-042
#[cfg(test)]
mod tests {
    use super::*;

    /// Lowercase hex of an independent digest (sha2 0.11 arrays have no LowerHex).
    fn hex_of(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    // FIPS 180-4 / NIST CAVP known answers.
    #[test]
    fn fips_known_answers() {
        assert_eq!(
            sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(
            sha256_hex(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
        assert_eq!(
            sha256_hex(
                b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"
            ),
            "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"
        );
        // One million 'a' — exercises many blocks and the length field.
        let million = vec![b'a'; 1_000_000];
        assert_eq!(
            sha256_hex(&million),
            "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
        );
    }

    /// Padding boundaries: every length from 0 to 200 bytes crosses the
    /// 55/56/63/64-byte cases that decide whether padding needs a second
    /// block. Checked against the independent `sha2` crate (dev-dep).
    #[test]
    fn matches_sha2_across_padding_boundaries() {
        use sha2::Digest;
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
            assert_eq!(sha256_hex(&buf), expect, "len {len}");
        }
    }
}
