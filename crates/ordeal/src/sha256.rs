//! SHA-256 (FIPS 180-4), in-tree and dependency-free (#162 / TR-045).
//! Since TR-075 the implementation lives in the solver-free
//! `ordeal-cert` crate (`ordeal_cert::sha256`), re-exported here
//! unchanged; the known-answer tests stay here.

pub use ordeal_cert::sha256::*;

// rivet: verifies VER-042
#[cfg(test)]
mod tests {
    use super::*;

    // FIPS 180-4 / NIST CAVP known answers. (The differential against the
    // independent `sha2` crate lives in tests/sha256_differential.rs so the
    // library's unit tests stay free of dev-dependencies — Bazel's
    // `rust_test` compiles them without Cargo's dev-deps.)
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
}
