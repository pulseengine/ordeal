{
  description = "ordeal — a pure-Rust, certificate-checked QF_BV SMT solver";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, rust-overlay }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs {
          inherit system overlays;
        };

        # Rust toolchain: stable, tracking rust-toolchain.toml.
        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
          extensions = [
            "rust-src"
            "rust-analyzer"
            "clippy"
            "rustfmt"
            "llvm-tools-preview"
          ];
        };

        commonPackages = [
          # -- Rust ---------------------------------------------------
          rustToolchain
          pkgs.cargo-nextest         # Better test runner
          pkgs.cargo-watch           # Watch mode

          # -- SMT oracle ---------------------------------------------
          # Z3 backs the optional `oracle` cargo feature, which
          # differential-checks ordeal's answers against Z3.
          pkgs.z3

          # -- General dev tools --------------------------------------
          pkgs.git
          pkgs.jq
        ];

        # Platform-specific packages
        darwinPackages = pkgs.lib.optionals pkgs.stdenv.hostPlatform.isDarwin (with pkgs; [
          libiconv
        ]);

      in
      {
        devShells.default = pkgs.mkShell {
          name = "ordeal-dev";

          buildInputs = commonPackages ++ darwinPackages;

          shellHook = ''
            echo "ordeal dev shell"
            echo "  rust:  $(rustc --version)"
            echo "  cargo: $(cargo --version)"
            echo "  z3:    $(z3 --version 2>&1 | head -1)"
            echo ""
            echo "Quick start:"
            echo "  cargo test --all                     # Run all tests"
            echo "  cargo clippy --all-targets            # Lint"
            echo "  cargo test --all --features oracle    # Z3 differential oracle"
          '';

          # Z3 headers for the optional `oracle` feature (z3-sys crate).
          Z3_SYS_Z3_HEADER = "${pkgs.z3.dev}/include/z3.h";

          # libclang for bindgen (used by z3-sys and other -sys crates)
          LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";
        };

        # Expose the Rust toolchain as a package for other flakes to consume.
        packages.rust-toolchain = rustToolchain;
      }
    );
}
