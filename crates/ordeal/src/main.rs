//! Minimal `ordeal` CLI.
//!
//! The production interface is the Rust API (loom/synth embed the crate
//! in-process; there is no SMT-LIB front end by design — see TR-010/SYS-006).
//! This binary exists so the crate builds a runnable artifact and so the
//! command surface is reserved; it prints the engine status.

fn main() {
    let version = env!("CARGO_PKG_VERSION");
    println!("ordeal {version}");
    println!("certificate-checked QF_BV SMT solver for the PulseEngine toolchain");
    println!();
    println!("engine: certificate-checked pipeline (bit-blast -> AIG -> Tseitin ->");
    println!("own CDCL core -> LRAT). SAT verdicts carry self-checked models;");
    println!("UNSAT verdicts carry an LRAT certificate validated by the");
    println!("ordeal-lrat checker before being returned — an Unsat the checker");
    println!("did not accept is never reported. The checker's formal soundness");
    println!("proof (Aeneas -> Lean 4) is the remaining P2 obligation.");
    println!("See ROADMAP.md (phases P0-P5) for status.");
}
