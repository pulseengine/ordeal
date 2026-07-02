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
    println!("engine: P1 pipeline (bit-blast -> AIG -> Tseitin -> own CDCL core).");
    println!("SAT verdicts carry self-checked counterexample models; engine-UNSAT");
    println!("is reported as Unknown until the P2 verified LRAT checker lands —");
    println!("an Unsat this build cannot certify is never returned.");
    println!("See ROADMAP.md (phases P0-P5) for status.");
}
