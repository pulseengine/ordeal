//! Minimal `ordeal` CLI.
//!
//! The decision engine is not yet implemented (phase-0 skeleton). This binary
//! exists so the crate builds a runnable artifact and so the command surface is
//! reserved; it prints a notice pointing at the roadmap.

fn main() {
    let version = env!("CARGO_PKG_VERSION");
    println!("ordeal {version}");
    println!("certificate-checked QF_BV SMT solver for the PulseEngine toolchain");
    println!();
    println!("engine not yet implemented — this is the phase-0 skeleton.");
    println!("The solver conservatively returns Unknown until the");
    println!("bit-blaster + SAT engine + verified LRAT checker land.");
    println!("See ROADMAP.md (phases P0–P5) for status.");
}
