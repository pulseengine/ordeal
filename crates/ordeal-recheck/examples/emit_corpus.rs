//! Write the TR-075 bundle corpus (`tests/corpus/mod.rs`) to a directory,
//! one `ordeal-cert/v1`..`v4` bundle per file — real solver output for an
//! auditor to feed to `ordeal-recheck`:
//!
//! ```sh
//! cargo run -p ordeal-recheck --example emit_corpus -- target/corpus
//! cargo run -p ordeal-recheck -- target/corpus/v[1-4]-*sat*.json
//! ```

#[path = "../tests/corpus/mod.rs"]
mod corpus;

use std::process::ExitCode;

fn main() -> ExitCode {
    let Some(dir) = std::env::args().nth(1) else {
        eprintln!("usage: emit_corpus <OUT-DIR>");
        return ExitCode::from(2);
    };
    if let Err(e) = std::fs::create_dir_all(&dir) {
        eprintln!("emit_corpus: {dir}: {e}");
        return ExitCode::FAILURE;
    }
    for e in corpus::corpus() {
        let path = std::path::Path::new(&dir).join(&e.name);
        if let Err(err) = std::fs::write(&path, e.json.as_bytes()) {
            eprintln!("emit_corpus: {}: {err}", path.display());
            return ExitCode::FAILURE;
        }
        println!("{}", path.display());
    }
    ExitCode::SUCCESS
}
