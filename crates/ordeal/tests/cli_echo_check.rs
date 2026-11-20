//! `ordeal echo-check` with the real binary (#281 E3, TR-098): the
//! end-to-end leg (every repository script ordeal certifies unsat, and the
//! gale Verus logs, through `--cert-out … --echo` and `echo-check`), its
//! negative controls, and the refusal in a build without the features.

use std::process::{Command, Output};

const ORDEAL: &str = env!("CARGO_BIN_EXE_ordeal");

fn ordeal(args: &[&str]) -> Output {
    Command::new(ORDEAL)
        .args(args)
        .output()
        .expect("run ordeal")
}

fn code(o: &Output) -> i32 {
    o.status.code().expect("exit code")
}

// rivet: verifies VER-098
#[cfg(not(all(feature = "oracle", feature = "cert-bundle")))]
#[test]
fn echo_check_without_the_features_exits_2() {
    let o = ordeal(&["echo-check", "a.smt2", "b.json"]);
    assert_eq!(code(&o), 2);
    assert!(String::from_utf8_lossy(&o.stderr).contains("--features oracle,cert-bundle"));
}

#[cfg(all(feature = "oracle", feature = "cert-bundle"))]
mod with_z3 {
    use super::*;
    use std::path::{Path, PathBuf};

    fn scratch(tag: &str) -> PathBuf {
        let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("echo-check-{tag}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        d
    }

    fn fixture(name: &str) -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures")
            .join(name)
    }

    const VERUS_MARKER: &str = ";; query spun off because: bitvector";

    fn smt2_files(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for e in entries.flatten() {
            let p = e.path();
            let name = e.file_name().to_string_lossy().into_owned();
            if p.is_dir() {
                if !name.starts_with('.')
                    && !matches!(name.as_str(), "target" | "node_modules" | "fuzz")
                    && !name.starts_with("target")
                {
                    smt2_files(&p, out);
                }
            } else if name.ends_with(".smt2") {
                out.push(p);
            }
        }
    }

    /// Certify `file` with `--echo`; the v5 bundle's path if the verdict is
    /// unsat and the printer did not refuse.
    fn unsat_v5(file: &Path, dir: &Path) -> Option<PathBuf> {
        let log = std::fs::read_to_string(file).ok()?;
        let stem = file.file_stem()?.to_string_lossy().into_owned();
        let bundle = if log.contains(VERUS_MARKER) {
            ordeal(&[
                "verus",
                file.to_str()?,
                "--cert-out",
                dir.to_str()?,
                "--echo",
            ]);
            dir.join(format!("{stem}.cert.json"))
        } else {
            let out = dir.join(format!("{stem}.cert.json"));
            ordeal(&[
                "check",
                file.to_str()?,
                "--cert-out",
                out.to_str()?,
                "--echo",
                "--timeout-ms",
                "20000",
            ]);
            out
        };
        let json = std::fs::read_to_string(&bundle).ok()?;
        let compact: String = json.chars().filter(|c| !c.is_whitespace()).collect();
        (compact.contains("\"format\":\"ordeal-cert/v5\"")
            && compact.contains("\"verdict\":\"unsat\""))
        .then_some(bundle)
    }

    // rivet: verifies VER-098
    #[test]
    fn every_certified_repository_script_implies_its_echo() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let mut files = Vec::new();
        smt2_files(&root, &mut files);
        files.sort();
        let dir = scratch("corpus");
        let (mut compared, mut verus) = (0, 0);
        let mut failures = Vec::new();
        for f in &files {
            let Some(bundle) = unsat_v5(f, &dir) else {
                continue;
            };
            let o = ordeal(&["echo-check", f.to_str().unwrap(), bundle.to_str().unwrap()]);
            compared += 1;
            if std::fs::read_to_string(f).unwrap().contains(VERUS_MARKER) {
                verus += 1;
            }
            if code(&o) != 0 {
                failures.push(format!(
                    "{}: exit {} {}{}",
                    f.display(),
                    code(&o),
                    String::from_utf8_lossy(&o.stdout),
                    String::from_utf8_lossy(&o.stderr)
                ));
            }
        }
        eprintln!(
            "echo-check: {compared} unsat v5 bundles compared ({verus} Verus logs) of {} .smt2 files",
            files.len()
        );
        assert!(failures.is_empty(), "{}", failures.join("\n"));
        // A run that compared nothing does not pass; the gale logs must be in it.
        assert!(compared >= 10, "only {compared} bundles compared");
        assert!(verus >= 2, "only {verus} Verus logs compared");
    }

    /// An unsat script with a satisfiable weakening (drop the last assert).
    const UNSAT: &str = "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n\
        (declare-const y (_ BitVec 8))\n(assert (bvult x y))\n(assert (bvult y x))\n\
        (check-sat)\n";

    fn certify(dir: &Path) -> (PathBuf, PathBuf) {
        let input = dir.join("q.smt2");
        std::fs::write(&input, UNSAT).unwrap();
        let bundle = dir.join("q.cert.json");
        let o = ordeal(&[
            "check",
            input.to_str().unwrap(),
            "--cert-out",
            bundle.to_str().unwrap(),
            "--echo",
        ]);
        assert_eq!(String::from_utf8_lossy(&o.stdout).trim(), "unsat");
        (input, bundle)
    }

    // rivet: verifies VER-098
    #[test]
    fn a_weaker_input_is_not_implied_and_the_script_is_written() {
        let dir = scratch("weaker");
        let (_, bundle) = certify(&dir);
        let weaker = dir.join("weaker.smt2");
        std::fs::write(&weaker, UNSAT.replace("(assert (bvult y x))\n", "")).unwrap();
        let script = dir.join("cmp.smt2");
        let o = ordeal(&[
            "echo-check",
            weaker.to_str().unwrap(),
            bundle.to_str().unwrap(),
            "--script-out",
            script.to_str().unwrap(),
            "--format",
            "json",
        ]);
        assert_eq!(code(&o), 1, "{}", String::from_utf8_lossy(&o.stdout));
        assert!(String::from_utf8_lossy(&o.stdout).contains("\"result\":\"not-implied\""));
        let text = std::fs::read_to_string(&script).unwrap();
        assert!(text.contains("(assert (= |x| |e.x|))"), "{text}");
        assert!(text.ends_with("(check-sat)\n"));
    }

    // rivet: verifies VER-098
    #[test]
    fn a_tampered_or_sat_bundle_is_refused() {
        let dir = scratch("tamper");
        let (input, bundle) = certify(&dir);
        let i = input.to_str().unwrap();
        assert_eq!(
            code(&ordeal(&["echo-check", i, bundle.to_str().unwrap()])),
            0
        );

        // An echo byte flipped: refused by hash when the bundle is read.
        let json = std::fs::read_to_string(&bundle).unwrap();
        let flipped = dir.join("flipped.json");
        std::fs::write(&flipped, json.replacen("bvult", "bvule", 1)).unwrap();
        assert_ne!(std::fs::read_to_string(&flipped).unwrap(), json);
        assert_eq!(
            code(&ordeal(&["echo-check", i, flipped.to_str().unwrap()])),
            2
        );

        // A sat bundle: the echo is for unsat; check the model instead.
        let sat = dir.join("sat.smt2");
        std::fs::write(&sat, UNSAT.replace("(assert (bvult y x))\n", "")).unwrap();
        let sat_bundle = dir.join("sat.cert.json");
        ordeal(&[
            "check",
            sat.to_str().unwrap(),
            "--cert-out",
            sat_bundle.to_str().unwrap(),
            "--echo",
        ]);
        let o = ordeal(&[
            "echo-check",
            sat.to_str().unwrap(),
            sat_bundle.to_str().unwrap(),
        ]);
        assert_eq!(code(&o), 2);
        assert!(String::from_utf8_lossy(&o.stderr).contains("sat bundle"));

        // Usage errors.
        assert_eq!(code(&ordeal(&["echo-check", i])), 2);
        assert_eq!(code(&ordeal(&["echo-check", i, i, "--bogus"])), 2);
    }

    // rivet: verifies VER-098
    #[test]
    fn the_gale_verus_log_implies_its_echo() {
        let dir = scratch("gale");
        for name in [
            "verus_gale_cpu_mask_raw.smt2",
            "verus_gale_mpu_pow2_raw.smt2",
        ] {
            let log = fixture(name);
            let bundle = unsat_v5(&log, &dir).expect("an unsat v5 bundle");
            let o = ordeal(&[
                "echo-check",
                log.to_str().unwrap(),
                bundle.to_str().unwrap(),
            ]);
            assert_eq!(
                code(&o),
                0,
                "{name}: {}",
                String::from_utf8_lossy(&o.stdout)
            );
        }
    }
}
