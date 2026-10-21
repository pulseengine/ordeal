//! #192 phase 7 (TR-069): `ordeal check --format json --with-term` carries
//! the term the query was lowered from, and the JSON is itself evidence —
//! this test re-establishes both verdicts at the TERM level with the
//! trusted crate alone, decoding the blocks from the output.

use std::io::Write;
use std::process::{Command, Stdio};

fn ordeal_stdin(args: &[&str], input: &str) -> std::process::Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_ordeal"))
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ordeal");
    child
        .stdin
        .take()
        .expect("stdin")
        .write_all(input.as_bytes())
        .expect("write script");
    child.wait_with_output().expect("wait")
}

fn hex_of(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

const UNSAT_SCRIPT: &str = "(set-logic QF_BV)\n(declare-const a (_ BitVec 8))\n\
     (declare-const b (_ BitVec 8))\n(declare-const x (_ BitVec 8))\n\
     (assert (distinct (bvmul a b) (bvmul b a)))\n\
     (assert (bvugt (bvadd x (bvmul #x02 #x03)) (bvadd x #x06)))\n\
     (assert (distinct (bvsrem a b) (bvsub a (bvmul (bvsdiv a b) b))))\n(check-sat)\n";
const SAT_SCRIPT: &str = "(set-logic QF_BV)\n(declare-const a (_ BitVec 8))\n\
     (declare-const b (_ BitVec 8))\n(assert (= (bvadd a b) #x09))\n\
     (assert (bvugt b a))\n(assert (= (bvmul a #x02) b))\n(check-sat)\n";

fn nodes_of(v: &serde_json::Value) -> Vec<ordeal_lrat::blast_kernel::DagNode> {
    v.as_array()
        .expect("nodes")
        .iter()
        .map(|n| {
            let items = n.as_array().expect("node array");
            let op = items[0].as_str().expect("op");
            let args: Vec<usize> = items[1..]
                .iter()
                .map(|a| a.as_u64().expect("arg") as usize)
                .collect();
            ordeal::query::node_from_op(op, &args).expect("known op")
        })
        .collect()
}

fn usizes(v: &serde_json::Value) -> Vec<usize> {
    v.as_array()
        .expect("array")
        .iter()
        .map(|x| x.as_u64().expect("usize") as usize)
        .collect()
}

fn query_of(cert: &serde_json::Value) -> ordeal::QueryDag {
    ordeal::QueryDag {
        nodes: nodes_of(&cert["query"]["nodes"]),
        bits: ordeal::query::bits_from_string(cert["query"]["bits"].as_str().expect("bits"))
            .expect("bitstring"),
        roots: usizes(&cert["query"]["roots"]),
        hints: usizes(&cert["query"]["hints"]),
    }
}

fn term_of(cert: &serde_json::Value) -> ordeal::QueryTerm {
    ordeal::QueryTerm {
        nodes: nodes_of(&cert["term"]["nodes"]),
        bits: ordeal::query::bits_from_string(cert["term"]["bits"].as_str().expect("bits"))
            .expect("bitstring"),
        roots: usizes(&cert["term"]["roots"]),
        vars: cert["term"]["vars"]
            .as_array()
            .expect("vars")
            .iter()
            .map(|e| {
                (
                    e["name"].as_str().expect("name").to_string(),
                    e["width"].as_u64().expect("width") as u32,
                    e["node"].as_u64().expect("node") as usize,
                )
            })
            .collect(),
        map: usizes(&cert["term"]["map"]),
        shared: false,
    }
}

// rivet: verifies VER-069
/// `--with-term` on `unsat`: the term block is decoded from the JSON and
/// the trusted crate alone relates it to the query (`check_term_dag`) and
/// refutes the query (`check_query`); the term hash is checked with an
/// independent SHA-256; the term is the question as asked (`bvugt`, the
/// unfolded product, both `bvmul` orders); a term that asks a different
/// question is rejected.
#[test]
fn format_json_with_term_carries_a_recheckable_term() {
    use sha2::Digest;
    let out = ordeal_stdin(
        &["check", "-", "--format", "json", "--with-term"],
        UNSAT_SCRIPT,
    );
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let v: serde_json::Value = serde_json::from_slice(&out.stdout).expect("json");
    assert_eq!(v["verdict"], "unsat");
    let cert = &v["certificate"];
    assert_eq!(cert["term"]["encoding"], ordeal::query::TERM_ENCODING);
    let query = query_of(cert);
    let term = term_of(cert);
    assert_eq!(cert["term"]["num_nodes"], term.nodes.len());
    assert_eq!(
        ordeal_lrat::check_term_dag(
            &term.nodes,
            &term.bits,
            &term.roots,
            &term.map,
            &query.nodes,
            &query.bits,
            &query.roots
        ),
        Ok(()),
        "the trusted crate accepts the term-to-DAG correspondence"
    );
    let lrat = cert["lrat"].as_str().expect("lrat text");
    ordeal_lrat::check_query(&query.nodes, &query.bits, &query.roots, &query.hints, lrat)
        .expect("the trusted crate refutes the query");
    let expect = hex_of(&sha2::Sha256::digest(term.canonical_text().as_bytes()));
    assert_eq!(
        cert["term"]["sha256"], expect,
        "term hash (independent SHA-256)"
    );
    use ordeal_lrat::blast_kernel::DagNode as N;
    assert!(
        term.nodes.iter().any(|n| matches!(n, N::Ugt(_, _))),
        "bvugt as asked"
    );
    assert!(
        term.nodes
            .iter()
            .filter(|n| matches!(n, N::Mul(_, _)))
            .count()
            >= 3,
        "both bvmul orders and the constant product, unfolded"
    );
    assert!(term.nodes.iter().any(|n| matches!(n, N::Srem(_, _))));
    assert!(
        term.map.contains(&usize::MAX),
        "folded children have no image"
    );
    // A different question: `bvugt` turned into `bvuge` in the term.
    let mut other = term.clone();
    let i = other
        .nodes
        .iter()
        .position(|n| matches!(n, N::Ugt(_, _)))
        .unwrap();
    if let N::Ugt(x, y) = other.nodes[i] {
        other.nodes[i] = N::Uge(x, y);
    }
    assert!(
        ordeal_lrat::check_term_dag(
            &other.nodes,
            &other.bits,
            &other.roots,
            &other.map,
            &query.nodes,
            &query.bits,
            &query.roots
        )
        .is_err(),
        "a term asking a different question does not re-check against the same DAG"
    );
}

// rivet: verifies VER-069
/// `--with-term` on `sat`: the term, the query and the inputs are decoded
/// and the trusted crate alone accepts the correspondence, the model, and
/// the binding of every printed value through the term's variable map.
#[test]
fn format_json_with_term_carries_a_recheckable_model() {
    let out = ordeal_stdin(
        &["check", "-", "--format", "json", "--with-term"],
        SAT_SCRIPT,
    );
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let v: serde_json::Value = serde_json::from_slice(&out.stdout).expect("json");
    assert_eq!(v["verdict"], "sat");
    let cert = &v["certificate"];
    let query = query_of(cert);
    let term = term_of(cert);
    let inputs = ordeal::query::bits_from_string(cert["inputs"]["bits"].as_str().unwrap()).unwrap();
    assert_eq!(
        ordeal_lrat::check_term_dag(
            &term.nodes,
            &term.bits,
            &term.roots,
            &term.map,
            &query.nodes,
            &query.bits,
            &query.roots
        ),
        Ok(())
    );
    ordeal_lrat::check_query_model(&query.nodes, &query.bits, &query.roots, &inputs)
        .expect("the trusted crate accepts the model");
    let model = v["model"].as_array().expect("model");
    assert_eq!(model.len(), 2);
    for entry in model {
        let name = entry["name"].as_str().unwrap();
        let value = u128::from_str_radix(
            entry["value"].as_str().unwrap().trim_start_matches("#x"),
            16,
        )
        .unwrap();
        let (_, width, node) = term
            .vars
            .iter()
            .find(|(n, _, _)| n == name)
            .expect("a term variable");
        let image = term.map[*node];
        let offset = ordeal_lrat::var_offset(&query.nodes, image).unwrap();
        assert!(
            ordeal_lrat::check_input_value(&inputs, offset, *width as usize, value),
            "{name} = {value}"
        );
        assert!(!ordeal_lrat::check_input_value(
            &inputs,
            offset,
            *width as usize,
            value ^ 1
        ));
    }
    assert_eq!(
        (
            model[0]["value"].as_str().unwrap(),
            model[1]["value"].as_str().unwrap()
        ),
        ("#x03", "#x06")
    );
}

// rivet: verifies VER-069
/// `--with-term` is opt-in and JSON only, and its output is exactly the
/// `--with-query` output plus the `term` block; the default output and
/// the `--with-query` output are untouched.
#[test]
fn with_term_is_opt_in_and_a_superset_of_with_query() {
    for script in [UNSAT_SCRIPT, SAT_SCRIPT] {
        let plain = ordeal_stdin(&["check", "-", "--format", "json"], script);
        let vp: serde_json::Value = serde_json::from_slice(&plain.stdout).expect("json");
        assert!(
            vp["certificate"].get("term").is_none() && vp["certificate"].get("query").is_none()
        );
        let q = ordeal_stdin(&["check", "-", "--format", "json", "--with-query"], script);
        let t = ordeal_stdin(&["check", "-", "--format", "json", "--with-term"], script);
        let vq: serde_json::Value = serde_json::from_slice(&q.stdout).expect("json");
        let mut vt: serde_json::Value = serde_json::from_slice(&t.stdout).expect("json");
        assert!(
            vq["certificate"].get("term").is_none(),
            "--with-query carries no term"
        );
        let cert = vt["certificate"]
            .as_object_mut()
            .expect("certificate object");
        assert!(cert.remove("term").is_some(), "--with-term adds the term");
        assert_eq!(
            vq, vt,
            "--with-term output is the --with-query output plus the term"
        );
    }
    let out = ordeal_stdin(&["check", "-", "--with-term"], UNSAT_SCRIPT);
    assert_eq!(out.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&out.stderr).contains("--format json"));
    let help = Command::new(env!("CARGO_BIN_EXE_ordeal"))
        .arg("--help")
        .output()
        .expect("help");
    assert!(String::from_utf8_lossy(&help.stdout).contains("--with-term"));
}
