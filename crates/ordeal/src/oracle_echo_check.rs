//! `ordeal echo-check` (#281 E3, design note §2): does the consumer's own
//! script imply the certified echo of an `unsat` bundle?
//!
//! An `ordeal-cert/v5` bundle carries the echo `E`: the query ordeal
//! certified, printed back as SMT-LIB by the trusted printer and re-derived
//! by the recheck. The proven chain gives "`E` is unsatisfiable" under the
//! Lean model of SMT-LIB meaning. The consumer's script `I` is another
//! matter: ordeal's reader turned `I` into the certified tree, and the
//! reader is not proven. This module writes the one-direction comparison
//! the design note describes, and runs it with Z3:
//!
//! 1. `I`'s commands up to its `check-sat`, verbatim, minus commands with
//!    no meaning for the assertions (`set-logic`, `set-option`, `set-info`,
//!    `get-…`, `echo`);
//! 2. `E`'s constants renamed by the byte substitution `|n|` → `|e.n|` (a
//!    prefix no name of `I` starts with), its functions shared with `I`;
//! 3. a link per constant `I` declares: `(= |n| |e.n|)`, or
//!    `(= |n| (= |e.n| #b1))` when `I` declares `n` as `Bool` (ordeal holds
//!    a `Bool` as a BV1 variable);
//! 4. `(assert (not (and E₁ … Eₙ)))` and `(check-sat)`.
//!
//! **`unsat` means `I ⊨ E`**, so the certified `unsat` holds for `I`.
//! `sat` means `I` does not imply `E`: the certificate is not about this
//! input. A name `E` uses and `I` does not declare is left unlinked, which
//! only makes `unsat` harder to reach. A sort error in a link (a name ordeal
//! read with another sort than Z3 does) is Z3 refusing the script, never a
//! false `unsat`.
//!
//! The script is the output: [`Comparison::script`] runs the same way
//! under `z3 script.smt2`, so the comparison can be audited and re-run with
//! any solver.
//!
//! **Blind spot.** `I ⊨ E` holds for every `E` when `I` is itself unsat,
//! and Z3 may show that without looking at `E`. So `implied` on an unsat
//! input says the input is unsat (by Z3, the solver the consumer chose for
//! this check), not that ordeal read it right; a misread echo of an unsat
//! input still passes. The certificate's own value is that the
//! comparison is usually easy for Z3 (the echo is the input's own
//! assertions, renamed) while the original query may not be.
//!
//! What it trusts: Z3 and its parser for one implication, this module (it
//! writes the script; the script can be read), and the Lean model of
//! SMT-LIB meaning the printer is proven against. Not trusted by ordeal,
//! not on any verdict path (`oracle.rs` header).
//!
//! # Refused inputs
//!
//! `push`, `pop`, `reset`, `reset-assertions` and `check-sat-assuming`:
//! the comparison would have to model scopes or assumptions, and a script
//! that Z3 reads with a popped assertion still in force would make `I`
//! look stronger than it is. They are refused ("cannot compare"), which is
//! not a verdict.

use super::front::{Z3Reading, z3_read};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use z3::{Params, SatResult, Solver};

/// The default Z3 time limit for the comparison, in milliseconds.
pub const ECHO_CHECK_TIMEOUT_MS: u32 = 60_000;

/// The comparison script and what went into it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Comparison {
    /// The SMT-LIB script; `unsat` means the input implies the echo.
    pub script: String,
    /// The prefix the echo's constants were renamed with (`e.`, or `e1.`,
    /// `e2.`, … when a name of the input starts with `e.`).
    pub prefix: String,
    /// Links written (one per echo constant the input declares).
    pub links: usize,
    /// The echo's assertions.
    pub echo_asserts: usize,
}

/// Why no comparison script could be written. Not a verdict.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScriptError {
    /// The input script could not be split into commands, or uses a
    /// command the comparison does not model.
    Input(String),
    /// The echo is not in the printer's layout.
    Echo(String),
}

impl std::fmt::Display for ScriptError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ScriptError::Input(m) => write!(f, "input: {m}"),
            ScriptError::Echo(m) => write!(f, "echo: {m}"),
        }
    }
}

/// What Z3 made of the comparison.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EchoCheck {
    /// `unsat`: the input implies the echo.
    Implied,
    /// `sat`: the input does not imply the echo; Z3's model.
    NotImplied(String),
    /// Z3 refused the script or could not decide it; the reason.
    Unknown(String),
}

// ─── A small s-expression splitter (untrusted; its output is the script) ────

#[derive(Clone, Debug, PartialEq, Eq)]
enum Sx {
    /// A symbol by its content (`|x|` and `x` are one symbol), a numeral,
    /// a keyword or a string literal (with its quotes).
    Atom(String),
    List(Vec<Sx>),
}

impl Sx {
    fn atom(&self) -> Option<&str> {
        match self {
            Sx::Atom(a) => Some(a),
            Sx::List(_) => None,
        }
    }
}

/// One top-level command: its bytes in the input and its tree.
struct Command {
    start: usize,
    end: usize,
    items: Vec<Sx>,
}

fn commands(input: &str) -> Result<Vec<Command>, String> {
    let b = input.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();
    // (start of the open list, its items so far)
    let mut stack: Vec<(usize, Vec<Sx>)> = Vec::new();
    while i < b.len() {
        let c = b[i];
        match c {
            b' ' | b'\t' | b'\r' | b'\n' => i += 1,
            b';' => {
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
            }
            b'(' => {
                stack.push((i, Vec::new()));
                i += 1;
            }
            b')' => {
                let (start, items) = stack.pop().ok_or(format!("unbalanced ')' at byte {i}"))?;
                i += 1;
                match stack.last_mut() {
                    Some((_, parent)) => parent.push(Sx::List(items)),
                    None => out.push(Command {
                        start,
                        end: i,
                        items,
                    }),
                }
            }
            _ => {
                let begin = i;
                let atom = if c == b'|' {
                    let close = b[i + 1..]
                        .iter()
                        .position(|&x| x == b'|')
                        .ok_or(format!("unterminated quoted symbol at byte {begin}"))?;
                    i += close + 2;
                    input[begin + 1..i - 1].to_string()
                } else if c == b'"' {
                    i += 1;
                    loop {
                        match b.get(i) {
                            None => return Err(format!("unterminated string at byte {begin}")),
                            Some(b'"') if b.get(i + 1) == Some(&b'"') => i += 2,
                            Some(b'"') => {
                                i += 1;
                                break;
                            }
                            Some(_) => i += 1,
                        }
                    }
                    input[begin..i].to_string()
                } else {
                    while i < b.len()
                        && !matches!(
                            b[i],
                            b' ' | b'\t' | b'\r' | b'\n' | b'(' | b')' | b';' | b'|' | b'"'
                        )
                    {
                        i += 1;
                    }
                    input[begin..i].to_string()
                };
                match stack.last_mut() {
                    Some((_, items)) => items.push(Sx::Atom(atom)),
                    None => return Err(format!("a top-level atom at byte {begin}: `{atom}`")),
                }
            }
        }
    }
    if let Some((start, _)) = stack.last() {
        return Err(format!("unclosed '(' at byte {start}"));
    }
    Ok(out)
}

// ─── The comparison script ───────────────────────────────────────────────────

/// Commands with no meaning for the assertions in force at `check-sat`.
fn dropped(head: &str) -> bool {
    matches!(head, "set-logic" | "set-option" | "set-info" | "echo") || head.starts_with("get-")
}

/// Commands whose meaning the comparison does not model.
fn refused(head: &str) -> bool {
    matches!(
        head,
        "push" | "pop" | "reset" | "reset-assertions" | "check-sat-assuming"
    )
}

/// `|n|` → `|<prefix>n|` for every name of `line` not in `keep`. Exact
/// without a parser: every name in the echo is quoted, no other token is,
/// and no name contains `|` (the printer's layout, re-derived by the
/// recheck).
fn rename(line: &str, prefix: &str, keep: &BTreeSet<String>) -> Result<String, ScriptError> {
    let parts: Vec<&str> = line.split('|').collect();
    if parts.len().is_multiple_of(2) {
        return Err(ScriptError::Echo(format!("odd number of '|' in `{line}`")));
    }
    let mut out = String::with_capacity(line.len() + 8);
    for (k, p) in parts.iter().enumerate() {
        if !k.is_multiple_of(2) {
            out.push('|');
            if !keep.contains(*p) {
                out.push_str(prefix);
            }
            out.push_str(p);
            out.push('|');
        } else {
            out.push_str(p);
        }
    }
    Ok(out)
}

/// The first quoted name on a line.
fn first_name(line: &str) -> Option<&str> {
    let a = line.find('|')?;
    let b = line[a + 1..].find('|')?;
    Some(&line[a + 1..a + 1 + b])
}

/// Write the comparison script for input `input` and echo `echo` (the
/// bundle's `echo.text`). See the module header.
pub fn comparison_script(input: &str, echo: &str) -> Result<Comparison, ScriptError> {
    if input.contains('\0') {
        return Err(ScriptError::Input("NUL byte in the input".into()));
    }
    let cmds = commands(input).map_err(ScriptError::Input)?;

    // 1. The input, up to its check-sat.
    let mut kept = String::new();
    let mut declared: BTreeMap<String, bool> = BTreeMap::new(); // name -> is Bool
    let mut names: BTreeSet<String> = BTreeSet::new();
    let mut reached_check_sat = false;
    for c in &cmds {
        let head = c.items.first().and_then(Sx::atom).unwrap_or("");
        if head == "check-sat" {
            reached_check_sat = true;
            break;
        }
        if head == "exit" {
            break;
        }
        if refused(head) {
            return Err(ScriptError::Input(format!(
                "`{head}` is not compared (scopes and assumptions are not modelled)"
            )));
        }
        if dropped(head) {
            continue;
        }
        if (head.starts_with("declare-") || head.starts_with("define-"))
            && let Some(name) = c.items.get(1).and_then(Sx::atom)
        {
            names.insert(name.to_string());
            let sort = match (head, c.items.get(2)) {
                ("declare-const", s) => s,
                ("declare-fun", Some(Sx::List(args))) if args.is_empty() => c.items.get(3),
                _ => None,
            };
            if let Some(s) = sort {
                declared.insert(name.to_string(), s.atom() == Some("Bool"));
            }
        }
        kept.push_str(&input[c.start..c.end]);
        kept.push('\n');
    }

    // 2. The echo: functions shared, constants renamed.
    let lines: Vec<&str> = echo.lines().collect();
    if !lines.first().is_some_and(|l| l.starts_with("(set-logic ")) {
        return Err(ScriptError::Echo("does not open with (set-logic …)".into()));
    }
    if lines.last() != Some(&"(check-sat)") {
        return Err(ScriptError::Echo("does not end with (check-sat)".into()));
    }
    let mut funs: BTreeSet<String> = BTreeSet::new();
    for l in &lines {
        if l.starts_with("(declare-fun ") {
            let n = first_name(l).ok_or_else(|| ScriptError::Echo(format!("no name in `{l}`")))?;
            funs.insert(n.to_string());
        }
    }
    let mut prefix = String::from("e.");
    let mut k = 0;
    while names.iter().any(|n| n.starts_with(&prefix)) {
        k += 1;
        prefix = format!("e{k}.");
    }
    let mut consts: Vec<String> = Vec::new();
    let mut decls = String::new();
    let mut bodies: Vec<String> = Vec::new();
    for l in &lines[1..lines.len() - 1] {
        if l.starts_with("(declare-fun ") {
            continue;
        } else if l.starts_with("(declare-const ") {
            let n = first_name(l).ok_or_else(|| ScriptError::Echo(format!("no name in `{l}`")))?;
            consts.push(n.to_string());
            decls.push_str(&rename(l, &prefix, &funs)?);
            decls.push('\n');
        } else if let Some(body) = l.strip_prefix("(assert ").and_then(|r| r.strip_suffix(')')) {
            bodies.push(rename(body, &prefix, &funs)?);
        } else {
            return Err(ScriptError::Echo(format!("unexpected line `{l}`")));
        }
    }

    // 3. Links; 4. the negated echo.
    let mut s = String::new();
    s.push_str("; ordeal echo-check (#281 E3): unsat means the input implies the\n");
    s.push_str("; certified echo, so the bundle's unsat holds for the input.\n");
    if !reached_check_sat {
        s.push_str("; (the input has no check-sat: every command up to the end is kept)\n");
    }
    s.push_str("; ---- the input, up to its check-sat\n");
    s.push_str(&kept);
    let _ = writeln!(
        s,
        "; ---- the certified echo, constants renamed with `{prefix}`"
    );
    s.push_str(&decls);
    s.push_str("; ---- links\n");
    let mut links = 0;
    for n in &consts {
        match declared.get(n) {
            Some(true) => {
                let _ = writeln!(s, "(assert (= |{n}| (= |{prefix}{n}| #b1)))");
                links += 1;
            }
            Some(false) => {
                let _ = writeln!(s, "(assert (= |{n}| |{prefix}{n}|))");
                links += 1;
            }
            None => {
                let _ = writeln!(s, "; |{n}|: not declared by the input, left unlinked");
            }
        }
    }
    s.push_str("; ---- not the echo\n");
    match bodies.len() {
        0 => s.push_str("(assert false)\n"),
        1 => {
            let _ = writeln!(s, "(assert (not {}))", bodies[0]);
        }
        _ => {
            let _ = writeln!(s, "(assert (not (and {})))", bodies.join(" "));
        }
    }
    s.push_str("(check-sat)\n");
    Ok(Comparison {
        script: s,
        prefix,
        links,
        echo_asserts: bodies.len(),
    })
}

/// Run a comparison script with Z3 (time limit `timeout_ms`).
pub fn run(script: &str, timeout_ms: u32) -> EchoCheck {
    let assertions = match z3_read(script) {
        Z3Reading::Accepted(a) => a,
        Z3Reading::Refused(m) => return EchoCheck::Unknown(format!("Z3 refuses the script: {m}")),
    };
    let solver = Solver::new();
    let mut params = Params::new();
    params.set_u32("timeout", timeout_ms);
    solver.set_params(&params);
    for a in &assertions {
        solver.assert(a);
    }
    match solver.check() {
        SatResult::Unsat => EchoCheck::Implied,
        SatResult::Sat => EchoCheck::NotImplied(
            solver
                .get_model()
                .map(|m| m.to_string())
                .unwrap_or_default(),
        ),
        SatResult::Unknown => EchoCheck::Unknown(format!(
            "Z3 could not decide ({})",
            solver.get_reason_unknown().unwrap_or_default()
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn echo_of(script: &str) -> String {
        let reading = crate::smtlib::read_script(script).expect("ordeal reads it");
        match super::super::echo::echo_core(&reading.assertions) {
            super::super::echo::Echoed::Text(t) => String::from_utf8(t).unwrap(),
            other => panic!("no echo: {other:?}"),
        }
    }

    fn check(input: &str, echo: &str) -> EchoCheck {
        let c = comparison_script(input, echo).expect("script");
        run(&c.script, ECHO_CHECK_TIMEOUT_MS)
    }

    const UNSAT: &str = "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n\
        (declare-const |a b| (_ BitVec 8))\n(declare-const p Bool)\n\
        (assert (bvult x #x10))\n(assert (bvugt x |a b|))\n(assert (= |a b| #x20))\n\
        (assert p)\n(check-sat)\n(get-model)\n";

    // rivet: verifies VER-098
    #[test]
    fn the_input_implies_its_own_echo() {
        assert_eq!(check(UNSAT, &echo_of(UNSAT)), EchoCheck::Implied);
    }

    // rivet: verifies VER-098
    #[test]
    fn a_weaker_input_does_not_imply_the_echo() {
        // Drop the third assertion from the input: the echo still has it.
        let weaker = UNSAT.replace("(assert (= |a b| #x20))\n", "");
        match check(&weaker, &echo_of(UNSAT)) {
            EchoCheck::NotImplied(_) => {}
            other => panic!("expected NotImplied, got {other:?}"),
        }
    }

    /// `UNSAT` without its contradiction: satisfiable, so an implication
    /// from it says something about the echo.
    const SAT: &str = "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n\
        (declare-const |a b| (_ BitVec 8))\n(declare-const p Bool)\n\
        (assert (bvult x #x10))\n(assert (bvugt x |a b|))\n(assert (= |a b| #x02))\n\
        (assert p)\n(check-sat)\n";

    // rivet: verifies VER-098
    #[test]
    fn an_echo_that_misreads_an_operator_is_not_implied() {
        assert_eq!(check(SAT, &echo_of(SAT)), EchoCheck::Implied);
        for (from, to) in [
            ("bvult", "bvugt"),
            ("bvugt", "bvult"),
            ("#b00000010", "#b00000011"),
        ] {
            let echo = echo_of(SAT).replacen(from, to, 1);
            assert_ne!(echo, echo_of(SAT), "the mutation {from} -> {to} applied");
            match check(SAT, &echo) {
                EchoCheck::NotImplied(_) => {}
                other => panic!("{from} -> {to}: expected NotImplied, got {other:?}"),
            }
        }
        // A Bool read with the wrong polarity.
        let echo = echo_of(SAT).replace("(= |p| #b1)", "(= |p| #b0)");
        assert_ne!(echo, echo_of(SAT), "the polarity mutation applied");
        assert!(matches!(check(SAT, &echo), EchoCheck::NotImplied(_)));
    }

    // rivet: verifies VER-098
    #[test]
    fn an_unsat_input_implies_any_echo() {
        // The instrument's blind spot, pinned: `I ⊨ E` holds for every `E`
        // when `I` is unsat, so on an unsat input Z3 may decide `I` itself
        // and a misread echo still passes. The answer is still right about
        // the input (it is unsat); it rests on Z3, not on the certificate.
        let echo = echo_of(UNSAT).replace("bvugt", "bvult");
        assert_eq!(check(UNSAT, &echo), EchoCheck::Implied);
    }

    // rivet: verifies VER-098
    #[test]
    fn a_bool_is_linked_through_bv1() {
        let c = comparison_script(UNSAT, &echo_of(UNSAT)).unwrap();
        assert!(
            c.script.contains("(assert (= |p| (= |e.p| #b1)))"),
            "{}",
            c.script
        );
        assert!(
            c.script.contains("(assert (= |a b| |e.a b|))"),
            "{}",
            c.script
        );
        assert_eq!(c.links, 3);
        // Assertions after the input's check-sat are not part of it.
        assert!(!c.script.contains("get-model"));
    }

    // rivet: verifies VER-098
    #[test]
    fn the_prefix_avoids_the_inputs_names() {
        let input = UNSAT.replace("(assert p)", "(declare-const e.x (_ BitVec 8))\n(assert p)");
        let c = comparison_script(&input, &echo_of(UNSAT)).unwrap();
        assert_eq!(c.prefix, "e1.");
        assert_eq!(run(&c.script, ECHO_CHECK_TIMEOUT_MS), EchoCheck::Implied);
    }

    // rivet: verifies VER-098
    #[test]
    fn scopes_are_refused_not_compared() {
        let input = UNSAT.replace("(assert p)", "(push 1)\n(assert p)\n(pop 1)");
        assert!(matches!(
            comparison_script(&input, &echo_of(UNSAT)),
            Err(ScriptError::Input(_))
        ));
    }

    // rivet: verifies VER-098
    #[test]
    fn the_script_runs_as_text() {
        // The comparison is its script: Z3 reads it back and decides it the
        // same way (no hidden state beside the text).
        let c = comparison_script(UNSAT, &echo_of(UNSAT)).unwrap();
        assert!(c.script.ends_with("(check-sat)\n"));
        assert!(matches!(z3_read(&c.script), Z3Reading::Accepted(_)));
    }
}
