//! The Z3 parser differential, **echo leg** (#281 phase E1, design note §6).
//!
//! The front leg ([`super::front`]) checks ordeal's SMT-LIB *reader*
//! against Z3's parser. This leg checks the *printer*: the certified echo
//! (`ordeal_lrat::echo_term` / `echo_ext`) is proven in Lean against a
//! model of SMT-LIB (`lean/EchoSpec.lean`), and here Z3's own parser reads
//! the printed bytes, so a difference between that model and a real
//! solver's reading of the printer's language shows up as a disagreement.
//!
//! For a script `S`: Z3 parses `S` (assertions `A[k]`); ordeal's reader
//! reads `S`; the reading is flattened by the production flattener
//! (`ordeal_lrat::flatten_tree` over `crate::mirror::of_bools`, then
//! `project_core`: the calls of `QueryTermFlatten::flatten`, and the node
//! list, constant table, roots and name tables are passed to the printer
//! verbatim); `echo_term` prints the echo `E`; Z3 parses `E` (assertions
//! `E[k]`); and for every `k` Z3 decides `A[k] xor E[k]` under the `Bool`
//! links of the front leg (a `Bool` name `b` of `S` is the BV1 constant
//! `b` of `E`, read as `b = #b1`). Unsat for every `k` means the echo and
//! the original script say the same thing, assertion by assertion, which
//! implies that they are equisatisfiable.
//!
//! # Names
//!
//! The reader keeps a quoted symbol that is not a simple symbol with its
//! bars (`|a b|`, `|0v|`, `|v#0|`; `smtlib::canonical_quoted`, #294), and
//! that spelling is the name the flattener and the bundle carry. The
//! printer refuses a name with a `|` in it, so on the production path a
//! script with such a symbol is a printer refusal (`EchoError::Name`),
//! listed here. To still put the printer's quoting in front of Z3, a
//! script refused for that reason is echoed a second time with every name
//! reduced to its content (the front leg's `rename_bool`: `|a b|` is the
//! symbol `a b`), in a tally of its own. That second pass is not the
//! production path: it shows what the printer prints for such names, not
//! what ordeal emits today.
//!
//! For the sliver (`echo_ext`), there is no reader: the original is the
//! [`ExtBoolTerm`] tree through [`super::ext_bool_to_z3`], flattened by
//! `flatten_tree` over `crate::mirror::of_ext_bools` (the call of
//! `QueryTermFlatten::flatten_sliver`).
//!
//! # Outcome classes
//!
//! - **agree** — every xor is unsat;
//! - **disagree** — some xor has a model, the counts differ, or Z3 cannot
//!   decide: a failure, reported with Z3's witness;
//! - **Z3 refuses the echo** — a failure: the printer emitted text a
//!   solver does not read;
//! - **printer refuses** — `EchoError`: counted by reason and listed, not
//!   a failure (no echo is no claim);
//! - **not echoed** — the original was not read by both Z3 and ordeal, or
//!   the flattener refused it: the front leg's subject, counted only.
//!
//! A run that compared nothing does not pass ([`EchoTally::passes`]).
//!
//! Not trusted, not on any verdict path (`oracle.rs` header).

use super::ext_bool_to_z3;
use super::front::{CHECK_TIMEOUT_MS, Z3Reading, bool_links, rename_bool, z3_read};
use crate::sliver::ExtBoolTerm;
use crate::smtlib;
use crate::term::BoolTerm;
use ordeal_lrat::EchoError;
use std::collections::BTreeMap;
use std::fmt::Write as _;
use z3::ast::Bool;
use z3::{Params, SatResult, Solver};

// ─── Printing, through the production flattening ─────────────────────────────

/// What the printer made of a query.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Echoed {
    /// The printed script.
    Text(Vec<u8>),
    /// The printer refused, with its reason.
    Refused(EchoError),
    /// The flattener refused the trees (no node list to print).
    Unflattened(String),
}

/// The echo of a core query: the trees flattened as
/// `QueryTermFlatten::flatten` flattens them, printed by `echo_term`.
pub fn echo_core(assertions: &[BoolTerm]) -> Echoed {
    let flat = match ordeal_lrat::flatten_tree(&crate::mirror::of_bools(assertions)) {
        Ok(f) => f,
        Err(e) => return Echoed::Unflattened(format!("flatten_tree: {e:?}")),
    };
    let nodes = match ordeal_lrat::project_core(&flat.nodes) {
        Ok(n) => n,
        Err(e) => return Echoed::Unflattened(format!("project_core: {e:?}")),
    };
    match ordeal_lrat::echo_term(
        &nodes,
        &flat.bits,
        &flat.roots,
        &flat.names,
        &flat.name_start,
        &flat.name_len,
        &flat.var_node,
        &flat.var_width,
    ) {
        Ok(text) => Echoed::Text(text),
        Err(e) => Echoed::Refused(e),
    }
}

/// The echo of a sliver query: the trees flattened as
/// `QueryTermFlatten::flatten_sliver` flattens them, printed by `echo_ext`.
pub fn echo_sliver(assertions: &[ExtBoolTerm]) -> Echoed {
    let flat = match ordeal_lrat::flatten_tree(&crate::mirror::of_ext_bools(assertions)) {
        Ok(f) => f,
        Err(e) => return Echoed::Unflattened(format!("flatten_tree: {e:?}")),
    };
    match ordeal_lrat::echo_ext(
        &flat.nodes,
        &flat.bits,
        &flat.side,
        &flat.roots,
        &flat.names,
        &flat.name_start,
        &flat.name_len,
        &flat.var_node,
        &flat.var_width,
        &flat.anames,
        &flat.aname_start,
        &flat.aname_len,
        &flat.fnames,
        &flat.fname_start,
        &flat.fname_len,
        &flat.func_width,
    ) {
        Ok(text) => Echoed::Text(text),
        Err(e) => Echoed::Refused(e),
    }
}

// ─── Outcome classes ─────────────────────────────────────────────────────────

/// One query's outcome class.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EchoClass {
    /// Every assertion of the echo agrees with the original.
    Agree,
    /// An assertion differs (with Z3's witness). Fails.
    Disagree,
    /// Z3 refuses the printed text. Fails.
    Z3RefusesEcho,
    /// The printer refused: listed with its reason.
    PrinterRefuses(EchoError),
    /// No original to compare against, or nothing to print.
    NotEchoed,
}

/// One query's echo-leg result.
#[derive(Clone, Debug)]
pub struct EchoResult {
    /// The class.
    pub class: EchoClass,
    /// Assertions compared (each an unsat xor) before the result was known.
    pub compared: usize,
    /// The witness or the refusal, for the report.
    pub detail: String,
    /// `(input bytes, echo bytes)` when a text script was echoed.
    pub sizes: Option<(usize, usize)>,
}

/// A rewrite of the printed text before Z3 reads it: the identity in the
/// leg, a mutation in a negative control.
pub type Post = fn(String) -> String;

fn result(class: EchoClass, compared: usize, detail: String) -> EchoResult {
    EchoResult {
        class,
        compared,
        detail,
        sizes: None,
    }
}

/// Classify one echo against the original's assertions as Z3 holds them.
fn classify(originals: &[Bool], links: &[Bool], echoed: Echoed, post: Option<Post>) -> EchoResult {
    let bytes = match echoed {
        Echoed::Text(b) => b,
        Echoed::Refused(e) => return result(EchoClass::PrinterRefuses(e), 0, format!("{e:?}")),
        Echoed::Unflattened(why) => return result(EchoClass::NotEchoed, 0, why),
    };
    let text = match String::from_utf8(bytes) {
        Ok(t) => t,
        Err(_) => return result(EchoClass::Z3RefusesEcho, 0, "the echo is not UTF-8".into()),
    };
    let text = match post {
        Some(f) => f(text),
        None => text,
    };
    let echo_asserts = match z3_read(&text) {
        Z3Reading::Accepted(a) => a,
        Z3Reading::Refused(z) => {
            return result(EchoClass::Z3RefusesEcho, 0, format!("{z}; echo: {text}"));
        }
    };
    if echo_asserts.len() != originals.len() {
        return result(
            EchoClass::Disagree,
            0,
            format!(
                "assertion count: original {} vs echo {}",
                originals.len(),
                echo_asserts.len()
            ),
        );
    }
    let mut params = Params::new();
    params.set_u32("timeout", CHECK_TIMEOUT_MS);
    for (k, (ao, ae)) in originals.iter().zip(&echo_asserts).enumerate() {
        let solver = Solver::new();
        solver.set_params(&params);
        for l in links {
            solver.assert(l);
        }
        solver.assert(ao.xor(ae));
        match solver.check() {
            SatResult::Unsat => {}
            SatResult::Sat => {
                let model = solver
                    .get_model()
                    .map(|m| m.to_string())
                    .unwrap_or_default();
                return result(
                    EchoClass::Disagree,
                    k,
                    format!(
                        "assertion {k}: the original is {ao}, the echo reads {ae}; witness: {}",
                        model.replace('\n', " ")
                    ),
                );
            }
            SatResult::Unknown => {
                return result(
                    EchoClass::Disagree,
                    k,
                    format!(
                        "assertion {k}: Z3 could not decide the xor ({})",
                        solver.get_reason_unknown().unwrap_or_default()
                    ),
                );
            }
        }
    }
    result(EchoClass::Agree, originals.len(), String::new())
}

/// How the reading's names reach the flattener.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Names {
    /// As the reader spells them: the production path.
    AsRead,
    /// Reduced to the symbol's content (`|a b|` to `a b`): not the
    /// production path, see the module docs.
    Content,
}

fn echo_leg_with(script: &str, names: Names, post: Option<Post>) -> EchoResult {
    let (originals, reading) = match (z3_read(script), smtlib::read_script(script)) {
        (Z3Reading::Accepted(a), Ok(r)) => (a, r),
        (Z3Reading::Refused(z), _) => {
            return result(
                EchoClass::NotEchoed,
                0,
                format!("Z3 refuses the input: {z}"),
            );
        }
        (_, Err(o)) => {
            return result(
                EchoClass::NotEchoed,
                0,
                format!("ordeal refuses the input: {o}"),
            );
        }
    };
    let echoed = match names {
        Names::AsRead => echo_core(&reading.assertions),
        Names::Content => {
            let renamed: Vec<BoolTerm> = reading.assertions.iter().map(rename_bool).collect();
            echo_core(&renamed)
        }
    };
    let sizes = match &echoed {
        Echoed::Text(t) => Some((script.len(), t.len())),
        _ => None,
    };
    let mut r = classify(&originals, &bool_links(&reading), echoed, post);
    r.sizes = sizes;
    r
}

/// Run the echo leg on one SMT-LIB script (`echo_term`), the names as the
/// reader spells them.
pub fn echo_leg(script: &str) -> EchoResult {
    echo_leg_with(script, Names::AsRead, None)
}

/// [`echo_leg`] with every name reduced to its content.
pub fn echo_leg_content_names(script: &str) -> EchoResult {
    echo_leg_with(script, Names::Content, None)
}

fn echo_leg_sliver_with(assertions: &[ExtBoolTerm], post: Option<Post>) -> EchoResult {
    let originals: Vec<Bool> = assertions.iter().map(ext_bool_to_z3).collect();
    classify(&originals, &[], echo_sliver(assertions), post)
}

/// Run the echo leg on one sliver query (`echo_ext`).
pub fn echo_leg_sliver(assertions: &[ExtBoolTerm]) -> EchoResult {
    echo_leg_sliver_with(assertions, None)
}

// ─── The tally ───────────────────────────────────────────────────────────────

/// Listed (non-failing) lines kept per reason; the counts are exact.
const LISTED_PER_REASON: usize = 5;

/// Counts of every class over a run, with the failing and listed queries.
#[derive(Default, Debug)]
pub struct EchoTally {
    /// Queries in each class.
    pub agree: usize,
    pub disagree: usize,
    pub z3_refuses: usize,
    pub not_echoed: usize,
    /// Printer refusals by reason (`EchoError`'s name).
    pub printer_refuses: BTreeMap<String, usize>,
    /// Assertions compared (unsat xors) over the run.
    pub assertions_compared: usize,
    /// `label: detail` of each failing query (disagree, Z3 refuses).
    pub failures: Vec<String>,
    /// `label: detail` of the first few listed queries of each reason.
    pub listed: Vec<String>,
    /// `(input bytes, echo bytes)` of every echoed text script.
    pub sizes: Vec<(usize, usize)>,
}

impl EchoTally {
    /// Record one query's result under `label`.
    pub fn record(&mut self, label: &str, r: &EchoResult) {
        self.assertions_compared += r.compared;
        if let Some(s) = r.sizes {
            self.sizes.push(s);
        }
        let line = format!("{label}: {}", r.detail);
        match r.class {
            EchoClass::Agree => self.agree += 1,
            EchoClass::Disagree => {
                self.disagree += 1;
                self.failures.push(format!("[disagree] {line}"));
            }
            EchoClass::Z3RefusesEcho => {
                self.z3_refuses += 1;
                self.failures.push(format!("[Z3 refuses the echo] {line}"));
            }
            EchoClass::PrinterRefuses(e) => {
                let n = self.printer_refuses.entry(format!("{e:?}")).or_insert(0);
                *n += 1;
                if *n <= LISTED_PER_REASON {
                    self.listed.push(format!("[printer refuses] {line}"));
                }
            }
            EchoClass::NotEchoed => {
                self.not_echoed += 1;
                if self.not_echoed <= LISTED_PER_REASON {
                    self.listed.push(format!("[not echoed] {line}"));
                }
            }
        }
    }

    /// Echoes Z3 read and compared (agree + disagree).
    pub fn compared(&self) -> usize {
        self.agree + self.disagree
    }

    /// Printer refusals over all reasons.
    pub fn refused(&self) -> usize {
        self.printer_refuses.values().sum()
    }

    /// The one-line tally printed on every run.
    pub fn summary(&self) -> String {
        self.summary_as("echo leg")
    }

    /// [`EchoTally::summary`] under another title.
    pub fn summary_as(&self, title: &str) -> String {
        let reasons: Vec<String> = self
            .printer_refuses
            .iter()
            .map(|(k, v)| format!("{k} {v}"))
            .collect();
        format!(
            "{title}: {} echoes compared ({} assertions): agree {}, disagree {}, \
             Z3-refuses-echo {}, printer-refuses {} [{}], not echoed {}",
            self.compared(),
            self.assertions_compared,
            self.agree,
            self.disagree,
            self.z3_refuses,
            self.refused(),
            reasons.join(", "),
            self.not_echoed
        )
    }

    /// `echo bytes / input bytes` over the echoed text scripts: the median
    /// and the maximum of the ratio, and of the echo's size.
    pub fn size_line(&self) -> Option<String> {
        if self.sizes.is_empty() {
            return None;
        }
        let mut ratio: Vec<f64> = self
            .sizes
            .iter()
            .map(|&(i, e)| e as f64 / i.max(1) as f64)
            .collect();
        ratio.sort_by(f64::total_cmp);
        let mut echo: Vec<usize> = self.sizes.iter().map(|&(_, e)| e).collect();
        echo.sort_unstable();
        let mut input: Vec<usize> = self.sizes.iter().map(|&(i, _)| i).collect();
        input.sort_unstable();
        let n = ratio.len();
        Some(format!(
            "echo size: {n} scripts; echo/input bytes median {:.2}, max {:.2}; \
             echo bytes median {}, max {}; input bytes median {}, max {}",
            ratio[n / 2],
            ratio[n - 1],
            echo[n / 2],
            echo[n - 1],
            input[n / 2],
            input[n - 1]
        ))
    }

    /// The full report: the summary, the sizes, every failure, the listed
    /// queries.
    pub fn report(&self) -> String {
        self.report_as("echo leg")
    }

    /// [`EchoTally::report`] under another title.
    pub fn report_as(&self, title: &str) -> String {
        let mut s = self.summary_as(title);
        if let Some(l) = self.size_line() {
            let _ = write!(s, "\n{l}");
        }
        for f in &self.failures {
            let _ = write!(s, "\n  FAIL {f}");
        }
        for l in &self.listed {
            let _ = write!(s, "\n  list {l}");
        }
        s
    }

    /// Whether the run passes: something was compared, nothing failed.
    pub fn passes(&self) -> bool {
        self.compared() > 0 && self.failures.is_empty()
    }
}

/// The two tallies of a run over SMT-LIB scripts.
#[derive(Default, Debug)]
pub struct EchoRun {
    /// Every script, the names as the reader spells them (production).
    pub as_read: EchoTally,
    /// The scripts `as_read` lists as refused for a name, echoed again
    /// with the names reduced to their content.
    pub content: EchoTally,
}

impl EchoRun {
    /// Both tallies, the production one first.
    pub fn report(&self) -> String {
        format!(
            "{}\n{}",
            self.as_read.report(),
            self.content.report_as("echo leg, content names")
        )
    }

    /// Whether the run passes: the production path compared something, and
    /// neither pass failed.
    pub fn passes(&self) -> bool {
        self.as_read.passes() && self.content.failures.is_empty()
    }
}

/// Run the echo leg over labelled scripts.
pub fn run_echo_leg<'a>(scripts: impl IntoIterator<Item = (String, &'a str)>) -> EchoRun {
    let mut run = EchoRun::default();
    for (label, script) in scripts {
        let r = echo_leg(script);
        run.as_read.record(&label, &r);
        if r.class == EchoClass::PrinterRefuses(EchoError::Name) {
            run.content.record(&label, &echo_leg_content_names(script));
        }
    }
    run
}

#[cfg(test)]
mod tests {
    //! The echo leg's gate. Run with the front leg:
    //! `cargo test -p ordeal --features oracle --release --lib -- oracle::front::tests oracle::echo::tests`
    //! (CI job "SMT-LIB parser differential", blocking).

    use super::*;
    use crate::oracle::{gen_sliver_corpus, gen_sliver_lifted_corpus, gen_smtlib_text};
    use crate::term::{BvTerm, Sort};
    use std::time::Instant;

    /// The front leg's corpus: the same seed and count, so the echo leg
    /// prints what the front leg read.
    const GEN_COUNT: usize = 10_000;
    const GEN_SEED: u64 = 0x0281_E0F0;

    /// Negative control (design note §6): the printed `bvslt` and `bvsle`
    /// swapped, as if the `Sle` arm printed `bvslt` (the kernel mutation
    /// `push_sym_ok` kills in Lean; the differential must catch it alone).
    fn swap_slt_sle(text: String) -> String {
        text.replace("bvslt", "\u{1}")
            .replace("bvsle", "bvslt")
            .replace('\u{1}', "bvsle")
    }

    /// Negative control (design note §6): every `#b` literal printed LSB
    /// first.
    fn bits_lsb_first(text: String) -> String {
        let mut out = String::with_capacity(text.len());
        let mut rest = text.as_str();
        while let Some(at) = rest.find("#b") {
            out.push_str(&rest[..at + 2]);
            rest = &rest[at + 2..];
            let n = rest.find(|c| c != '0' && c != '1').unwrap_or(rest.len());
            out.extend(rest[..n].chars().rev());
            rest = &rest[n..];
        }
        out.push_str(rest);
        out
    }

    /// Negative control: the last assertion dropped.
    fn drop_last_assert(text: String) -> String {
        match text.rfind("(assert ") {
            Some(at) => format!("{}(check-sat)\n", &text[..at]),
            None => text,
        }
    }

    #[test]
    fn echo_leg_agrees_on_every_repository_smt2_file() {
        let scripts = crate::oracle::front::repository_scripts();
        let t = Instant::now();
        let run = run_echo_leg(scripts.iter().map(|(l, s)| (l.clone(), s.as_str())));
        eprintln!(
            "{} files (echo), {:.2?}\n{}",
            scripts.len(),
            t.elapsed(),
            run.report()
        );
        assert!(run.passes(), "{}", run.report());
    }

    fn generated_run(seed: u64, n: usize) {
        let t = Instant::now();
        let scripts = gen_smtlib_text(seed, n);
        let run = run_echo_leg(
            scripts
                .iter()
                .enumerate()
                .map(|(i, s)| (format!("gen#{i}"), s.as_str())),
        );
        eprintln!(
            "{n} generated scripts (echo, seed {seed:#x}), {:.2?}\n{}",
            t.elapsed(),
            run.report()
        );
        assert!(run.passes(), "{}", run.report());
        let (prod, content) = (&run.as_read, &run.content);
        // The generator emits only scripts both sides read, so the
        // production path either compares a script or refuses it for a
        // name the reader kept with its bars...
        assert_eq!(prod.not_echoed, 0, "{}", run.report());
        assert_eq!(prod.compared() + prod.refused(), n, "{}", run.report());
        assert_eq!(
            prod.refused(),
            prod.printer_refuses.get("Name").copied().unwrap_or(0),
            "{}",
            run.report()
        );
        // ...and with the names reduced to their content every one of
        // those is printed and compared: no script is left unread.
        assert_eq!(
            content.refused() + content.not_echoed,
            0,
            "{}",
            run.report()
        );
        assert_eq!(prod.compared() + content.compared(), n, "{}", run.report());
    }

    #[test]
    fn echo_leg_agrees_on_generated_scripts() {
        generated_run(GEN_SEED, GEN_COUNT);
    }

    /// The 10^5 run, the front leg's nightly seed.
    #[test]
    #[ignore = "10^5 scripts, minutes: nightly-exhaustive.yml"]
    fn echo_leg_agrees_on_1e5_generated_scripts() {
        generated_run(0x0281_E0F1, 100_000);
    }

    /// `echo_ext` over the two seeded sliver corpora (arrays, uninterpreted
    /// functions, every lifted operator).
    #[test]
    fn echo_ext_leg_agrees_on_the_sliver_corpora() {
        let t = Instant::now();
        let mut corpus = gen_sliver_corpus(0x0281_E1A0, 500);
        corpus.extend(gen_sliver_lifted_corpus(0x0281_E1A1, 500));
        let mut tally = EchoTally::default();
        for (i, q) in corpus.iter().enumerate() {
            tally.record(&format!("sliver#{i}"), &echo_leg_sliver(q));
        }
        eprintln!(
            "{} sliver queries (echo_ext), {:.2?}\n{}",
            corpus.len(),
            t.elapsed(),
            tally.report()
        );
        assert!(tally.passes(), "{}", tally.report());
        assert_eq!(
            tally.compared() + tally.refused() + tally.not_echoed,
            corpus.len()
        );
        assert!(tally.compared() * 2 > corpus.len(), "{}", tally.report());
    }

    /// The leg as the controls run it: the production names, and the
    /// content names where the printer refused the production ones.
    fn echo_leg_either(script: &str, post: Option<Post>) -> EchoResult {
        let r = echo_leg_with(script, Names::AsRead, post);
        if r.class == EchoClass::PrinterRefuses(EchoError::Name) {
            echo_leg_with(script, Names::Content, post)
        } else {
            r
        }
    }

    /// Each echo negative control turns the leg red, and the same queries
    /// agree without it.
    #[test]
    fn every_echo_negative_control_turns_the_leg_red() {
        let scripts = gen_smtlib_text(GEN_SEED, 1_000);
        let controls: [(&str, Post); 3] = [
            ("bvslt<->bvsle", swap_slt_sle),
            ("#b LSB first", bits_lsb_first),
            ("last assert dropped", drop_last_assert),
        ];
        for (name, post) in controls {
            let mut tally = EchoTally::default();
            let mut red = Vec::new();
            for (i, s) in scripts.iter().enumerate() {
                let r = echo_leg_either(s, Some(post));
                tally.record(&format!("gen#{i}"), &r);
                if matches!(r.class, EchoClass::Disagree | EchoClass::Z3RefusesEcho) {
                    red.push(i);
                }
            }
            eprintln!(
                "control echo {name}: {} of {} scripts red; {}\n  first: {}",
                red.len(),
                scripts.len(),
                tally.summary(),
                tally.failures.first().map_or("", String::as_str)
            );
            assert!(!red.is_empty(), "control {name} did not turn the leg red");
            assert!(!tally.passes(), "control {name}: the run still passes");
            for i in red {
                assert_eq!(
                    echo_leg_either(&scripts[i], None).class,
                    EchoClass::Agree,
                    "gen#{i} is red without the control {name}"
                );
            }
        }
        // And on `echo_ext`: the sliver leg under the same swap.
        let corpus = gen_sliver_lifted_corpus(0x0281_E1A1, 300);
        let red = corpus
            .iter()
            .filter(|q| echo_leg_sliver_with(q, Some(swap_slt_sle)).class == EchoClass::Disagree)
            .count();
        eprintln!(
            "control echo_ext bvslt<->bvsle: {red} of {} sliver queries red",
            corpus.len()
        );
        assert!(red > 0, "the swap did not turn the sliver leg red");
    }

    /// One fixture per outcome class, for the harness itself.
    #[test]
    fn echo_harness_classifies_one_fixture_per_outcome_class() {
        let agree = "(declare-const x (_ BitVec 8))(declare-const |p| Bool)\
                     (assert (=> p (bvslt x #x02)))(check-sat)";
        let r = echo_leg(agree);
        assert_eq!((r.class, r.compared), (EchoClass::Agree, 1), "{r:?}");
        assert!(r.sizes.is_some());

        // A quoted symbol that is not simple keeps its bars in the reading:
        // the printer refuses it as read, and prints its content.
        let quoted = "(declare-const |x y| (_ BitVec 8))(declare-const |p q| Bool)\
                      (assert (=> |p q| (bvslt |x y| #x02)))(check-sat)";
        let r = echo_leg(quoted);
        assert_eq!(r.class, EchoClass::PrinterRefuses(EchoError::Name), "{r:?}");
        let r = echo_leg_content_names(quoted);
        assert_eq!((r.class, r.compared), (EchoClass::Agree, 1), "{r:?}");
        let run = run_echo_leg([("quoted".to_string(), quoted)]);
        assert_eq!((run.as_read.refused(), run.content.agree), (1, 1));
        assert!(!run.passes(), "the production path compared nothing");

        // disagree, with Z3's witness.
        let r = echo_leg_with(agree, Names::AsRead, Some(swap_slt_sle));
        assert_eq!(r.class, EchoClass::Disagree, "{r:?}");
        assert!(r.detail.contains("witness"), "{r:?}");
        // disagree: an assertion missing.
        let two = "(declare-const x (_ BitVec 8))(assert (bvult x #x02))\
                   (assert (bvult #x00 x))(check-sat)";
        assert_eq!(echo_leg(two).class, EchoClass::Agree);
        let r = echo_leg_with(two, Names::AsRead, Some(drop_last_assert));
        assert_eq!(r.class, EchoClass::Disagree, "{r:?}");
        assert!(r.detail.contains("assertion count"), "{r:?}");

        // Z3 refuses the echo: fails the run.
        let r = echo_leg_with(agree, Names::AsRead, Some(|_| "(assert (= x".to_string()));
        assert_eq!(r.class, EchoClass::Z3RefusesEcho, "{r:?}");
        let mut t = EchoTally::default();
        t.record("garbled", &r);
        t.record("agree", &echo_leg(agree));
        assert!(!t.passes(), "a refused echo must fail the run");

        // The printer refuses: a variable named like a theory symbol. Listed.
        let reserved = BoolTerm::Eq(
            Box::new(BvTerm::Var {
                name: "bvadd".into(),
                sort: Sort::new(8),
            }),
            Box::new(BvTerm::Const {
                value: 1,
                sort: Sort::new(8),
            }),
        );
        let echoed = echo_core(std::slice::from_ref(&reserved));
        assert_eq!(echoed, Echoed::Refused(EchoError::Name));
        let r = classify(&[], &[], echoed, None);
        assert_eq!(r.class, EchoClass::PrinterRefuses(EchoError::Name));
        let mut t = EchoTally::default();
        t.record("reserved", &r);
        assert_eq!(t.refused(), 1);
        assert!(t.failures.is_empty() && !t.passes(), "{}", t.report());

        // Not echoed: ordeal refuses the input (an uninterpreted function).
        let uf = "(declare-fun f ((_ BitVec 8)) (_ BitVec 8))(declare-const x (_ BitVec 8))\
                  (assert (= (f x) x))(check-sat)";
        assert_eq!(echo_leg(uf).class, EchoClass::NotEchoed);

        // No vacuous pass: a run that compared nothing fails.
        let mut empty = EchoTally::default();
        empty.record("uf", &echo_leg(uf));
        assert!(!empty.passes());
    }
}
