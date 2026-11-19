//! The certified query echo in a certificate (issue #281, phase E2): the
//! SMT-LIB text the trusted printer (`ordeal_lrat::echo_term` /
//! `echo_ext`, proven in `lean/Echo.lean`) makes of a bundle's `term` or
//! `ext` block, carried next to the certificate so a consumer can compare
//! it with its own input (`ordeal-cert/v5`, `crate::cert_bundle`).
//!
//! The echo is a pure function of the block it prints, so it adds no
//! freedom to a bundle: [`EchoCertificate::recheck`] re-runs the full
//! v3 / v4 recheck of the certificate, prints the block again with the
//! trusted printer and compares the bytes. No SMT-LIB parser is involved.
//! A printer refusal ([`ordeal_lrat::EchoError`]) is never a verdict: the
//! producer writes the v3 / v4 bundle without an echo instead.
//!
//! Always compiled, dependency-free beyond `ordeal-lrat`, like
//! [`crate::query`].

use crate::query::{
    QueryTerm, SliverBlock, SliverCertificate, SliverModelRecheckError, SliverRecheckError,
    SliverSatCertificate, TermCertificate, TermModelRecheckError, TermRecheckError,
    TermSatCertificate,
};
use crate::sha256::sha256_hex;
use ordeal_lrat::EchoError;

/// The `echo.encoding` of an `ordeal-cert/v5` bundle: the printer's
/// output format (design note `docs/design/query-echo.md` §3), version 1.
pub const ECHO_ENCODING: &str = "ordeal-echo/v1";

/// The `format` of a bundle carrying the echo.
pub const V5_FORMAT: &str = "ordeal-cert/v5";

/// The `recheck.min_version` of an `ordeal-cert/v5` bundle: readers from
/// this version on decode it. (A query block that itself needs a newer
/// reader would raise it; none does at 0.38.0.)
pub const V5_MIN_VERSION: &str = "0.38.0";

/// The clause a v5 bundle appends to the v3 `recheck.cmd` (core).
pub const V5_ECHO_TERM_CMD: &str = " && ordeal_lrat::echo_term(term.nodes, term.bits, term.roots, \
     term.vars) == Ok(echo.text)";

/// The clause a v5 bundle appends to the v4 `recheck.cmd` (extended).
pub const V5_ECHO_EXT_CMD: &str = " && ordeal_lrat::echo_ext(ext.nodes, ext.bits, ext.side, \
     ext.roots, ext.vars, ext.arrays, ext.funcs) == Ok(echo.text)";

/// Pack names into the printer's name table: the bytes, a start and a
/// length per name.
fn name_table<'a>(names: impl Iterator<Item = &'a str>) -> (Vec<u8>, Vec<usize>, Vec<usize>) {
    let (mut bytes, mut start, mut len) = (Vec::new(), Vec::new(), Vec::new());
    for n in names {
        start.push(bytes.len());
        len.push(n.len());
        bytes.extend_from_slice(n.as_bytes());
    }
    (bytes, start, len)
}

impl QueryTerm {
    /// The certified echo of this term (`ordeal_lrat::echo_term` over the
    /// node list, constants, roots and variable table, verbatim): the
    /// SMT-LIB script `kernel.spec.echo_term_sound` relates to it.
    pub fn echo(&self) -> Result<Vec<u8>, EchoError> {
        let (names, name_start, name_len) = name_table(self.vars.iter().map(|v| v.0.as_str()));
        let var_node: Vec<usize> = self.vars.iter().map(|v| v.2).collect();
        let var_width: Vec<usize> = self.vars.iter().map(|v| v.1 as usize).collect();
        ordeal_lrat::echo_term(
            &self.nodes,
            &self.bits,
            &self.roots,
            &names,
            &name_start,
            &name_len,
            &var_node,
            &var_width,
        )
    }
}

impl SliverBlock {
    /// The certified echo of the extended query as asked
    /// (`ordeal_lrat::echo_ext` over the `ext` block's nodes, constants,
    /// side table, roots and its variable, array and function tables).
    pub fn echo(&self) -> Result<Vec<u8>, EchoError> {
        let e = &self.ext;
        let (names, name_start, name_len) = name_table(e.vars.iter().map(|v| v.0.as_str()));
        let var_node: Vec<usize> = e.vars.iter().map(|v| v.2).collect();
        let var_width: Vec<usize> = e.vars.iter().map(|v| v.1 as usize).collect();
        let (anames, aname_start, aname_len) = name_table(e.arrays.iter().map(String::as_str));
        let (fnames, fname_start, fname_len) = name_table(e.funcs.iter().map(|f| f.0.as_str()));
        let func_width: Vec<usize> = e.funcs.iter().map(|f| f.1 as usize).collect();
        ordeal_lrat::echo_ext(
            &e.nodes,
            &e.bits,
            &e.side,
            &e.roots,
            &names,
            &name_start,
            &name_len,
            &var_node,
            &var_width,
            &anames,
            &aname_start,
            &aname_len,
            &fnames,
            &fname_start,
            &fname_len,
            &func_width,
        )
    }
}

/// The logic a printed echo declares: `X` of its first line
/// `(set-logic X)`, or `None` if the text does not start with one.
pub fn echo_logic(text: &[u8]) -> Option<&str> {
    let rest = text.strip_prefix(b"(set-logic ")?;
    let end = rest.iter().position(|&b| b == b')')?;
    if rest.get(end + 1) != Some(&b'\n') {
        return None;
    }
    std::str::from_utf8(&rest[..end]).ok()
}

/// The `echo` block of an `ordeal-cert/v5` bundle: the printed text and
/// the logic its first line declares.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QueryEcho {
    /// The printed SMT-LIB script, byte for byte.
    pub text: String,
    /// The logic the script declares (`QF_BV`, `QF_ABV` or `QF_AUFBV`).
    pub logic: String,
}

impl QueryEcho {
    /// The echo block of printed bytes; `None` if they are not UTF-8 or do
    /// not open with `(set-logic …)` (the printer always does both).
    pub fn from_printed(bytes: Vec<u8>) -> Option<Self> {
        let logic = echo_logic(&bytes)?.to_string();
        let text = String::from_utf8(bytes).ok()?;
        Some(QueryEcho { text, logic })
    }

    /// `sha256(text)`, the block's `sha256`: integrity and a lookup key,
    /// nothing more (the recheck re-derives the text).
    #[must_use]
    pub fn sha256(&self) -> String {
        sha256_hex(self.text.as_bytes())
    }
}

/// The certificate an `ordeal-cert/v5` bundle carries the echo of: one of
/// the four term-carrying kinds, told apart by verdict and by whether an
/// `ext` block is present.
#[derive(Clone, Debug)]
pub enum EchoSubject {
    /// UNSAT about a core term (the v3 UNSAT blocks); the echo prints `term`.
    Unsat(TermCertificate),
    /// UNSAT about an extended query (the v4 UNSAT blocks); the echo
    /// prints `ext`.
    UnsatExt(SliverCertificate),
    /// SAT about a core term (the v3 SAT blocks); the echo prints `term`.
    Sat(TermSatCertificate),
    /// SAT about an extended query (the v4 SAT blocks); the echo prints
    /// `ext`.
    SatExt(SliverSatCertificate),
}

impl EchoSubject {
    /// The verdict: `"unsat"` or `"sat"`.
    pub fn verdict(&self) -> &'static str {
        match self {
            EchoSubject::Unsat(_) | EchoSubject::UnsatExt(_) => "unsat",
            EchoSubject::Sat(_) | EchoSubject::SatExt(_) => "sat",
        }
    }

    /// The trusted printer's output for this certificate's question: the
    /// `term` block of a core certificate, the `ext` block of an extended
    /// one.
    pub fn printed(&self) -> Result<Vec<u8>, EchoError> {
        match self {
            EchoSubject::Unsat(c) => c.term.echo(),
            EchoSubject::UnsatExt(c) => c.sliver.echo(),
            EchoSubject::Sat(c) => c.term.echo(),
            EchoSubject::SatExt(c) => c.sliver.echo(),
        }
    }
}

/// A term-carrying certificate together with the certified echo of its
/// question (#281 E2, `ordeal-cert/v5`).
#[derive(Clone, Debug)]
pub struct EchoCertificate {
    /// The certificate (v3 / v4 content).
    pub subject: EchoSubject,
    /// The echo of `subject`'s `term` / `ext` block.
    pub echo: QueryEcho,
}

/// Why an [`EchoCertificate::recheck`] did not accept.
#[derive(Debug)]
pub enum EchoRecheckError {
    /// The v3 UNSAT recheck failed.
    Unsat(TermRecheckError),
    /// The v4 UNSAT recheck failed.
    UnsatExt(SliverRecheckError),
    /// The v3 SAT recheck failed.
    Sat(TermModelRecheckError),
    /// The v4 SAT recheck failed.
    SatExt(SliverModelRecheckError),
    /// The trusted printer refused the block, so no echo can be right.
    Printer(EchoError),
    /// The printed block is not the echo the bundle carries.
    TextMismatch,
    /// The echo's `logic` is not the logic the printed text declares.
    LogicMismatch,
}

impl std::fmt::Display for EchoRecheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EchoRecheckError::Unsat(e) => write!(f, "{e}"),
            EchoRecheckError::UnsatExt(e) => write!(f, "{e}"),
            EchoRecheckError::Sat(e) => write!(f, "{e}"),
            EchoRecheckError::SatExt(e) => write!(f, "{e}"),
            EchoRecheckError::Printer(e) => {
                write!(f, "the trusted printer refuses the block: {e:?}")
            }
            EchoRecheckError::TextMismatch => {
                write!(
                    f,
                    "the echo is not the trusted printer's output for the block"
                )
            }
            EchoRecheckError::LogicMismatch => {
                write!(f, "the echo's logic is not the one its text declares")
            }
        }
    }
}

impl std::error::Error for EchoRecheckError {}

impl EchoCertificate {
    /// Attach the echo of `subject` (printed by the trusted printer), or
    /// return the printer's refusal: the caller then writes the v3 / v4
    /// bundle without an echo. A refusal is never a verdict.
    pub fn new(subject: EchoSubject) -> Result<Self, EchoError> {
        let echo = QueryEcho::from_printed(subject.printed()?).ok_or(EchoError::Malformed)?;
        Ok(EchoCertificate { subject, echo })
    }

    /// The full recheck of a v5 bundle: the v3 / v4 recheck of the
    /// certificate, then the echo re-derived byte for byte from the block
    /// it prints (`echo_term(term…)` / `echo_ext(ext…)` `== Ok(echo.text)`),
    /// and its `logic` checked against the text.
    pub fn recheck(&self) -> Result<(), EchoRecheckError> {
        match &self.subject {
            EchoSubject::Unsat(c) => c.recheck().map_err(EchoRecheckError::Unsat)?,
            EchoSubject::UnsatExt(c) => c.recheck().map_err(EchoRecheckError::UnsatExt)?,
            EchoSubject::Sat(c) => c.recheck().map_err(EchoRecheckError::Sat)?,
            EchoSubject::SatExt(c) => c.recheck().map_err(EchoRecheckError::SatExt)?,
        }
        let printed = self.subject.printed().map_err(EchoRecheckError::Printer)?;
        if printed != self.echo.text.as_bytes() {
            return Err(EchoRecheckError::TextMismatch);
        }
        if echo_logic(&printed) != Some(self.echo.logic.as_str()) {
            return Err(EchoRecheckError::LogicMismatch);
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn echo_logic_reads_the_first_line_only() {
        assert_eq!(
            echo_logic(b"(set-logic QF_BV)\n(check-sat)\n"),
            Some("QF_BV")
        );
        assert_eq!(echo_logic(b"(set-logic QF_AUFBV)\n"), Some("QF_AUFBV"));
        assert_eq!(echo_logic(b"(set-logic QF_BV) \n"), None);
        assert_eq!(echo_logic(b"(check-sat)\n"), None);
        assert_eq!(echo_logic(b""), None);
    }
}
