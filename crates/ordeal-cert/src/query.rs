//! The certificate-carried query, term and extended query
//! (`ordeal-cert/v2`..`v4`, issue #192 phases 4–7, TR-072) — the data
//! types and their trusted re-checks, extracted from `ordeal::query`
//! (TR-075) so a re-checker can be built without the solver.
//!
//! Every `recheck` here calls the trusted `ordeal-lrat` functions exactly
//! as `ordeal` always did (the code moved verbatim); the solver-side
//! constructors (`QueryTerm::flatten`, `QueryTerm::flatten_sliver`) and
//! the `*CheckResult` verdict types stay in `ordeal::query`, which
//! re-exports everything here.
//!
//! Always compiled (no feature gate, no dependencies beyond
//! `ordeal-lrat`); the JSON envelopes are in [`crate::cert_bundle`]
//! behind the `json` feature. The canonical texts and content hashes are
//! computed HERE so the CLI's blocks and the API's bundles are
//! byte-for-byte the same.

use crate::certificate::Certificate;
use crate::sha256::sha256_hex;
use crate::witness::SatCertificate;
use ordeal_lrat::blast_kernel as k;

/// The "no image" entry of a term or extended map: a node that has none
/// (the inside of a folded constant). `ordeal::dag::NO_IMAGE` is this
/// constant.
pub const NO_IMAGE: usize = usize::MAX;

/// The `query.encoding` value of a DAG over the phase-3 node kinds: a
/// `DagNode` list (`[op, args…]` per node, operands as indices of earlier
/// nodes), a `0`/`1` constant table, root indices and compaction hints.
/// Since #192 phase 5 a DAG that uses one of the five derived-op node kinds
/// (`bvnot`, `neg`, `rotl`, `sdiv`, `srem`) is tagged [`QUERY_ENCODING_V2`]
/// instead, so a v0.27.0 reader refuses it rather than misreading it; a DAG
/// without them keeps this tag, and v0.27.0 readers keep reading it.
/// [`QueryDag::encoding`] picks the tag; readers accept both and reject any
/// other.
pub const QUERY_ENCODING: &str = "ordeal-dag/v1";

/// The `query.encoding` value of a DAG that uses a derived-op node kind
/// (`ordeal-dag/v1` plus `bvnot`, `neg`, `rotl`, `sdiv`, `srem`; #192
/// phase 5). Readers from v0.28.0 on.
pub const QUERY_ENCODING_V2: &str = "ordeal-dag/v2";

/// Is `encoding` one this reader decodes?
pub fn encoding_supported(encoding: &str) -> bool {
    encoding == QUERY_ENCODING || encoding == QUERY_ENCODING_V2
}

/// The lowered query: exactly the inputs the proven lowering (and the
/// trusted re-check) consumes.
#[derive(Clone, Default, PartialEq, Eq)]
pub struct QueryDag {
    /// The term DAG, topologically ordered (every operand is an earlier
    /// node) — the closed `term.rs` fragment.
    pub nodes: Vec<k::DagNode>,
    /// The constant table the `Const(s, w)` nodes slice, LSB first.
    pub bits: Vec<bool>,
    /// The asserted boolean nodes (one per assertion).
    pub roots: Vec<usize>,
    /// The structural-hashing hints the solver compacted with (untrusted
    /// advice: `compact` checks each one; a wrong hint costs a duplicate
    /// gate, never a wrong value). Carried so the re-encoded CNF is the
    /// CNF the proof refutes, gate for gate.
    pub hints: Vec<usize>,
}

impl std::fmt::Debug for QueryDag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("QueryDag")
            .field("nodes", &self.nodes.len())
            .field("bits", &self.bits.len())
            .field("roots", &self.roots)
            .field("hints", &self.hints.len())
            .field("sha256", &self.sha256())
            .finish()
    }
}

/// A node as its `[op, args…]` spelling: the operator mnemonic and its
/// integer arguments in the order the constructor takes them
/// (`Var(w)` → `("var", [w])`, `Const(s, w)` → `("const", [s, w])`,
/// `Extract(hi, lo, a)` → `("extract", [hi, lo, a])`, `ZeroExt(a, by)` →
/// `("zero_ext", [a, by])`, `Ite(c, t, e)` → `("ite", [c, t, e])`, binary
/// ops → `(op, [a, b])`, `Not(a)` → `("not", [a])`).
pub fn node_op(node: &k::DagNode) -> (&'static str, Vec<usize>) {
    use k::DagNode as N;
    match *node {
        N::Var(w) => ("var", vec![w]),
        N::Const(s, w) => ("const", vec![s, w]),
        N::Add(a, b) => ("add", vec![a, b]),
        N::Sub(a, b) => ("sub", vec![a, b]),
        N::Mul(a, b) => ("mul", vec![a, b]),
        N::Udiv(a, b) => ("udiv", vec![a, b]),
        N::Urem(a, b) => ("urem", vec![a, b]),
        N::And(a, b) => ("and", vec![a, b]),
        N::Or(a, b) => ("or", vec![a, b]),
        N::Xor(a, b) => ("xor", vec![a, b]),
        N::Shl(a, b) => ("shl", vec![a, b]),
        N::Lshr(a, b) => ("lshr", vec![a, b]),
        N::Ashr(a, b) => ("ashr", vec![a, b]),
        N::Rotr(a, b) => ("rotr", vec![a, b]),
        N::Extract(hi, lo, a) => ("extract", vec![hi, lo, a]),
        N::Concat(a, b) => ("concat", vec![a, b]),
        N::ZeroExt(a, by) => ("zero_ext", vec![a, by]),
        N::SignExt(a, by) => ("sign_ext", vec![a, by]),
        N::Ite(c, t, e) => ("ite", vec![c, t, e]),
        N::Eq(a, b) => ("eq", vec![a, b]),
        N::Ne(a, b) => ("ne", vec![a, b]),
        N::Ult(a, b) => ("ult", vec![a, b]),
        N::Ule(a, b) => ("ule", vec![a, b]),
        N::Ugt(a, b) => ("ugt", vec![a, b]),
        N::Uge(a, b) => ("uge", vec![a, b]),
        N::Slt(a, b) => ("slt", vec![a, b]),
        N::Sle(a, b) => ("sle", vec![a, b]),
        N::Sgt(a, b) => ("sgt", vec![a, b]),
        N::Sge(a, b) => ("sge", vec![a, b]),
        N::Not(a) => ("not", vec![a]),
        N::BoolAnd(a, b) => ("bool_and", vec![a, b]),
        N::BoolOr(a, b) => ("bool_or", vec![a, b]),
        N::BvNot(a) => ("bvnot", vec![a]),
        N::Neg(a) => ("neg", vec![a]),
        N::Rotl(a, b) => ("rotl", vec![a, b]),
        N::Sdiv(a, b) => ("sdiv", vec![a, b]),
        N::Srem(a, b) => ("srem", vec![a, b]),
    }
}

/// Is this one of the five derived-op node kinds of #192 phase 5 (the ones
/// `ordeal-dag/v1` cannot express)?
pub fn node_is_derived(node: &k::DagNode) -> bool {
    use k::DagNode as N;
    matches!(
        node,
        N::BvNot(_) | N::Neg(_) | N::Rotl(_, _) | N::Sdiv(_, _) | N::Srem(_, _)
    )
}

/// The inverse of [`node_op`]: `None` for an unknown mnemonic or a wrong
/// argument count (a reader reports that as malformed; well-formedness of
/// the operands is the trusted `dag_wf`'s job, not the reader's).
pub fn node_from_op(op: &str, args: &[usize]) -> Option<k::DagNode> {
    use k::DagNode as N;
    let one = || if args.len() == 1 { Some(args[0]) } else { None };
    let two = || {
        if args.len() == 2 {
            Some((args[0], args[1]))
        } else {
            None
        }
    };
    let three = || {
        if args.len() == 3 {
            Some((args[0], args[1], args[2]))
        } else {
            None
        }
    };
    Some(match op {
        "var" => N::Var(one()?),
        "const" => {
            let (s, w) = two()?;
            N::Const(s, w)
        }
        "add" => {
            let (a, b) = two()?;
            N::Add(a, b)
        }
        "sub" => {
            let (a, b) = two()?;
            N::Sub(a, b)
        }
        "mul" => {
            let (a, b) = two()?;
            N::Mul(a, b)
        }
        "udiv" => {
            let (a, b) = two()?;
            N::Udiv(a, b)
        }
        "urem" => {
            let (a, b) = two()?;
            N::Urem(a, b)
        }
        "and" => {
            let (a, b) = two()?;
            N::And(a, b)
        }
        "or" => {
            let (a, b) = two()?;
            N::Or(a, b)
        }
        "xor" => {
            let (a, b) = two()?;
            N::Xor(a, b)
        }
        "shl" => {
            let (a, b) = two()?;
            N::Shl(a, b)
        }
        "lshr" => {
            let (a, b) = two()?;
            N::Lshr(a, b)
        }
        "ashr" => {
            let (a, b) = two()?;
            N::Ashr(a, b)
        }
        "rotr" => {
            let (a, b) = two()?;
            N::Rotr(a, b)
        }
        "extract" => {
            let (hi, lo, a) = three()?;
            N::Extract(hi, lo, a)
        }
        "concat" => {
            let (a, b) = two()?;
            N::Concat(a, b)
        }
        "zero_ext" => {
            let (a, by) = two()?;
            N::ZeroExt(a, by)
        }
        "sign_ext" => {
            let (a, by) = two()?;
            N::SignExt(a, by)
        }
        "ite" => {
            let (c, t, e) = three()?;
            N::Ite(c, t, e)
        }
        "eq" => {
            let (a, b) = two()?;
            N::Eq(a, b)
        }
        "ne" => {
            let (a, b) = two()?;
            N::Ne(a, b)
        }
        "ult" => {
            let (a, b) = two()?;
            N::Ult(a, b)
        }
        "ule" => {
            let (a, b) = two()?;
            N::Ule(a, b)
        }
        "ugt" => {
            let (a, b) = two()?;
            N::Ugt(a, b)
        }
        "uge" => {
            let (a, b) = two()?;
            N::Uge(a, b)
        }
        "slt" => {
            let (a, b) = two()?;
            N::Slt(a, b)
        }
        "sle" => {
            let (a, b) = two()?;
            N::Sle(a, b)
        }
        "sgt" => {
            let (a, b) = two()?;
            N::Sgt(a, b)
        }
        "sge" => {
            let (a, b) = two()?;
            N::Sge(a, b)
        }
        "not" => N::Not(one()?),
        "bool_and" => {
            let (a, b) = two()?;
            N::BoolAnd(a, b)
        }
        "bool_or" => {
            let (a, b) = two()?;
            N::BoolOr(a, b)
        }
        "bvnot" => N::BvNot(one()?),
        "neg" => N::Neg(one()?),
        "rotl" => {
            let (a, b) = two()?;
            N::Rotl(a, b)
        }
        "sdiv" => {
            let (a, b) = two()?;
            N::Sdiv(a, b)
        }
        "srem" => {
            let (a, b) = two()?;
            N::Srem(a, b)
        }
        _ => return None,
    })
}

/// The constant table as a `0`/`1` string, `bits[0]` first.
pub fn bits_string(bits: &[bool]) -> String {
    let mut s = String::with_capacity(bits.len());
    for &b in bits {
        s.push(if b { '1' } else { '0' });
    }
    s
}

/// Parse a `0`/`1` string back into a constant table; `None` on any other
/// character.
pub fn bits_from_string(s: &str) -> Option<Vec<bool>> {
    let mut out = Vec::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '0' => out.push(false),
            '1' => out.push(true),
            _ => return None,
        }
    }
    Some(out)
}

fn push_usizes(s: &mut String, xs: &[usize]) {
    for x in xs {
        s.push(' ');
        s.push_str(&wire_usize(*x).to_string());
    }
}

/// The portable spelling of an index in a bundle and in the canonical
/// texts its hashes cover (TR-075): [`NO_IMAGE`] is `u64::MAX` on every
/// target, every other index its value. On a 64-bit host this is the
/// identity (`usize::MAX == u64::MAX`), so bundles and hashes are
/// byte-identical to what 64-bit ordeal always wrote; on a 32-bit target
/// (the wasm32-wasip2 `ordeal-recheck`) the sentinel keeps its spelling
/// instead of becoming `4294967295`.
pub fn wire_usize(x: usize) -> u64 {
    if x == NO_IMAGE { u64::MAX } else { x as u64 }
}

/// The inverse of [`wire_usize`]: `u64::MAX` is [`NO_IMAGE`]; any other
/// value must fit this target's `usize` (`None` otherwise — a reader
/// reports it as malformed).
pub fn unwire_usize(x: u64) -> Option<usize> {
    if x == u64::MAX {
        Some(NO_IMAGE)
    } else {
        usize::try_from(x).ok()
    }
}

impl QueryDag {
    /// Does the DAG use one of the derived-op node kinds of #192 phase 5?
    #[must_use]
    pub fn has_derived(&self) -> bool {
        self.nodes.iter().any(node_is_derived)
    }

    /// The encoding tag this DAG is emitted under: the lowest one that can
    /// express it — [`QUERY_ENCODING`] (`ordeal-dag/v1`, readable by
    /// v0.27.0) unless a derived-op node is present, then
    /// [`QUERY_ENCODING_V2`].
    #[must_use]
    pub fn encoding(&self) -> &'static str {
        if self.has_derived() {
            QUERY_ENCODING_V2
        } else {
            QUERY_ENCODING
        }
    }

    /// The canonical text the content hash covers (stable, diff-friendly):
    /// the encoding tag ([`QueryDag::encoding`]), `nodes <n>`, one `<op>
    /// <args…>` line per node, then `bits <bitstring>`, `roots <r…>` and
    /// `hints <h…>`.
    pub fn canonical_text(&self) -> String {
        self.canonical_text_tagged(self.encoding())
    }

    /// [`QueryDag::canonical_text`] under an explicit encoding tag — what a
    /// reader hashes to verify a block that DECLARES its tag (a v1-tagged
    /// block hashes with the v1 tag even on a reader that would emit v2).
    pub fn canonical_text_tagged(&self, encoding: &str) -> String {
        let mut s = String::new();
        s.push_str(encoding);
        s.push('\n');
        s.push_str("nodes ");
        s.push_str(&self.nodes.len().to_string());
        s.push('\n');
        for n in &self.nodes {
            let (op, args) = node_op(n);
            s.push_str(op);
            push_usizes(&mut s, &args);
            s.push('\n');
        }
        s.push_str("bits ");
        s.push_str(&bits_string(&self.bits));
        s.push('\n');
        s.push_str("roots");
        push_usizes(&mut s, &self.roots);
        s.push('\n');
        s.push_str("hints");
        push_usizes(&mut s, &self.hints);
        s.push('\n');
        s
    }

    /// `sha256(canonical_text)` — the bundle's `query.sha256` (rivet:
    /// `query-sha256`). Integrity only: the verdict rests on the recheck.
    #[must_use]
    pub fn sha256(&self) -> String {
        sha256_hex(self.canonical_text().as_bytes())
    }

    /// [`QueryDag::sha256`] under an explicit encoding tag (see
    /// [`QueryDag::canonical_text_tagged`]).
    #[must_use]
    pub fn sha256_tagged(&self, encoding: &str) -> String {
        sha256_hex(self.canonical_text_tagged(encoding).as_bytes())
    }
}

/// A certificate together with the query it certifies (issue #192 phase
/// 4): the v1 pair (`certificate.cnf`, `certificate.lrat`) plus the lowered
/// [`QueryDag`]. [`QueryCertificate::recheck`] is the stronger re-check:
/// the trusted crate re-encodes the DAG itself and checks the proof
/// against the CNF *it* produced, so an accepted re-check proves the DAG
/// unsatisfiable — `kernel.spec.check_query_sound`.
#[derive(Clone, Debug)]
pub struct QueryCertificate {
    /// The v1 pair: the CNF the solver produced from the DAG, and the LRAT
    /// proof the checker validated against it. `certificate.recheck()` is
    /// the v1 (CNF-level) re-check, still available.
    pub certificate: Certificate,
    /// The lowered query the CNF was encoded from.
    pub query: QueryDag,
}

/// Why a [`QueryCertificate::recheck`] could not confirm the proof.
#[derive(Debug)]
pub enum QueryRecheckError {
    /// The LRAT bytes were not valid UTF-8 (only possible for a hand-built
    /// certificate).
    NotText,
    /// The trusted crate rejected: the DAG is malformed or too large, or
    /// the proof does not refute the CNF re-encoded from it.
    Rejected(ordeal_lrat::QueryCheckError),
    /// The trusted re-encoding of the DAG is not the CNF the certificate
    /// carries — the bundle is internally inconsistent (a v1 reader would
    /// be checking a different formula than the query's).
    CnfMismatch,
}

impl std::fmt::Display for QueryRecheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QueryRecheckError::NotText => write!(f, "LRAT certificate is not valid UTF-8"),
            QueryRecheckError::Rejected(e) => write!(f, "trusted query re-check rejected: {e}"),
            QueryRecheckError::CnfMismatch => write!(
                f,
                "the CNF re-encoded from the query differs from the carried CNF"
            ),
        }
    }
}

impl std::error::Error for QueryRecheckError {}

impl QueryCertificate {
    /// Re-establish the verdict at the QUERY level, with zero trust in the
    /// solver: `ordeal_lrat::check_query` checks the DAG well-formed
    /// (`dag_wf`), re-runs the proven lowering over it, and checks the LRAT
    /// proof against the CNF it produced. `Ok(())` ⟹ no assignment to the
    /// DAG's variables makes every root true (`check_query_sound`). The
    /// re-encoded CNF must also equal `certificate.cnf`, so the v1 pair a
    /// bundle carries for older readers is the query's CNF and not another.
    pub fn recheck(&self) -> Result<(), QueryRecheckError> {
        let text = self
            .certificate
            .lrat_text()
            .ok_or(QueryRecheckError::NotText)?;
        let q = &self.query;
        let cnf = ordeal_lrat::check_query(&q.nodes, &q.bits, &q.roots, &q.hints, text)
            .map_err(QueryRecheckError::Rejected)?;
        if cnf != self.certificate.cnf {
            return Err(QueryRecheckError::CnfMismatch);
        }
        Ok(())
    }
}

// ── #192 phase 6: the SAT direction at the query level ─────────────────

/// The `inputs.encoding` value: `bits` is the DAG's primary-input
/// assignment as a `0`/`1` string, input 0 first — the `Var` nodes' bits
/// in node order, LSB first within each variable (exactly the `inp` list
/// the DAG semantics `dagSim` reads and `check_query_model` evaluates).
pub const INPUTS_ENCODING: &str = "ordeal-inputs/v1";

/// The DAG's primary-input assignment a SAT verdict is re-checked with
/// (issue #192 phase 6, TR-065): what the trusted
/// `ordeal_lrat::check_query_model` consumes, plus the untrusted map from
/// the model's named variables to the `Var` nodes that read those bits.
#[derive(Clone, Default, PartialEq, Eq)]
pub struct QueryInputs {
    /// `bits[k]` is primary input `k` (see [`INPUTS_ENCODING`]).
    pub bits: Vec<bool>,
    /// Per model variable: (name, width, index of its `Var` node in the
    /// DAG). Untrusted glue — the DAG builder's choice of node for a name
    /// — carried so a reader can confirm the advertised model IS the
    /// assignment the trusted check accepted
    /// ([`QueryInputs::check_consistent`]).
    pub vars: Vec<(String, u32, usize)>,
}

impl std::fmt::Debug for QueryInputs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("QueryInputs")
            .field("bits", &self.bits.len())
            .field("vars", &self.vars.len())
            .field("sha256", &self.sha256())
            .finish()
    }
}

/// The input offset of every `Var` node: `(node, offset, width)` in node
/// order — the encoder numbers the inputs this way (`dagNin`).
fn var_offsets(nodes: &[k::DagNode]) -> Vec<(usize, usize, usize)> {
    let mut out = Vec::new();
    let mut nin = 0usize;
    for (i, n) in nodes.iter().enumerate() {
        if let k::DagNode::Var(w) = *n {
            out.push((i, nin, w));
            nin = nin.saturating_add(w);
        }
    }
    out
}

impl QueryInputs {
    /// Build the assignment from a model: for every `Var` node of the
    /// DAG, the bits (LSB first) of the model value of the variable the
    /// builder mapped to it (`vars`, from `dag::Dag::vars`); a variable
    /// without a binding reads as zero (and fails
    /// [`QueryInputs::check_consistent`]).
    #[must_use]
    pub fn from_model(
        query: &QueryDag,
        vars: &[(String, u32, usize)],
        model: &crate::certificate::Model,
    ) -> QueryInputs {
        let mut bits = Vec::new();
        for (node, _offset, width) in var_offsets(&query.nodes) {
            let value = vars
                .iter()
                .find(|(_, _, n)| *n == node)
                .and_then(|(name, _, _)| model.assignments.iter().find(|(k, _)| k == name))
                .map_or(0u128, |(_, v)| *v);
            for j in 0..width {
                // A `Var` wider than 128 never reaches here (`Sort` caps the
                // width); the guard keeps the shift in range regardless.
                bits.push(j < 128 && (value >> j) & 1 == 1);
            }
        }
        QueryInputs {
            bits,
            vars: vars.to_vec(),
        }
    }

    /// The canonical text the content hash covers: the encoding tag,
    /// `bits <bitstring>`, then one `var <name> <width> <node>` line per
    /// variable.
    pub fn canonical_text(&self) -> String {
        let mut s = String::new();
        s.push_str(INPUTS_ENCODING);
        s.push('\n');
        s.push_str("bits ");
        s.push_str(&bits_string(&self.bits));
        s.push('\n');
        for (name, width, node) in &self.vars {
            s.push_str("var ");
            s.push_str(name);
            s.push(' ');
            s.push_str(&width.to_string());
            s.push(' ');
            s.push_str(&node.to_string());
            s.push('\n');
        }
        s
    }

    /// `sha256(canonical_text)` — the bundle's `inputs.sha256`. Integrity
    /// only: the verdict rests on the recheck.
    #[must_use]
    pub fn sha256(&self) -> String {
        sha256_hex(self.canonical_text().as_bytes())
    }

    /// The UNTRUSTED half of a SAT recheck: the advertised model is the
    /// assignment. Every model binding names a `vars` entry whose node is
    /// a `Var` node of that width, and the model value's bits equal the
    /// input bits at that node's offset. (What this does NOT establish —
    /// that the DAG asks the caller's question — is the DAG builder's
    /// trust, as for the UNSAT direction.)
    pub fn check_consistent(
        &self,
        query: &QueryDag,
        model: &crate::certificate::Model,
    ) -> Result<(), QueryModelRecheckError> {
        for (name, value) in &model.assignments {
            let Some((_, width, node)) = self.vars.iter().find(|(n, _, _)| n == name) else {
                return Err(QueryModelRecheckError::UnmappedVariable(name.clone()));
            };
            let w = *width as usize;
            if !matches!(query.nodes.get(*node), Some(k::DagNode::Var(vw)) if *vw == w) {
                return Err(QueryModelRecheckError::UnmappedVariable(name.clone()));
            }
            // The bit comparison is the trusted crate's since #192 phase
            // 7d: `var_offset` is proven to compute the node's input offset
            // (`dagNin` of the prefix) and `check_input_value` to accept
            // iff the value's bits ARE the inputs there, LSB first
            // (`kernel.spec.check_input_value_sound`).
            let Ok(offset) = ordeal_lrat::var_offset(&query.nodes, *node) else {
                return Err(QueryModelRecheckError::UnmappedVariable(name.clone()));
            };
            if offset.saturating_add(w) > self.bits.len() {
                return Err(QueryModelRecheckError::UnmappedVariable(name.clone()));
            }
            if !ordeal_lrat::check_input_value(&self.bits, offset, w, *value) {
                return Err(QueryModelRecheckError::InputMismatch(name.clone()));
            }
        }
        Ok(())
    }
}

/// A SAT witness together with the query it satisfies (issue #192 phase
/// 6): the v1 [`SatCertificate`] (model, CNF, assignment, bit map) plus
/// the lowered [`QueryDag`] and the DAG's input assignment
/// ([`QueryInputs`]). [`QuerySatCertificate::recheck`] is the stronger
/// re-check: the trusted crate evaluates the DAG itself under the inputs
/// (`ordeal_lrat::check_query_model`), so an accepted re-check proves the
/// DAG satisfiable — `kernel.spec.check_query_model_sound`, in the same
/// semantics `check_query_sound` negates. The SAT twin of
/// [`QueryCertificate`].
#[derive(Clone, Debug)]
pub struct QuerySatCertificate {
    /// The v1 witness: CNF-level, re-checked by `check_sat` /
    /// `check_binding` (`witness.recheck()`), still available.
    pub witness: SatCertificate,
    /// The lowered query the witness is a model of.
    pub query: QueryDag,
    /// The DAG's input assignment and the model-to-node map.
    pub inputs: QueryInputs,
}

/// Why a [`QuerySatCertificate::recheck`] could not confirm the model.
#[derive(Debug)]
pub enum QueryModelRecheckError {
    /// The v1 (CNF-level) witness failed its own recheck.
    Witness(crate::witness::SatRecheckError),
    /// A model binding has no `vars` entry, its entry does not name a
    /// `Var` node of its width, or that node's bits are not in the
    /// assignment — the advertised model is not covered by the inputs.
    UnmappedVariable(String),
    /// A model binding's value disagrees with the input bits of its node.
    InputMismatch(String),
    /// The trusted crate rejected: the DAG is malformed or too large, the
    /// assignment is too short, or a root evaluates to false under it.
    Rejected(ordeal_lrat::ModelError),
}

impl std::fmt::Display for QueryModelRecheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QueryModelRecheckError::Witness(e) => write!(f, "witness recheck failed: {e}"),
            QueryModelRecheckError::UnmappedVariable(n) => {
                write!(
                    f,
                    "model binding '{n}' is not mapped to a Var node of the query"
                )
            }
            QueryModelRecheckError::InputMismatch(n) => {
                write!(f, "model binding '{n}' disagrees with the query inputs")
            }
            QueryModelRecheckError::Rejected(e) => {
                write!(f, "trusted model re-check rejected: {e:?}")
            }
        }
    }
}

impl std::error::Error for QueryModelRecheckError {}

impl QuerySatCertificate {
    /// Re-establish the verdict at the QUERY level, with zero trust in the
    /// solver: the v1 witness recheck first (defence in depth — the
    /// CNF-level claim), the untrusted consistency check that the
    /// advertised model is the assignment, then the trusted
    /// `ordeal_lrat::check_query_model`: the DAG well-formed (`dag_wf`),
    /// the assignment covering its inputs, and EVERY root true under it
    /// (`check_query_model_sound`). The verdict rests on the last step.
    pub fn recheck(&self) -> Result<(), QueryModelRecheckError> {
        self.witness
            .recheck()
            .map_err(QueryModelRecheckError::Witness)?;
        self.inputs
            .check_consistent(&self.query, &self.witness.model)?;
        let q = &self.query;
        ordeal_lrat::check_query_model(&q.nodes, &q.bits, &q.roots, &self.inputs.bits)
            .map_err(QueryModelRecheckError::Rejected)
    }
}

// ── #192 phase 7: the term as asked, next to the DAG it was lowered to ──

/// The `term.encoding` value: the caller's assertions flattened as they
/// were asked (`dag::flatten` — no canonicalization, no hash-consing;
/// variables shared by name, constants interned), in the
/// [`QUERY_ENCODING_V2`] node spelling, with the variable names and the
/// map to the lowered DAG's nodes.
pub const TERM_ENCODING: &str = "ordeal-term/v1";

/// The `term.encoding` of a sliver bundle (TR-072, `ordeal-cert/v4`): the
/// LOWERED core — `sliver::lower`'s output — flattened with hash-consing
/// (so that a shared lowered subterm is one node, which is what the read
/// and call tables are keyed on) and with the lowered index of every read
/// and the lowered arguments of every call appended as non-root nodes
/// (so the trusted check and the model can always reach them). The
/// question as asked is the `ext` block; this term is the checked
/// intermediate, as the `query` block is.
pub const TERM_ENCODING_V2: &str = "ordeal-term/v2";

/// The `ext.encoding` value (TR-072): the extended query flattened as it
/// was asked — `ordeal::sliver::flatten_ext` — plus the untrusted map
/// and tables the trusted `check_sliver_lowering` verifies.
pub const EXT_ENCODING: &str = "ordeal-ext/v1";

/// The term a `v3` certificate is about (#192 phase 7): what the caller
/// asserted, flattened, plus the untrusted index map from its nodes to the
/// lowered [`QueryDag`]'s. The trusted `ordeal_lrat::check_term_dag`
/// verifies, node by node along the map, that the DAG is a
/// semantics-preserving rewrite of this term — the two rewrites
/// canonicalization makes (a commutative swap, a comparison mirror), a
/// constant fold (evaluated by the proven encoder and simulator) and
/// hash-consing (the map itself) — so a consumer that compares this block
/// with its own query certifies the QUESTION, not the solver's DAG.
#[derive(Clone, Default, PartialEq, Eq)]
pub struct QueryTerm {
    /// The term's nodes, operands before operators, left to right.
    pub nodes: Vec<k::DagNode>,
    /// The term's constant table (LSB first).
    pub bits: Vec<bool>,
    /// The asserted nodes, one per assertion, in assertion order.
    pub roots: Vec<usize>,
    /// Per variable: (name, width, its `Var` node in `nodes`).
    pub vars: Vec<(String, u32, usize)>,
    /// `map[i]`: the lowered DAG's node term node `i` became, or
    /// [`NO_IMAGE`] (`usize::MAX`) for a node that has none
    /// (the inside of a folded constant). Untrusted advice: the trusted
    /// check rejects a wrong entry.
    pub map: Vec<usize>,
    /// Whether this is a sliver bundle's lowered core ([`TERM_ENCODING_V2`]:
    /// hash-consed, with the reads' indices and the calls' arguments
    /// appended) rather than the assertions flattened 1:1
    /// ([`TERM_ENCODING`]). The canonical text carries the tag.
    pub shared: bool,
}

impl std::fmt::Debug for QueryTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("QueryTerm")
            .field("nodes", &self.nodes.len())
            .field("bits", &self.bits.len())
            .field("roots", &self.roots)
            .field("vars", &self.vars.len())
            .field("shared", &self.shared)
            .field("sha256", &self.sha256())
            .finish()
    }
}

impl QueryTerm {
    /// The `term.encoding` this term carries.
    pub fn encoding(&self) -> &'static str {
        if self.shared {
            TERM_ENCODING_V2
        } else {
            TERM_ENCODING
        }
    }

    /// The trusted check: is `query` a semantics-preserving rewrite of
    /// this term along the map (`ordeal_lrat::check_term_dag`,
    /// `kernel.spec.check_term_dag_sound`)?
    pub fn check(&self, query: &QueryDag) -> Result<(), ordeal_lrat::TermError> {
        ordeal_lrat::check_term_dag(
            &self.nodes,
            &self.bits,
            &self.roots,
            &self.map,
            &query.nodes,
            &query.bits,
            &query.roots,
        )
    }

    /// The canonical text the content hash covers: the encoding tag,
    /// `nodes <n>`, one `<op> <args…>` line per node, `bits <bitstring>`,
    /// `roots <r…>`, one `var <name> <width> <node>` line per variable,
    /// then `map <m…>`.
    pub fn canonical_text(&self) -> String {
        let mut s = String::new();
        s.push_str(self.encoding());
        s.push('\n');
        s.push_str("nodes ");
        s.push_str(&self.nodes.len().to_string());
        s.push('\n');
        for n in &self.nodes {
            let (op, args) = node_op(n);
            s.push_str(op);
            push_usizes(&mut s, &args);
            s.push('\n');
        }
        s.push_str("bits ");
        s.push_str(&bits_string(&self.bits));
        s.push('\n');
        s.push_str("roots");
        push_usizes(&mut s, &self.roots);
        s.push('\n');
        for (name, width, node) in &self.vars {
            s.push_str("var ");
            s.push_str(name);
            s.push(' ');
            s.push_str(&width.to_string());
            s.push(' ');
            s.push_str(&node.to_string());
            s.push('\n');
        }
        s.push_str("map");
        push_usizes(&mut s, &self.map);
        s.push('\n');
        s
    }

    /// `sha256(canonical_text)` — the bundle's `term.sha256`. Integrity
    /// only: the verdict rests on the recheck.
    #[must_use]
    pub fn sha256(&self) -> String {
        sha256_hex(self.canonical_text().as_bytes())
    }
}

/// An UNSAT certificate together with the query it refutes AND the term
/// that query was lowered from (#192 phase 7, `ordeal-cert/v3`).
/// [`TermCertificate::recheck`] is the strongest re-check: the trusted
/// crate relates the term to the DAG (`check_term_dag`) and refutes the
/// DAG (`check_query`), so an accepted re-check proves the TERM
/// unsatisfiable — `kernel.spec.check_term_unsat_sound`.
#[derive(Clone, Debug)]
pub struct TermCertificate {
    /// The v2 certificate: the v1 pair plus the lowered query.
    pub query: QueryCertificate,
    /// The term and its map onto `query.query`.
    pub term: QueryTerm,
}

/// Why a [`TermCertificate::recheck`] could not confirm the proof.
#[derive(Debug)]
pub enum TermRecheckError {
    /// The trusted crate rejected the term-to-DAG correspondence: the DAG
    /// is not a rewrite of the term along the map.
    Term(ordeal_lrat::TermError),
    /// The v2 (query-level) re-check failed.
    Query(QueryRecheckError),
}

impl std::fmt::Display for TermRecheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TermRecheckError::Term(e) => write!(f, "trusted term re-check rejected: {e:?}"),
            TermRecheckError::Query(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for TermRecheckError {}

impl TermCertificate {
    /// Re-establish the verdict at the TERM level, with zero trust in the
    /// solver: `ordeal_lrat::check_term_dag` over the term, the map and the
    /// lowered DAG, then the v2 recheck (`ordeal_lrat::check_query`).
    /// `Ok(())` ⟹ no assignment to the term's variables makes every
    /// asserted root true (`check_term_unsat_sound`).
    pub fn recheck(&self) -> Result<(), TermRecheckError> {
        self.term
            .check(&self.query.query)
            .map_err(TermRecheckError::Term)?;
        self.query.recheck().map_err(TermRecheckError::Query)
    }
}

/// A SAT witness together with the query it satisfies AND the term that
/// query was lowered from (#192 phase 7, `ordeal-cert/v3`).
/// [`TermSatCertificate::recheck`] relates the term to the DAG
/// (`check_term_dag`), evaluates the DAG under the inputs
/// (`check_query_model`) and, new, ties every advertised model value to
/// the inputs with the proven `var_offset` / `check_input_value` through
/// the term's own variable map — so an accepted re-check proves the TERM
/// satisfied by the advertised model (`check_term_model_sound`, and the
/// only untrusted step left is the variable's name).
#[derive(Clone, Debug)]
pub struct TermSatCertificate {
    /// The v2 SAT certificate: the v1 witness plus the query and inputs.
    pub query: QuerySatCertificate,
    /// The term and its map onto `query.query`.
    pub term: QueryTerm,
}

/// Why a [`TermSatCertificate::recheck`] could not confirm the model.
#[derive(Debug)]
pub enum TermModelRecheckError {
    /// The trusted crate rejected the term-to-DAG correspondence.
    Term(ordeal_lrat::TermError),
    /// The v2 (query-level) re-check failed.
    Query(QueryModelRecheckError),
    /// A model binding is not a variable of the term, its variable has no
    /// image in the DAG, or the value is not the input bits at that
    /// image's offset (`check_input_value` rejected).
    Binding(String),
}

impl std::fmt::Display for TermModelRecheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TermModelRecheckError::Term(e) => {
                write!(f, "trusted term re-check rejected: {e:?}")
            }
            TermModelRecheckError::Query(e) => write!(f, "{e}"),
            TermModelRecheckError::Binding(n) => {
                write!(
                    f,
                    "model binding '{n}' is not the term variable's input bits"
                )
            }
        }
    }
}

impl std::error::Error for TermModelRecheckError {}

impl TermSatCertificate {
    /// The term-level SAT re-check: `check_term_dag`, the v2 recheck
    /// (witness, consistency, `check_query_model`), then every model
    /// binding through the TERM's variable map: its `Var` node's image
    /// under the map, that image's input offset (`var_offset`, proven),
    /// and the value's bits at that offset (`check_input_value`, proven).
    pub fn recheck(&self) -> Result<(), TermModelRecheckError> {
        self.term
            .check(&self.query.query)
            .map_err(TermModelRecheckError::Term)?;
        self.query.recheck().map_err(TermModelRecheckError::Query)?;
        let dag = &self.query.query;
        let inputs = &self.query.inputs.bits;
        for (name, value) in &self.query.witness.model.assignments {
            let bad = || TermModelRecheckError::Binding(name.clone());
            let Some((_, width, node)) = self.term.vars.iter().find(|(n, _, _)| n == name) else {
                return Err(bad());
            };
            let w = *width as usize;
            if !matches!(self.term.nodes.get(*node), Some(k::DagNode::Var(vw)) if *vw == w) {
                return Err(bad());
            }
            let image = *self.term.map.get(*node).ok_or_else(bad)?;
            if image == NO_IMAGE {
                return Err(bad());
            }
            let offset = ordeal_lrat::var_offset(&dag.nodes, image).map_err(|_| bad())?;
            if !ordeal_lrat::check_input_value(inputs, offset, w, *value) {
                return Err(bad());
            }
        }
        // TR-073: the binding BY NAME through the kernel's variable table
        // (`term.vars` is the table verbatim): every mapped table entry
        // reads the value advertised under its name
        // (`ordeal_lrat::check_tree_model`, `kernel.spec.tree_model_sound`).
        let (var_node, var_width, values) =
            table_values(&self.term.vars, &self.term.map, &self.query.witness.model)
                .map_err(TermModelRecheckError::Binding)?;
        if !ordeal_lrat::check_tree_model(
            &var_node,
            &var_width,
            &self.term.map,
            &dag.nodes,
            inputs,
            &values,
        ) {
            return Err(TermModelRecheckError::Binding("<table>".into()));
        }
        Ok(())
    }
}

/// The kernel's model-binding arguments: `(var_node, var_width, values)`.
type ModelBinding = (Vec<usize>, Vec<usize>, Vec<u128>);

/// The kernel's model-binding arguments from a variable table: the nodes,
/// the widths, and per entry the value the model advertises under its
/// name (`0` for an entry the DAG dropped — `map` says `NO_IMAGE` — which
/// the kernel skips; an entry with an image but no advertised value is an
/// error, named).
fn table_values(
    vars: &[(String, u32, usize)],
    map: &[usize],
    model: &crate::certificate::Model,
) -> Result<ModelBinding, String> {
    let mut var_node = Vec::with_capacity(vars.len());
    let mut var_width = Vec::with_capacity(vars.len());
    let mut values = Vec::with_capacity(vars.len());
    for (name, width, node) in vars {
        var_node.push(*node);
        var_width.push(*width as usize);
        let mapped = map.get(*node).is_some_and(|&m| m != NO_IMAGE);
        match model.assignments.iter().find(|(n, _)| n == name) {
            Some((_, v)) => values.push(*v),
            None if !mapped => values.push(0),
            None => return Err(name.clone()),
        }
    }
    Ok((var_node, var_width, values))
}

// ── TR-072: the extended query, next to the core it was lowered to ──

use crate::sliver::{ExtQuery, SliverModel};
use ordeal_lrat::{ExtNode, SliverCheckError};

/// The `ext` block of an `ordeal-cert/v4` bundle (TR-072): the extended
/// query as asked ([`ExtQuery`]) plus the untrusted map from its nodes to
/// the lowered core's ([`QueryTerm`] with [`TERM_ENCODING_V2`]) and the
/// untrusted read and call tables — everything
/// `ordeal_lrat::check_sliver_lowering` verifies.
#[derive(Clone, Default, PartialEq, Eq)]
pub struct SliverBlock {
    /// The extended query as asked.
    pub ext: ExtQuery,
    /// Extended node → core node, [`NO_IMAGE`] for none.
    pub map: Vec<usize>,
    /// The read table, 3 per entry: `(read var node, array id, index node)`.
    pub reads: Vec<usize>,
    /// The call table, 4 per entry: `(result var node, function id,
    /// first argument in `cargs`, arity)`.
    pub calls: Vec<usize>,
    /// The calls' argument nodes.
    pub cargs: Vec<usize>,
}

impl std::fmt::Debug for SliverBlock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SliverBlock")
            .field("ext", &self.ext)
            .field("reads", &(self.reads.len() / 3))
            .field("calls", &(self.calls.len() / 4))
            .field("sha256", &self.sha256())
            .finish()
    }
}

/// The spelling of an extended node in the `ext` block and its canonical
/// text: a closed node as [`node_op`], `["select", aid, idx, s, n]`,
/// `["call", fid, w, s, n]`.
pub fn ext_node_op(node: &ExtNode) -> (&'static str, Vec<usize>) {
    match node {
        ExtNode::Core(nd) => node_op(nd),
        ExtNode::Select(aid, idx, s, n) => ("select", vec![*aid, *idx, *s, *n]),
        ExtNode::Call(fid, w, s, n) => ("call", vec![*fid, *w, *s, *n]),
    }
}

/// The inverse of [`ext_node_op`]; `None` for an unknown spelling.
pub fn ext_node_from_op(op: &str, args: &[usize]) -> Option<ExtNode> {
    match (op, args) {
        ("select", [aid, idx, s, n]) => Some(ExtNode::Select(*aid, *idx, *s, *n)),
        ("call", [fid, w, s, n]) => Some(ExtNode::Call(*fid, *w, *s, *n)),
        _ => node_from_op(op, args).map(ExtNode::Core),
    }
}

impl SliverBlock {
    /// The trusted check: is `term` (the lowered core) the elimination of
    /// the extended query along the map and tables
    /// (`ordeal_lrat::check_sliver_lowering`,
    /// `kernel.spec.check_sliver_lowering_sound`)?
    pub fn check(&self, term: &QueryTerm) -> Result<(), SliverCheckError> {
        ordeal_lrat::check_sliver_lowering(
            &self.ext.nodes,
            &self.ext.bits,
            &self.ext.side,
            &self.ext.roots,
            &self.map,
            &self.reads,
            &self.calls,
            &self.cargs,
            &term.nodes,
            &term.bits,
            &term.roots,
        )
    }

    /// The canonical text the content hash covers: the encoding tag,
    /// `nodes <n>`, one `<op> <args…>` line per node, `bits <bitstring>`,
    /// `side <s…>`, `roots <r…>`, one `var <name> <width> <node>` line per
    /// variable, one `array <name>` line per array id, one `func <name>
    /// <width>` line per function id, then `map <m…>`, `reads <r…>`,
    /// `calls <c…>`, `cargs <a…>`.
    pub fn canonical_text(&self) -> String {
        let mut s = String::new();
        s.push_str(EXT_ENCODING);
        s.push('\n');
        s.push_str("nodes ");
        s.push_str(&self.ext.nodes.len().to_string());
        s.push('\n');
        for n in &self.ext.nodes {
            let (op, args) = ext_node_op(n);
            s.push_str(op);
            push_usizes(&mut s, &args);
            s.push('\n');
        }
        s.push_str("bits ");
        s.push_str(&bits_string(&self.ext.bits));
        s.push('\n');
        s.push_str("side");
        push_usizes(&mut s, &self.ext.side);
        s.push('\n');
        s.push_str("roots");
        push_usizes(&mut s, &self.ext.roots);
        s.push('\n');
        for (name, width, node) in &self.ext.vars {
            s.push_str("var ");
            s.push_str(name);
            s.push(' ');
            s.push_str(&width.to_string());
            s.push(' ');
            s.push_str(&node.to_string());
            s.push('\n');
        }
        for name in &self.ext.arrays {
            s.push_str("array ");
            s.push_str(name);
            s.push('\n');
        }
        for (name, width) in &self.ext.funcs {
            s.push_str("func ");
            s.push_str(name);
            s.push(' ');
            s.push_str(&width.to_string());
            s.push('\n');
        }
        for (key, xs) in [
            ("map", &self.map),
            ("reads", &self.reads),
            ("calls", &self.calls),
            ("cargs", &self.cargs),
        ] {
            s.push_str(key);
            push_usizes(&mut s, xs);
            s.push('\n');
        }
        s
    }

    /// `sha256(canonical_text)` — the bundle's `ext.sha256`. Integrity
    /// only: the verdict rests on the recheck.
    #[must_use]
    pub fn sha256(&self) -> String {
        sha256_hex(self.canonical_text().as_bytes())
    }

    /// The extended model a core model denotes — the pullback the SAT
    /// capstone is stated with (`kernel.spec.check_sliver_model_sound`):
    /// the lowered core is evaluated under the model with the proven
    /// encoder and simulator, and then every base array holds, at each
    /// read's index value, the read variable's value; every function maps
    /// each call's argument values to the result variable's value; the
    /// query variables keep their bindings. Cells and tuples no read or
    /// call touched are free and read as `0`. `None` if a table entry is
    /// out of range (the trusted check would have rejected it).
    pub fn pullback_model(
        &self,
        term: &QueryTerm,
        model: &crate::certificate::Model,
    ) -> Option<SliverModel> {
        let dag = QueryDag {
            nodes: term.nodes.clone(),
            bits: term.bits.clone(),
            roots: term.roots.clone(),
            hints: Vec::new(),
        };
        let inputs = QueryInputs::from_model(&dag, &term.vars, model);
        let mut raw = k::aig_new();
        let (words, _) = k::encode(&mut raw, &term.nodes, &term.bits, &[]);
        let vals = k::simulate(&raw, &inputs.bits);
        let value = |node: usize| -> Option<u128> {
            let word = words.get(node)?;
            let mut v = 0u128;
            for (j, l) in word.iter().enumerate().take(128) {
                if k::eval_lit(&vals, *l) {
                    v |= 1u128 << j;
                }
            }
            Some(v)
        };
        let mut out = SliverModel::default();
        for (name, _, _) in &self.ext.vars {
            if let Some((_, v)) = model.assignments.iter().find(|(n, _)| n == name) {
                out.env.insert(name.clone(), *v);
            }
        }
        for &[var, aid, idx] in self.reads.as_chunks::<3>().0 {
            let array = self.ext.arrays.get(aid)?;
            let i = value(idx)? as u32;
            let v = value(var)? as u8;
            out.arrays.entry(array.clone()).or_default().insert(i, v);
        }
        for &[var, fid, s, n] in self.calls.as_chunks::<4>().0 {
            let (func, _) = self.ext.funcs.get(fid)?;
            let args = self.cargs.get(s..s.checked_add(n)?)?;
            let argv = args.iter().map(|&a| value(a)).collect::<Option<Vec<_>>>()?;
            out.calls.insert((func.clone(), argv), value(var)?);
        }
        Some(out)
    }
}

/// An UNSAT certificate about an EXTENDED query (TR-072, `ordeal-cert/v4`):
/// the v3 term certificate about the lowered core, plus the `ext` block
/// relating that core to the query as asked.
/// [`SliverCertificate::recheck`] is the strongest re-check: the trusted
/// crate relates the extended query to the core (`check_sliver_lowering`),
/// the core to the DAG (`check_term_dag`) and refutes the DAG
/// (`check_query`), so an accepted re-check proves the EXTENDED query
/// unsatisfiable under every array and UF interpretation —
/// `kernel.spec.check_sliver_unsat_sound`.
#[derive(Clone, Debug)]
pub struct SliverCertificate {
    /// The v3 certificate about the lowered core.
    pub term: TermCertificate,
    /// The extended query, its map and tables onto `term.term`.
    pub sliver: SliverBlock,
}

/// Why a [`SliverCertificate::recheck`] could not confirm the proof.
#[derive(Debug)]
pub enum SliverRecheckError {
    /// The trusted crate rejected the extended-to-core correspondence.
    Sliver(SliverCheckError),
    /// The v3 (term-level) re-check failed.
    Term(TermRecheckError),
}

impl std::fmt::Display for SliverRecheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SliverRecheckError::Sliver(e) => write!(f, "trusted sliver re-check rejected: {e:?}"),
            SliverRecheckError::Term(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for SliverRecheckError {}

impl SliverCertificate {
    /// Re-establish the verdict at the EXTENDED level, with zero trust in
    /// the solver: `check_sliver_lowering`, then the v3 recheck.
    pub fn recheck(&self) -> Result<(), SliverRecheckError> {
        self.sliver
            .check(&self.term.term)
            .map_err(SliverRecheckError::Sliver)?;
        self.term.recheck().map_err(SliverRecheckError::Term)
    }
}

/// A SAT witness about an EXTENDED query (TR-072, `ordeal-cert/v4`): the
/// v3 SAT certificate about the lowered core, the `ext` block, and the
/// extended model the core model pulls back to
/// ([`SliverBlock::pullback_model`]). An accepted
/// [`SliverSatCertificate::recheck`] proves the EXTENDED query satisfied
/// by an interpretation built from the model —
/// `kernel.spec.check_sliver_model_sound`.
#[derive(Clone, Debug)]
pub struct SliverSatCertificate {
    /// The v3 SAT certificate about the lowered core.
    pub term: TermSatCertificate,
    /// The extended query, its map and tables onto `term.term`.
    pub sliver: SliverBlock,
    /// The extended model: the pullback of the core model.
    pub model: SliverModel,
}

/// Why a [`SliverSatCertificate::recheck`] could not confirm the model.
#[derive(Debug)]
pub enum SliverModelRecheckError {
    /// The trusted crate rejected the extended-to-core correspondence.
    Sliver(SliverCheckError),
    /// The v3 (term-level) re-check failed.
    Term(TermModelRecheckError),
    /// The advertised extended model is not the pullback of the core
    /// model through the tables.
    Model,
}

impl std::fmt::Display for SliverModelRecheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SliverModelRecheckError::Sliver(e) => {
                write!(f, "trusted sliver re-check rejected: {e:?}")
            }
            SliverModelRecheckError::Term(e) => write!(f, "{e}"),
            SliverModelRecheckError::Model => {
                write!(
                    f,
                    "the extended model is not the pullback of the core model"
                )
            }
        }
    }
}

impl std::error::Error for SliverModelRecheckError {}

impl SliverSatCertificate {
    /// `check_sliver_lowering`, the v3 SAT recheck, then that the
    /// advertised extended model is the pullback of the core model.
    pub fn recheck(&self) -> Result<(), SliverModelRecheckError> {
        self.sliver
            .check(&self.term.term)
            .map_err(SliverModelRecheckError::Sliver)?;
        self.term.recheck().map_err(SliverModelRecheckError::Term)?;
        let expected = self
            .sliver
            .pullback_model(&self.term.term, &self.term.query.witness.model)
            .ok_or(SliverModelRecheckError::Model)?;
        if expected.env != self.model.env
            || expected.arrays != self.model.arrays
            || expected.calls != self.model.calls
        {
            return Err(SliverModelRecheckError::Model);
        }
        // TR-073: the extended model's variables BY NAME through the
        // kernel's variable table of the extended query, the extended map
        // and the term map (`check_tree_model_ext`,
        // `kernel.spec.ext_tree_model_sound`).
        let ext = &self.sliver.ext;
        let mut var_node = Vec::with_capacity(ext.vars.len());
        let mut var_width = Vec::with_capacity(ext.vars.len());
        let mut values = Vec::with_capacity(ext.vars.len());
        for (name, width, node) in &ext.vars {
            var_node.push(*node);
            var_width.push(*width as usize);
            let mapped = self
                .sliver
                .map
                .get(*node)
                .and_then(|&m| (m != NO_IMAGE).then(|| self.term.term.map.get(m)))
                .flatten()
                .is_some_and(|&m| m != NO_IMAGE);
            match self.model.env.get(name) {
                Some(v) => values.push(*v),
                None if !mapped => values.push(0),
                None => return Err(SliverModelRecheckError::Model),
            }
        }
        if !ordeal_lrat::check_tree_model_ext(
            &var_node,
            &var_width,
            &self.sliver.map,
            &self.term.term.nodes,
            &self.term.term.map,
            &self.term.query.query.nodes,
            &self.term.query.inputs.bits,
            &values,
        ) {
            return Err(SliverModelRecheckError::Model);
        }
        Ok(())
    }
}
