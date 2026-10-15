//! The certificate-carried query (issue #192 phase 4, `ordeal-cert/v2`):
//! the term DAG the solver lowered, kept next to the certificate so that a
//! consumer re-checks the QUERY, not a CNF it has to take on faith.
//!
//! Since phase 3 the solver lowers every query through the proven
//! `blast_kernel::encode` / `compact` / `tseitin` (now in the trusted
//! `ordeal-lrat` crate). A v1 certificate carries the CNF those produced
//! plus the LRAT proof; `recheck()` proves the CNF unsatisfiable, and the
//! step from the query to the CNF is the solver's word. A
//! [`QueryCertificate`] carries, in addition, the lowered query itself —
//! the [`QueryDag`]: the `DagNode` list, its constant table, the asserted
//! roots and the compaction hints — and its `recheck()` calls
//! `ordeal_lrat::check_query`, which re-runs the proven lowering over the
//! DAG inside the trusted crate and checks the LRAT proof against the CNF
//! *it* produced (`kernel.spec.check_query_sound`, `lean/QueryCheck.lean`:
//! accepted ⟹ no assignment to the DAG's variables makes every root
//! true). What stays untrusted is the untrusted `dag.rs` builder's choice of
//! DAG for the assertions, canon, lowering of derived ops, the sliver and
//! the front ends (`docs/formal-verification.md`).
//!
//! Always compiled (no feature gate, no dependencies): like the SAT witness
//! this is plain data plus the trusted recheck; the `ordeal-cert/v2` JSON
//! envelope (serde) is behind the `cert-bundle` feature in
//! [`crate::cert_bundle`], and the CLI emits the same block with
//! `--with-query`. The canonical text and the content hash are computed
//! HERE so the CLI's block and the API's bundle are byte-for-byte the same
//! query.

use crate::blast_kernel as k;
use crate::sha256::sha256_hex;
use crate::solver::Certificate;
use crate::witness::SatCertificate;

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
        s.push_str(&x.to_string());
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
        model: &crate::solver::Model,
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
        model: &crate::solver::Model,
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

/// The result of [`crate::Solver::check_with_query`]: like
/// [`crate::witness::WitnessCheckResult`] but both decided verdicts carry
/// the lowered query — `Unsat` a [`QueryCertificate`], `Sat` (since #192
/// phase 6) a [`QuerySatCertificate`] — whose trusted re-check passed
/// before it was returned.
#[derive(Clone, Debug)]
pub enum QueryCheckResult {
    /// Unsatisfiable, with the certificate and the query it refutes; the
    /// trusted `check_query` accepted it before return.
    Unsat(QueryCertificate),
    /// Satisfiable, with the witness, the query and the input assignment
    /// that satisfies it; the trusted `check_query_model` accepted it
    /// before return (`.witness` is the v1 [`SatCertificate`]).
    Sat(QuerySatCertificate),
    /// No claim (identical semantics to [`crate::CheckResult::Unknown`]).
    Unknown,
}

// ── #192 phase 7: the term as asked, next to the DAG it was lowered to ──

/// The `term.encoding` value: the caller's assertions flattened as they
/// were asked (`dag::flatten` — no canonicalization, no hash-consing;
/// variables shared by name, constants interned), in the
/// [`QUERY_ENCODING_V2`] node spelling, with the variable names and the
/// map to the lowered DAG's nodes.
pub const TERM_ENCODING: &str = "ordeal-term/v1";

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
    /// [`crate::dag::NO_IMAGE`] (`usize::MAX`) for a node that has none
    /// (the inside of a folded constant). Untrusted advice: the trusted
    /// check rejects a wrong entry.
    pub map: Vec<usize>,
}

impl std::fmt::Debug for QueryTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("QueryTerm")
            .field("nodes", &self.nodes.len())
            .field("bits", &self.bits.len())
            .field("roots", &self.roots)
            .field("vars", &self.vars.len())
            .field("sha256", &self.sha256())
            .finish()
    }
}

impl QueryTerm {
    /// Flatten `assertions` and map the result onto the lowered `query`
    /// (`query_vars`: the lowered DAG's `(name, width, Var node)` map).
    /// Fails only on an ill-sorted term.
    pub fn flatten(
        assertions: &[crate::term::BoolTerm],
        query: &QueryDag,
        query_vars: &[(String, u32, usize)],
    ) -> Result<QueryTerm, crate::eval::EvalError> {
        let term = crate::dag::flatten(assertions)?;
        let map = crate::dag::term_map(&term, &query.nodes, &query.bits, &query.roots, query_vars);
        Ok(QueryTerm {
            nodes: term.nodes,
            bits: term.bits,
            roots: term.roots,
            vars: term.vars,
            map,
        })
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
        s.push_str(TERM_ENCODING);
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
            if image == crate::dag::NO_IMAGE {
                return Err(bad());
            }
            let offset = ordeal_lrat::var_offset(&dag.nodes, image).map_err(|_| bad())?;
            if !ordeal_lrat::check_input_value(inputs, offset, w, *value) {
                return Err(bad());
            }
        }
        Ok(())
    }
}

/// The result of [`crate::Solver::check_with_term`]: like
/// [`QueryCheckResult`] but both decided verdicts also carry the term the
/// query was lowered from — `Unsat` a [`TermCertificate`], `Sat` a
/// [`TermSatCertificate`] — whose trusted re-check (term-to-DAG
/// correspondence included) passed before it was returned.
#[derive(Clone, Debug)]
pub enum TermCheckResult {
    /// Unsatisfiable: the certificate, the query it refutes and the term;
    /// `check_term_dag` and `check_query` accepted before return.
    Unsat(TermCertificate),
    /// Satisfiable: the witness, the query, the inputs and the term;
    /// `check_term_dag`, `check_query_model` and the binding checks
    /// accepted before return.
    Sat(TermSatCertificate),
    /// No claim (identical semantics to [`crate::CheckResult::Unknown`]).
    Unknown,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BoolTerm, BvTerm, Solver, Sort};

    fn var(name: &str, w: u32) -> BvTerm {
        BvTerm::Var {
            name: name.into(),
            sort: Sort::new(w),
        }
    }

    fn konst(v: u128, w: u32) -> BvTerm {
        BvTerm::Const {
            value: v,
            sort: Sort::new(w),
        }
    }

    /// `x + 5 == 3` and `x - 7 != 3 - 7 - 5 + ... `: an UNSAT query whose
    /// refutation depends on the constants — `(x + 5 = 3) ∧ (x ≠ 254)` at
    /// width 8 (x = 254 is the only solution of the first conjunct).
    fn unsat_query() -> Solver {
        let mut s = Solver::new();
        s.assert(BoolTerm::Eq(
            Box::new(BvTerm::Add(Box::new(var("x", 8)), Box::new(konst(5, 8)))),
            Box::new(konst(3, 8)),
        ));
        s.assert(BoolTerm::Ne(Box::new(var("x", 8)), Box::new(konst(254, 8))));
        s
    }

    fn unsat_cert() -> QueryCertificate {
        match unsat_query().check_with_query() {
            QueryCheckResult::Unsat(c) => c,
            other => panic!("expected Unsat, got {other:?}"),
        }
    }

    // rivet: verifies VER-062
    #[test]
    fn query_certificate_rechecks_through_the_trusted_crate() {
        let cert = unsat_cert();
        cert.recheck().expect("fresh query certificate re-checks");
        // The v1 pair inside is the usual checker-validated one.
        cert.certificate.recheck().expect("v1 pair re-checks");
        assert!(!cert.query.nodes.is_empty());
        assert_eq!(cert.query.roots.len(), 2);
        // Deterministic: same query, same bytes, same hash.
        assert_eq!(cert.query.sha256(), unsat_cert().query.sha256());
    }

    // rivet: verifies VER-062
    /// The phase-4 acceptance criterion (#192): flipping ONE constant bit
    /// of the query fails the recheck although the CNF and the proof are
    /// untouched — the trusted crate re-encodes the DAG it is given, and
    /// the proof no longer refutes (or the CNF no longer matches) that.
    #[test]
    fn flipping_one_constant_bit_fails_the_recheck_with_cnf_and_proof_untouched() {
        let mut cert = unsat_cert();
        let (cnf, lrat) = (cert.certificate.cnf.clone(), cert.certificate.lrat.clone());
        let mut rejected = 0;
        for i in 0..cert.query.bits.len() {
            cert.query.bits[i] = !cert.query.bits[i];
            let r = cert.recheck();
            assert_eq!(cert.certificate.cnf, cnf, "CNF must be untouched");
            assert_eq!(cert.certificate.lrat, lrat, "proof must be untouched");
            if r.is_err() {
                rejected += 1;
            }
            cert.query.bits[i] = !cert.query.bits[i];
        }
        // Every constant bit of this query influences its refutation.
        assert_eq!(
            rejected,
            cert.query.bits.len(),
            "every single-bit flip must be rejected"
        );
        cert.recheck().expect("restored query re-checks again");
    }

    // rivet: verifies VER-062
    /// Tampering with the DAG structure (not just a constant) is caught the
    /// same way; a malformed DAG is rejected by `dag_wf` before any
    /// encoding.
    #[test]
    fn structural_tampering_and_malformed_dags_are_rejected() {
        let mut cert = unsat_cert();
        // Swap the two roots' meaning: assert the negation of the first.
        let first_root = cert.query.roots[0];
        cert.query.nodes.push(k::DagNode::Not(first_root));
        let not_node = cert.query.nodes.len() - 1;
        cert.query.roots[0] = not_node;
        assert!(cert.recheck().is_err(), "negated root must not re-check");

        // A malformed DAG: an operand that is not an earlier node.
        let mut cert = unsat_cert();
        cert.query.nodes[0] = k::DagNode::Add(usize::MAX, 0);
        match cert.recheck() {
            Err(QueryRecheckError::Rejected(ordeal_lrat::QueryCheckError::Query(
                ordeal_lrat::QueryError::NodeNotWellFormed { node: 0 },
            ))) => {}
            other => panic!("expected NodeNotWellFormed at node 0, got {other:?}"),
        }
        // A root that is not boolean.
        let mut cert = unsat_cert();
        let var_node = cert
            .query
            .nodes
            .iter()
            .position(|n| matches!(n, k::DagNode::Var(_)))
            .expect("the query has a variable");
        cert.query.roots[0] = var_node;
        match cert.recheck() {
            Err(QueryRecheckError::Rejected(ordeal_lrat::QueryCheckError::Query(
                ordeal_lrat::QueryError::BadRoot { root: 0 },
            ))) => {}
            other => panic!("expected BadRoot 0, got {other:?}"),
        }
    }

    // rivet: verifies VER-062
    /// Wrong hints never make a wrong verdict: they change the gate
    /// sharing, so the re-encoded CNF is a different (equisatisfiable) CNF
    /// and the carried pair no longer matches it — `CnfMismatch`, not an
    /// accept of a formula the proof does not refute.
    #[test]
    fn hints_are_advice_not_trust() {
        let mut cert = unsat_cert();
        cert.query.hints = (0..cert.query.hints.len()).collect(); // share nothing
        match cert.recheck() {
            Err(QueryRecheckError::CnfMismatch | QueryRecheckError::Rejected(_)) => {}
            other => panic!("expected a rejection, got {other:?}"),
        }
    }

    // rivet: verifies VER-062
    /// `node_op` / `node_from_op` round-trip every constructor, and the
    /// canonical text pins the spelling.
    #[test]
    fn node_spelling_round_trips() {
        use k::DagNode as N;
        let all = [
            N::Var(8),
            N::Const(3, 8),
            N::Add(0, 1),
            N::Sub(0, 1),
            N::Mul(0, 1),
            N::Udiv(0, 1),
            N::Urem(0, 1),
            N::And(0, 1),
            N::Or(0, 1),
            N::Xor(0, 1),
            N::Shl(0, 1),
            N::Lshr(0, 1),
            N::Ashr(0, 1),
            N::Rotr(0, 1),
            N::Extract(7, 2, 0),
            N::Concat(0, 1),
            N::ZeroExt(0, 4),
            N::SignExt(0, 4),
            N::Ite(2, 0, 1),
            N::Eq(0, 1),
            N::Ne(0, 1),
            N::Ult(0, 1),
            N::Ule(0, 1),
            N::Ugt(0, 1),
            N::Uge(0, 1),
            N::Slt(0, 1),
            N::Sle(0, 1),
            N::Sgt(0, 1),
            N::Sge(0, 1),
            N::Not(2),
            N::BoolAnd(2, 3),
            N::BoolOr(2, 3),
            N::BvNot(0),
            N::Neg(0),
            N::Rotl(0, 1),
            N::Sdiv(0, 1),
            N::Srem(0, 1),
        ];
        for n in all {
            let (op, args) = node_op(&n);
            assert!(node_from_op(op, &args) == Some(n), "{op}");
            assert!(node_from_op(op, &[]).is_none(), "{op}: wrong arity");
        }
        assert!(node_from_op("bvfoo", &[0, 1]).is_none());
        let q = QueryDag {
            nodes: vec![N::Var(2), N::Const(0, 2), N::Eq(0, 1)],
            bits: vec![true, false],
            roots: vec![2],
            hints: vec![0, 1, 2],
        };
        assert_eq!(q.encoding(), QUERY_ENCODING);
        assert!(!q.has_derived());
        assert_eq!(
            q.canonical_text(),
            "ordeal-dag/v1\nnodes 3\nvar 2\nconst 0 2\neq 0 1\nbits 10\nroots 2\nhints 0 1 2\n"
        );
        assert_eq!(bits_from_string("10"), Some(vec![true, false]));
        assert_eq!(bits_from_string("1x"), None);
        // #192 phase 5: a derived-op node lifts the tag to ordeal-dag/v2,
        // and the hash follows the tag it is computed under.
        let q2 = QueryDag {
            nodes: vec![N::Var(2), N::Var(2), N::Sdiv(0, 1), N::Neg(2), N::Eq(2, 3)],
            bits: vec![],
            roots: vec![4],
            hints: vec![],
        };
        assert!(q2.has_derived());
        assert_eq!(q2.encoding(), QUERY_ENCODING_V2);
        assert_eq!(
            q2.canonical_text(),
            "ordeal-dag/v2\nnodes 5\nvar 2\nvar 2\nsdiv 0 1\nneg 2\neq 2 3\nbits \nroots 4\nhints\n"
        );
        assert_eq!(q2.sha256(), q2.sha256_tagged(QUERY_ENCODING_V2));
        assert_ne!(q2.sha256(), q2.sha256_tagged(QUERY_ENCODING));
        assert!(encoding_supported(QUERY_ENCODING) && encoding_supported(QUERY_ENCODING_V2));
        assert!(!encoding_supported("ordeal-dag/v3"));
    }

    /// #192 phase 5: a query whose refutation rests on `bvsdiv`'s semantics,
    /// as `check_with_query` lowers it — the DAG carries an `Sdiv` node
    /// (not its rewrite), the trusted crate re-checks it, and the block is
    /// tagged `ordeal-dag/v2`.
    fn sdiv_query_certificate() -> QueryCertificate {
        // `(a sdiv b) ≠ rewrite(a sdiv b)` at width 8: UNSAT only because
        // the node IS signed division (the rewrite's sign-mask construction
        // over `bvudiv`).
        let a = var("a", 8);
        let b = var("b", 8);
        let sdiv = BvTerm::Sdiv(Box::new(a.clone()), Box::new(b.clone()));
        let twin = crate::lowering::expand_bv(&sdiv).expect("sorted");
        let mut s = Solver::new();
        s.assert(BoolTerm::Ne(Box::new(sdiv), Box::new(twin)));
        match s.check_with_query() {
            QueryCheckResult::Unsat(c) => c,
            other => panic!("expected Unsat, got {other:?}"),
        }
    }

    // rivet: verifies VER-064
    /// The derived op reaches the certificate as ITS OWN node: the query
    /// block of an `(a sdiv b) ≠ rewrite(a sdiv b)` refutation holds an
    /// `Sdiv` node next to the rewrite's `Udiv`, is tagged `ordeal-dag/v2`,
    /// and re-checks through the trusted crate.
    #[test]
    fn derived_op_is_carried_as_its_own_node_and_rechecks() {
        let cert = sdiv_query_certificate();
        cert.recheck()
            .expect("the trusted crate re-encodes the Sdiv node");
        assert!(cert.query.has_derived());
        assert_eq!(cert.query.encoding(), QUERY_ENCODING_V2);
        let kinds: Vec<&str> = cert.query.nodes.iter().map(|n| node_op(n).0).collect();
        assert!(
            kinds.contains(&"sdiv"),
            "the query block carries the operation: {kinds:?}"
        );
        assert!(
            kinds.contains(&"udiv"),
            "the rewritten twin is next to it: {kinds:?}"
        );
        assert!(
            cert.query.canonical_text().starts_with("ordeal-dag/v2\n"),
            "the hash covers the v2 tag"
        );
    }

    // rivet: verifies VER-064
    /// The phase-5 negative control: change the `Sdiv` node of that
    /// certificate to `Udiv` (same operands, hash recomputed so integrity
    /// passes) with the CNF and the proof untouched — the recheck FAILS,
    /// because the trusted crate re-encodes `udiv` and the carried proof
    /// no longer refutes (nor matches) that CNF. The semantics differ (a
    /// negative dividend), so this is not a formatting accident.
    #[test]
    fn sdiv_node_swapped_to_udiv_fails_the_recheck() {
        let mut cert = sdiv_query_certificate();
        let (cnf, lrat) = (cert.certificate.cnf.clone(), cert.certificate.lrat.clone());
        let i = cert
            .query
            .nodes
            .iter()
            .position(|n| matches!(n, k::DagNode::Sdiv(_, _)))
            .expect("an Sdiv node");
        let k::DagNode::Sdiv(a, b) = cert.query.nodes[i] else {
            unreachable!()
        };
        cert.query.nodes[i] = k::DagNode::Udiv(a, b);
        assert!(!cert.query.has_derived(), "no derived node is left");
        assert_eq!(
            cert.query.encoding(),
            QUERY_ENCODING,
            "tag follows the content"
        );
        let r = cert.recheck();
        assert_eq!(cert.certificate.cnf, cnf, "CNF must be untouched");
        assert_eq!(cert.certificate.lrat, lrat, "proof must be untouched");
        assert!(r.is_err(), "Sdiv → Udiv must fail the recheck: {r:?}");
        // …and the CNF-level (v1) recheck of the untouched pair still passes:
        // exactly the gap the query re-check closes.
        cert.certificate.recheck().expect("v1 pair re-checks");
        // The other direction too: a derived node forged INTO the twin's
        // `udiv` (hash recomputed) does not re-check either.
        let mut cert = sdiv_query_certificate();
        let j = cert
            .query
            .nodes
            .iter()
            .position(|n| matches!(n, k::DagNode::Udiv(_, _)))
            .expect("the rewrite's Udiv node");
        let k::DagNode::Udiv(a, b) = cert.query.nodes[j] else {
            unreachable!()
        };
        cert.query.nodes[j] = k::DagNode::Srem(a, b);
        assert!(cert.recheck().is_err(), "Udiv → Srem must fail the recheck");
    }

    // rivet: verifies VER-062
    /// `check_with_query` agrees with `check` / `check_with_witness` on
    /// every verdict direction, and a SAT query comes back with the usual
    /// witness (inside the query-carrying certificate since phase 6).
    #[test]
    fn check_with_query_matches_the_other_entries() {
        let s = unsat_query();
        assert!(matches!(s.check(), crate::CheckResult::Unsat(_)));
        assert!(matches!(s.check_with_query(), QueryCheckResult::Unsat(_)));
        let mut sat = Solver::new();
        sat.assert(BoolTerm::Eq(
            Box::new(BvTerm::Urem(Box::new(var("a", 8)), Box::new(konst(5, 8)))),
            Box::new(konst(3, 8)),
        ));
        match sat.check_with_query() {
            QueryCheckResult::Sat(w) => {
                w.witness.recheck().expect("v1 witness re-checks");
                w.recheck().expect("query-level model re-checks");
            }
            other => panic!("expected Sat, got {other:?}"),
        }
        let empty = Solver::new();
        match empty.check_with_query() {
            QueryCheckResult::Sat(w) => {
                assert!(w.query.nodes.is_empty() && w.inputs.bits.is_empty());
                w.recheck().expect("the empty query re-checks vacuously");
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    // ── #192 phase 6: the SAT direction at the query level ─────────────

    /// `(a + b = 9) ∧ (a < b) ∧ (a * 2 = b)` at width 8 — a two-variable
    /// SAT query with arithmetic, so the input assignment has two `Var`
    /// nodes to map, and a UNIQUE model (`3a = 9` mod 256 ⟹ `a = 3`,
    /// `b = 6`), so every single input-bit flip is a non-model.
    fn sat_query_certificate() -> QuerySatCertificate {
        let mut s = Solver::new();
        s.assert(BoolTerm::Eq(
            Box::new(BvTerm::Add(Box::new(var("a", 8)), Box::new(var("b", 8)))),
            Box::new(konst(9, 8)),
        ));
        s.assert(BoolTerm::Ult(Box::new(var("a", 8)), Box::new(var("b", 8))));
        s.assert(BoolTerm::Eq(
            Box::new(BvTerm::Mul(Box::new(var("a", 8)), Box::new(konst(2, 8)))),
            Box::new(var("b", 8)),
        ));
        match s.check_with_query() {
            QueryCheckResult::Sat(c) => c,
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    // rivet: verifies VER-065
    /// The positive path: a real SAT query comes back with a certificate
    /// the trusted `check_query_model` accepts; the inputs are the model's
    /// bits at each variable's `Var` node (LSB first), the model is the
    /// expected one, and the block is deterministic.
    #[test]
    fn query_sat_certificate_rechecks_through_the_trusted_crate() {
        let cert = sat_query_certificate();
        cert.recheck().expect("fresh SAT certificate re-checks");
        ordeal_lrat::check_query_model(
            &cert.query.nodes,
            &cert.query.bits,
            &cert.query.roots,
            &cert.inputs.bits,
        )
        .expect("the trusted crate alone accepts the inputs");
        assert_eq!(cert.query.roots.len(), 3);
        assert_eq!(cert.inputs.vars.len(), 2);
        assert_eq!(cert.inputs.bits.len(), 16);
        let value = |name: &str| {
            cert.witness
                .model
                .assignments
                .iter()
                .find(|(n, _)| n == name)
                .map(|(_, v)| *v)
                .expect(name)
        };
        assert_eq!((value("a"), value("b")), (3, 6));
        // The inputs ARE the model: for each var, the bits at its node's
        // offset spell its value LSB first.
        let mut nin = 0;
        for (i, n) in cert.query.nodes.iter().enumerate() {
            if let k::DagNode::Var(w) = *n {
                let (name, width, _) = cert
                    .inputs
                    .vars
                    .iter()
                    .find(|(_, _, node)| *node == i)
                    .expect("every Var node is a model variable");
                assert_eq!(*width as usize, w);
                let v: u128 = (0..w)
                    .map(|j| u128::from(cert.inputs.bits[nin + j]) << j)
                    .sum();
                assert_eq!(v, value(name), "{name}");
                nin += w;
            }
        }
        assert_eq!(nin, 16);
        assert_eq!(
            cert.inputs.sha256(),
            sat_query_certificate().inputs.sha256()
        );
        assert!(
            cert.inputs
                .canonical_text()
                .starts_with("ordeal-inputs/v1\nbits ")
        );
    }

    // rivet: verifies VER-065
    /// The phase-6 negative controls: with the v1 witness UNTOUCHED (same
    /// CNF, assignment, bit map — it keeps re-checking), (1) one flipped
    /// input bit fails the trusted check; (2) a negated root fails it with
    /// the inputs untouched too; (3) a constant bit of the query flipped
    /// fails it; (4) a `vars` entry pointing at the wrong node fails the
    /// consistency check. The CNF-level witness cannot see any of these —
    /// exactly the gap the query-level check closes.
    #[test]
    fn tampering_the_inputs_or_the_query_fails_the_model_recheck() {
        let cert = sat_query_certificate();
        let (cnf, assignment) = (cert.witness.cnf.clone(), cert.witness.assignment.clone());
        // (1) Every single input bit matters here: a = 3, b = 6 is the
        // unique model (a + 2a = 9, a < 2a), so each flip is rejected.
        let mut rejected = 0;
        for i in 0..cert.inputs.bits.len() {
            let mut t = cert.clone();
            t.inputs.bits[i] = !t.inputs.bits[i];
            let direct = ordeal_lrat::check_query_model(
                &t.query.nodes,
                &t.query.bits,
                &t.query.roots,
                &t.inputs.bits,
            );
            assert!(
                matches!(direct, Err(ordeal_lrat::ModelError::RootFalse { .. })),
                "bit {i}: {direct:?}"
            );
            assert!(t.witness.recheck().is_ok(), "the v1 witness is untouched");
            assert!(t.recheck().is_err(), "bit {i}");
            rejected += 1;
        }
        assert_eq!(rejected, 16);
        // (2) The negated root.
        let mut t = cert.clone();
        let root = t.query.roots[0];
        t.query.nodes.push(k::DagNode::Not(root));
        t.query.roots[0] = t.query.nodes.len() - 1;
        t.inputs
            .check_consistent(&t.query, &t.witness.model)
            .expect("the model is still the inputs");
        match t.recheck() {
            Err(QueryModelRecheckError::Rejected(ordeal_lrat::ModelError::RootFalse {
                root: 0,
            })) => {}
            other => panic!("expected RootFalse at root 0, got {other:?}"),
        }
        // (3) A flipped constant bit (the `9`, the `2`: every constant bit
        // of this query is load-bearing).
        let mut rejected = 0;
        for i in 0..cert.query.bits.len() {
            let mut t = cert.clone();
            t.query.bits[i] = !t.query.bits[i];
            if t.recheck().is_err() {
                rejected += 1;
            }
            assert_eq!(t.witness.cnf, cnf);
            assert_eq!(t.witness.assignment, assignment);
        }
        assert_eq!(
            rejected,
            cert.query.bits.len(),
            "every constant bit flip is rejected"
        );
        // (4) A model variable mapped to the other variable's node.
        let mut t = cert.clone();
        let (na, nb) = (t.inputs.vars[0].2, t.inputs.vars[1].2);
        t.inputs.vars[0].2 = nb;
        t.inputs.vars[1].2 = na;
        assert!(matches!(
            t.recheck(),
            Err(QueryModelRecheckError::InputMismatch(_))
        ));
        // (5) A malformed query and a short assignment are the trusted
        // crate's own rejections (the malformed node is a non-`Var`, so
        // the untrusted var map stays intact and the trusted `dag_wf` is
        // what rejects).
        let mut t = cert.clone();
        let j = t
            .query
            .nodes
            .iter()
            .position(|n| !matches!(n, k::DagNode::Var(_)))
            .expect("a non-Var node");
        t.query.nodes[j] = k::DagNode::Add(usize::MAX, 0);
        match t.recheck() {
            Err(QueryModelRecheckError::Rejected(ordeal_lrat::ModelError::Query(
                ordeal_lrat::QueryError::NodeNotWellFormed { node },
            ))) if node == j => {}
            other => panic!("expected NodeNotWellFormed at node {j}, got {other:?}"),
        }
        let mut t = cert;
        t.inputs.bits.pop();
        assert!(matches!(
            t.recheck(),
            Err(QueryModelRecheckError::UnmappedVariable(_))
                | Err(QueryModelRecheckError::Rejected(
                    ordeal_lrat::ModelError::ModelTooShort { .. }
                ))
        ));
    }
}
