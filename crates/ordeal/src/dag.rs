//! The term DAG the proven encoder consumes (issue #192 phase 3).
//!
//! The solver's assertions are lowered to a `blast_kernel::DagNode` list —
//! topologically ordered, hash-consed, variables shared by name — and the
//! Lean-proven `blast_kernel::encode` turns that DAG into the AIG, calling
//! the proven rule for every node. `blast_kernel::compact` then applies the
//! constant folding and structural hashing the shipped `aig::Aig::and`
//! used to apply gate by gate, driven by the hints [`strash_hints`]
//! computes here. Everything in this module is UNTRUSTED glue: the builder
//! decides which node to create for which term (a wrong decision changes
//! the question asked, which phase 4's certificate-carried DAG and the
//! model self-check guard against, exactly as the old term walk was), and
//! the hints only steer gate sharing — `compact` checks every hint and a
//! wrong one costs a duplicate gate, never a wrong value
//! (`lean/BlasterCompact.lean`, `compact_sound`).
//!
//! # Why the shipped CNF is byte-identical to the term walk's
//!
//! The old walk (`solver.rs` before this phase) blasted each assertion
//! recursively, creating a variable's inputs at its first occurrence and
//! replaying every rule through `Aig::and` (fold + hash) at once. This
//! builder visits the same terms in the same post-order, interns a node at
//! the first occurrence of a subterm and reuses it afterwards; the old walk
//! re-blasted a repeated subterm, but every one of its `Aig::and` calls
//! then hit the strash, so the arena did not change. The raw arena `encode`
//! builds is therefore the concatenation, in the walk's order, of the
//! reference arenas the old bridge replayed one rule at a time, and
//! `compact` over it makes the same fold and hash decisions gate by gate
//! (`compact_and` is `Aig::and` spelled in the Aeneas fragment, the hints
//! standing in for its `HashMap`). `tests::dag_path_matches_replay_*`
//! pins that claim on every bench and oracle corpus; the
//! `cnf_gap_digest` digests and the v0.25.0 CLI byte comparison in
//! `docs/design/query-cnf-gap.md` pin it on the shipped bytes.

use crate::blast_kernel as k;
use crate::eval::{self, EvalError};
use crate::term::{BoolTerm, BvTerm};
use std::collections::HashMap;

/// A lowered query: the DAG, its constant table, the asserted root nodes
/// and the variables in creation order.
#[derive(Clone, Default)]
pub struct Dag {
    /// Topologically ordered nodes (every operand index is smaller).
    pub nodes: Vec<k::DagNode>,
    /// The constant table `Const(s, w)` nodes slice, LSB first.
    pub bits: Vec<bool>,
    /// The asserted boolean nodes, one per assertion.
    pub roots: Vec<usize>,
    /// Variables in creation order: `(name, width, node)`.
    pub vars: Vec<(String, u32, usize)>,
}

/// Operator tags for the hash-consing key.
mod tag {
    pub const ADD: u8 = 1;
    pub const SUB: u8 = 2;
    pub const MUL: u8 = 3;
    pub const UDIV: u8 = 4;
    pub const UREM: u8 = 5;
    pub const AND: u8 = 6;
    pub const OR: u8 = 7;
    pub const XOR: u8 = 8;
    pub const SHL: u8 = 9;
    pub const LSHR: u8 = 10;
    pub const ASHR: u8 = 11;
    pub const ROTR: u8 = 12;
    pub const EXTRACT: u8 = 13;
    pub const CONCAT: u8 = 14;
    pub const ZEXT: u8 = 15;
    pub const SEXT: u8 = 16;
    pub const ITE: u8 = 17;
    pub const EQ: u8 = 18;
    pub const NE: u8 = 19;
    pub const ULT: u8 = 20;
    pub const ULE: u8 = 21;
    pub const UGT: u8 = 22;
    pub const UGE: u8 = 23;
    pub const SLT: u8 = 24;
    pub const SLE: u8 = 25;
    pub const SGT: u8 = 26;
    pub const SGE: u8 = 27;
    pub const NOT: u8 = 28;
    pub const BAND: u8 = 29;
    pub const BOR: u8 = 30;
    // The formerly derived ops (#192 phase 5).
    pub const BVNOT: u8 = 31;
    pub const NEG: u8 = 32;
    pub const ROTL: u8 = 33;
    pub const SDIV: u8 = 34;
    pub const SREM: u8 = 35;
}

/// Builds a [`Dag`] from (canonicalized) assertions.
#[derive(Default)]
pub struct DagBuilder {
    dag: Dag,
    /// Structural hash-consing: `(tag, operand, operand, operand)` → node.
    memo: HashMap<(u8, usize, usize, usize), usize>,
    /// Constants by `(value, width)`.
    consts: HashMap<(u128, u32), usize>,
    /// Variables by name.
    var_index: HashMap<String, usize>,
    /// Whether repeated subterms share a node. Off, every occurrence gets
    /// its own node (the `AigOptions::RAW` / `FOLD_ONLY` measurement
    /// configurations, where the old walk re-blasted repeats too).
    hash_cons: bool,
}

impl DagBuilder {
    /// A builder; `hash_cons` is the production setting (`true`).
    pub fn new(hash_cons: bool) -> Self {
        DagBuilder {
            hash_cons,
            ..Default::default()
        }
    }

    fn push(&mut self, node: k::DagNode) -> usize {
        let i = self.dag.nodes.len();
        self.dag.nodes.push(node);
        i
    }

    fn intern(&mut self, key: (u8, usize, usize, usize), node: k::DagNode) -> usize {
        if self.hash_cons
            && let Some(&i) = self.memo.get(&key)
        {
            return i;
        }
        let i = self.push(node);
        if self.hash_cons {
            self.memo.insert(key, i);
        }
        i
    }

    /// The node of a bitvector term. Visits operands left to right (the
    /// old walk's order), sort-checking each term as it did.
    pub fn bv(&mut self, t: &BvTerm) -> Result<usize, EvalError> {
        let width = eval::bv_sort(t)?.width;
        Ok(match t {
            BvTerm::Const { value, .. } => {
                if let Some(&i) = self.consts.get(&(*value, width)) {
                    return Ok(i);
                }
                let s = self.dag.bits.len();
                for j in 0..width {
                    self.dag.bits.push((*value >> j) & 1 == 1);
                }
                let i = self.push(k::DagNode::Const(s, width as usize));
                self.consts.insert((*value, width), i);
                i
            }
            BvTerm::Var { name, .. } => {
                if let Some(&i) = self.var_index.get(name) {
                    return Ok(i);
                }
                let i = self.push(k::DagNode::Var(width as usize));
                self.var_index.insert(name.clone(), i);
                self.dag.vars.push((name.clone(), width, i));
                i
            }
            BvTerm::Add(a, b) => self.bin(tag::ADD, a, b, k::DagNode::Add)?,
            BvTerm::Sub(a, b) => self.bin(tag::SUB, a, b, k::DagNode::Sub)?,
            BvTerm::Mul(a, b) => self.bin(tag::MUL, a, b, k::DagNode::Mul)?,
            BvTerm::Udiv(a, b) => self.bin(tag::UDIV, a, b, k::DagNode::Udiv)?,
            BvTerm::Urem(a, b) => self.bin(tag::UREM, a, b, k::DagNode::Urem)?,
            BvTerm::And(a, b) => self.bin(tag::AND, a, b, k::DagNode::And)?,
            BvTerm::Or(a, b) => self.bin(tag::OR, a, b, k::DagNode::Or)?,
            BvTerm::Xor(a, b) => self.bin(tag::XOR, a, b, k::DagNode::Xor)?,
            BvTerm::Shl(a, b) => self.bin(tag::SHL, a, b, k::DagNode::Shl)?,
            BvTerm::Lshr(a, b) => self.bin(tag::LSHR, a, b, k::DagNode::Lshr)?,
            BvTerm::Ashr(a, b) => self.bin(tag::ASHR, a, b, k::DagNode::Ashr)?,
            BvTerm::Rotr(a, b) => self.bin(tag::ROTR, a, b, k::DagNode::Rotr)?,
            // The formerly derived ops (#192 phase 5) become nodes of their
            // own; `Solver::check`'s default path never shows them to the
            // builder (it rewrites them first), `check_with_query` does.
            BvTerm::Not(a) => {
                let x = self.bv(a)?;
                self.intern((tag::BVNOT, x, 0, 0), k::DagNode::BvNot(x))
            }
            BvTerm::Neg(a) => {
                let x = self.bv(a)?;
                self.intern((tag::NEG, x, 0, 0), k::DagNode::Neg(x))
            }
            BvTerm::Rotl(a, b) => self.bin(tag::ROTL, a, b, k::DagNode::Rotl)?,
            BvTerm::Sdiv(a, b) => self.bin(tag::SDIV, a, b, k::DagNode::Sdiv)?,
            BvTerm::Srem(a, b) => self.bin(tag::SREM, a, b, k::DagNode::Srem)?,
            BvTerm::Extract { hi, lo, arg } => {
                let x = self.bv(arg)?;
                let (hi, lo) = (*hi as usize, *lo as usize);
                self.intern((tag::EXTRACT, x, hi, lo), k::DagNode::Extract(hi, lo, x))
            }
            BvTerm::Concat(a, b) => self.bin(tag::CONCAT, a, b, k::DagNode::Concat)?,
            BvTerm::ZeroExt { by, arg } => {
                let x = self.bv(arg)?;
                let by = *by as usize;
                self.intern((tag::ZEXT, x, by, 0), k::DagNode::ZeroExt(x, by))
            }
            BvTerm::SignExt { by, arg } => {
                let x = self.bv(arg)?;
                let by = *by as usize;
                self.intern((tag::SEXT, x, by, 0), k::DagNode::SignExt(x, by))
            }
            BvTerm::Ite { cond, then_, else_ } => {
                let c = self.boolean(cond)?;
                let (x, y) = (self.bv(then_)?, self.bv(else_)?);
                self.intern((tag::ITE, c, x, y), k::DagNode::Ite(c, x, y))
            }
        })
    }

    fn bin(
        &mut self,
        tag: u8,
        a: &BvTerm,
        b: &BvTerm,
        mk: fn(usize, usize) -> k::DagNode,
    ) -> Result<usize, EvalError> {
        let (x, y) = (self.bv(a)?, self.bv(b)?);
        Ok(self.intern((tag, x, y, 0), mk(x, y)))
    }

    fn cmp(
        &mut self,
        tag: u8,
        a: &BvTerm,
        b: &BvTerm,
        mk: fn(usize, usize) -> k::DagNode,
    ) -> Result<usize, EvalError> {
        let (x, y) = (self.bv(a)?, self.bv(b)?);
        Ok(self.intern((tag, x, y, 0), mk(x, y)))
    }

    /// The node of a boolean term.
    pub fn boolean(&mut self, t: &BoolTerm) -> Result<usize, EvalError> {
        Ok(match t {
            BoolTerm::Eq(a, b) => self.cmp(tag::EQ, a, b, k::DagNode::Eq)?,
            BoolTerm::Ne(a, b) => self.cmp(tag::NE, a, b, k::DagNode::Ne)?,
            BoolTerm::Ult(a, b) => self.cmp(tag::ULT, a, b, k::DagNode::Ult)?,
            BoolTerm::Ule(a, b) => self.cmp(tag::ULE, a, b, k::DagNode::Ule)?,
            BoolTerm::Ugt(a, b) => self.cmp(tag::UGT, a, b, k::DagNode::Ugt)?,
            BoolTerm::Uge(a, b) => self.cmp(tag::UGE, a, b, k::DagNode::Uge)?,
            BoolTerm::Slt(a, b) => self.cmp(tag::SLT, a, b, k::DagNode::Slt)?,
            BoolTerm::Sle(a, b) => self.cmp(tag::SLE, a, b, k::DagNode::Sle)?,
            BoolTerm::Sgt(a, b) => self.cmp(tag::SGT, a, b, k::DagNode::Sgt)?,
            BoolTerm::Sge(a, b) => self.cmp(tag::SGE, a, b, k::DagNode::Sge)?,
            BoolTerm::Not(x) => {
                let x = self.boolean(x)?;
                self.intern((tag::NOT, x, 0, 0), k::DagNode::Not(x))
            }
            BoolTerm::And(a, b) => {
                let (x, y) = (self.boolean(a)?, self.boolean(b)?);
                self.intern((tag::BAND, x, y, 0), k::DagNode::BoolAnd(x, y))
            }
            BoolTerm::Or(a, b) => {
                let (x, y) = (self.boolean(a)?, self.boolean(b)?);
                self.intern((tag::BOR, x, y, 0), k::DagNode::BoolOr(x, y))
            }
        })
    }

    /// Assert a (canonicalized) boolean term: its node becomes a root.
    pub fn assert_root(&mut self, t: &BoolTerm) -> Result<(), EvalError> {
        let r = self.boolean(t)?;
        self.dag.roots.push(r);
        Ok(())
    }

    /// The finished DAG.
    pub fn finish(self) -> Dag {
        self.dag
    }
}

/// Structural-hashing hints for `blast_kernel::compact` (untrusted): for
/// every node of the raw arena, the earlier node whose compacted gate it
/// may share — itself when there is none. Computed by running the
/// compaction's own fold and normalisation with a `HashMap` keyed on the
/// normalised operand pair, exactly the shipped `Aig::and`'s strash, so
/// `compact` reproduces the gate sharing of the old `Aig::and` replay gate
/// for gate. A hint is advice: `compact` checks each one against the gate
/// it names and ignores a wrong one.
pub fn strash_hints(raw: &k::Aig) -> Vec<usize> {
    let n = raw.nodes.len();
    let mut hints: Vec<usize> = Vec::with_capacity(n);
    let mut map: Vec<k::Lit> = Vec::with_capacity(n);
    let mut out_len = 1usize;
    let mut table: HashMap<(usize, bool, usize, bool), usize> = HashMap::new();
    let f = k::lit_false();
    let t = k::lit_true();
    for (i, nd) in raw.nodes.iter().enumerate() {
        let (lit, hint) = match *nd {
            k::Node::False => (f, i),
            k::Node::Input(_) => {
                let l = k::Lit {
                    node: out_len,
                    neg: false,
                };
                out_len += 1;
                (l, i)
            }
            k::Node::And(x, y) => {
                let (rx, ry) = (k::map_lit(&map, x), k::map_lit(&map, y));
                if k::lit_eq(rx, f) || k::lit_eq(ry, f) || k::lit_eq(rx, k::lit_not(ry)) {
                    (f, i)
                } else if k::lit_eq(rx, t) {
                    (ry, i)
                } else if k::lit_eq(ry, t) || k::lit_eq(rx, ry) {
                    (rx, i)
                } else {
                    let (p, q) = if k::lit_le(rx, ry) {
                        (rx, ry)
                    } else {
                        (ry, rx)
                    };
                    let key = (p.node, p.neg, q.node, q.neg);
                    if let Some(&j) = table.get(&key) {
                        (map[j], j)
                    } else {
                        table.insert(key, i);
                        let l = k::Lit {
                            node: out_len,
                            neg: false,
                        };
                        out_len += 1;
                        (l, i)
                    }
                }
            }
        };
        map.push(lit);
        hints.push(hint);
    }
    hints
}

/// Hints that share nothing (`AigOptions::FOLD_ONLY`: folding, no hashing).
pub fn no_hints(raw: &k::Aig) -> Vec<usize> {
    (0..raw.nodes.len()).collect()
}

// ── #192 phase 7: the term as asked, and its map to the lowered DAG ──────

/// The term as the caller asked it (#192 phase 7, `ordeal-term/v1`): the
/// assertions flattened with NO canonicalization and NO hash-consing —
/// variables shared by name, constants interned, every other subterm its
/// own node, operands before operators, left to right. The same
/// [`DagBuilder`] walk the lowered DAG comes from, minus the two things a
/// consumer cannot audit without re-running them. The trusted
/// `ordeal_lrat::check_term_dag` relates this to the lowered DAG along
/// [`term_map`]'s map.
pub fn flatten(assertions: &[BoolTerm]) -> Result<Dag, EvalError> {
    let mut builder = DagBuilder::new(false);
    for a in assertions {
        builder.assert_root(a)?;
    }
    Ok(builder.finish())
}

/// `usize::MAX`: the map entry of a term node that has no image.
pub const NO_IMAGE: usize = usize::MAX;

/// The operands of a node (the earlier nodes whose values it reads), in
/// constructor order.
fn operands(n: &k::DagNode) -> Vec<usize> {
    use k::DagNode as N;
    match *n {
        N::Var(_) | N::Const(_, _) => vec![],
        N::Extract(_, _, a)
        | N::ZeroExt(a, _)
        | N::SignExt(a, _)
        | N::Not(a)
        | N::BvNot(a)
        | N::Neg(a) => vec![a],
        N::Ite(c, t, e) => vec![c, t, e],
        N::Add(a, b)
        | N::Sub(a, b)
        | N::Mul(a, b)
        | N::Udiv(a, b)
        | N::Urem(a, b)
        | N::And(a, b)
        | N::Or(a, b)
        | N::Xor(a, b)
        | N::Shl(a, b)
        | N::Lshr(a, b)
        | N::Ashr(a, b)
        | N::Rotr(a, b)
        | N::Concat(a, b)
        | N::Eq(a, b)
        | N::Ne(a, b)
        | N::Ult(a, b)
        | N::Ule(a, b)
        | N::Ugt(a, b)
        | N::Uge(a, b)
        | N::Slt(a, b)
        | N::Sle(a, b)
        | N::Sgt(a, b)
        | N::Sge(a, b)
        | N::BoolAnd(a, b)
        | N::BoolOr(a, b)
        | N::Rotl(a, b)
        | N::Sdiv(a, b)
        | N::Srem(a, b) => vec![a, b],
    }
}

/// A node with its operands replaced by `f(operand)`; `None` if `f` has no
/// image for one of them.
fn map_operands(n: &k::DagNode, f: impl Fn(usize) -> Option<usize>) -> Option<k::DagNode> {
    use k::DagNode as N;
    Some(match *n {
        N::Var(w) => N::Var(w),
        N::Const(s, w) => N::Const(s, w),
        N::Extract(hi, lo, a) => N::Extract(hi, lo, f(a)?),
        N::ZeroExt(a, by) => N::ZeroExt(f(a)?, by),
        N::SignExt(a, by) => N::SignExt(f(a)?, by),
        N::Not(a) => N::Not(f(a)?),
        N::BvNot(a) => N::BvNot(f(a)?),
        N::Neg(a) => N::Neg(f(a)?),
        N::Ite(c, t, e) => N::Ite(f(c)?, f(t)?, f(e)?),
        N::Add(a, b) => N::Add(f(a)?, f(b)?),
        N::Sub(a, b) => N::Sub(f(a)?, f(b)?),
        N::Mul(a, b) => N::Mul(f(a)?, f(b)?),
        N::Udiv(a, b) => N::Udiv(f(a)?, f(b)?),
        N::Urem(a, b) => N::Urem(f(a)?, f(b)?),
        N::And(a, b) => N::And(f(a)?, f(b)?),
        N::Or(a, b) => N::Or(f(a)?, f(b)?),
        N::Xor(a, b) => N::Xor(f(a)?, f(b)?),
        N::Shl(a, b) => N::Shl(f(a)?, f(b)?),
        N::Lshr(a, b) => N::Lshr(f(a)?, f(b)?),
        N::Ashr(a, b) => N::Ashr(f(a)?, f(b)?),
        N::Rotr(a, b) => N::Rotr(f(a)?, f(b)?),
        N::Concat(a, b) => N::Concat(f(a)?, f(b)?),
        N::Eq(a, b) => N::Eq(f(a)?, f(b)?),
        N::Ne(a, b) => N::Ne(f(a)?, f(b)?),
        N::Ult(a, b) => N::Ult(f(a)?, f(b)?),
        N::Ule(a, b) => N::Ule(f(a)?, f(b)?),
        N::Ugt(a, b) => N::Ugt(f(a)?, f(b)?),
        N::Uge(a, b) => N::Uge(f(a)?, f(b)?),
        N::Slt(a, b) => N::Slt(f(a)?, f(b)?),
        N::Sle(a, b) => N::Sle(f(a)?, f(b)?),
        N::Sgt(a, b) => N::Sgt(f(a)?, f(b)?),
        N::Sge(a, b) => N::Sge(f(a)?, f(b)?),
        N::BoolAnd(a, b) => N::BoolAnd(f(a)?, f(b)?),
        N::BoolOr(a, b) => N::BoolOr(f(a)?, f(b)?),
        N::Rotl(a, b) => N::Rotl(f(a)?, f(b)?),
        N::Sdiv(a, b) => N::Sdiv(f(a)?, f(b)?),
        N::Srem(a, b) => N::Srem(f(a)?, f(b)?),
    })
}

/// A commutative node with its operands swapped (what `canon.rs` may do).
fn swap_comm(n: &k::DagNode) -> k::DagNode {
    use k::DagNode as N;
    match *n {
        N::Add(a, b) => N::Add(b, a),
        N::Mul(a, b) => N::Mul(b, a),
        N::And(a, b) => N::And(b, a),
        N::Or(a, b) => N::Or(b, a),
        N::Xor(a, b) => N::Xor(b, a),
        N::Eq(a, b) => N::Eq(b, a),
        N::Ne(a, b) => N::Ne(b, a),
        N::BoolAnd(a, b) => N::BoolAnd(b, a),
        N::BoolOr(a, b) => N::BoolOr(b, a),
        other => other,
    }
}

/// A comparison mirrored (`a > b` as `b < a`, …; what `canon.rs` does to
/// the four "greater" forms).
fn mirror(n: &k::DagNode) -> k::DagNode {
    use k::DagNode as N;
    match *n {
        N::Ult(a, b) => N::Ugt(b, a),
        N::Ule(a, b) => N::Uge(b, a),
        N::Ugt(a, b) => N::Ult(b, a),
        N::Uge(a, b) => N::Ule(b, a),
        N::Slt(a, b) => N::Sgt(b, a),
        N::Sle(a, b) => N::Sge(b, a),
        N::Sgt(a, b) => N::Slt(b, a),
        N::Sge(a, b) => N::Sle(b, a),
        other => other,
    }
}

/// The map from the term's nodes to the lowered DAG's (#192 phase 7):
/// `map[i]` is the DAG node term node `i` became under canonicalization
/// and hash-consing, or [`NO_IMAGE`] — the inside of a folded constant
/// subterm, whose children do not exist in the DAG. UNTRUSTED: the
/// trusted `ordeal_lrat::check_term_dag` verifies every entry (a wrong
/// map is rejected and the verdict degrades to `Unknown`, never
/// accepted on a different formula); `denotation_guard` is its positive
/// control.
///
/// Computed after the fact, with no access to the builder's tables: a
/// variable by its name (`vars`, the lowered DAG's `(name, width, node)`
/// map), a constant by its bits, an operator by the structural key of its
/// mapped image — as is, with a commutative swap, or with a comparison
/// mirror (hash-consing made each key unique) — and, when none of those
/// hits, a closed operator by the constant its value interned to: the
/// value comes from the proven encoder and simulator at the all-false
/// assignment, which is exactly how the trusted check will evaluate it.
pub fn term_map(
    term: &Dag,
    nodes: &[k::DagNode],
    bits: &[bool],
    vars: &[(String, u32, usize)],
) -> Vec<usize> {
    use k::DagNode as N;
    // The lowered DAG's lookup tables. A constant may have SEVERAL nodes
    // with the same bits (the builder interns by the `u128` value, and
    // two input constants can agree on their low `w` bits and differ
    // above), so a term constant keeps every candidate until a parent's
    // structural lookup picks the one the DAG actually used.
    let mut by_key: HashMap<(&'static str, Vec<usize>), usize> = HashMap::new();
    let mut by_bits: HashMap<Vec<bool>, Vec<usize>> = HashMap::new();
    for (j, n) in nodes.iter().enumerate() {
        match *n {
            N::Var(_) => {}
            N::Const(s, w) => {
                if s.saturating_add(w) <= bits.len() {
                    by_bits.entry(bits[s..s + w].to_vec()).or_default().push(j);
                }
            }
            _ => {
                by_key.entry(crate::query::node_op(n)).or_insert(j);
            }
        }
    }
    // Term constant node → its remaining candidates (more than one).
    let mut cands: HashMap<usize, Vec<usize>> = HashMap::new();
    let var_by_name: HashMap<&str, usize> = vars
        .iter()
        .map(|(name, _, node)| (name.as_str(), *node))
        .collect();
    let name_of: HashMap<usize, &str> = term
        .vars
        .iter()
        .map(|(name, _, node)| (*node, name.as_str()))
        .collect();
    // The term's values under the proven encoder and simulator, all
    // inputs false, and from them which nodes are constant-valued — the
    // trusted check's own rule (`kernel::node_const`): a constant is, a
    // variable is not, an operator is iff its operands are, except the
    // three short-circuits of the evaluator behind canonicalization: an
    // `ite` with a constant condition through the branch it selects, a
    // boolean `and` / `or` with a constant operand that decides it.
    let nin: usize = term
        .nodes
        .iter()
        .map(|n| if let N::Var(w) = n { *w } else { 0 })
        .sum();
    let mut raw = k::aig_new();
    let (words, _) = k::encode(&mut raw, &term.nodes, &term.bits, &[]);
    let vals = k::simulate(&raw, &vec![false; nin]);
    let cond = |c: usize| k::eval_lit(&vals, words[c][0]);
    let mut closed: Vec<bool> = Vec::with_capacity(term.nodes.len());
    for n in &term.nodes {
        let c = match *n {
            N::Var(_) => false,
            N::Const(_, _) => true,
            N::Ite(c, t, e) => closed[c] && if cond(c) { closed[t] } else { closed[e] },
            N::BoolAnd(a, b) => {
                (closed[a] && !cond(a)) || (closed[b] && !cond(b)) || (closed[a] && closed[b])
            }
            N::BoolOr(a, b) => {
                (closed[a] && cond(a)) || (closed[b] && cond(b)) || (closed[a] && closed[b])
            }
            _ => operands(n).iter().all(|&a| closed[a]),
        };
        closed.push(c);
    }
    let lookup = |e: &k::DagNode| -> Option<usize> {
        by_key
            .get(&crate::query::node_op(e))
            .or_else(|| by_key.get(&crate::query::node_op(&swap_comm(e))))
            .or_else(|| by_key.get(&crate::query::node_op(&mirror(e))))
            .copied()
    };
    let mut map: Vec<usize> = Vec::with_capacity(term.nodes.len());
    for (i, n) in term.nodes.iter().enumerate() {
        let image = match *n {
            N::Var(_) => name_of
                .get(&i)
                .and_then(|name| var_by_name.get(name))
                .copied(),
            N::Const(s, w) => {
                let cs = by_bits
                    .get(&term.bits[s..s + w])
                    .cloned()
                    .unwrap_or_default();
                if cs.len() > 1 {
                    cands.insert(i, cs.clone());
                }
                cs.first().copied()
            }
            _ => {
                // The structural lookup, over every choice of candidate for
                // the constant operands still undecided (almost always one
                // choice); a hit commits the choices.
                let ops = operands(n);
                let mut undecided: Vec<usize> = ops
                    .iter()
                    .copied()
                    .filter(|a| map[*a] != NO_IMAGE && cands.contains_key(a))
                    .collect();
                undecided.sort_unstable();
                undecided.dedup();
                let mut structural: Option<usize> = None;
                if ops.iter().all(|&a| map[a] != NO_IMAGE) {
                    let mut idx = vec![0usize; undecided.len()];
                    loop {
                        let choice: HashMap<usize, usize> = undecided
                            .iter()
                            .zip(&idx)
                            .map(|(&a, &k)| (a, cands[&a][k]))
                            .collect();
                        let at = |a: usize| -> Option<usize> {
                            Some(choice.get(&a).copied().unwrap_or(map[a]))
                        };
                        if let Some(hit) = map_operands(n, at).and_then(|e| lookup(&e)) {
                            for (&a, &c) in &choice {
                                map[a] = c;
                                cands.remove(&a);
                            }
                            structural = Some(hit);
                            break;
                        }
                        // The next combination (mixed radix), or done.
                        let mut pos = 0;
                        loop {
                            if pos == idx.len() {
                                break;
                            }
                            idx[pos] += 1;
                            if idx[pos] < cands[&undecided[pos]].len() {
                                break;
                            }
                            idx[pos] = 0;
                            pos += 1;
                        }
                        if pos == idx.len() {
                            break;
                        }
                    }
                }
                structural.or_else(|| {
                    // A fold: the constant with the node's value — every
                    // candidate kept, as for a constant node.
                    if closed[i] {
                        let value: Vec<bool> =
                            words[i].iter().map(|l| k::eval_lit(&vals, *l)).collect();
                        let cs = by_bits.get(&value).cloned().unwrap_or_default();
                        if cs.len() > 1 {
                            cands.insert(i, cs.clone());
                        }
                        cs.first().copied()
                    } else {
                        None
                    }
                })
            }
        };
        map.push(image.unwrap_or(NO_IMAGE));
    }
    map
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aig::{self, AigOptions};
    use crate::term::Sort;

    fn var(name: &str, w: u32) -> BvTerm {
        BvTerm::Var {
            name: name.into(),
            sort: Sort::new(w),
        }
    }
    fn c(value: u128, w: u32) -> BvTerm {
        BvTerm::Const {
            value,
            sort: Sort::new(w),
        }
    }
    fn b(t: BvTerm) -> Box<BvTerm> {
        Box::new(t)
    }
    fn bb(t: BoolTerm) -> Box<BoolTerm> {
        Box::new(t)
    }

    /// The shipped replay (phase 2's bridge, one `Aig::and` per raw gate),
    /// as the reference for `compact`: the raw arena node by node through
    /// `aig::Aig` with the given options.
    fn replay(raw: &k::Aig, opts: AigOptions) -> (aig::Aig, Vec<aig::Lit>) {
        let mut g = aig::Aig::with_options(opts);
        let mut map: Vec<aig::Lit> = Vec::with_capacity(raw.nodes.len());
        let lift = |map: &[aig::Lit], l: k::Lit| {
            if l.neg {
                map[l.node].not()
            } else {
                map[l.node]
            }
        };
        for n in &raw.nodes {
            let r = match *n {
                k::Node::False => aig::Lit::FALSE,
                k::Node::Input(_) => g.input(),
                k::Node::And(x, y) => {
                    let (rx, ry) = (lift(&map, x), lift(&map, y));
                    g.and(rx, ry)
                }
            };
            map.push(r);
        }
        (g, map)
    }

    /// `compact` with `strash_hints` IS the `Aig::and` replay: the same
    /// arena node for node (inputs and gates, operands included) and the
    /// same literal for every raw node; and the kernel `tseitin` on it is
    /// `cnf::tseitin` on the replay, clause for clause.
    pub(crate) fn assert_compact_is_replay(raw: &k::Aig, outs: &[k::Lit], what: &str) {
        for (opts, hints) in [
            (AigOptions::default(), strash_hints(raw)),
            (AigOptions::FOLD_ONLY, no_hints(raw)),
        ] {
            let (ref_aig, ref_map) = replay(raw, opts);
            let (got, map) = k::compact(raw, &hints);
            assert_eq!(
                got.nodes.len(),
                ref_aig.num_vars() as usize,
                "{what} {opts:?}: node count"
            );
            let ref_gates: Vec<(u32, u32, u32)> = ref_aig
                .and_gates()
                .map(|(v, a, b)| (v, a.raw(), b.raw()))
                .collect();
            let got_gates: Vec<(u32, u32, u32)> = got
                .nodes
                .iter()
                .enumerate()
                .filter_map(|(i, n)| match n {
                    k::Node::And(x, y) => Some((
                        i as u32,
                        (x.node as u32) << 1 | x.neg as u32,
                        (y.node as u32) << 1 | y.neg as u32,
                    )),
                    _ => None,
                })
                .collect();
            assert_eq!(got_gates, ref_gates, "{what} {opts:?}: gates");
            for (i, (m, r)) in map.iter().zip(&ref_map).enumerate() {
                assert_eq!(
                    (m.node as u32) << 1 | m.neg as u32,
                    r.raw(),
                    "{what} {opts:?}: map of raw node {i}"
                );
            }
            let mapped = k::map_word(&map, outs);
            let ref_outs: Vec<aig::Lit> = outs
                .iter()
                .map(|&l| {
                    if l.neg {
                        ref_map[l.node].not()
                    } else {
                        ref_map[l.node]
                    }
                })
                .collect();
            let (ref_cnf, _) = crate::cnf::tseitin(&ref_aig, &ref_outs);
            let cnf = k::tseitin(&got, &mapped);
            assert_eq!(
                ref_cnf.num_vars as usize,
                got.nodes.len(),
                "{what} {opts:?}: num_vars"
            );
            assert_eq!(ref_cnf.clauses, cnf, "{what} {opts:?}: CNF");
        }
    }

    // rivet: verifies VER-061
    /// The DAG path's compaction equals the shipped replay on a query that
    /// exercises folding (constants), sharing (a repeated subterm) and
    /// every boolean connective.
    #[test]
    fn compact_matches_replay_on_a_shared_query() {
        let x = var("x", 8);
        let y = var("y", 8);
        let t = BvTerm::Add(b(x.clone()), b(y.clone()));
        let q = vec![
            BoolTerm::Or(
                bb(BoolTerm::Ult(b(t.clone()), b(c(17, 8)))),
                bb(BoolTerm::Not(bb(BoolTerm::Eq(
                    b(BvTerm::Mul(b(t.clone()), b(c(3, 8)))),
                    b(BvTerm::And(b(x.clone()), b(c(0xF0, 8)))),
                )))),
            ),
            BoolTerm::And(
                bb(BoolTerm::Sle(b(t), b(y))),
                bb(BoolTerm::Ne(b(x), b(c(0, 8)))),
            ),
        ];
        let mut bld = DagBuilder::new(true);
        for a in &q {
            bld.assert_root(&crate::canon::canonicalize_bool(a))
                .unwrap();
        }
        let dag = bld.finish();
        assert_eq!(dag.roots.len(), 2);
        let mut raw = k::aig_new();
        let (_, outs) = k::encode(&mut raw, &dag.nodes, &dag.bits, &dag.roots);
        assert!(
            raw.nodes.len() > 100,
            "the raw arena holds the full circuits"
        );
        assert_compact_is_replay(&raw, &outs, "shared query");
    }

    // rivet: verifies VER-061
    /// Wrong hints are harmless: pointing every gate at node 0, at a
    /// random earlier node, or past the end gives a correct (merely
    /// unshared) arena whose outputs simulate like the raw ones.
    #[test]
    fn wrong_hints_only_cost_sharing() {
        let x = var("x", 6);
        let y = var("y", 6);
        let q = BoolTerm::Eq(
            b(BvTerm::Mul(b(x.clone()), b(y.clone()))),
            b(BvTerm::Mul(b(y), b(x))),
        );
        let mut bld = DagBuilder::new(true);
        bld.assert_root(&q).unwrap();
        let dag = bld.finish();
        let mut raw = k::aig_new();
        let (_, outs) = k::encode(&mut raw, &dag.nodes, &dag.bits, &dag.roots);
        let n = raw.nodes.len();
        let good = strash_hints(&raw);
        let (ref_aig, ref_map) = k::compact(&raw, &good);
        let ref_out = k::map_word(&ref_map, &outs);
        let bad_sets: [Vec<usize>; 4] = [
            vec![0; n],
            (0..n).map(|i| (i * 7919) % n).collect(),
            vec![usize::MAX; n],
            vec![],
        ];
        for (k_, bad) in bad_sets.iter().enumerate() {
            let (aig2, map2) = k::compact(&raw, bad);
            let out2 = k::map_word(&map2, &outs);
            assert!(
                aig2.nodes.len() >= ref_aig.nodes.len(),
                "hint set {k_}: no better than the real strash"
            );
            for bits in 0u32..4096 {
                let inputs: Vec<bool> = (0..12).map(|j| bits >> j & 1 == 1).collect();
                let v_raw = k::eval_lit(&k::simulate(&raw, &inputs), outs[0]);
                let v_ref = k::eval_lit(&k::simulate(&ref_aig, &inputs), ref_out[0]);
                let v2 = k::eval_lit(&k::simulate(&aig2, &inputs), out2[0]);
                assert_eq!(v_raw, v_ref, "hinted compaction preserves the output");
                assert_eq!(v_raw, v2, "hint set {k_}: wrong hints preserve the output");
            }
        }
    }
}

/// #192 evidence before proof: the untrusted translation from a term to the
/// trusted crate's DAG — `canon.rs`, `dag.rs` and the model→inputs glue —
/// checked against the independent evaluator `eval.rs`. For random
/// assertions over every operator at the odd widths the #182 class hid at,
/// and random models, `ordeal_lrat::check_query_model` (proven against the
/// Lean `BitVec` semantics of the DAG) must accept exactly when `eval.rs`
/// says the ORIGINAL assertion holds. A translation bug that changes the
/// meaning of a term shows up as a disagreement here.
#[cfg(test)]
mod denotation_guard {
    use super::DagBuilder;
    use crate::eval::{self, Env};
    use crate::query::{QueryDag, QueryInputs};
    use crate::solver::Model;
    use crate::term::{BoolTerm, BvTerm, Sort};
    use ordeal_lrat as k;

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
        fn value(&mut self, w: u32) -> u128 {
            let r = (u128::from(self.next()) << 64) | u128::from(self.next());
            // Bias toward the edge values the SMT-LIB corner cases live at.
            let v = match self.below(6) {
                0 => 0,
                1 => u128::MAX,
                2 => 1,
                3 => 1u128 << (w - 1),
                _ => r,
            };
            if w >= 128 { v } else { v & ((1u128 << w) - 1) }
        }
    }

    /// The widths: the odd ones #182 hid at, the powers of two, and the
    /// extremes.
    const WIDTHS: [u32; 10] = [1, 3, 5, 8, 12, 16, 24, 32, 64, 128];

    fn b<T>(t: T) -> Box<T> {
        Box::new(t)
    }

    fn var(w: u32, k: u64) -> BvTerm {
        BvTerm::Var {
            name: format!("v{w}_{k}"),
            sort: Sort::new(w),
        }
    }

    /// A random term of exactly width `w`.
    fn gen_bv(rng: &mut Rng, w: u32, depth: u32) -> BvTerm {
        if depth == 0 || rng.below(4) == 0 {
            return if rng.below(3) == 0 {
                BvTerm::Const {
                    value: rng.value(w),
                    sort: Sort::new(w),
                }
            } else {
                var(w, rng.below(3))
            };
        }
        let d = depth - 1;
        let sub = |rng: &mut Rng| gen_bv(rng, w, d);
        match rng.below(24) {
            0 => BvTerm::Add(b(sub(rng)), b(sub(rng))),
            1 => BvTerm::Sub(b(sub(rng)), b(sub(rng))),
            2 => BvTerm::Mul(b(sub(rng)), b(sub(rng))),
            3 => BvTerm::Udiv(b(sub(rng)), b(sub(rng))),
            4 => BvTerm::Urem(b(sub(rng)), b(sub(rng))),
            5 => BvTerm::And(b(sub(rng)), b(sub(rng))),
            6 => BvTerm::Or(b(sub(rng)), b(sub(rng))),
            7 => BvTerm::Xor(b(sub(rng)), b(sub(rng))),
            8 => BvTerm::Shl(b(sub(rng)), b(sub(rng))),
            9 => BvTerm::Lshr(b(sub(rng)), b(sub(rng))),
            10 => BvTerm::Ashr(b(sub(rng)), b(sub(rng))),
            11 => BvTerm::Rotr(b(sub(rng)), b(sub(rng))),
            12 => BvTerm::Rotl(b(sub(rng)), b(sub(rng))),
            13 => BvTerm::Sdiv(b(sub(rng)), b(sub(rng))),
            14 => BvTerm::Srem(b(sub(rng)), b(sub(rng))),
            15 => BvTerm::Not(b(sub(rng))),
            16 => BvTerm::Neg(b(sub(rng))),
            17 => BvTerm::Ite {
                cond: b(gen_bool(rng, d)),
                then_: b(sub(rng)),
                else_: b(sub(rng)),
            },
            // Width-changing constructs, each producing exactly `w`.
            18 if w > 1 => {
                let lo_w = 1 + rng.below(u64::from(w - 1)) as u32;
                BvTerm::Concat(b(gen_bv(rng, w - lo_w, d)), b(gen_bv(rng, lo_w, d)))
            }
            19 if w < 128 => {
                let wider = w + 1 + rng.below(u64::from(128 - w).min(16)) as u32;
                let lo = rng.below(u64::from(wider - w + 1)) as u32;
                BvTerm::Extract {
                    hi: lo + w - 1,
                    lo,
                    arg: b(gen_bv(rng, wider, d)),
                }
            }
            20 | 21 if w > 1 => {
                let by = 1 + rng.below(u64::from(w - 1)) as u32;
                let arg = b(gen_bv(rng, w - by, d));
                if rng.below(2) == 0 {
                    BvTerm::ZeroExt { by, arg }
                } else {
                    BvTerm::SignExt { by, arg }
                }
            }
            // Commuted operands, so canonicalization's reordering is hit.
            _ => {
                let (x, y) = (sub(rng), sub(rng));
                BvTerm::Add(
                    b(BvTerm::Mul(b(x.clone()), b(y.clone()))),
                    b(BvTerm::Mul(b(y), b(x))),
                )
            }
        }
    }

    fn gen_bool(rng: &mut Rng, depth: u32) -> BoolTerm {
        if depth == 0 || rng.below(3) != 0 {
            let w = WIDTHS[rng.below(WIDTHS.len() as u64) as usize];
            let d = depth.min(2);
            let (x, y) = (b(gen_bv(rng, w, d)), b(gen_bv(rng, w, d)));
            return match rng.below(10) {
                0 => BoolTerm::Eq(x, y),
                1 => BoolTerm::Ne(x, y),
                2 => BoolTerm::Ult(x, y),
                3 => BoolTerm::Ule(x, y),
                4 => BoolTerm::Ugt(x, y),
                5 => BoolTerm::Uge(x, y),
                6 => BoolTerm::Slt(x, y),
                7 => BoolTerm::Sle(x, y),
                8 => BoolTerm::Sgt(x, y),
                _ => BoolTerm::Sge(x, y),
            };
        }
        let d = depth - 1;
        match rng.below(3) {
            0 => BoolTerm::Not(b(gen_bool(rng, d))),
            1 => BoolTerm::And(b(gen_bool(rng, d)), b(gen_bool(rng, d))),
            _ => BoolTerm::Or(b(gen_bool(rng, d)), b(gen_bool(rng, d))),
        }
    }

    /// Does the trusted crate accept the assertion under `env`, after the
    /// production translation (optionally rewriting the derived ops first,
    /// as the default path does)?
    fn trusted_accepts(a: &BoolTerm, env: &Env, rewrite: bool) -> bool {
        let a = if rewrite {
            crate::lowering::expand_bool(a).expect("well-sorted")
        } else {
            a.clone()
        };
        let a = crate::canon::canonicalize_bool(&a);
        let mut builder = DagBuilder::new(true);
        builder.assert_root(&a).expect("well-sorted");
        let dag = builder.finish();
        let query = QueryDag {
            nodes: dag.nodes,
            bits: dag.bits,
            roots: dag.roots,
            hints: Vec::new(),
        };
        let model = Model {
            assignments: env.iter().map(|(k, v)| (k.clone(), *v)).collect(),
        };
        let inputs = QueryInputs::from_model(&query, &dag.vars, &model);
        match k::check_query_model(&query.nodes, &query.bits, &query.roots, &inputs.bits) {
            Ok(()) => true,
            Err(k::ModelError::RootFalse { .. }) => false,
            Err(e) => panic!("the DAG of a well-sorted assertion was refused: {e:?}"),
        }
    }

    /// The term-to-DAG correspondence of the production translation of
    /// `a` — `canon` + `DagBuilder` against `flatten` + `term_map` — is
    /// accepted by the trusted `check_term_dag`.
    fn term_is_mapped_and_accepted(a: &BoolTerm, case: usize) {
        let canon = crate::canon::canonicalize_bool(a);
        let mut builder = DagBuilder::new(true);
        builder.assert_root(&canon).expect("well-sorted");
        let dag = builder.finish();
        let query = QueryDag {
            nodes: dag.nodes,
            bits: dag.bits,
            roots: dag.roots,
            hints: Vec::new(),
        };
        let term = crate::query::QueryTerm::flatten(std::slice::from_ref(a), &query, &dag.vars)
            .expect("well-sorted");
        assert_eq!(
            term.check(&query),
            Ok(()),
            "case {case}: the trusted term check must accept the production translation of {a:?} (map {:?})",
            term.map
        );
    }

    fn env_for(rng: &mut Rng) -> Env {
        let mut env = Env::new();
        // Every width: Concat / Extract / ZeroExt / SignExt reach widths
        // outside WIDTHS.
        for w in 1..=128u32 {
            for k in 0..3 {
                env.insert(format!("v{w}_{k}"), rng.value(w));
            }
        }
        env
    }

    // rivet: verifies VER-068
    // rivet: verifies VER-069
    #[test]
    fn dag_translation_agrees_with_the_evaluator() {
        let mut rng = Rng(0x0192_DE40_7A71_0001);
        let (mut trues, mut falses) = (0u32, 0u32);
        for i in 0..1500 {
            let a = gen_bool(&mut rng, 3);
            let env = env_for(&mut rng);
            let want = eval::eval_bool(&a, &env).expect("well-sorted");
            // canon.rs alone must preserve the meaning…
            assert_eq!(
                eval::eval_bool(&crate::canon::canonicalize_bool(&a), &env),
                Ok(want),
                "case {i}: canonicalization changed the value of {a:?}"
            );
            // …and so must the whole translation, on both paths.
            for rewrite in [false, true] {
                assert_eq!(
                    trusted_accepts(&a, &env, rewrite),
                    want,
                    "case {i} (rewrite = {rewrite}): the trusted DAG value differs from eval.rs for {a:?} under {env:?}"
                );
            }
            // #192 phase 7 (TR-069): the production translation is also
            // accepted by the trusted term-to-DAG check — the positive
            // control of `term_map` on every operator and width.
            term_is_mapped_and_accepted(&a, i);
            if want { trues += 1 } else { falses += 1 }
        }
        // Both outcomes must be well represented, or the check is lopsided.
        assert!(
            trues > 300 && falses > 300,
            "trues {trues}, falses {falses}"
        );
    }
}
