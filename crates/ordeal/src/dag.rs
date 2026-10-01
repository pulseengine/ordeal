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
