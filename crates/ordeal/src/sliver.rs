//! The loom array/UF sliver (P3) — an extended query layer that is
//! **preprocessed away** into the closed QF_BV core before bit-blasting.
//!
//! The core `term.rs` fragment stays closed (CLAUDE.md / loom #246): these
//! constructs have **no bit-blasting rule**. Instead they live in a separate
//! extended term language here and are eliminated by preprocessing
//! ([`lower`]) into a conjunction of plain [`BoolTerm`] assertions that the
//! existing pipeline decides. No array/UF ops ever reach the AIG.
//!
//! What loom emits (ARCHITECTURE.md → "The array / UF sliver", TR-008):
//!
//! - **Non-extensional `Array(BV32 → BV8)`** modeling linear memory:
//!   `store`/`select` over **concrete and symbolic** BV32 indices (symbolic
//!   decided since v0.11.0 / TR-028). No whole-array equality. Eliminated by
//!   **eager read-over-write**: a `select` on a `store` chain reduces to a
//!   nested if-then-else over index equalities (constant-folded when both
//!   indices are concrete) down to the base array's fresh per-index
//!   variables.
//! - **Uninterpreted `pure_call`** with **congruence** (same args ⇒ same
//!   result). Eliminated by **Ackermannization**: each distinct call site
//!   becomes a fresh variable, plus congruence constraints
//!   `args_i = args_j → result_i = result_j` across call sites of the same
//!   function.
//!
//! Design decision (rivet DES-014): a separate `Ext*` layer rather than
//! widening `BvTerm`, so the core fragment's "every op has a proven
//! bit-blasting rule" invariant is preserved by construction — the sliver
//! is sound *because* it never reaches the blaster, only the core does.

use crate::eval::{self, Env, EvalError};
use crate::term::{BoolTerm, BvTerm, Sort};
use ordeal_lrat::ExtNode;
use ordeal_lrat::blast_kernel::DagNode;
use std::collections::{BTreeMap, BTreeSet};

/// An array-sorted term: `Array(BV32 → BV8)`, non-extensional.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum ArrayTerm {
    /// A free array variable (base linear memory).
    Var { name: String },
    /// `store(array, index, value)` — index is BV32, value is BV8.
    Store {
        /// The array being updated.
        array: Box<ArrayTerm>,
        /// The BV32 index written.
        index: Box<ExtBvTerm>,
        /// The BV8 value written.
        value: Box<ExtBvTerm>,
    },
}

/// A bitvector-sorted term in the extended (sliver) language: the closed
/// core plus `select` and uninterpreted `pure_call`.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum ExtBvTerm {
    /// A pure-core term (no sliver constructs beneath it), embedded verbatim.
    Core(BvTerm),
    /// A core operation whose children may themselves be extended. Mirrors
    /// `BvTerm`'s recursive structure but over `ExtBvTerm` children, so a
    /// `select` can appear anywhere a bitvector is expected. Preprocessing
    /// pushes elimination through these.
    Op(Box<ExtOp>),
    /// `select(array, index)` — reads the BV8 at BV32 `index`.
    Select {
        /// The array read from.
        array: Box<ArrayTerm>,
        /// The BV32 index read.
        index: Box<ExtBvTerm>,
    },
    /// An uninterpreted function application returning `sort`. Congruence:
    /// equal argument tuples must yield equal results.
    PureCall {
        /// The function's name (its identity for congruence).
        name: String,
        /// The argument terms.
        args: Vec<ExtBvTerm>,
        /// The result sort.
        sort: Sort,
    },
}

/// The recursive core operations lifted over `ExtBvTerm` children.
/// (One variant per `BvTerm` operator that has bitvector children;
/// leaves — `Const`/`Var` — use [`ExtBvTerm::Core`].) Each lowers to the
/// `BvTerm` node of the same name, so no operator is added to the closed
/// core: the sliver only lets a `select`/`pure_call` sit beneath it (#231).
#[derive(Clone, Debug)]
#[allow(missing_docs)]
#[non_exhaustive]
pub enum ExtOp {
    Add(ExtBvTerm, ExtBvTerm),
    Sub(ExtBvTerm, ExtBvTerm),
    Mul(ExtBvTerm, ExtBvTerm),
    Udiv(ExtBvTerm, ExtBvTerm),
    Urem(ExtBvTerm, ExtBvTerm),
    Sdiv(ExtBvTerm, ExtBvTerm),
    Srem(ExtBvTerm, ExtBvTerm),
    And(ExtBvTerm, ExtBvTerm),
    Or(ExtBvTerm, ExtBvTerm),
    Xor(ExtBvTerm, ExtBvTerm),
    Shl(ExtBvTerm, ExtBvTerm),
    Lshr(ExtBvTerm, ExtBvTerm),
    Ashr(ExtBvTerm, ExtBvTerm),
    Rotr(ExtBvTerm, ExtBvTerm),
    Rotl(ExtBvTerm, ExtBvTerm),
    Not(ExtBvTerm),
    Neg(ExtBvTerm),
    Extract {
        hi: u32,
        lo: u32,
        arg: ExtBvTerm,
    },
    Concat(ExtBvTerm, ExtBvTerm),
    ZeroExt {
        by: u32,
        arg: ExtBvTerm,
    },
    SignExt {
        by: u32,
        arg: ExtBvTerm,
    },
    /// `cond ? then_ : else_`, where the condition and both branches may
    /// contain sliver constructs. Lowers to [`BvTerm::Ite`]. The Ackermann
    /// and array congruence constraints are emitted unconditionally, so a
    /// call or read under the untaken branch is still constrained
    /// consistently: they hold in every model.
    Ite {
        cond: ExtBoolTerm,
        then_: ExtBvTerm,
        else_: ExtBvTerm,
    },
}

/// A boolean-sorted term in the extended language.
#[derive(Clone, Debug)]
#[allow(missing_docs)]
#[non_exhaustive]
pub enum ExtBoolTerm {
    Eq(ExtBvTerm, ExtBvTerm),
    Ne(ExtBvTerm, ExtBvTerm),
    Ult(ExtBvTerm, ExtBvTerm),
    Ule(ExtBvTerm, ExtBvTerm),
    Ugt(ExtBvTerm, ExtBvTerm),
    Uge(ExtBvTerm, ExtBvTerm),
    Slt(ExtBvTerm, ExtBvTerm),
    Sle(ExtBvTerm, ExtBvTerm),
    Sgt(ExtBvTerm, ExtBvTerm),
    Sge(ExtBvTerm, ExtBvTerm),
    Not(Box<ExtBoolTerm>),
    And(Box<ExtBoolTerm>, Box<ExtBoolTerm>),
    Or(Box<ExtBoolTerm>, Box<ExtBoolTerm>),
}

/// Why a sliver query is outside the supported fragment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SliverError {
    /// **Never returned.** Symbolic BV32 indices have been decided since
    /// v0.11.0 (TR-028): [`lower`] accepts any BV32 index, concrete or not,
    /// and builds the read-over-write `ite` over the index equality. The
    /// variant is kept only so that consumers who match `SliverError`
    /// exhaustively keep compiling; it will be removed in a breaking release.
    NonConcreteIndex,
    /// A `select`/`store` index was not BV32, or a value not BV8.
    BadArraySort,
    /// A `pure_call`'s argument arity/sorts were inconsistent across sites.
    InconsistentCall {
        /// The offending function name.
        name: String,
    },
}

/// Eliminate the sliver into a pure-core conjunction (DES-014/015/016).
///
/// Returns the lowered [`BoolTerm`] assertions (the read-over-write
/// expansions followed by the Ackermannization congruence constraints)
/// that are equisatisfiable with the input, or a [`SliverError`] if the
/// query is out of the supported sliver.
///
/// The result contains no array/UF constructs — only the closed core — so
/// the existing blast → AIG → CNF → CDCL → checker pipeline decides it
/// unchanged. Lowering is deterministic: the same input always yields the
/// same output (fresh-variable names are assigned in a fixed traversal
/// order and memoized).
pub fn lower(assertions: &[ExtBoolTerm]) -> Result<Vec<BoolTerm>, SliverError> {
    lower_traced(assertions).map(|l| l.assertions)
}

/// The lowered core plus the provenance of every fresh variable it
/// introduced — the extra bookkeeping [`lower`] discards.
///
/// [`lower`] is the production entry point (it returns only the core
/// assertions). [`lower_traced`] additionally reports which core variable
/// stands for each array read and each uninterpreted-call site, which lets
/// a caller reconstruct a core model from a concrete [`SliverModel`] (see
/// the module tests). The `assertions` field is exactly what [`lower`]
/// returns.
#[derive(Clone, Debug, Default)]
pub struct Lowered {
    /// The lowered pure-core assertions (originals, then the array
    /// congruence roots, then the call congruence roots — each set in the
    /// table order of [`Lowered::read_sites`] / [`Lowered::calls`]: pairs
    /// `p < q` of one array / one function).
    pub assertions: Vec<BoolTerm>,
    /// Fresh per-index read variables: `(core_var_name, base_array, index)`.
    /// Concrete reads only; [`Lowered::read_sites`] has every read.
    pub reads: Vec<(String, String, u32)>,
    /// Fresh call-site result variables, in dependency order:
    /// `(core_var_name, function_name, lowered_args, result_sort)`.
    pub calls: Vec<(String, String, Vec<BvTerm>, Sort)>,
    /// Every base-array read, in creation order — the read table of the
    /// trusted check (TR-072): `(core_var_name, base_array, lowered
    /// index)`. The lowered index is what the read was memoized on, so two
    /// entries never share `(base_array, index)`.
    pub read_sites: Vec<(String, String, BvTerm)>,
}

/// The extended query flattened as it was asked (`ordeal-ext/v1`, TR-072):
/// a node list over [`ExtNode`] — 1:1 with the [`ExtBoolTerm`] tree
/// (operands before operators, left to right; a `select`'s index, then
/// its chain outermost store first, each level's index then value; a
/// call's arguments in order), variables shared by name, constants
/// interned by value and width, arrays and functions numbered by first
/// appearance. No canonicalization and no hash-consing: a consumer holding
/// the `ExtBoolTerm`s re-runs [`flatten_ext`] and compares the hash.
#[derive(Clone, Default, PartialEq, Eq)]
pub struct ExtQuery {
    /// The nodes.
    pub nodes: Vec<ExtNode>,
    /// The constant table (LSB first).
    pub bits: Vec<bool>,
    /// The side table: store chains (index, value pairs) and call arguments.
    pub side: Vec<usize>,
    /// The asserted nodes, one per assertion, in assertion order.
    pub roots: Vec<usize>,
    /// Per query variable: `(name, width, its `Var` node)`.
    pub vars: Vec<(String, u32, usize)>,
    /// Array names by id.
    pub arrays: Vec<String>,
    /// Function names and result widths by id.
    pub funcs: Vec<(String, u32)>,
}

impl std::fmt::Debug for ExtQuery {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExtQuery")
            .field("nodes", &self.nodes.len())
            .field("bits", &self.bits.len())
            .field("side", &self.side.len())
            .field("roots", &self.roots)
            .field("vars", &self.vars.len())
            .field("arrays", &self.arrays)
            .field("funcs", &self.funcs)
            .finish()
    }
}

/// What [`lower_ext`] produces: the extended query flattened, its lowered
/// core with the fresh-variable tables, and per extended node the lowered
/// image of a `select` or a call (what the untrusted mapper interns to find
/// the node's core image; a closed node's image is its operator over its
/// operands' images).
#[derive(Clone, Debug, Default)]
pub struct SliverTrace {
    /// The extended query as asked.
    pub ext: ExtQuery,
    /// The lowered core and the read / call tables.
    pub lowered: Lowered,
    /// Per extended node: the lowered term of a `select` or a call, `None`
    /// for a closed node.
    pub images: Vec<Option<BvTerm>>,
}

/// A closed core assertion as an extended one (every leaf an
/// [`ExtBvTerm::Core`]): how a [`crate::Solver`] built by
/// [`crate::Solver::from_sliver`] keeps a later `assert` in its extended
/// query, so the lowering it re-runs for the trusted check is the whole
/// query.
pub fn ext_of_core(t: &BoolTerm) -> ExtBoolTerm {
    let c = |x: &BvTerm| ExtBvTerm::Core(x.clone());
    match t {
        BoolTerm::Eq(a, b) => ExtBoolTerm::Eq(c(a), c(b)),
        BoolTerm::Ne(a, b) => ExtBoolTerm::Ne(c(a), c(b)),
        BoolTerm::Ult(a, b) => ExtBoolTerm::Ult(c(a), c(b)),
        BoolTerm::Ule(a, b) => ExtBoolTerm::Ule(c(a), c(b)),
        BoolTerm::Ugt(a, b) => ExtBoolTerm::Ugt(c(a), c(b)),
        BoolTerm::Uge(a, b) => ExtBoolTerm::Uge(c(a), c(b)),
        BoolTerm::Slt(a, b) => ExtBoolTerm::Slt(c(a), c(b)),
        BoolTerm::Sle(a, b) => ExtBoolTerm::Sle(c(a), c(b)),
        BoolTerm::Sgt(a, b) => ExtBoolTerm::Sgt(c(a), c(b)),
        BoolTerm::Sge(a, b) => ExtBoolTerm::Sge(c(a), c(b)),
        BoolTerm::Not(x) => ExtBoolTerm::Not(Box::new(ext_of_core(x))),
        BoolTerm::And(a, b) => ExtBoolTerm::And(Box::new(ext_of_core(a)), Box::new(ext_of_core(b))),
        BoolTerm::Or(a, b) => ExtBoolTerm::Or(Box::new(ext_of_core(a)), Box::new(ext_of_core(b))),
    }
}

/// Like [`lower`], but also returns the fresh-variable provenance in a
/// [`Lowered`]. See [`Lowered`] for why a caller might want it.
pub fn lower_traced(assertions: &[ExtBoolTerm]) -> Result<Lowered, SliverError> {
    lower_ext(assertions).map(|t| t.lowered)
}

/// Flatten the extended query as asked (`ordeal-ext/v1`): the consumer's
/// side of the trusted sliver check — what an `ordeal-cert/v4` bundle's
/// `ext` block carries, re-runnable from the `ExtBoolTerm`s alone. Fails
/// only on an out-of-sliver query (it is one walk with the lowering).
pub fn flatten_ext(assertions: &[ExtBoolTerm]) -> Result<ExtQuery, SliverError> {
    lower_ext(assertions).map(|t| t.ext)
}

/// Lower AND flatten in one walk (TR-072): the lowered core with its
/// tables, the extended query as asked, and per extended node the lowered
/// image of every `select` and call. One traversal assigns the extended
/// node ids and lowers, so the two never disagree on which node is which.
pub fn lower_ext(assertions: &[ExtBoolTerm]) -> Result<SliverTrace, SliverError> {
    let mut low = Lowering::default();
    for a in assertions {
        names_bool(a, &mut low.taken);
    }
    let mut out = Vec::with_capacity(assertions.len());
    for a in assertions {
        let (core, id) = low.lower_bool(a)?;
        out.push(core);
        low.ext.roots.push(id);
    }
    out.extend(low.array_congruence());
    out.extend(low.congruence());
    #[cfg(test)]
    if hooks::dropping_last_congruence() && out.len() > assertions.len() {
        // The negative control of TR-072: a lowering that forgets one
        // congruence clause — the core, the DAG and the CNF all agree on
        // the forgetful lowering, so only the trusted sliver check can
        // catch it (by the root count it expects).
        out.pop();
    }
    let read_sites = low
        .reads
        .iter()
        .map(|r| (r.var_name.clone(), r.array.clone(), r.index.clone()))
        .collect();
    let ExtFlat {
        nodes,
        bits,
        side,
        roots,
        vars,
        arrays,
        funcs,
        lowered,
        ..
    } = low.ext;
    Ok(SliverTrace {
        ext: ExtQuery {
            nodes,
            bits,
            side,
            roots,
            vars,
            arrays,
            funcs,
        },
        lowered: Lowered {
            assertions: out,
            reads: low.read_trace,
            calls: low.call_trace,
            read_sites,
        },
        images: lowered,
    })
}

/// The test-only hook of the TR-072 negative control: a lowering that
/// omits its last congruence clause. Armed per thread by a unit test
/// around a real entry point; compiled out of every non-test build.
#[cfg(test)]
pub(crate) mod hooks {
    use std::cell::Cell;

    thread_local! {
        static DROP_LAST: Cell<bool> = const { Cell::new(false) };
    }

    /// Arm the hook for the calling thread; the guard disarms it on drop.
    pub(crate) fn drop_last_congruence() -> Armed {
        DROP_LAST.with(|c| c.set(true));
        Armed
    }

    pub(crate) fn dropping_last_congruence() -> bool {
        DROP_LAST.with(|c| c.get())
    }

    /// Disarms the hook when dropped.
    pub(crate) struct Armed;

    impl Drop for Armed {
        fn drop(&mut self) {
            DROP_LAST.with(|c| c.set(false));
        }
    }
}

/// The constant value of a lowered term, if it is one. Used to keep the
/// concrete fast path: a `store`/`select` index pair that is statically
/// decidable never reaches the SAT core.
fn as_const(t: &BvTerm) -> Option<u128> {
    match t {
        // Masked (#262): two constants with equal bits are one index, as
        // the trusted check reads them; the raw value's bits above the
        // width mean nothing to the core.
        BvTerm::Const { value, sort } => Some(eval::mask_to(*value, sort.width)),
        _ => None,
    }
}

/// A closed term with every constant MASKED to its width (#262): what the
/// lowered core carries, so that two constants with equal bits are one
/// constant everywhere downstream — the solver's DAG interns by value,
/// the trusted sliver check keys the read table on node identity, and
/// the read / call memos compare values.
pub fn masked_bv(t: &BvTerm) -> BvTerm {
    use BvTerm as B;
    let c = |x: &BvTerm| Box::new(masked_bv(x));
    match t {
        B::Const { value, sort } => B::Const {
            value: eval::mask_to(*value, sort.width),
            sort: *sort,
        },
        B::Var { .. } => t.clone(),
        B::Add(a, b) => B::Add(c(a), c(b)),
        B::Sub(a, b) => B::Sub(c(a), c(b)),
        B::Mul(a, b) => B::Mul(c(a), c(b)),
        B::Udiv(a, b) => B::Udiv(c(a), c(b)),
        B::Urem(a, b) => B::Urem(c(a), c(b)),
        B::And(a, b) => B::And(c(a), c(b)),
        B::Or(a, b) => B::Or(c(a), c(b)),
        B::Xor(a, b) => B::Xor(c(a), c(b)),
        B::Shl(a, b) => B::Shl(c(a), c(b)),
        B::Lshr(a, b) => B::Lshr(c(a), c(b)),
        B::Ashr(a, b) => B::Ashr(c(a), c(b)),
        B::Rotr(a, b) => B::Rotr(c(a), c(b)),
        B::Rotl(a, b) => B::Rotl(c(a), c(b)),
        B::Sdiv(a, b) => B::Sdiv(c(a), c(b)),
        B::Srem(a, b) => B::Srem(c(a), c(b)),
        B::Concat(a, b) => B::Concat(c(a), c(b)),
        B::Not(a) => B::Not(c(a)),
        B::Neg(a) => B::Neg(c(a)),
        B::Extract { hi, lo, arg } => B::Extract {
            hi: *hi,
            lo: *lo,
            arg: c(arg),
        },
        B::ZeroExt { by, arg } => B::ZeroExt {
            by: *by,
            arg: c(arg),
        },
        B::SignExt { by, arg } => B::SignExt {
            by: *by,
            arg: c(arg),
        },
        B::Ite { cond, then_, else_ } => B::Ite {
            cond: Box::new(masked_bool(cond)),
            then_: c(then_),
            else_: c(else_),
        },
    }
}

/// [`masked_bv`] on a closed boolean term.
pub fn masked_bool(t: &BoolTerm) -> BoolTerm {
    use BoolTerm as T;
    let c = |x: &BvTerm| Box::new(masked_bv(x));
    match t {
        T::Eq(a, b) => T::Eq(c(a), c(b)),
        T::Ne(a, b) => T::Ne(c(a), c(b)),
        T::Ult(a, b) => T::Ult(c(a), c(b)),
        T::Ule(a, b) => T::Ule(c(a), c(b)),
        T::Ugt(a, b) => T::Ugt(c(a), c(b)),
        T::Uge(a, b) => T::Uge(c(a), c(b)),
        T::Slt(a, b) => T::Slt(c(a), c(b)),
        T::Sle(a, b) => T::Sle(c(a), c(b)),
        T::Sgt(a, b) => T::Sgt(c(a), c(b)),
        T::Sge(a, b) => T::Sge(c(a), c(b)),
        T::Not(a) => T::Not(Box::new(masked_bool(a))),
        T::And(a, b) => T::And(Box::new(masked_bool(a)), Box::new(masked_bool(b))),
        T::Or(a, b) => T::Or(Box::new(masked_bool(a)), Box::new(masked_bool(b))),
    }
}

/// The memo key of a lowered index or argument term: a constant by its
/// masked value (#262), anything else by its structure.
fn term_key(t: &BvTerm) -> String {
    match as_const(t) {
        Some(c) => format!("#{c}"),
        None => format!("{t:?}"),
    }
}

/// A distinct uninterpreted-call site kept for congruence: its function,
/// its lowered argument terms and the fresh core variable standing for
/// its result.
struct CallSite {
    name: String,
    args: Vec<BvTerm>,
    result: BvTerm,
}

/// A distinct base-array read kept for congruence: its array, the lowered
/// BV32 index and the fresh BV8 variable standing for the byte at that
/// index.
struct ArrayRead {
    array: String,
    var_name: String,
    index: BvTerm,
    value: BvTerm,
}

/// The extended query being flattened alongside the lowering (TR-072):
/// one node per extended subterm, in the walk's post-order.
#[derive(Default)]
struct ExtFlat {
    nodes: Vec<ExtNode>,
    bits: Vec<bool>,
    consts: BTreeMap<(u128, u32), usize>,
    side: Vec<usize>,
    roots: Vec<usize>,
    vars: Vec<(String, u32, usize)>,
    var_index: BTreeMap<String, usize>,
    arrays: Vec<String>,
    array_index: BTreeMap<String, usize>,
    funcs: Vec<(String, u32)>,
    func_index: BTreeMap<String, usize>,
    /// Per node: the lowered term of a `select` or a call.
    lowered: Vec<Option<BvTerm>>,
}

impl ExtFlat {
    fn push(&mut self, node: ExtNode, image: Option<BvTerm>) -> usize {
        let i = self.nodes.len();
        self.nodes.push(node);
        self.lowered.push(image);
        i
    }

    fn var(&mut self, name: &str, width: u32) -> usize {
        if let Some(&i) = self.var_index.get(name) {
            return i;
        }
        let i = self.push(ExtNode::Core(DagNode::Var(width as usize)), None);
        self.var_index.insert(name.to_string(), i);
        self.vars.push((name.to_string(), width, i));
        i
    }

    fn konst(&mut self, value: u128, width: u32) -> usize {
        if let Some(&i) = self.consts.get(&(value, width)) {
            return i;
        }
        let s = self.bits.len();
        for j in 0..width {
            self.bits.push((value >> j) & 1 == 1);
        }
        let i = self.push(ExtNode::Core(DagNode::Const(s, width as usize)), None);
        self.consts.insert((value, width), i);
        i
    }

    fn array_id(&mut self, name: &str) -> usize {
        if let Some(&i) = self.array_index.get(name) {
            return i;
        }
        let i = self.arrays.len();
        self.arrays.push(name.to_string());
        self.array_index.insert(name.to_string(), i);
        i
    }

    fn func_id(&mut self, name: &str, width: u32) -> usize {
        if let Some(&i) = self.func_index.get(name) {
            return i;
        }
        let i = self.funcs.len();
        self.funcs.push((name.to_string(), width));
        self.func_index.insert(name.to_string(), i);
        i
    }

    /// A closed bitvector subterm (an [`ExtBvTerm::Core`] leaf), node for
    /// node — exactly as `dag::flatten` spells it.
    fn core_bv(&mut self, t: &BvTerm) -> usize {
        use BvTerm as B;
        let bin = |this: &mut Self, a: &BvTerm, b: &BvTerm, mk: fn(usize, usize) -> DagNode| {
            let (x, y) = (this.core_bv(a), this.core_bv(b));
            this.push(ExtNode::Core(mk(x, y)), None)
        };
        match t {
            B::Const { value, sort } => self.konst(*value, sort.width),
            B::Var { name, sort } => self.var(name, sort.width),
            B::Add(a, b) => bin(self, a, b, DagNode::Add),
            B::Sub(a, b) => bin(self, a, b, DagNode::Sub),
            B::Mul(a, b) => bin(self, a, b, DagNode::Mul),
            B::Udiv(a, b) => bin(self, a, b, DagNode::Udiv),
            B::Urem(a, b) => bin(self, a, b, DagNode::Urem),
            B::And(a, b) => bin(self, a, b, DagNode::And),
            B::Or(a, b) => bin(self, a, b, DagNode::Or),
            B::Xor(a, b) => bin(self, a, b, DagNode::Xor),
            B::Shl(a, b) => bin(self, a, b, DagNode::Shl),
            B::Lshr(a, b) => bin(self, a, b, DagNode::Lshr),
            B::Ashr(a, b) => bin(self, a, b, DagNode::Ashr),
            B::Rotr(a, b) => bin(self, a, b, DagNode::Rotr),
            B::Rotl(a, b) => bin(self, a, b, DagNode::Rotl),
            B::Sdiv(a, b) => bin(self, a, b, DagNode::Sdiv),
            B::Srem(a, b) => bin(self, a, b, DagNode::Srem),
            B::Concat(a, b) => bin(self, a, b, DagNode::Concat),
            B::Not(a) => {
                let x = self.core_bv(a);
                self.push(ExtNode::Core(DagNode::BvNot(x)), None)
            }
            B::Neg(a) => {
                let x = self.core_bv(a);
                self.push(ExtNode::Core(DagNode::Neg(x)), None)
            }
            B::Extract { hi, lo, arg } => {
                let x = self.core_bv(arg);
                self.push(
                    ExtNode::Core(DagNode::Extract(*hi as usize, *lo as usize, x)),
                    None,
                )
            }
            B::ZeroExt { by, arg } => {
                let x = self.core_bv(arg);
                self.push(ExtNode::Core(DagNode::ZeroExt(x, *by as usize)), None)
            }
            B::SignExt { by, arg } => {
                let x = self.core_bv(arg);
                self.push(ExtNode::Core(DagNode::SignExt(x, *by as usize)), None)
            }
            B::Ite { cond, then_, else_ } => {
                let c = self.core_bool(cond);
                let (x, y) = (self.core_bv(then_), self.core_bv(else_));
                self.push(ExtNode::Core(DagNode::Ite(c, x, y)), None)
            }
        }
    }

    /// A closed boolean subterm, node for node.
    fn core_bool(&mut self, t: &BoolTerm) -> usize {
        use BoolTerm as T;
        let cmp = |this: &mut Self, a: &BvTerm, b: &BvTerm, mk: fn(usize, usize) -> DagNode| {
            let (x, y) = (this.core_bv(a), this.core_bv(b));
            this.push(ExtNode::Core(mk(x, y)), None)
        };
        match t {
            T::Eq(a, b) => cmp(self, a, b, DagNode::Eq),
            T::Ne(a, b) => cmp(self, a, b, DagNode::Ne),
            T::Ult(a, b) => cmp(self, a, b, DagNode::Ult),
            T::Ule(a, b) => cmp(self, a, b, DagNode::Ule),
            T::Ugt(a, b) => cmp(self, a, b, DagNode::Ugt),
            T::Uge(a, b) => cmp(self, a, b, DagNode::Uge),
            T::Slt(a, b) => cmp(self, a, b, DagNode::Slt),
            T::Sle(a, b) => cmp(self, a, b, DagNode::Sle),
            T::Sgt(a, b) => cmp(self, a, b, DagNode::Sgt),
            T::Sge(a, b) => cmp(self, a, b, DagNode::Sge),
            T::Not(x) => {
                let a = self.core_bool(x);
                self.push(ExtNode::Core(DagNode::Not(a)), None)
            }
            T::And(a, b) => {
                let (x, y) = (self.core_bool(a), self.core_bool(b));
                self.push(ExtNode::Core(DagNode::BoolAnd(x, y)), None)
            }
            T::Or(a, b) => {
                let (x, y) = (self.core_bool(a), self.core_bool(b));
                self.push(ExtNode::Core(DagNode::BoolOr(x, y)), None)
            }
        }
    }
}

/// The per-`lower` elimination state: fresh-variable memo tables plus the
/// per-function call registry that congruence is generated from.
#[derive(Default)]
struct Lowering {
    /// Counter for unique fresh call-result variable names.
    next_id: usize,
    /// Every name a fresh variable must not take (#247): the core
    /// variables of the query, then each fresh name as it is issued. A
    /// fresh name that collided with a query variable would silently
    /// identify the read or call with it — a certified wrong `Unsat`.
    taken: BTreeSet<String>,
    /// Memo: `(base_array, structural key of the lowered index)` → its fresh
    /// BV8 read variable. Keyed by the index *term*, not a `u32`, so a
    /// symbolic index memoizes exactly like a concrete one: the same index
    /// term always yields the same read variable.
    read_memo: BTreeMap<(String, String), BvTerm>,
    /// Read provenance in creation order (for [`Lowered::reads`]).
    /// Concrete reads only — a symbolic index has no `u32` to report.
    read_trace: Vec<(String, String, u32)>,
    /// The access set — every base-array read `(array, lowered index, its
    /// read variable)` — in creation order. This is what array congruence
    /// is generated from (TR-028): a base-array read is a unary
    /// uninterpreted function of its index, so two reads of one array must
    /// agree wherever their indices do. Creation order is the table order
    /// the trusted check enumerates the congruence roots in (TR-072).
    reads: Vec<ArrayRead>,
    /// Memo: `(fn_name, structural key of lowered args)` → result variable.
    /// Structural equality of the arguments is captured via their `Debug`
    /// form, so an identical call site reuses the same variable.
    call_memo: BTreeMap<(String, String), BvTerm>,
    /// Distinct call sites, in creation order, for pairwise congruence
    /// (again the trusted check's table order).
    sites: Vec<CallSite>,
    /// The extended query, flattened alongside (TR-072).
    ext: ExtFlat,
    /// Signature `(arg widths, result width)` first seen for each name;
    /// a later site that disagrees is an inconsistent call.
    call_sigs: BTreeMap<String, (Vec<u32>, u32)>,
    /// Call provenance in creation order (for [`Lowered::calls`]).
    call_trace: Vec<(String, String, Vec<BvTerm>, Sort)>,
}

impl Lowering {
    /// A fresh variable name based on `base`, distinct from every query
    /// variable and every name issued so far (#247): `'` is appended until
    /// the name is unused. Deterministic — the same query always gets the
    /// same names, and a query that uses no `$`-prefixed names keeps the
    /// names it always had.
    fn fresh(&mut self, base: String) -> String {
        let mut name = base;
        while self.taken.contains(&name) {
            name.push('\'');
        }
        self.taken.insert(name.clone());
        name
    }

    /// Lower an extended boolean term to a pure-core [`BoolTerm`] and
    /// flatten it: the lowered term and its extended node (TR-072 — one
    /// walk does both, so the ids and the lowering never disagree).
    fn lower_bool(&mut self, t: &ExtBoolTerm) -> Result<(BoolTerm, usize), SliverError> {
        type Pair = (Box<BvTerm>, Box<BvTerm>);
        let cmp = |this: &mut Self,
                   a: &ExtBvTerm,
                   b: &ExtBvTerm,
                   mk: fn(usize, usize) -> DagNode|
         -> Result<(Pair, usize), SliverError> {
            let (la, ia) = this.lower_bv(a)?;
            let (lb, ib) = this.lower_bv(b)?;
            let id = this.ext.push(ExtNode::Core(mk(ia, ib)), None);
            Ok(((Box::new(la), Box::new(lb)), id))
        };
        Ok(match t {
            ExtBoolTerm::Eq(a, b) => {
                let ((a, b), id) = cmp(self, a, b, DagNode::Eq)?;
                (BoolTerm::Eq(a, b), id)
            }
            ExtBoolTerm::Ne(a, b) => {
                let ((a, b), id) = cmp(self, a, b, DagNode::Ne)?;
                (BoolTerm::Ne(a, b), id)
            }
            ExtBoolTerm::Ult(a, b) => {
                let ((a, b), id) = cmp(self, a, b, DagNode::Ult)?;
                (BoolTerm::Ult(a, b), id)
            }
            ExtBoolTerm::Ule(a, b) => {
                let ((a, b), id) = cmp(self, a, b, DagNode::Ule)?;
                (BoolTerm::Ule(a, b), id)
            }
            ExtBoolTerm::Ugt(a, b) => {
                let ((a, b), id) = cmp(self, a, b, DagNode::Ugt)?;
                (BoolTerm::Ugt(a, b), id)
            }
            ExtBoolTerm::Uge(a, b) => {
                let ((a, b), id) = cmp(self, a, b, DagNode::Uge)?;
                (BoolTerm::Uge(a, b), id)
            }
            ExtBoolTerm::Slt(a, b) => {
                let ((a, b), id) = cmp(self, a, b, DagNode::Slt)?;
                (BoolTerm::Slt(a, b), id)
            }
            ExtBoolTerm::Sle(a, b) => {
                let ((a, b), id) = cmp(self, a, b, DagNode::Sle)?;
                (BoolTerm::Sle(a, b), id)
            }
            ExtBoolTerm::Sgt(a, b) => {
                let ((a, b), id) = cmp(self, a, b, DagNode::Sgt)?;
                (BoolTerm::Sgt(a, b), id)
            }
            ExtBoolTerm::Sge(a, b) => {
                let ((a, b), id) = cmp(self, a, b, DagNode::Sge)?;
                (BoolTerm::Sge(a, b), id)
            }
            ExtBoolTerm::Not(x) => {
                let (lx, ix) = self.lower_bool(x)?;
                let id = self.ext.push(ExtNode::Core(DagNode::Not(ix)), None);
                (BoolTerm::Not(Box::new(lx)), id)
            }
            ExtBoolTerm::And(a, b) => {
                let (la, ia) = self.lower_bool(a)?;
                let (lb, ib) = self.lower_bool(b)?;
                let id = self.ext.push(ExtNode::Core(DagNode::BoolAnd(ia, ib)), None);
                (BoolTerm::And(Box::new(la), Box::new(lb)), id)
            }
            ExtBoolTerm::Or(a, b) => {
                let (la, ia) = self.lower_bool(a)?;
                let (lb, ib) = self.lower_bool(b)?;
                let id = self.ext.push(ExtNode::Core(DagNode::BoolOr(ia, ib)), None);
                (BoolTerm::Or(Box::new(la), Box::new(lb)), id)
            }
        })
    }

    /// Lower an extended bitvector term to a pure-core [`BvTerm`],
    /// eliminating any `select`/`pure_call` beneath it, and flatten it:
    /// the lowered term and its extended node.
    fn lower_bv(&mut self, t: &ExtBvTerm) -> Result<(BvTerm, usize), SliverError> {
        Ok(match t {
            ExtBvTerm::Core(bv) => {
                let id = self.ext.core_bv(bv);
                (masked_bv(bv), id)
            }
            ExtBvTerm::Op(op) => self.lower_op(op)?,
            ExtBvTerm::Select { array, index } => {
                let (j, ij) = self.lower_index(index)?;
                let mut levels: Vec<(usize, usize)> = Vec::new();
                let (lowered, aid) = self.resolve_select(array, &j, &mut levels, true)?;
                // `needed` was true at the top, so the term is there.
                let lowered = lowered.unwrap_or_else(|| BvTerm::Const {
                    value: 0,
                    sort: Sort::new(8),
                });
                let s = self.ext.side.len();
                for (x, v) in &levels {
                    self.ext.side.push(*x);
                    self.ext.side.push(*v);
                }
                let id = self.ext.push(
                    ExtNode::Select(aid, ij, s, levels.len()),
                    Some(lowered.clone()),
                );
                (lowered, id)
            }
            ExtBvTerm::PureCall { name, args, sort } => {
                let mut largs = Vec::with_capacity(args.len());
                let mut ids = Vec::with_capacity(args.len());
                for a in args {
                    let (l, i) = self.lower_bv(a)?;
                    largs.push(l);
                    ids.push(i);
                }
                let result = self.ackermann(name, largs, *sort)?;
                let fid = self.ext.func_id(name, sort.width);
                let s = self.ext.side.len();
                self.ext.side.extend(ids.iter().copied());
                let id = self.ext.push(
                    ExtNode::Call(fid, sort.width as usize, s, ids.len()),
                    Some(result.clone()),
                );
                (result, id)
            }
        })
    }

    /// Lower a lifted core operation, recursing into extended children.
    fn lower_op(&mut self, op: &ExtOp) -> Result<(BvTerm, usize), SliverError> {
        type Pair = (Box<BvTerm>, Box<BvTerm>);
        let bin = |this: &mut Self,
                   a: &ExtBvTerm,
                   b: &ExtBvTerm,
                   mk: fn(usize, usize) -> DagNode|
         -> Result<(Pair, usize), SliverError> {
            let (la, ia) = this.lower_bv(a)?;
            let (lb, ib) = this.lower_bv(b)?;
            let id = this.ext.push(ExtNode::Core(mk(ia, ib)), None);
            Ok(((Box::new(la), Box::new(lb)), id))
        };
        Ok(match op {
            ExtOp::Add(a, b) => {
                let ((a, b), id) = bin(self, a, b, DagNode::Add)?;
                (BvTerm::Add(a, b), id)
            }
            ExtOp::Sub(a, b) => {
                let ((a, b), id) = bin(self, a, b, DagNode::Sub)?;
                (BvTerm::Sub(a, b), id)
            }
            ExtOp::Mul(a, b) => {
                let ((a, b), id) = bin(self, a, b, DagNode::Mul)?;
                (BvTerm::Mul(a, b), id)
            }
            ExtOp::Udiv(a, b) => {
                let ((a, b), id) = bin(self, a, b, DagNode::Udiv)?;
                (BvTerm::Udiv(a, b), id)
            }
            ExtOp::And(a, b) => {
                let ((a, b), id) = bin(self, a, b, DagNode::And)?;
                (BvTerm::And(a, b), id)
            }
            ExtOp::Or(a, b) => {
                let ((a, b), id) = bin(self, a, b, DagNode::Or)?;
                (BvTerm::Or(a, b), id)
            }
            ExtOp::Xor(a, b) => {
                let ((a, b), id) = bin(self, a, b, DagNode::Xor)?;
                (BvTerm::Xor(a, b), id)
            }
            ExtOp::Shl(a, b) => {
                let ((a, b), id) = bin(self, a, b, DagNode::Shl)?;
                (BvTerm::Shl(a, b), id)
            }
            ExtOp::Lshr(a, b) => {
                let ((a, b), id) = bin(self, a, b, DagNode::Lshr)?;
                (BvTerm::Lshr(a, b), id)
            }
            ExtOp::Ashr(a, b) => {
                let ((a, b), id) = bin(self, a, b, DagNode::Ashr)?;
                (BvTerm::Ashr(a, b), id)
            }
            ExtOp::Rotr(a, b) => {
                let ((a, b), id) = bin(self, a, b, DagNode::Rotr)?;
                (BvTerm::Rotr(a, b), id)
            }
            ExtOp::Urem(a, b) => {
                let ((a, b), id) = bin(self, a, b, DagNode::Urem)?;
                (BvTerm::Urem(a, b), id)
            }
            ExtOp::Sdiv(a, b) => {
                let ((a, b), id) = bin(self, a, b, DagNode::Sdiv)?;
                (BvTerm::Sdiv(a, b), id)
            }
            ExtOp::Srem(a, b) => {
                let ((a, b), id) = bin(self, a, b, DagNode::Srem)?;
                (BvTerm::Srem(a, b), id)
            }
            ExtOp::Rotl(a, b) => {
                let ((a, b), id) = bin(self, a, b, DagNode::Rotl)?;
                (BvTerm::Rotl(a, b), id)
            }
            ExtOp::Not(x) => {
                let (l, i) = self.lower_bv(x)?;
                let id = self.ext.push(ExtNode::Core(DagNode::BvNot(i)), None);
                (BvTerm::Not(Box::new(l)), id)
            }
            ExtOp::Neg(x) => {
                let (l, i) = self.lower_bv(x)?;
                let id = self.ext.push(ExtNode::Core(DagNode::Neg(i)), None);
                (BvTerm::Neg(Box::new(l)), id)
            }
            ExtOp::Ite { cond, then_, else_ } => {
                let (c, ic) = self.lower_bool(cond)?;
                let (x, ix) = self.lower_bv(then_)?;
                let (y, iy) = self.lower_bv(else_)?;
                let id = self.ext.push(ExtNode::Core(DagNode::Ite(ic, ix, iy)), None);
                (
                    BvTerm::Ite {
                        cond: Box::new(c),
                        then_: Box::new(x),
                        else_: Box::new(y),
                    },
                    id,
                )
            }
            ExtOp::Extract { hi, lo, arg } => {
                let (l, i) = self.lower_bv(arg)?;
                let id = self.ext.push(
                    ExtNode::Core(DagNode::Extract(*hi as usize, *lo as usize, i)),
                    None,
                );
                (
                    BvTerm::Extract {
                        hi: *hi,
                        lo: *lo,
                        arg: Box::new(l),
                    },
                    id,
                )
            }
            ExtOp::Concat(a, b) => {
                let ((a, b), id) = bin(self, a, b, DagNode::Concat)?;
                (BvTerm::Concat(a, b), id)
            }
            ExtOp::ZeroExt { by, arg } => {
                let (l, i) = self.lower_bv(arg)?;
                let id = self
                    .ext
                    .push(ExtNode::Core(DagNode::ZeroExt(i, *by as usize)), None);
                (
                    BvTerm::ZeroExt {
                        by: *by,
                        arg: Box::new(l),
                    },
                    id,
                )
            }
            ExtOp::SignExt { by, arg } => {
                let (l, i) = self.lower_bv(arg)?;
                let id = self
                    .ext
                    .push(ExtNode::Core(DagNode::SignExt(i, *by as usize)), None);
                (
                    BvTerm::SignExt {
                        by: *by,
                        arg: Box::new(l),
                    },
                    id,
                )
            }
        })
    }

    /// Eager read-over-write (DES-015, extended by TR-028): resolve a
    /// `select` at BV32 index `j` — **concrete or symbolic** — down the store
    /// chain to a single BV8 core term.
    ///
    /// `select(store(a, i, v), j)` is `ite(i = j, v, select(a, j))`. When both
    /// `i` and `j` are constants the equality is settled *statically* and no
    /// `ite` is built — that is the concrete fast path, preserved verbatim
    /// from the original concrete-only lowering, so nothing regresses for
    /// queries that never use a symbolic index. Otherwise the equality is a
    /// real `Eq` over BV32 and the branch becomes an `Ite`, which is already
    /// in the closed fragment with a proven per-bit mux rule — so this adds
    /// **no new solver theory and no new trusted operation**.
    ///
    /// The full chain is always walked, so every node is sort-checked even
    /// when its value is not selected. `levels` collects each store's
    /// extended `(index, value)` nodes, outermost first (the `select`'s
    /// chain in the flattening); the array's id comes back with the term.
    /// `needed` says whether the read below this level can still be
    /// selected: past a concrete hit it cannot, and then the base array is
    /// walked but NOT read — a read variable nothing selects would be a
    /// dead table entry the trusted check refuses (TR-072), and it is
    /// otherwise unconstrained, so leaving it out changes no verdict. The
    /// term is `None` exactly when `needed` is false.
    fn resolve_select(
        &mut self,
        array: &ArrayTerm,
        j: &BvTerm,
        levels: &mut Vec<(usize, usize)>,
        needed: bool,
    ) -> Result<(Option<BvTerm>, usize), SliverError> {
        match array {
            ArrayTerm::Var { name } => {
                let aid = self.ext.array_id(name);
                let read = if needed {
                    Some(self.read_at(name, j))
                } else {
                    None
                };
                Ok((read, aid))
            }
            ArrayTerm::Store {
                array,
                index,
                value,
            } => {
                let (i, ii) = self.lower_index(index)?;
                let (v, iv) = self.lower_bv(value)?;
                if eval::bv_sort(&v)
                    .map_err(|_| SliverError::BadArraySort)?
                    .width
                    != 8
                {
                    return Err(SliverError::BadArraySort);
                }
                levels.push((ii, iv));
                let hit = matches!((as_const(&i), as_const(j)), (Some(a), Some(b)) if a == b);
                let (rest, aid) = self.resolve_select(array, j, levels, needed && !hit)?;
                let lowered = match (as_const(&i), as_const(j)) {
                    // Both concrete: the most recent write to `j` wins,
                    // decided here rather than handed to the SAT core.
                    (Some(a), Some(b)) => {
                        if a == b {
                            Some(v)
                        } else {
                            rest
                        }
                    }
                    // Otherwise the aliasing is a real query.
                    _ => rest.map(|rest| BvTerm::Ite {
                        cond: Box::new(BoolTerm::Eq(Box::new(i), Box::new(j.clone()))),
                        then_: Box::new(v),
                        else_: Box::new(rest),
                    }),
                };
                Ok((lowered, aid))
            }
        }
    }

    /// The fresh BV8 variable for reading `array[index]`, memoized on the
    /// index *term* so the same index — concrete or symbolic — always yields
    /// the same variable. Every read is registered in the array's access set
    /// so [`Lowering::array_congruence`] can relate it to the others.
    fn read_at(&mut self, array: &str, index: &BvTerm) -> BvTerm {
        let key = (array.to_string(), term_key(index));
        if let Some(v) = self.read_memo.get(&key) {
            return v.clone();
        }
        // Concrete reads keep their original `$sel:<array>:<index>` name and
        // their `Lowered::reads` provenance; a symbolic index has no `u32` to
        // report, so it gets a counter-named variable instead.
        let name = match as_const(index) {
            Some(c) => self.fresh(format!("$sel:{array}:{c}")),
            None => {
                let n = self.fresh(format!("$sel:{array}:#{}", self.next_id));
                self.next_id += 1;
                n
            }
        };
        let v = BvTerm::Var {
            name: name.clone(),
            sort: Sort::new(8),
        };
        self.read_memo.insert(key, v.clone());
        if let Some(c) = as_const(index) {
            // The index is BV32 (checked in `lower_index`), so it fits.
            self.read_trace
                .push((name.clone(), array.to_string(), c as u32));
        }
        self.reads.push(ArrayRead {
            array: array.to_string(),
            var_name: name,
            index: index.clone(),
            value: v.clone(),
        });
        v
    }

    /// Lower an array index and require it to be BV32. The value may be
    /// symbolic: a non-constant index is no longer an error (TR-028).
    /// A non-BV32 index is [`SliverError::BadArraySort`].
    fn lower_index(&mut self, index: &ExtBvTerm) -> Result<(BvTerm, usize), SliverError> {
        let (lowered, id) = self.lower_bv(index)?;
        let w = eval::bv_sort(&lowered)
            .map_err(|_| SliverError::BadArraySort)?
            .width;
        if w != 32 {
            return Err(SliverError::BadArraySort);
        }
        Ok((lowered, id))
    }

    /// Ackermannization (DES-016): replace this call site with a fresh
    /// result variable (memoized per identical site) and register it so
    /// congruence can be emitted. Arity/sorts must be consistent across all
    /// sites of `name`, else [`SliverError::InconsistentCall`].
    fn ackermann(
        &mut self,
        name: &str,
        args: Vec<BvTerm>,
        sort: Sort,
    ) -> Result<BvTerm, SliverError> {
        let widths = args
            .iter()
            .map(|a| eval::bv_sort(a).map(|s| s.width))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|_| SliverError::InconsistentCall {
                name: name.to_string(),
            })?;
        let sig = (widths, sort.width);
        match self.call_sigs.get(name) {
            Some(prev) if *prev != sig => {
                return Err(SliverError::InconsistentCall {
                    name: name.to_string(),
                });
            }
            None => {
                self.call_sigs.insert(name.to_string(), sig);
            }
            _ => {}
        }

        let key = (
            name.to_string(),
            args.iter().map(term_key).collect::<Vec<_>>().join(","),
        );
        if let Some(v) = self.call_memo.get(&key) {
            return Ok(v.clone());
        }
        let var_name = self.fresh(format!("$uf:{name}:{}", self.next_id));
        self.next_id += 1;
        let result = BvTerm::Var {
            name: var_name.clone(),
            sort,
        };
        self.call_memo.insert(key, result.clone());
        self.sites.push(CallSite {
            name: name.to_string(),
            args: args.clone(),
            result: result.clone(),
        });
        self.call_trace
            .push((var_name, name.to_string(), args, sort));
        Ok(result)
    }

    /// Emit array congruence (TR-028): for every pair of distinct reads of
    /// one base array, `index_i = index_j → value_i = value_j`.
    ///
    /// A base-array read is a unary uninterpreted function of its index, so
    /// this is Ackermann over the access set — the same shape as
    /// [`Lowering::congruence`], specialised to the one-argument case.
    ///
    /// **This is the soundness core of symbolic indexing.** Without it, a
    /// symbolic read `mem[j]` and a concrete read `mem[5]` would be unrelated
    /// variables, and the solver could satisfy `j = 5 ∧ mem[j] ≠ mem[5]` — a
    /// spurious model. Identical index terms already share a variable via the
    /// read memo, so no pair here is trivially reflexive.
    ///
    /// Two *distinct constant* indices are statically unequal, so their
    /// implication is vacuous and is skipped rather than handed to the SAT
    /// core — which is why a fully concrete query pays nothing for this.
    ///
    /// The pairs come in the access set's creation order (`p < q`, one
    /// array), which is the order the trusted check enumerates them in
    /// (TR-072, `kernel::sliver_kernel::array_cong`): the check computes
    /// the expected roots, it is not told them.
    fn array_congruence(&self) -> Vec<BoolTerm> {
        let mut out = Vec::new();
        let reads = &self.reads;
        for i in 0..reads.len() {
            for j in (i + 1)..reads.len() {
                let (a, b) = (&reads[i], &reads[j]);
                if a.array != b.array {
                    continue;
                }
                if let (Some(x), Some(y)) = (as_const(&a.index), as_const(&b.index)) {
                    debug_assert_ne!(x, y, "identical indices must share a read variable");
                    continue; // distinct constants never alias
                }
                let ante = BoolTerm::Eq(Box::new(a.index.clone()), Box::new(b.index.clone()));
                let concl = BoolTerm::Eq(Box::new(a.value.clone()), Box::new(b.value.clone()));
                out.push(BoolTerm::Or(
                    Box::new(BoolTerm::Not(Box::new(ante))),
                    Box::new(concl),
                ));
            }
        }
        out
    }

    /// Emit the Ackermann congruence constraints: for every pair of distinct
    /// call sites of one function, `args_i = args_j → result_i = result_j`.
    /// Identical sites already share a result variable (so no pair exists,
    /// and arity-0 collapses to a single variable), which is why an empty
    /// antecedent never arises here. Pairs in creation order (`p < q`, one
    /// function), the trusted check's table order (TR-072).
    fn congruence(&self) -> Vec<BoolTerm> {
        let mut out = Vec::new();
        let sites = &self.sites;
        for i in 0..sites.len() {
            for j in (i + 1)..sites.len() {
                let (a, b) = (&sites[i], &sites[j]);
                if a.name != b.name || a.args.len() != b.args.len() {
                    continue; // another function, or an arity mismatch (rejected earlier)
                }
                let mut ante: Option<BoolTerm> = None;
                for (x, y) in a.args.iter().zip(&b.args) {
                    let eq = BoolTerm::Eq(Box::new(x.clone()), Box::new(y.clone()));
                    ante = Some(match ante {
                        None => eq,
                        Some(p) => BoolTerm::And(Box::new(p), Box::new(eq)),
                    });
                }
                let concl = BoolTerm::Eq(Box::new(a.result.clone()), Box::new(b.result.clone()));
                out.push(match ante {
                    Some(p) => BoolTerm::Or(Box::new(BoolTerm::Not(Box::new(p))), Box::new(concl)),
                    None => concl,
                });
            }
        }
        out
    }
}

// ─── Concrete sliver evaluator ───────────────────────────────────────────────

/// A concrete model for the extended language: the non-Z3 test oracle.
///
/// A model is *total* — any base-array cell or call tuple not listed reads
/// as `0` — so [`eval_ext_bool`] always yields a definite truth value given
/// bindings for the free core variables.
#[derive(Clone, Debug, Default)]
pub struct SliverModel {
    /// Bindings for the free core bitvector variables.
    pub env: Env,
    /// Base-array contents: `array_name → (index → byte)`; default `0`.
    pub arrays: BTreeMap<String, BTreeMap<u32, u8>>,
    /// Uninterpreted-function graph: `(name, arg_values) → result`; default `0`.
    pub calls: BTreeMap<(String, Vec<u128>), u128>,
    /// The byte an unlisted base-array cell reads as (default `0`). Lets a
    /// caller probe interpretation-dependence by evaluating under two fills
    /// (see [`eval_const`]).
    pub base_fill: u8,
}

fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

/// Fold an [`ExtBvTerm`] into a *ground* core [`BvTerm`] under `model`,
/// replacing every `select` and `pure_call` by the constant it evaluates
/// to. The result reuses [`crate::eval`] for all operator semantics.
fn concretize_bv(t: &ExtBvTerm, model: &SliverModel) -> Result<BvTerm, EvalError> {
    Ok(match t {
        ExtBvTerm::Core(bv) => bv.clone(),
        ExtBvTerm::Op(op) => concretize_op(op, model)?,
        ExtBvTerm::Select { array, index } => {
            let idx = eval::eval_bv(&concretize_bv(index, model)?, &model.env)? as u32;
            let v = eval_array(array, idx, model)?;
            BvTerm::Const {
                value: v as u128,
                sort: Sort::new(8),
            }
        }
        ExtBvTerm::PureCall { name, args, sort } => {
            let argv = args
                .iter()
                .map(|a| eval::eval_bv(&concretize_bv(a, model)?, &model.env))
                .collect::<Result<Vec<_>, _>>()?;
            let v = model.calls.get(&(name.clone(), argv)).copied().unwrap_or(0);
            BvTerm::Const {
                value: v & mask(sort.width),
                sort: *sort,
            }
        }
    })
}

fn concretize_op(op: &ExtOp, model: &SliverModel) -> Result<BvTerm, EvalError> {
    let bin = |a: &ExtBvTerm, b: &ExtBvTerm| {
        Ok::<_, EvalError>((
            Box::new(concretize_bv(a, model)?),
            Box::new(concretize_bv(b, model)?),
        ))
    };
    Ok(match op {
        ExtOp::Add(a, b) => {
            let (a, b) = bin(a, b)?;
            BvTerm::Add(a, b)
        }
        ExtOp::Sub(a, b) => {
            let (a, b) = bin(a, b)?;
            BvTerm::Sub(a, b)
        }
        ExtOp::Mul(a, b) => {
            let (a, b) = bin(a, b)?;
            BvTerm::Mul(a, b)
        }
        ExtOp::Udiv(a, b) => {
            let (a, b) = bin(a, b)?;
            BvTerm::Udiv(a, b)
        }
        ExtOp::And(a, b) => {
            let (a, b) = bin(a, b)?;
            BvTerm::And(a, b)
        }
        ExtOp::Or(a, b) => {
            let (a, b) = bin(a, b)?;
            BvTerm::Or(a, b)
        }
        ExtOp::Xor(a, b) => {
            let (a, b) = bin(a, b)?;
            BvTerm::Xor(a, b)
        }
        ExtOp::Shl(a, b) => {
            let (a, b) = bin(a, b)?;
            BvTerm::Shl(a, b)
        }
        ExtOp::Lshr(a, b) => {
            let (a, b) = bin(a, b)?;
            BvTerm::Lshr(a, b)
        }
        ExtOp::Ashr(a, b) => {
            let (a, b) = bin(a, b)?;
            BvTerm::Ashr(a, b)
        }
        ExtOp::Rotr(a, b) => {
            let (a, b) = bin(a, b)?;
            BvTerm::Rotr(a, b)
        }
        ExtOp::Urem(a, b) => {
            let (a, b) = bin(a, b)?;
            BvTerm::Urem(a, b)
        }
        ExtOp::Sdiv(a, b) => {
            let (a, b) = bin(a, b)?;
            BvTerm::Sdiv(a, b)
        }
        ExtOp::Srem(a, b) => {
            let (a, b) = bin(a, b)?;
            BvTerm::Srem(a, b)
        }
        ExtOp::Rotl(a, b) => {
            let (a, b) = bin(a, b)?;
            BvTerm::Rotl(a, b)
        }
        ExtOp::Not(x) => BvTerm::Not(Box::new(concretize_bv(x, model)?)),
        ExtOp::Neg(x) => BvTerm::Neg(Box::new(concretize_bv(x, model)?)),
        ExtOp::Ite { cond, then_, else_ } => BvTerm::Ite {
            cond: Box::new(concretize_bool(cond, model)?),
            then_: Box::new(concretize_bv(then_, model)?),
            else_: Box::new(concretize_bv(else_, model)?),
        },
        ExtOp::Extract { hi, lo, arg } => BvTerm::Extract {
            hi: *hi,
            lo: *lo,
            arg: Box::new(concretize_bv(arg, model)?),
        },
        ExtOp::Concat(a, b) => {
            let (a, b) = bin(a, b)?;
            BvTerm::Concat(a, b)
        }
        ExtOp::ZeroExt { by, arg } => BvTerm::ZeroExt {
            by: *by,
            arg: Box::new(concretize_bv(arg, model)?),
        },
        ExtOp::SignExt { by, arg } => BvTerm::SignExt {
            by: *by,
            arg: Box::new(concretize_bv(arg, model)?),
        },
    })
}

/// Read `array[idx]` under `model`, walking the store chain (most recent
/// write wins) down to the base array's contents.
fn eval_array(array: &ArrayTerm, idx: u32, model: &SliverModel) -> Result<u8, EvalError> {
    match array {
        ArrayTerm::Var { name } => Ok(model
            .arrays
            .get(name)
            .and_then(|m| m.get(&idx))
            .copied()
            .unwrap_or(model.base_fill)),
        ArrayTerm::Store {
            array,
            index,
            value,
        } => {
            let i = eval::eval_bv(&concretize_bv(index, model)?, &model.env)? as u32;
            if i == idx {
                Ok(eval::eval_bv(&concretize_bv(value, model)?, &model.env)? as u8)
            } else {
                eval_array(array, idx, model)
            }
        }
    }
}

/// Fold an [`ExtBoolTerm`] into a ground core [`BoolTerm`] under `model`.
fn concretize_bool(t: &ExtBoolTerm, model: &SliverModel) -> Result<BoolTerm, EvalError> {
    let cmp = |a: &ExtBvTerm, b: &ExtBvTerm| {
        Ok::<_, EvalError>((
            Box::new(concretize_bv(a, model)?),
            Box::new(concretize_bv(b, model)?),
        ))
    };
    Ok(match t {
        ExtBoolTerm::Eq(a, b) => {
            let (a, b) = cmp(a, b)?;
            BoolTerm::Eq(a, b)
        }
        ExtBoolTerm::Ne(a, b) => {
            let (a, b) = cmp(a, b)?;
            BoolTerm::Ne(a, b)
        }
        ExtBoolTerm::Ult(a, b) => {
            let (a, b) = cmp(a, b)?;
            BoolTerm::Ult(a, b)
        }
        ExtBoolTerm::Ule(a, b) => {
            let (a, b) = cmp(a, b)?;
            BoolTerm::Ule(a, b)
        }
        ExtBoolTerm::Ugt(a, b) => {
            let (a, b) = cmp(a, b)?;
            BoolTerm::Ugt(a, b)
        }
        ExtBoolTerm::Uge(a, b) => {
            let (a, b) = cmp(a, b)?;
            BoolTerm::Uge(a, b)
        }
        ExtBoolTerm::Slt(a, b) => {
            let (a, b) = cmp(a, b)?;
            BoolTerm::Slt(a, b)
        }
        ExtBoolTerm::Sle(a, b) => {
            let (a, b) = cmp(a, b)?;
            BoolTerm::Sle(a, b)
        }
        ExtBoolTerm::Sgt(a, b) => {
            let (a, b) = cmp(a, b)?;
            BoolTerm::Sgt(a, b)
        }
        ExtBoolTerm::Sge(a, b) => {
            let (a, b) = cmp(a, b)?;
            BoolTerm::Sge(a, b)
        }
        ExtBoolTerm::Not(x) => BoolTerm::Not(Box::new(concretize_bool(x, model)?)),
        ExtBoolTerm::And(a, b) => BoolTerm::And(
            Box::new(concretize_bool(a, model)?),
            Box::new(concretize_bool(b, model)?),
        ),
        ExtBoolTerm::Or(a, b) => BoolTerm::Or(
            Box::new(concretize_bool(a, model)?),
            Box::new(concretize_bool(b, model)?),
        ),
    })
}

/// Evaluate an [`ExtBoolTerm`] directly under a concrete [`SliverModel`] —
/// the independent (non-Z3) oracle for the lowering.
pub fn eval_ext_bool(t: &ExtBoolTerm, model: &SliverModel) -> Result<bool, EvalError> {
    eval::eval_bool(&concretize_bool(t, model)?, &model.env)
}

/// Evaluate an [`ExtBvTerm`] directly under a concrete [`SliverModel`].
/// Evaluate a **ground** extended term to its constant value (TR-029, issue
/// #71): the term must contain no free core variables, no base-array reads
/// that reach evaluation, and no `pure_call`s — anything whose value depends
/// on an interpretation makes the term non-constant and yields `None`.
///
/// This is deliberately stricter than [`eval_ext_bv`] under a default
/// [`SliverModel`]: the model is *total* (unbound cells and call tuples read
/// as 0), so evaluating a non-ground term there would silently return a
/// value that is only correct for one arbitrary interpretation. A constant
/// helper must refuse instead.
pub fn eval_const(t: &ExtBvTerm) -> Option<u128> {
    fn ground_bv(t: &ExtBvTerm) -> bool {
        match t {
            ExtBvTerm::Core(bv) => ground_core(bv),
            ExtBvTerm::Op(op) => ground_op(op),
            // A select is syntactically ground when every index/value in its
            // chain is; whether the read actually resolves to a STORE (vs
            // consulting the base array, which has no fixed contents) is
            // decided semantically by the dual-fill check below.
            ExtBvTerm::Select { array, index } => ground_array(array) && ground_bv(index),
            ExtBvTerm::PureCall { .. } => false,
        }
    }
    fn ground_ext_bool(t: &ExtBoolTerm) -> bool {
        match t {
            ExtBoolTerm::Eq(a, b)
            | ExtBoolTerm::Ne(a, b)
            | ExtBoolTerm::Ult(a, b)
            | ExtBoolTerm::Ule(a, b)
            | ExtBoolTerm::Ugt(a, b)
            | ExtBoolTerm::Uge(a, b)
            | ExtBoolTerm::Slt(a, b)
            | ExtBoolTerm::Sle(a, b)
            | ExtBoolTerm::Sgt(a, b)
            | ExtBoolTerm::Sge(a, b) => ground_bv(a) && ground_bv(b),
            ExtBoolTerm::Not(x) => ground_ext_bool(x),
            ExtBoolTerm::And(a, b) | ExtBoolTerm::Or(a, b) => {
                ground_ext_bool(a) && ground_ext_bool(b)
            }
        }
    }
    fn ground_array(a: &ArrayTerm) -> bool {
        match a {
            ArrayTerm::Var { .. } => true, // reads may still miss; see dual-fill check
            ArrayTerm::Store {
                array,
                index,
                value,
            } => ground_array(array) && ground_bv(index) && ground_bv(value),
        }
    }
    fn ground_core(t: &BvTerm) -> bool {
        use crate::term::BvTerm as B;
        match t {
            B::Const { .. } => true,
            B::Var { .. } => false,
            B::Add(a, b)
            | B::Sub(a, b)
            | B::Mul(a, b)
            | B::Udiv(a, b)
            | B::Urem(a, b)
            | B::And(a, b)
            | B::Or(a, b)
            | B::Xor(a, b)
            | B::Shl(a, b)
            | B::Lshr(a, b)
            | B::Ashr(a, b)
            | B::Rotr(a, b)
            | B::Rotl(a, b)
            | B::Sdiv(a, b)
            | B::Srem(a, b)
            | B::Concat(a, b) => ground_core(a) && ground_core(b),
            B::Extract { arg, .. }
            | B::ZeroExt { arg, .. }
            | B::SignExt { arg, .. }
            | B::Not(arg)
            | B::Neg(arg) => ground_core(arg),
            B::Ite { cond, then_, else_ } => {
                ground_bool_core(cond) && ground_core(then_) && ground_core(else_)
            }
        }
    }
    fn ground_bool_core(t: &BoolTerm) -> bool {
        use crate::term::BoolTerm as T;
        match t {
            T::Eq(a, b)
            | T::Ne(a, b)
            | T::Ult(a, b)
            | T::Ule(a, b)
            | T::Ugt(a, b)
            | T::Uge(a, b)
            | T::Slt(a, b)
            | T::Sle(a, b)
            | T::Sgt(a, b)
            | T::Sge(a, b) => ground_core(a) && ground_core(b),
            T::Not(x) => ground_bool_core(x),
            T::And(a, b) | T::Or(a, b) => ground_bool_core(a) && ground_bool_core(b),
        }
    }
    fn ground_op(op: &ExtOp) -> bool {
        match op {
            ExtOp::Add(a, b)
            | ExtOp::Sub(a, b)
            | ExtOp::Mul(a, b)
            | ExtOp::Udiv(a, b)
            | ExtOp::And(a, b)
            | ExtOp::Or(a, b)
            | ExtOp::Xor(a, b)
            | ExtOp::Shl(a, b)
            | ExtOp::Lshr(a, b)
            | ExtOp::Ashr(a, b)
            | ExtOp::Rotr(a, b)
            | ExtOp::Urem(a, b)
            | ExtOp::Sdiv(a, b)
            | ExtOp::Srem(a, b)
            | ExtOp::Rotl(a, b)
            | ExtOp::Concat(a, b) => ground_bv(a) && ground_bv(b),
            ExtOp::Extract { arg, .. }
            | ExtOp::Not(arg)
            | ExtOp::Neg(arg)
            | ExtOp::ZeroExt { by: _, arg }
            | ExtOp::SignExt { by: _, arg } => ground_bv(arg),
            ExtOp::Ite { cond, then_, else_ } => {
                ground_ext_bool(cond) && ground_bv(then_) && ground_bv(else_)
            }
        }
    }

    if !ground_bv(t) {
        return None;
    }
    // Constancy is decided structurally (#248), not by sampling: a ground
    // term is constant iff no `select` in it falls through its store chain
    // to the base array (whose contents are free). Index and store-index
    // values are computable here because the term is ground and every read
    // they make is checked the same way first. Conservative: every branch of
    // an `ite` is checked, so a term may be refused although its taken
    // branch is constant — never the other way round.
    fn reaches_base(t: &ExtBvTerm) -> bool {
        match t {
            ExtBvTerm::Core(_) => false,
            ExtBvTerm::Op(op) => match op.as_ref() {
                ExtOp::Add(a, b)
                | ExtOp::Sub(a, b)
                | ExtOp::Mul(a, b)
                | ExtOp::Udiv(a, b)
                | ExtOp::Urem(a, b)
                | ExtOp::Sdiv(a, b)
                | ExtOp::Srem(a, b)
                | ExtOp::And(a, b)
                | ExtOp::Or(a, b)
                | ExtOp::Xor(a, b)
                | ExtOp::Shl(a, b)
                | ExtOp::Lshr(a, b)
                | ExtOp::Ashr(a, b)
                | ExtOp::Rotr(a, b)
                | ExtOp::Rotl(a, b)
                | ExtOp::Concat(a, b) => reaches_base(a) || reaches_base(b),
                ExtOp::Not(a)
                | ExtOp::Neg(a)
                | ExtOp::Extract { arg: a, .. }
                | ExtOp::ZeroExt { arg: a, .. }
                | ExtOp::SignExt { arg: a, .. } => reaches_base(a),
                ExtOp::Ite { cond, then_, else_ } => {
                    reaches_base_bool(cond) || reaches_base(then_) || reaches_base(else_)
                }
            },
            ExtBvTerm::Select { array, index } => {
                if reaches_base(index) {
                    return true;
                }
                match eval_ext_bv(index, &SliverModel::default()) {
                    Ok(idx) => chain_reaches_base(array, idx as u32),
                    Err(_) => true,
                }
            }
            ExtBvTerm::PureCall { .. } => true,
        }
    }
    fn reaches_base_bool(t: &ExtBoolTerm) -> bool {
        match t {
            ExtBoolTerm::Eq(a, b)
            | ExtBoolTerm::Ne(a, b)
            | ExtBoolTerm::Ult(a, b)
            | ExtBoolTerm::Ule(a, b)
            | ExtBoolTerm::Ugt(a, b)
            | ExtBoolTerm::Uge(a, b)
            | ExtBoolTerm::Slt(a, b)
            | ExtBoolTerm::Sle(a, b)
            | ExtBoolTerm::Sgt(a, b)
            | ExtBoolTerm::Sge(a, b) => reaches_base(a) || reaches_base(b),
            ExtBoolTerm::Not(x) => reaches_base_bool(x),
            ExtBoolTerm::And(a, b) | ExtBoolTerm::Or(a, b) => {
                reaches_base_bool(a) || reaches_base_bool(b)
            }
        }
    }
    /// Does reading `array[idx]` fall through every store to the base?
    fn chain_reaches_base(array: &ArrayTerm, idx: u32) -> bool {
        match array {
            ArrayTerm::Var { .. } => true,
            ArrayTerm::Store {
                array,
                index,
                value,
            } => {
                if reaches_base(index) {
                    return true;
                }
                match eval_ext_bv(index, &SliverModel::default()) {
                    Ok(i) if i as u32 == idx => reaches_base(value),
                    Ok(_) => chain_reaches_base(array, idx),
                    Err(_) => true,
                }
            }
        }
    }
    if reaches_base(t) {
        return None;
    }
    eval_ext_bv(t, &SliverModel::default()).ok()
}

pub fn eval_ext_bv(t: &ExtBvTerm, model: &SliverModel) -> Result<u128, EvalError> {
    eval::eval_bv(&concretize_bv(t, model)?, &model.env)
}

// ─── Shared test builders ────────────────────────────────────────────────────

/// Collect the core variable names of an extended boolean term (#247).
fn names_bool(t: &ExtBoolTerm, out: &mut BTreeSet<String>) {
    match t {
        ExtBoolTerm::Eq(a, b)
        | ExtBoolTerm::Ne(a, b)
        | ExtBoolTerm::Ult(a, b)
        | ExtBoolTerm::Ule(a, b)
        | ExtBoolTerm::Ugt(a, b)
        | ExtBoolTerm::Uge(a, b)
        | ExtBoolTerm::Slt(a, b)
        | ExtBoolTerm::Sle(a, b)
        | ExtBoolTerm::Sgt(a, b)
        | ExtBoolTerm::Sge(a, b) => {
            names_bv(a, out);
            names_bv(b, out);
        }
        ExtBoolTerm::Not(x) => names_bool(x, out),
        ExtBoolTerm::And(a, b) | ExtBoolTerm::Or(a, b) => {
            names_bool(a, out);
            names_bool(b, out);
        }
    }
}

fn names_bv(t: &ExtBvTerm, out: &mut BTreeSet<String>) {
    match t {
        ExtBvTerm::Core(bv) => names_core_bv(bv, out),
        ExtBvTerm::Op(op) => match op.as_ref() {
            ExtOp::Add(a, b)
            | ExtOp::Sub(a, b)
            | ExtOp::Mul(a, b)
            | ExtOp::Udiv(a, b)
            | ExtOp::Urem(a, b)
            | ExtOp::Sdiv(a, b)
            | ExtOp::Srem(a, b)
            | ExtOp::And(a, b)
            | ExtOp::Or(a, b)
            | ExtOp::Xor(a, b)
            | ExtOp::Shl(a, b)
            | ExtOp::Lshr(a, b)
            | ExtOp::Ashr(a, b)
            | ExtOp::Rotr(a, b)
            | ExtOp::Rotl(a, b)
            | ExtOp::Concat(a, b) => {
                names_bv(a, out);
                names_bv(b, out);
            }
            ExtOp::Not(a)
            | ExtOp::Neg(a)
            | ExtOp::Extract { arg: a, .. }
            | ExtOp::ZeroExt { arg: a, .. }
            | ExtOp::SignExt { arg: a, .. } => names_bv(a, out),
            ExtOp::Ite { cond, then_, else_ } => {
                names_bool(cond, out);
                names_bv(then_, out);
                names_bv(else_, out);
            }
        },
        ExtBvTerm::Select { array, index } => {
            names_array(array, out);
            names_bv(index, out);
        }
        ExtBvTerm::PureCall { args, .. } => args.iter().for_each(|a| names_bv(a, out)),
    }
}

fn names_array(a: &ArrayTerm, out: &mut BTreeSet<String>) {
    match a {
        ArrayTerm::Var { .. } => {}
        ArrayTerm::Store {
            array,
            index,
            value,
        } => {
            names_array(array, out);
            names_bv(index, out);
            names_bv(value, out);
        }
    }
}

fn names_core_bv(t: &BvTerm, out: &mut BTreeSet<String>) {
    use BvTerm as B;
    match t {
        B::Const { .. } => {}
        B::Var { name, .. } => {
            out.insert(name.clone());
        }
        B::Add(a, b)
        | B::Sub(a, b)
        | B::Mul(a, b)
        | B::Udiv(a, b)
        | B::Urem(a, b)
        | B::Sdiv(a, b)
        | B::Srem(a, b)
        | B::And(a, b)
        | B::Or(a, b)
        | B::Xor(a, b)
        | B::Shl(a, b)
        | B::Lshr(a, b)
        | B::Ashr(a, b)
        | B::Rotr(a, b)
        | B::Rotl(a, b)
        | B::Concat(a, b) => {
            names_core_bv(a, out);
            names_core_bv(b, out);
        }
        B::Not(a)
        | B::Neg(a)
        | B::Extract { arg: a, .. }
        | B::ZeroExt { arg: a, .. }
        | B::SignExt { arg: a, .. } => names_core_bv(a, out),
        B::Ite { cond, then_, else_ } => {
            names_core_bool(cond, out);
            names_core_bv(then_, out);
            names_core_bv(else_, out);
        }
    }
}

fn names_core_bool(t: &BoolTerm, out: &mut BTreeSet<String>) {
    use BoolTerm as T;
    match t {
        T::Eq(a, b)
        | T::Ne(a, b)
        | T::Ult(a, b)
        | T::Ule(a, b)
        | T::Ugt(a, b)
        | T::Uge(a, b)
        | T::Slt(a, b)
        | T::Sle(a, b)
        | T::Sgt(a, b)
        | T::Sge(a, b) => {
            names_core_bv(a, out);
            names_core_bv(b, out);
        }
        T::Not(x) => names_core_bool(x, out),
        T::And(a, b) | T::Or(a, b) => {
            names_core_bool(a, out);
            names_core_bool(b, out);
        }
    }
}

#[cfg(test)]
mod build {
    use super::*;

    /// An 8-bit constant as an extended term.
    pub fn c8(v: u128) -> ExtBvTerm {
        ExtBvTerm::Core(BvTerm::Const {
            value: v,
            sort: Sort::new(8),
        })
    }
    /// A 32-bit constant index as an extended term.
    pub fn i32c(v: u128) -> ExtBvTerm {
        ExtBvTerm::Core(BvTerm::Const {
            value: v,
            sort: Sort::new(32),
        })
    }
    /// An 8-bit core variable as an extended term.
    pub fn v8(name: &str) -> ExtBvTerm {
        ExtBvTerm::Core(BvTerm::Var {
            name: name.into(),
            sort: Sort::new(8),
        })
    }
    /// A 32-bit core variable as an extended term (a symbolic index).
    pub fn v32(name: &str) -> ExtBvTerm {
        ExtBvTerm::Core(BvTerm::Var {
            name: name.into(),
            sort: Sort::new(32),
        })
    }
    /// The base array variable `name`.
    pub fn arr(name: &str) -> ArrayTerm {
        ArrayTerm::Var { name: name.into() }
    }
    /// `store(a, index, value)`.
    pub fn store(a: ArrayTerm, index: ExtBvTerm, value: ExtBvTerm) -> ArrayTerm {
        ArrayTerm::Store {
            array: Box::new(a),
            index: Box::new(index),
            value: Box::new(value),
        }
    }
    /// `select(a, index)`.
    pub fn select(a: ArrayTerm, index: ExtBvTerm) -> ExtBvTerm {
        ExtBvTerm::Select {
            array: Box::new(a),
            index: Box::new(index),
        }
    }
    /// A `pure_call` returning BV8.
    pub fn call(name: &str, args: Vec<ExtBvTerm>) -> ExtBvTerm {
        ExtBvTerm::PureCall {
            name: name.into(),
            args,
            sort: Sort::new(8),
        }
    }
    /// Solve a lowered core conjunction with the real ordeal pipeline.
    pub fn solve(core: &[BoolTerm]) -> crate::solver::CheckResult {
        let mut s = crate::solver::Solver::new();
        for a in core {
            s.assert(a.clone());
        }
        s.check()
    }
}

// ─── Read-over-write elimination (DES-015 / UV-014) ──────────────────────────

#[cfg(test)]
mod array {
    use super::build::*;
    use super::*;
    use crate::solver::CheckResult;

    #[test]
    fn recent_write_at_matching_index_wins() {
        // select(store(store(a, 1, 10), 2, 20), 2) must be 20.
        let a = store(store(arr("a"), i32c(1), c8(10)), i32c(2), c8(20));
        let q = ExtBoolTerm::Eq(select(a, i32c(2)), c8(20));
        assert!(matches!(solve(&lower(&[q]).unwrap()), CheckResult::Sat(_)));
    }

    #[test]
    fn overwrite_then_reject_stale_value() {
        // store(a,3,42) then reading 3 as anything but 42 is UNSAT.
        let a = store(arr("a"), i32c(3), c8(42));
        let q = ExtBoolTerm::Ne(select(a, i32c(3)), c8(42));
        assert!(matches!(
            solve(&lower(&[q]).unwrap()),
            CheckResult::Unsat(_)
        ));
    }

    #[test]
    fn miss_falls_through_to_base_read() {
        // select(store(a, 1, 9), 2) reads the base array's cell 2, which is a
        // fresh unconstrained BV8 variable — so it can equal anything (SAT)
        // and can also differ from 9 (SAT), but is NOT forced to 9.
        let a = || store(arr("a"), i32c(1), c8(9));
        let must_be_9 = ExtBoolTerm::Eq(select(a(), i32c(2)), c8(9));
        assert!(matches!(
            solve(&lower(&[must_be_9]).unwrap()),
            CheckResult::Sat(_)
        ));
        let cannot_be_9 = ExtBoolTerm::Ne(select(a(), i32c(2)), c8(9));
        assert!(matches!(
            solve(&lower(&[cannot_be_9]).unwrap()),
            CheckResult::Sat(_)
        ));
    }

    #[test]
    fn same_index_read_is_memoized_to_one_variable() {
        // Two selects of a[5] must be the same variable, so a[5] != a[5] is
        // UNSAT and a[5] == a[5] is SAT.
        let ne = ExtBoolTerm::Ne(select(arr("a"), i32c(5)), select(arr("a"), i32c(5)));
        assert!(matches!(
            solve(&lower(&[ne]).unwrap()),
            CheckResult::Unsat(_)
        ));
        let lowered = lower_traced(&[ExtBoolTerm::Eq(
            select(arr("a"), i32c(5)),
            select(arr("a"), i32c(5)),
        )])
        .unwrap();
        assert_eq!(lowered.reads.len(), 1, "a[5] must map to one read variable");
    }

    // ── TR-028: symbolic-index select/store ──────────────────────────────
    //
    // These four replace the pair that asserted `NonConcreteIndex`, which
    // encoded the limitation this requirement removes (#70: loom's base
    // address is a symbolic BV32, so that limitation reverted every loom
    // function touching memory).

    // ── TR-029: eval_const (issue #71 ask c) ────────────────────────────

    /// A ground read that HITS a store is a constant.
    #[test]
    fn eval_const_ground_store_hit() {
        let a = store(arr("m"), i32c(4), c8(0x5A));
        let t = select(a, i32c(4));
        assert_eq!(eval_const(&t), Some(0x5A));
    }

    /// #248: a term whose value depends on a base cell is not constant even
    /// when two sample fills happen to agree. `(a[7] + 1) & 0xFE` is 0 under
    /// the fills 0x00 and 0xFF but 2 when `a[7] = 1`; the old two-fill probe
    /// reported `Some(0)`.
    // rivet: verifies VER-071
    #[test]
    fn eval_const_refuses_a_base_dependent_term_two_fills_agree_on() {
        let t = ExtBvTerm::Op(Box::new(ExtOp::And(
            ExtBvTerm::Op(Box::new(ExtOp::Add(select(arr("a"), i32c(7)), c8(1)))),
            c8(0xFE),
        )));
        assert_eq!(eval_const(&t), None);
        // The same shape over a read that hits a store IS constant.
        let hit = ExtBvTerm::Op(Box::new(ExtOp::And(
            ExtBvTerm::Op(Box::new(ExtOp::Add(
                select(store(arr("a"), i32c(7), c8(1)), i32c(7)),
                c8(1),
            ))),
            c8(0xFE),
        )));
        assert_eq!(eval_const(&hit), Some(2));
        // A read whose index is itself a store-hit read resolves too.
        let m = store(store(arr("a"), i32c(3), c8(9)), i32c(9), c8(0x77));
        let nested = select(
            m.clone(),
            ExtBvTerm::Op(Box::new(ExtOp::ZeroExt {
                by: 24,
                arg: select(m, i32c(3)),
            })),
        );
        assert_eq!(eval_const(&nested), Some(0x77));
    }

    /// A read that MISSES every store consults the base array — not constant.
    /// This is the case a naive total-model evaluation would silently get
    /// wrong (returning the arbitrary fill); the structural check refuses.
    #[test]
    fn eval_const_base_read_is_not_constant() {
        let a = store(arr("m"), i32c(4), c8(1));
        let t = select(a, i32c(7)); // misses the store at 4
        assert_eq!(eval_const(&t), None);
    }

    /// Free variables anywhere make the term non-constant.
    #[test]
    fn eval_const_free_var_is_not_constant() {
        let t = select(store(arr("m"), v32("i"), c8(1)), i32c(0));
        assert_eq!(eval_const(&t), None);
        assert_eq!(eval_const(&v32("x")), None);
    }

    /// Pure ground arithmetic evaluates.
    #[test]
    fn eval_const_ground_arith() {
        let t = ExtBvTerm::Op(Box::new(ExtOp::Add(i32c(40), i32c(2))));
        assert_eq!(eval_const(&t), Some(42));
    }

    #[test]
    fn symbolic_index_on_select_lowers() {
        let q = ExtBoolTerm::Eq(select(arr("a"), v32("i")), c8(0));
        assert!(
            lower(&[q]).is_ok(),
            "a symbolic select must lower, not error"
        );
    }

    #[test]
    fn symbolic_index_on_store_lowers() {
        let a = store(arr("a"), v32("i"), c8(1));
        let q = ExtBoolTerm::Eq(select(a, i32c(0)), c8(0));
        assert!(
            lower(&[q]).is_ok(),
            "a symbolic store must lower, not error"
        );
    }

    /// The concrete fast path is preserved: when every index is a constant
    /// the aliasing is settled statically, so no `Ite` and no congruence
    /// clause reaches the core. A fully concrete query pays nothing for
    /// symbolic support.
    #[test]
    fn concrete_indices_still_cost_nothing() {
        let a = store(store(arr("a"), i32c(4), c8(1)), i32c(7), c8(2));
        let core = lower(&[ExtBoolTerm::Eq(select(a, i32c(4)), c8(1))]).unwrap();
        let dump = format!("{core:?}");
        assert!(
            !dump.contains("Ite"),
            "concrete store-chain must settle statically, got: {dump}"
        );
        // Only the original assertion — no congruence clauses appended.
        assert_eq!(core.len(), 1, "no congruence for distinct constant indices");
    }

    /// A symbolic store index DOES build the mux — the aliasing is a real
    /// query, not something to guess.
    #[test]
    fn symbolic_index_builds_the_read_over_write_mux() {
        let a = store(arr("a"), v32("i"), c8(1));
        let core = lower(&[ExtBoolTerm::Eq(select(a, v32("j")), c8(0))]).unwrap();
        assert!(
            format!("{core:?}").contains("Ite"),
            "symbolic aliasing must lower to an Ite over Eq(i, j)"
        );
    }

    #[test]
    fn bad_index_width_is_rejected() {
        // An 8-bit index is not BV32.
        let q = ExtBoolTerm::Eq(select(arr("a"), c8(0)), c8(0));
        assert_eq!(lower(&[q]).err(), Some(SliverError::BadArraySort));
    }

    #[test]
    fn bad_value_width_is_rejected() {
        // Storing a 32-bit value into a BV8 array.
        let a = store(arr("a"), i32c(0), i32c(7));
        let q = ExtBoolTerm::Eq(select(a, i32c(0)), c8(7));
        assert_eq!(lower(&[q]).err(), Some(SliverError::BadArraySort));
    }

    #[test]
    fn output_is_pure_core_no_sliver_remains() {
        // A representative query lowers to assertions the core solver accepts
        // without ever seeing an array construct (it would panic otherwise).
        let a = store(arr("mem"), i32c(0), c8(1));
        let q = ExtBoolTerm::Ult(select(a, i32c(0)), c8(200));
        let core = lower(&[q]).unwrap();
        assert!(!core.is_empty());
        assert!(!matches!(solve(&core), CheckResult::Unknown));
    }
}

// ─── Ackermannization of uninterpreted calls (DES-016 / UV-015) ──────────────

#[cfg(test)]
mod uf {
    use super::build::*;
    use super::*;
    use crate::solver::CheckResult;

    #[test]
    fn congruence_forces_equal_results_on_equal_args() {
        // f(x) = 5, f(y) = 7, x = y  is UNSAT (congruence: f(x) = f(y)).
        let q = vec![
            ExtBoolTerm::Eq(call("f", vec![v8("x")]), c8(5)),
            ExtBoolTerm::Eq(call("f", vec![v8("y")]), c8(7)),
            ExtBoolTerm::Eq(v8("x"), v8("y")),
        ];
        assert!(matches!(solve(&lower(&q).unwrap()), CheckResult::Unsat(_)));
    }

    #[test]
    fn distinct_args_leave_results_free() {
        // f(x) = 5, f(y) = 7, x != y  is SAT (no congruence obligation).
        let q = vec![
            ExtBoolTerm::Eq(call("f", vec![v8("x")]), c8(5)),
            ExtBoolTerm::Eq(call("f", vec![v8("y")]), c8(7)),
            ExtBoolTerm::Ne(v8("x"), v8("y")),
        ];
        assert!(matches!(solve(&lower(&q).unwrap()), CheckResult::Sat(_)));
    }

    #[test]
    fn identical_call_sites_share_a_variable() {
        // f(x) appears twice; f(x) != f(x) is UNSAT and only one fresh
        // variable (hence no congruence clause) is created.
        let q = ExtBoolTerm::Ne(call("f", vec![v8("x")]), call("f", vec![v8("x")]));
        let lowered = lower_traced(&[q]).unwrap();
        assert_eq!(lowered.calls.len(), 1, "identical sites reuse one variable");
        assert_eq!(lowered.assertions.len(), 1, "no congruence clause expected");
        assert!(matches!(solve(&lowered.assertions), CheckResult::Unsat(_)));
    }

    #[test]
    fn two_distinct_sites_emit_one_congruence_clause() {
        let q = vec![
            ExtBoolTerm::Eq(call("f", vec![v8("x")]), c8(1)),
            ExtBoolTerm::Eq(call("f", vec![v8("y")]), c8(2)),
        ];
        let lowered = lower_traced(&q).unwrap();
        // Two originals + one congruence constraint.
        assert_eq!(lowered.assertions.len(), 3);
        assert_eq!(lowered.calls.len(), 2);
    }

    #[test]
    fn nested_calls_are_ackermannized() {
        // f(f(x)) = x, f(x) = x  is SAT (x a fixpoint); sanity that nesting
        // lowers and stays decidable.
        let q = vec![
            ExtBoolTerm::Eq(call("f", vec![call("f", vec![v8("x")])]), v8("x")),
            ExtBoolTerm::Eq(call("f", vec![v8("x")]), v8("x")),
        ];
        assert!(matches!(solve(&lower(&q).unwrap()), CheckResult::Sat(_)));
    }

    #[test]
    fn inconsistent_arity_is_rejected() {
        let q = vec![
            ExtBoolTerm::Eq(call("f", vec![v8("x")]), c8(1)),
            ExtBoolTerm::Eq(call("f", vec![v8("x"), v8("y")]), c8(2)),
        ];
        assert_eq!(
            lower(&q).err(),
            Some(SliverError::InconsistentCall { name: "f".into() })
        );
    }

    #[test]
    fn inconsistent_arg_width_is_rejected() {
        let wide = ExtBvTerm::Core(BvTerm::Var {
            name: "w".into(),
            sort: Sort::new(32),
        });
        let q = vec![
            ExtBoolTerm::Eq(call("f", vec![v8("x")]), c8(1)),
            // second site: same name/arity but a 32-bit argument
            ExtBoolTerm::Ult(call("f", vec![wide]), c8(2)),
        ];
        assert_eq!(
            lower(&q).err(),
            Some(SliverError::InconsistentCall { name: "f".into() })
        );
    }

    #[test]
    fn determinism_is_byte_for_byte() {
        let q = vec![
            ExtBoolTerm::Eq(call("g", vec![v8("x"), v8("y")]), c8(1)),
            ExtBoolTerm::Eq(call("g", vec![v8("y"), v8("x")]), c8(2)),
            ExtBoolTerm::Eq(select(store(arr("a"), i32c(4), c8(9)), i32c(4)), c8(9)),
        ];
        let one = format!("{:?}", lower(&q).unwrap());
        let two = format!("{:?}", lower(&q).unwrap());
        assert_eq!(one, two);
    }
}

// ─── Lowering vs the concrete evaluator (non-Z3 model preservation) ──────────

#[cfg(test)]
mod lowering {
    use super::build::*;
    use super::*;

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
    }

    /// A deterministic pseudo-random UF result for a call tuple.
    fn uf_result(name: &str, argv: &[u128]) -> u128 {
        let mut h = 1469598103934665603u64 ^ name.len() as u64;
        for b in name.bytes() {
            h = (h ^ b as u64).wrapping_mul(1099511628211);
        }
        for a in argv {
            h = (h ^ *a as u64).wrapping_mul(1099511628211);
        }
        (h & 0xFF) as u128
    }

    fn gen_bv(rng: &mut Rng, depth: u32) -> ExtBvTerm {
        if depth == 0 || rng.below(2) == 0 {
            return match rng.below(4) {
                0 => c8(rng.below(256) as u128),
                1 => v8(if rng.below(2) == 0 { "x" } else { "y" }),
                2 => {
                    let depth = rng.below(3) as u32;
                    let a = gen_array(rng, depth);
                    select(a, i32c(rng.below(4) as u128))
                }
                // f is arity 1, g is arity 2 — fixed to stay consistent.
                _ => {
                    if rng.below(2) == 0 {
                        call("f", vec![gen_bv(rng, depth.saturating_sub(1))])
                    } else {
                        call(
                            "g",
                            vec![
                                gen_bv(rng, depth.saturating_sub(1)),
                                gen_bv(rng, depth.saturating_sub(1)),
                            ],
                        )
                    }
                }
            };
        }
        let a = gen_bv(rng, depth - 1);
        let b = gen_bv(rng, depth - 1);
        // #231: every lifted operator, including an `ite` whose condition
        // and branches can hold a select/pure_call.
        ExtBvTerm::Op(Box::new(match rng.below(11) {
            0 => ExtOp::Add(a, b),
            1 => ExtOp::Xor(a, b),
            2 => ExtOp::And(a, b),
            3 => ExtOp::Sub(a, b),
            4 => ExtOp::Urem(a, b),
            5 => ExtOp::Sdiv(a, b),
            6 => ExtOp::Srem(a, b),
            7 => ExtOp::Rotl(a, b),
            8 => ExtOp::Not(a),
            9 => ExtOp::Neg(a),
            _ => ExtOp::Ite {
                cond: ExtBoolTerm::Ult(gen_bv(rng, 1), gen_bv(rng, 1)),
                then_: a,
                else_: b,
            },
        }))
    }

    fn gen_array(rng: &mut Rng, depth: u32) -> ArrayTerm {
        let base = arr(if rng.below(2) == 0 { "a" } else { "b" });
        (0..depth).fold(base, |acc, _| {
            store(acc, i32c(rng.below(4) as u128), gen_bv(rng, 1))
        })
    }

    fn gen_bool(rng: &mut Rng, depth: u32) -> ExtBoolTerm {
        if depth == 0 {
            let (a, b) = (gen_bv(rng, 2), gen_bv(rng, 2));
            return match rng.below(4) {
                0 => ExtBoolTerm::Eq(a, b),
                1 => ExtBoolTerm::Ne(a, b),
                2 => ExtBoolTerm::Ult(a, b),
                _ => ExtBoolTerm::Ule(a, b),
            };
        }
        match rng.below(3) {
            0 => ExtBoolTerm::Not(Box::new(gen_bool(rng, depth - 1))),
            1 => ExtBoolTerm::And(
                Box::new(gen_bool(rng, depth - 1)),
                Box::new(gen_bool(rng, depth - 1)),
            ),
            _ => ExtBoolTerm::Or(
                Box::new(gen_bool(rng, depth - 1)),
                Box::new(gen_bool(rng, depth - 1)),
            ),
        }
    }

    /// Reconstruct the core model from a concrete [`SliverModel`], filling the
    /// UF interpretation in-place so both sides agree, then return the core
    /// environment binding every fresh variable.
    fn core_env(model: &mut SliverModel, lowered: &Lowered) -> Env {
        let mut env = model.env.clone();
        for (var, arrname, idx) in &lowered.reads {
            let v = model
                .arrays
                .get(arrname)
                .and_then(|m| m.get(idx))
                .copied()
                .unwrap_or(0);
            env.insert(var.clone(), v as u128);
        }
        for (var, name, args, sort) in &lowered.calls {
            let argv: Vec<u128> = args
                .iter()
                .map(|a| eval::eval_bv(a, &env).unwrap())
                .collect();
            let result = *model
                .calls
                .entry((name.clone(), argv))
                .or_insert_with_key(|(n, av)| uf_result(n, av) & mask(sort.width));
            env.insert(var.clone(), result);
        }
        env
    }

    // rivet: verifies VER-073
    /// TR-073: the trusted `flatten_tree` over the kernel's copy of the
    /// extended trees produces exactly the `ordeal-ext/v1` block the
    /// lowering's own walk (`lower_ext`, the differential twin) produces —
    /// nodes, bits, side table, roots, variable / array / function tables
    /// — on three seeded corpora (the ones `sliver_lowering_preserves_every_model`
    /// and the v0.33.0 verdict scan used), and the copy round-trips.
    #[test]
    fn kernel_flattening_matches_the_lowering_walk() {
        let mut checked = 0usize;
        for (seed, n_queries, depth) in [
            (0x5117_5EED_0000_0001u64, 400usize, 2u32),
            (0x5111_0231_0000_0001, 300, 2),
            (0x5111_0DFF_0000_0001, 250, 3),
        ] {
            let mut rng = Rng(seed);
            for _ in 0..n_queries {
                let n = 1 + rng.below(3) as usize;
                let query: Vec<ExtBoolTerm> = (0..n).map(|_| gen_bool(&mut rng, depth)).collect();
                let Ok(trace) = lower_ext(&query) else {
                    continue;
                };
                let flat = ordeal_lrat::flatten_tree(&crate::mirror::of_ext_bools(&query))
                    .unwrap_or_else(|e| panic!("the kernel refused {query:?}: {e:?}"));
                let kernel = crate::mirror::ext_query(&flat).expect("utf-8");
                assert!(kernel == trace.ext, "the two walks differ on {query:?}");
                for a in &query {
                    let t = crate::mirror::of_ext_bool(a);
                    assert!(
                        crate::mirror::tree_eq(
                            &crate::mirror::of_ext_bool(&crate::mirror::to_ext_bool(&t)),
                            &t
                        ),
                        "round trip on {a:?}"
                    );
                }
                checked += 1;
            }
        }
        assert!(checked >= 900, "{checked} queries compared");
    }

    #[test]
    fn sliver_lowering_preserves_every_model() {
        let mut rng = Rng(0x5117_5EED_0000_0001);
        let mut checked = 0usize;
        for _ in 0..400 {
            let n = 1 + rng.below(3) as usize;
            let query: Vec<ExtBoolTerm> = (0..n).map(|_| gen_bool(&mut rng, 2)).collect();
            let lowered = match lower_traced(&query) {
                Ok(l) => l,
                Err(_) => continue, // out-of-sliver shapes cannot arise here
            };

            // A random total model over the core variables and base arrays.
            let mut model = SliverModel::default();
            model.env.insert("x".into(), rng.below(256) as u128);
            model.env.insert("y".into(), rng.below(256) as u128);
            for name in ["a", "b"] {
                let mut cells = BTreeMap::new();
                for idx in 0..4u32 {
                    cells.insert(idx, rng.below(256) as u8);
                }
                model.arrays.insert(name.into(), cells);
            }

            let env = core_env(&mut model, &lowered);
            let ext_sat = query.iter().all(|a| eval_ext_bool(a, &model).unwrap());
            let core_sat = lowered
                .assertions
                .iter()
                .all(|a| eval::eval_bool(a, &env).unwrap());
            assert_eq!(
                ext_sat, core_sat,
                "lowering changed the truth of a model\nquery: {query:?}"
            );
            checked += 1;
        }
        assert!(
            checked > 300,
            "generator produced too few in-sliver queries"
        );
    }

    /// #247: a query variable named like a fresh read or call variable
    /// (`$sel:a:5`, `$uf:f:0`, …) must stay distinct from the read or call.
    /// Before the fix `select(a, 5) != $sel:a:5` lowered to
    /// `$sel:a:5 != $sel:a:5` — a certified wrong `Unsat`. Checked here the
    /// strong way: on random models the lowered core and the extended query
    /// agree, with the colliding names in play.
    // rivet: verifies VER-071
    #[test]
    fn reserved_looking_query_names_stay_distinct_from_fresh_variables() {
        let mut rng = Rng(0x0247_5E1E_C7ED_0001);
        let reserved = |rng: &mut Rng| -> ExtBvTerm {
            match rng.below(4) {
                0 => v8(&format!("$sel:a:{}", rng.below(4))),
                1 => v8(&format!("$sel:b:{}", rng.below(4))),
                2 => v8(&format!("$uf:f:{}", rng.below(4))),
                _ => v8(&format!("$sel:a:#{}", rng.below(4))),
            }
        };
        let mut checked = 0usize;
        for _ in 0..400 {
            let other = match rng.below(3) {
                0 => select(
                    arr(if rng.below(2) == 0 { "a" } else { "b" }),
                    i32c(rng.below(4) as u128),
                ),
                1 => call("f", vec![gen_bv(&mut rng, 1)]),
                _ => gen_bv(&mut rng, 2),
            };
            let r = reserved(&mut rng);
            let query = vec![match rng.below(3) {
                0 => ExtBoolTerm::Ne(other, r),
                1 => ExtBoolTerm::Eq(other, r),
                _ => ExtBoolTerm::Ult(r, other),
            }];
            let lowered = lower_traced(&query).expect("in the sliver");
            let mut model = SliverModel::default();
            model.env.insert("x".into(), rng.below(256) as u128);
            model.env.insert("y".into(), rng.below(256) as u128);
            for name in [
                "$sel:a:0",
                "$sel:a:1",
                "$sel:a:2",
                "$sel:a:3",
                "$sel:b:0",
                "$sel:b:1",
                "$sel:b:2",
                "$sel:b:3",
                "$uf:f:0",
                "$uf:f:1",
                "$uf:f:2",
                "$uf:f:3",
                "$sel:a:#0",
                "$sel:a:#1",
                "$sel:a:#2",
                "$sel:a:#3",
            ] {
                model.env.insert(name.into(), rng.below(256) as u128);
            }
            for name in ["a", "b"] {
                let mut cells = BTreeMap::new();
                for idx in 0..4u32 {
                    cells.insert(idx, rng.below(256) as u8);
                }
                model.arrays.insert(name.into(), cells);
            }
            let env = core_env(&mut model, &lowered);
            let ext_sat = query.iter().all(|a| eval_ext_bool(a, &model).unwrap());
            let core_sat = lowered
                .assertions
                .iter()
                .all(|a| eval::eval_bool(a, &env).unwrap());
            assert_eq!(
                ext_sat, core_sat,
                "lowering changed the truth of a model\nquery: {query:?}"
            );
            checked += 1;
        }
        assert_eq!(checked, 400);
        // The reported query: the fresh read must get another name.
        let q = [ExtBoolTerm::Ne(select(arr("a"), i32c(5)), v8("$sel:a:5"))];
        let low = lower_traced(&q).unwrap();
        assert_eq!(
            low.reads,
            vec![("$sel:a:5'".to_string(), "a".to_string(), 5)]
        );
    }

    #[test]
    fn evaluator_reads_most_recent_write() {
        let mut model = SliverModel::default();
        model
            .arrays
            .insert("a".into(), BTreeMap::from([(7u32, 3u8)]));
        // select(store(a, 7, 99), 7) = 99, overriding the base cell's 3.
        let t = select(store(arr("a"), i32c(7), c8(99)), i32c(7));
        assert_eq!(eval_ext_bv(&t, &model).unwrap(), 99);
        // A miss reads the base cell.
        let t2 = select(store(arr("a"), i32c(1), c8(99)), i32c(7));
        assert_eq!(eval_ext_bv(&t2, &model).unwrap(), 3);
    }
}
