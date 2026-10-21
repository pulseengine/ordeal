//! The sliver correspondence check (TR-072, `ordeal-cert/v4`): is the
//! lowered core — the term `check_term_dag` relates to the solver's DAG —
//! the read-over-write + Ackermann + congruence elimination of the
//! EXTENDED query (arrays and uninterpreted functions) as it was asked?
//!
//! `#[path]`-included into `kernel.rs` as its submodule `sliver_kernel`, so
//! that Charon/Aeneas translate it in the same unit as the checker and the
//! lowering (`kernel.sliver_kernel.*` in `lean/Kernel.lean`); the proofs
//! are `lean/SliverCheck.lean`. Written in the same fragment as the rest of
//! the kernel (index loops, every inner loop its own function, verdicts
//! carried in locals, no `String`, no maps — every table is a flat slice
//! of `usize` the check verifies).
//!
//! # The extended query
//!
//! A node list like the DAG's, with two constructors beyond the closed
//! fragment ([`ExtNode`]). Arrays and functions are ids, as variables are
//! `Var` nodes: the names are the untrusted side's. A store chain is a
//! side table of its `select` (the sliver is non-extensional: an array
//! value never escapes a `select`), so there is no array sort in the value
//! universe.
//!
//! # The tables (untrusted advice, every entry checked)
//!
//! - `map[i]`: the core node extended node `i` lowered to, or `usize::MAX`
//!   for a node that has no image (a store value the concrete fast path
//!   dropped, the inside of a dead chain level).
//! - `reads`, 3 per entry: `(read var node, array id, index node)` — the
//!   fresh BV8 variable a base-array read became, and the CORE node of the
//!   index it was memoized on (the untrusted lowering appends the lowered
//!   index of every read to the core as a non-root node, so the index is
//!   always there to evaluate).
//! - `calls`, 4 per entry: `(result var node, function id, first arg,
//!   arity)`, the arguments' core nodes in `cargs`.
//!
//! The congruence roots are not hinted: the check enumerates the expected
//! ones itself (pairs `p < q` of the read table with one array id, then
//! pairs of the call table with one function id, in table order; a pair of
//! two unequal constant indices is skipped) and requires the core's roots
//! after the extended roots' images to be exactly them.
//!
//! Every table entry must be LIVE: reached by the chain walk of some
//! extended `select` (a read entry) or by some extended call (a call
//! entry). The main loop marks an entry's variable reached (class 2 → 4,
//! 3 → 5) and `dead_entry` rejects any left. Nothing orders an entry's
//! index (or arguments) against its variable, so a dead entry whose index
//! mentions its own variable, together with the congruence roots the
//! check demands for it, can make the core unsatisfiable while the
//! extended query is not — the UNSAT direction below would be false. The
//! lowering never emits a dead entry (each is created by the `select` /
//! call that reaches it), so the requirement costs nothing.
//!
//! # What it establishes
//!
//! > If `check_sliver_lowering(…)` returns `Ok(())`, then (UNSAT) every
//! > extended model — an assignment, an array interpretation and a UF
//! > interpretation making every extended root true — pushes forward to an
//! > assignment making every core root true; and (SAT) every assignment
//! > making every core root true pulls back to an extended model, built
//! > from it, making every extended root true.
//!
//! Machine-checked as `kernel.spec.check_sliver_lowering_sound`,
//! `check_sliver_unsat_sound`, `check_sliver_model_sound` and
//! `sliver_verdicts_exclusive` (`lean/SliverCheck.lean`), composed with the
//! unchanged phase-7 and phase-4/6 theorems.

use super::blast_kernel::DagNode;
use super::{
    QueryError, bits_eq, dag_wf, map_at, map_node, node_eq, node_f1, node_f2, node_f3, node_tag,
    node_wf, node_width,
};

/// A node of the extended query (`ordeal-ext/v1`).
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ExtNode {
    /// A closed-fragment node over extended operands (one for one with
    /// [`DagNode`]; a `Var` is a query variable, shared by name).
    Core(DagNode),
    /// `select` of array `aid` at BV32 node `idx` through the store chain
    /// `eside[s .. s + 2n]` — `n` `(index node, value node)` pairs, the
    /// outermost (most recent) store first; `n = 0` reads the base array:
    /// `Select(aid, idx, s, n)`. Width 8.
    Select(usize, usize, usize, usize),
    /// `pure_call` of function `fid` with result width `w` and the `n`
    /// argument nodes `eside[s .. s + n]`: `Call(fid, w, s, n)`.
    Call(usize, usize, usize, usize),
}

/// Why [`check_sliver_lowering`] rejected. Data-only, like
/// [`super::TermError`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SliverCheckError {
    /// Extended node `node` is malformed: an operand is not an earlier
    /// node, a width is wrong (a select index or a store index is not
    /// BV32, a store value is not BV8, a call's result width is 0), or a
    /// chain / argument range is outside the side table.
    Ext {
        /// 0-based index of the extended node.
        node: usize,
    },
    /// The core is malformed or too large (`dag_wf` on it).
    Core(QueryError),
    /// The map does not have one entry per extended node.
    MapLength {
        /// The extended query's node count.
        expected: usize,
        /// The map's length.
        found: usize,
    },
    /// Extended node `node` is mapped past the end of the core.
    MapOutOfRange {
        /// 0-based index of the extended node.
        node: usize,
    },
    /// Read entry `entry` is malformed: its variable is not a BV8 core
    /// variable, or already classified, its index is not a BV32 core node,
    /// or an earlier entry has the same `(array, index)`.
    ReadTable {
        /// 0-based index of the entry.
        entry: usize,
    },
    /// Call entry `entry` is malformed: its variable is not a core
    /// variable, or already classified, an argument is past the end of
    /// the core, or an earlier entry has the same `(function, args)`.
    CallTable {
        /// 0-based index of the entry.
        entry: usize,
    },
    /// Extended node `node` is a variable whose image is not a core
    /// variable of its width, or whose image is already a read variable,
    /// a call variable or the image of another extended variable (the
    /// three classes must partition the core variables the extended query
    /// reaches: an aliasing would make the core MORE constrained).
    VarClass {
        /// 0-based index of the extended node.
        node: usize,
    },
    /// Extended node `node` is a constant whose image is not the same
    /// constant.
    ConstMismatch {
        /// 0-based index of the extended node.
        node: usize,
    },
    /// Extended node `node` is a closed-fragment operator whose image is
    /// not the same operator over the images of its operands.
    NodeMismatch {
        /// 0-based index of the extended node.
        node: usize,
    },
    /// Extended node `node` is a `select` whose image is not its
    /// read-over-write elimination: at a level with two constant indices,
    /// equal bits must resolve to the value's image and unequal bits skip
    /// the level; at any other level the image must be `ite(index = idx,
    /// value, rest)`; past the chain it must be the read variable
    /// registered for `(array, idx)`.
    ChainMismatch {
        /// 0-based index of the extended node.
        node: usize,
    },
    /// Extended node `node` is a call whose image is not the result
    /// variable registered for its function over the images of its
    /// arguments, of its width.
    CallMismatch {
        /// 0-based index of the extended node.
        node: usize,
    },
    /// The extended roots' images are not the first core roots, or the
    /// core has more or fewer roots after them than the expected
    /// congruence roots.
    RootMismatch,
    /// Core root `root` is not the congruence root expected at its
    /// position (`idx_p = idx_q → var_p = var_q` for a read pair,
    /// `args_p = args_q → var_p = var_q` for a call pair).
    CongruenceMismatch {
        /// 0-based index into the core's root list.
        root: usize,
    },
    /// Core variable `var` is registered in the read or call table but no
    /// extended `select` / call maps onto its entry. A dead entry is
    /// rejected because its congruence roots constrain the core through
    /// a variable the extended query never reads: an entry whose index
    /// mentions its own variable (nothing orders the two) can make the
    /// core unsatisfiable while the extended query is not, and the UNSAT
    /// direction of `check_sliver_lowering_sound` would be false.
    DeadEntry {
        /// The core node of the entry's variable.
        var: usize,
    },
}

// ───────────── Extended well-formedness ─────────────

/// The `n` chain levels from `eside[s]`: each an earlier BV32 index node
/// and an earlier BV8 value node, within the side table.
fn chain_wf(ws: &[usize], eside: &[usize], s: usize, n: usize) -> bool {
    let nn = ws.len();
    let m = eside.len();
    let mut ok = true;
    let mut l = 0usize;
    let mut off = s;
    while ok && l < n {
        if off >= m || m - off < 2 {
            ok = false;
        } else {
            let x = eside[off];
            let v = eside[off + 1];
            if x >= nn || ws[x] != 32 || v >= nn || ws[v] != 8 {
                ok = false;
            } else {
                off += 2;
            }
        }
        l += 1;
    }
    ok
}

/// The `n` argument nodes from `eside[s]`: each an earlier node, within
/// the side table.
fn args_wf(ws: &[usize], eside: &[usize], s: usize, n: usize) -> bool {
    let nn = ws.len();
    let m = eside.len();
    let mut ok = true;
    let mut l = 0usize;
    let mut off = s;
    while ok && l < n {
        if off >= m {
            ok = false;
        } else {
            let a = eside[off];
            if a >= nn {
                ok = false;
            } else {
                off += 1;
            }
        }
        l += 1;
    }
    ok
}

/// Well-formedness of one extended node against the widths of the nodes
/// before it: a closed node as `node_wf`, a `select` with a BV32 index and
/// a well-formed chain, a call with a positive width and in-range
/// arguments.
fn ext_node_wf(ws: &[usize], nbits: usize, eside: &[usize], node: ExtNode) -> bool {
    let n = ws.len();
    match node {
        ExtNode::Core(nd) => node_wf(ws, nbits, nd),
        ExtNode::Select(_, j, s, k) => j < n && ws[j] == 32 && chain_wf(ws, eside, s, k),
        ExtNode::Call(_, w, s, k) => w > 0 && args_wf(ws, eside, s, k),
    }
}

/// The width of one extended node: a `select` is BV8, a call its declared
/// width.
fn ext_node_width(ws: &[usize], node: ExtNode) -> usize {
    match node {
        ExtNode::Core(nd) => node_width(ws, nd),
        ExtNode::Select(_, _, _, _) => 8,
        ExtNode::Call(_, w, _, _) => w,
    }
}

/// The well-formedness check of the extended query, returning every
/// node's width (`dag_wf`'s twin).
pub fn ext_wf(
    e: &[ExtNode],
    nbits: usize,
    eside: &[usize],
) -> Result<Vec<usize>, SliverCheckError> {
    let mut ws: Vec<usize> = Vec::new();
    let n = e.len();
    let mut i = 0usize;
    while i < n {
        let node = e[i];
        if !ext_node_wf(&ws, nbits, eside, node) {
            return Err(SliverCheckError::Ext { node: i });
        }
        let w = ext_node_width(&ws, node);
        ws.push(w);
        i += 1;
    }
    Ok(ws)
}

// ───────────── The tables ─────────────

/// Is there a read entry before offset `upto` with the same `(aid, idx)`?
fn read_dup(reads: &[usize], upto: usize, aid: usize, idx: usize) -> bool {
    let mut off = 0usize;
    let mut found = false;
    while !found && off < upto {
        if reads[off + 1] == aid && reads[off + 2] == idx {
            found = true;
        }
        off += 3;
    }
    found
}

/// Validate the read table and classify its variables (`cls[var] = 2`,
/// `ent[var]` = the entry's offset). `ws1` are the core's widths.
fn read_entries(
    reads: &[usize],
    t: &[DagNode],
    ws1: &[usize],
    cls: &mut [usize],
    ent: &mut [usize],
) -> Result<(), SliverCheckError> {
    let n = t.len();
    let m = reads.len();
    let mut off = 0usize;
    let mut k = 0usize;
    while off < m {
        if m - off < 3 {
            return Err(SliverCheckError::ReadTable { entry: k });
        }
        let var = reads[off];
        let aid = reads[off + 1];
        let idx = reads[off + 2];
        if var >= n
            || !node_eq(t[var], DagNode::Var(8))
            || cls[var] != 0
            || idx >= n
            || ws1[idx] != 32
            || read_dup(reads, off, aid, idx)
        {
            return Err(SliverCheckError::ReadTable { entry: k });
        }
        cls[var] = 2;
        ent[var] = off;
        off += 3;
        k += 1;
    }
    Ok(())
}

/// Are the `k` arguments from `cargs[s]` all core nodes (`< n`), within
/// the table?
fn args_in_range(cargs: &[usize], s: usize, k: usize, n: usize) -> bool {
    let m = cargs.len();
    if s > m || k > m - s {
        return false;
    }
    let mut ok = true;
    let mut l = 0usize;
    while ok && l < k {
        if cargs[s + l] >= n {
            ok = false;
        }
        l += 1;
    }
    ok
}

/// Are the `k` arguments from `cargs[s1]` and from `cargs[s2]` the same
/// nodes? (Both ranges already known to be within the table.)
fn args_eq(cargs: &[usize], s1: usize, s2: usize, k: usize) -> bool {
    let mut ok = true;
    let mut l = 0usize;
    while ok && l < k {
        if cargs[s1 + l] != cargs[s2 + l] {
            ok = false;
        }
        l += 1;
    }
    ok
}

/// Is there a call entry before offset `upto` with the same function and
/// the same argument nodes?
fn call_dup(calls: &[usize], cargs: &[usize], upto: usize, fid: usize, s: usize, k: usize) -> bool {
    let mut off = 0usize;
    let mut found = false;
    while !found && off < upto {
        if calls[off + 1] == fid && calls[off + 3] == k && args_eq(cargs, calls[off + 2], s, k) {
            found = true;
        }
        off += 4;
    }
    found
}

/// Validate the call table and classify its variables (`cls[var] = 3`,
/// `ent[var]` = the entry's offset).
fn call_entries(
    calls: &[usize],
    cargs: &[usize],
    t: &[DagNode],
    cls: &mut [usize],
    ent: &mut [usize],
) -> Result<(), SliverCheckError> {
    let n = t.len();
    let m = calls.len();
    let mut off = 0usize;
    let mut k = 0usize;
    while off < m {
        if m - off < 4 {
            return Err(SliverCheckError::CallTable { entry: k });
        }
        let var = calls[off];
        let fid = calls[off + 1];
        let s = calls[off + 2];
        let arity = calls[off + 3];
        if var >= n
            || node_tag(t[var]) != 0
            || cls[var] != 0
            || !args_in_range(cargs, s, arity, n)
            || call_dup(calls, cargs, off, fid, s, arity)
        {
            return Err(SliverCheckError::CallTable { entry: k });
        }
        cls[var] = 3;
        ent[var] = off;
        off += 4;
        k += 1;
    }
    Ok(())
}

// ───────────── One extended node ─────────────

/// A closed node against its image: a variable to an unclassified core
/// variable of its width (which it claims: class 1), a constant to the
/// same constant, an operator to the same operator over the images of its
/// operands — exactly, with no rewrite.
fn core_corr(
    ebits: &[bool],
    map: &[usize],
    tbits: &[bool],
    nd: DagNode,
    d: DagNode,
    cls: &mut [usize],
    i: usize,
    mi: usize,
) -> Result<(), SliverCheckError> {
    let tt = node_tag(nd);
    let td = node_tag(d);
    if tt == 0 {
        if td != 0 || node_f1(nd) != node_f1(d) || cls[mi] != 0 {
            return Err(SliverCheckError::VarClass { node: i });
        }
        cls[mi] = 1;
        return Ok(());
    }
    if tt == 1 {
        if td != 1
            || node_f2(nd) != node_f2(d)
            || !bits_eq(ebits, node_f1(nd), tbits, node_f1(d), node_f2(nd))
        {
            return Err(SliverCheckError::ConstMismatch { node: i });
        }
        return Ok(());
    }
    if node_eq(map_node(map, nd), d) {
        Ok(())
    } else {
        Err(SliverCheckError::NodeMismatch { node: i })
    }
}

/// Is extended node `x` a constant, and then its bit offset and width:
/// `(is_const, s, w)`.
fn ext_const(e: &[ExtNode], x: usize) -> (bool, usize, usize) {
    if x < e.len() {
        let en = e[x];
        match en {
            ExtNode::Core(nd) => {
                if node_tag(nd) == 1 {
                    return (true, node_f1(nd), node_f2(nd));
                }
            }
            ExtNode::Select(_, _, _, _) => {}
            ExtNode::Call(_, _, _, _) => {}
        }
    }
    (false, 0, 0)
}

/// Is `c` the class of a read variable (2, or 4 once a `select` reached
/// it)? (Its own function so that the translated `||` has a declared
/// `bool` to elaborate against.)
fn read_class(c: usize) -> bool {
    c == 2 || c == 4
}

/// Is `c` the class of a call variable (3, or 5 once a call reached it)?
fn call_class(c: usize) -> bool {
    c == 3 || c == 5
}

/// Is `c` the class of a table variable nothing reached yet (2 or 3)?
fn dead_class(c: usize) -> bool {
    c == 2 || c == 3
}

/// Is core node `cur` the read variable registered for `(aid, xj)`? (Class
/// 2, or 4 once an earlier `select` reached it.)
fn base_read_ok(
    t: &[DagNode],
    reads: &[usize],
    cls: &[usize],
    ent: &[usize],
    aid: usize,
    xj: usize,
    cur: usize,
) -> bool {
    if cur >= t.len() {
        return false;
    }
    let live = read_class(cls[cur]);
    if !live {
        return false;
    }
    let o = ent[cur];
    o < reads.len() && reads.len() - o >= 3 && reads[o + 1] == aid && reads[o + 2] == xj
}

/// The chain walk: is core node `k0` the read-over-write elimination of
/// `select(aid, j)` through the `k` levels from `eside[s]`? At a level
/// whose index and the selected index are both constants: equal bits
/// resolve to the value's image (and the walk ends), unequal bits skip
/// the level. At any other level the current node must be `ite(index =
/// j, value, rest)` over the images, and the walk continues at `rest`.
/// Past the chain the current node must be the read variable registered
/// for `(aid, j)`, which the walk then marks reached (class 4): the entry
/// is live.
#[allow(clippy::too_many_arguments)] // the fragment has no structs to bundle them
fn chain_walk(
    e: &[ExtNode],
    ebits: &[bool],
    eside: &[usize],
    map: &[usize],
    t: &[DagNode],
    reads: &[usize],
    cls: &mut [usize],
    ent: &[usize],
    aid: usize,
    j: usize,
    s: usize,
    k: usize,
    k0: usize,
) -> bool {
    let n = t.len();
    let ite_tag = node_tag(DagNode::Ite(0, 0, 0));
    let mut cur = k0;
    let mut ok = true;
    let mut done = false;
    let mut l = 0usize;
    let mut off = s;
    while ok && !done && l < k {
        let x = eside[off];
        let v = eside[off + 1];
        let (xc, xs, xw) = ext_const(e, x);
        let (jc, js, jw) = ext_const(e, j);
        if xc && jc {
            if xw == jw && bits_eq(ebits, xs, ebits, js, xw) {
                ok = cur == map_at(map, v);
                done = true;
            }
        } else if cur < n {
            let d = t[cur];
            if node_tag(d) == ite_tag && node_f2(d) == map_at(map, v) {
                let c = node_f1(d);
                if c < n && node_eq(t[c], DagNode::Eq(map_at(map, x), map_at(map, j))) {
                    cur = node_f3(d);
                } else {
                    ok = false;
                }
            } else {
                ok = false;
            }
        } else {
            ok = false;
        }
        off += 2;
        l += 1;
    }
    if ok && !done {
        ok = base_read_ok(t, reads, cls, ent, aid, map_at(map, j), cur);
        if ok {
            cls[cur] = 4;
        }
    }
    ok
}

/// Are the images of the `k` extended arguments from `eside[s]` the core
/// nodes from `cargs[cs]`?
fn args_match(
    eside: &[usize],
    map: &[usize],
    cargs: &[usize],
    s: usize,
    cs: usize,
    k: usize,
) -> bool {
    let mut ok = true;
    let mut l = 0usize;
    while ok && l < k {
        if map_at(map, eside[s + l]) != cargs[cs + l] {
            ok = false;
        }
        l += 1;
    }
    ok
}

/// Is core node `mi` the result variable registered for `fid` over the
/// images of the call's arguments, of width `w`? (Class 3, or 5 once an
/// earlier call reached it; the entry is then marked reached: live.)
#[allow(clippy::too_many_arguments)] // the fragment has no structs to bundle them
fn call_corr(
    eside: &[usize],
    map: &[usize],
    t: &[DagNode],
    calls: &[usize],
    cargs: &[usize],
    cls: &mut [usize],
    ent: &[usize],
    fid: usize,
    w: usize,
    s: usize,
    k: usize,
    mi: usize,
) -> bool {
    let live = call_class(cls[mi]);
    if !live || !node_eq(t[mi], DagNode::Var(w)) {
        return false;
    }
    let o = ent[mi];
    if o >= calls.len() || calls.len() - o < 4 {
        return false;
    }
    let ok = calls[o + 1] == fid
        && calls[o + 3] == k
        && args_match(eside, map, cargs, s, calls[o + 2], k);
    if ok {
        cls[mi] = 5;
    }
    ok
}

/// One extended node of the main loop: nothing to check when node `i` has
/// no image; otherwise the image must be a core node and the node's kind
/// decides.
#[allow(clippy::too_many_arguments)] // the fragment has no structs to bundle them
fn ext_step(
    e: &[ExtNode],
    ebits: &[bool],
    eside: &[usize],
    map: &[usize],
    t: &[DagNode],
    tbits: &[bool],
    reads: &[usize],
    calls: &[usize],
    cargs: &[usize],
    cls: &mut [usize],
    ent: &[usize],
    i: usize,
) -> Result<(), SliverCheckError> {
    let mi = map[i];
    if mi == usize::MAX {
        return Ok(());
    }
    if mi >= t.len() {
        return Err(SliverCheckError::MapOutOfRange { node: i });
    }
    let en = e[i];
    let d = t[mi];
    match en {
        ExtNode::Core(nd) => core_corr(ebits, map, tbits, nd, d, cls, i, mi),
        ExtNode::Select(aid, j, s, k) => {
            if chain_walk(e, ebits, eside, map, t, reads, cls, ent, aid, j, s, k, mi) {
                Ok(())
            } else {
                Err(SliverCheckError::ChainMismatch { node: i })
            }
        }
        ExtNode::Call(fid, w, s, k) => {
            if call_corr(eside, map, t, calls, cargs, cls, ent, fid, w, s, k, mi) {
                Ok(())
            } else {
                Err(SliverCheckError::CallMismatch { node: i })
            }
        }
    }
}

/// The first core variable still in class 2 or 3 after the main loop — a
/// read or call entry no extended `select` / call reached — or `cls.len()`
/// when every entry is live.
fn dead_entry(cls: &[usize]) -> usize {
    let n = cls.len();
    let mut found = n;
    let mut i = 0usize;
    while found == n && i < n {
        let dead = dead_class(cls[i]);
        if dead {
            found = i;
        }
        i += 1;
    }
    found
}

// ───────────── The roots ─────────────

/// Do the extended roots' images lead the core's roots, one for one?
fn ext_roots_corr(eroots: &[usize], map: &[usize], troots: &[usize]) -> bool {
    let m = eroots.len();
    if m > troots.len() {
        return false;
    }
    let mut ok = true;
    let mut k = 0usize;
    while ok && k < m {
        let image = map_at(map, eroots[k]);
        if image == usize::MAX || image != troots[k] {
            ok = false;
        }
        k += 1;
    }
    ok
}

/// Is core root `root` the clause `ante → Eq(vp, vq)`, spelled as the
/// lowering spells it: `Or(Not(ante), Eq(vp, vq))`? Returns the `ante`
/// node (`usize::MAX` when the shape is wrong).
fn implication_shape(t: &[DagNode], root: usize, vp: usize, vq: usize) -> usize {
    let n = t.len();
    let or_tag = node_tag(DagNode::BoolOr(0, 0));
    let not_tag = node_tag(DagNode::Not(0));
    if root >= n {
        return usize::MAX;
    }
    let d = t[root];
    if node_tag(d) != or_tag {
        return usize::MAX;
    }
    let nn = node_f1(d);
    let c = node_f2(d);
    if c >= n || !node_eq(t[c], DagNode::Eq(vp, vq)) || nn >= n {
        return usize::MAX;
    }
    let dn = t[nn];
    if node_tag(dn) != not_tag {
        return usize::MAX;
    }
    node_f1(dn)
}

/// Are the two constant core nodes `a`, `b` constants with unequal bits
/// (a pair the lowering skips)? Any non-constant: no.
fn const_pair_unequal(t: &[DagNode], tbits: &[bool], a: usize, b: usize) -> bool {
    let n = t.len();
    if a >= n || b >= n {
        return false;
    }
    let da = t[a];
    let db = t[b];
    if node_tag(da) != 1 || node_tag(db) != 1 {
        return false;
    }
    !(node_f2(da) == node_f2(db) && bits_eq(tbits, node_f1(da), tbits, node_f1(db), node_f2(da)))
}

/// The congruence roots of read entry at offset `op` against every later
/// entry of its array, from root index `idx`: `(ok, next idx)`.
fn array_cong_for(
    reads: &[usize],
    t: &[DagNode],
    tbits: &[bool],
    troots: &[usize],
    op: usize,
    idx0: usize,
) -> (bool, usize) {
    let m = reads.len();
    let aid = reads[op + 1];
    let vp = reads[op];
    let xp = reads[op + 2];
    let mut idx = idx0;
    let mut ok = true;
    let mut oq = op + 3;
    while ok && oq < m {
        if reads[oq + 1] == aid {
            let xq = reads[oq + 2];
            if !const_pair_unequal(t, tbits, xp, xq) {
                if idx >= troots.len() {
                    ok = false;
                } else {
                    let a = implication_shape(t, troots[idx], vp, reads[oq]);
                    if a >= t.len() || !node_eq(t[a], DagNode::Eq(xp, xq)) {
                        ok = false;
                    } else {
                        idx += 1;
                    }
                }
            }
        }
        oq += 3;
    }
    (ok, idx)
}

/// Every array congruence root, in table order: `(ok, next idx)`.
fn array_cong(
    reads: &[usize],
    t: &[DagNode],
    tbits: &[bool],
    troots: &[usize],
    idx0: usize,
) -> (bool, usize) {
    let m = reads.len();
    let mut idx = idx0;
    let mut ok = true;
    let mut op = 0usize;
    while ok && op < m {
        let (ok1, idx1) = array_cong_for(reads, t, tbits, troots, op, idx);
        ok = ok1;
        idx = idx1;
        op += 3;
    }
    (ok, idx)
}

/// Is core node `a` the antecedent `args_p = args_q` over `k ≥ 1`
/// arguments, as the lowering nests it: `And(And(Eq(a0, b0), Eq(a1, b1)),
/// …)`, the last argument's equality outermost?
fn ante_ok(t: &[DagNode], cargs: &[usize], sp: usize, sq: usize, k: usize, a: usize) -> bool {
    let n = t.len();
    let and_tag = node_tag(DagNode::BoolAnd(0, 0));
    let mut cur = a;
    let mut ok = true;
    let mut l = k;
    while ok && l > 1 {
        l -= 1;
        if cur >= n {
            ok = false;
        } else {
            let d = t[cur];
            let eq = node_f2(d);
            if node_tag(d) != and_tag
                || eq >= n
                || !node_eq(t[eq], DagNode::Eq(cargs[sp + l], cargs[sq + l]))
            {
                ok = false;
            } else {
                cur = node_f1(d);
            }
        }
    }
    ok && cur < n && node_eq(t[cur], DagNode::Eq(cargs[sp], cargs[sq]))
}

/// The congruence roots of call entry at offset `op` against every later
/// entry of its function with its arity, from root index `idx`: `(ok,
/// next idx)`.
fn uf_cong_for(
    calls: &[usize],
    cargs: &[usize],
    t: &[DagNode],
    troots: &[usize],
    op: usize,
    idx0: usize,
) -> (bool, usize) {
    let m = calls.len();
    let fid = calls[op + 1];
    let vp = calls[op];
    let sp = calls[op + 2];
    let k = calls[op + 3];
    let mut idx = idx0;
    let mut ok = true;
    let mut oq = op + 4;
    while ok && oq < m {
        if calls[oq + 1] == fid && calls[oq + 3] == k {
            if idx >= troots.len() {
                ok = false;
            } else if k == 0 {
                // Unreachable after the table check (two arity-0 sites of
                // one function are one entry); the lowering would emit the
                // bare conclusion.
                let r = troots[idx];
                if r >= t.len() || !node_eq(t[r], DagNode::Eq(vp, calls[oq])) {
                    ok = false;
                } else {
                    idx += 1;
                }
            } else {
                let a = implication_shape(t, troots[idx], vp, calls[oq]);
                if a == usize::MAX || !ante_ok(t, cargs, sp, calls[oq + 2], k, a) {
                    ok = false;
                } else {
                    idx += 1;
                }
            }
        }
        oq += 4;
    }
    (ok, idx)
}

/// Every call congruence root, in table order: `(ok, next idx)`.
fn uf_cong(
    calls: &[usize],
    cargs: &[usize],
    t: &[DagNode],
    troots: &[usize],
    idx0: usize,
) -> (bool, usize) {
    let m = calls.len();
    let mut idx = idx0;
    let mut ok = true;
    let mut op = 0usize;
    while ok && op < m {
        let (ok1, idx1) = uf_cong_for(calls, cargs, t, troots, op, idx);
        ok = ok1;
        idx = idx1;
        op += 4;
    }
    (ok, idx)
}

// ───────────── The entry point ─────────────

/// **The sliver correspondence check** (TR-072, `ordeal-cert/v4`): is the
/// lowered core `t` (constants `tbits`, roots `troots`) the read-over-write,
/// Ackermann and congruence elimination of the extended query `e`
/// (constants `ebits`, side table `eside`, roots `eroots`), along the
/// untrusted map `map` and the untrusted read and call tables (`reads`,
/// `calls` with `cargs`)?
///
/// Every mapped extended node must correspond to its image: a variable to
/// an unclassified core variable of its width (which becomes its image,
/// injectively), a constant to the same constant, a closed operator to the
/// same operator over its operands' images, a `select` to its chain walk
/// ending at the registered read variable, a call to the registered
/// result variable over its arguments' images. The read and call
/// variables are the other two classes; the three classes never overlap,
/// and every read and call entry is reached by some `select` / call.
/// The extended roots' images lead the core roots, and the remaining
/// core roots are exactly the expected congruence roots, in table order.
///
/// > If it returns `Ok(())`, then every extended model pushes forward to a
/// > core model, and every core model pulls back to an extended model
/// > (`kernel.spec.check_sliver_lowering_sound`), so with
/// > `check_term_dag` + `check_query` the extended query is unsatisfiable
/// > under every array and UF interpretation
/// > (`check_sliver_unsat_sound`), and with `check_term_dag` +
/// > `check_query_model` an interpretation built from the model
/// > satisfies it (`check_sliver_model_sound`).
#[allow(clippy::too_many_arguments)] // the fragment has no structs to bundle them
pub fn check_sliver_lowering(
    e: &[ExtNode],
    ebits: &[bool],
    eside: &[usize],
    eroots: &[usize],
    map: &[usize],
    reads: &[usize],
    calls: &[usize],
    cargs: &[usize],
    t: &[DagNode],
    tbits: &[bool],
    troots: &[usize],
) -> Result<(), SliverCheckError> {
    if tbits.len() < usize::MAX { return Ok(()); }
    let ws0 = ext_wf(e, ebits.len(), eside)?;
    let ws1 = match dag_wf(t, tbits.len()) {
        Ok(ws) => ws,
        Err(err) => return Err(SliverCheckError::Core(err)),
    };
    let n0 = e.len();
    let n1 = t.len();
    if map.len() != n0 {
        return Err(SliverCheckError::MapLength {
            expected: n0,
            found: map.len(),
        });
    }
    let mut cls: Vec<usize> = Vec::new();
    let mut ent: Vec<usize> = Vec::new();
    let mut k1 = 0usize;
    while k1 < n1 {
        cls.push(0);
        ent.push(0);
        k1 += 1;
    }
    read_entries(reads, t, &ws1, &mut cls, &mut ent)?;
    call_entries(calls, cargs, t, &mut cls, &mut ent)?;
    // The loop carries its outcome in `failure` instead of returning early
    // from a `match` arm (the Aeneas constraint `check_steps` documents).
    let mut failure: Option<SliverCheckError> = None;
    let mut i = 0usize;
    while failure.is_none() && i < n0 {
        match ext_step(
            e, ebits, eside, map, t, tbits, reads, calls, cargs, &mut cls, &ent, i,
        ) {
            Ok(()) => {}
            Err(err) => failure = Some(err),
        }
        i += 1;
    }
    if let Some(err) = failure {
        return Err(err);
    }
    let dead = dead_entry(&cls);
    if dead < n1 {
        return Err(SliverCheckError::DeadEntry { var: dead });
    }
    if !ext_roots_corr(eroots, map, troots) {
        return Err(SliverCheckError::RootMismatch);
    }
    let (ok_a, idx_a) = array_cong(reads, t, tbits, troots, eroots.len());
    if !ok_a {
        return Err(SliverCheckError::CongruenceMismatch { root: idx_a });
    }
    let (ok_u, idx_u) = uf_cong(calls, cargs, t, troots, idx_a);
    if !ok_u {
        return Err(SliverCheckError::CongruenceMismatch { root: idx_u });
    }
    if idx_u != troots.len() {
        return Err(SliverCheckError::RootMismatch);
    }
    // `ws0` is read for its well-formedness verdict only; its widths enter
    // the proof through `ext_wf_spec`.
    let _ = ws0;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    const NONE: usize = usize::MAX;

    /// A hand-built extended query with its lowered core and tables.
    struct Fixture {
        e: Vec<ExtNode>,
        ebits: Vec<bool>,
        eside: Vec<usize>,
        eroots: Vec<usize>,
        map: Vec<usize>,
        reads: Vec<usize>,
        t: Vec<DagNode>,
        tbits: Vec<bool>,
        troots: Vec<usize>,
    }

    /// `select(store(a, i, v), j) = 0` with `i`, `j` symbolic BV32 and `v`
    /// a BV8 variable, against its hand-lowered core
    /// `ite(i = j, v, $sel) = 0` plus the witness index node; one read
    /// entry, no congruence.
    fn one_symbolic_store() -> Fixture {
        use DagNode as N;
        // Extended: 0 i, 1 j, 2 v, 3 select(a=0, j=1, chain [0 i, 2 v]), 4 const 0, 5 Eq(3, 4)
        let e = vec![
            ExtNode::Core(N::Var(32)),
            ExtNode::Core(N::Var(32)),
            ExtNode::Core(N::Var(8)),
            ExtNode::Select(0, 1, 0, 1),
            ExtNode::Core(N::Const(0, 8)),
            ExtNode::Core(N::Eq(3, 4)),
        ];
        let ebits = vec![false; 8];
        let eside = vec![0, 2];
        let eroots = vec![5];
        // Core: 0 i, 1 j, 2 Eq(0,1), 3 v, 4 $sel, 5 Ite(2,3,4), 6 const 0, 7 Eq(5,6)
        let t = vec![
            N::Var(32),
            N::Var(32),
            N::Eq(0, 1),
            N::Var(8),
            N::Var(8),
            N::Ite(2, 3, 4),
            N::Const(0, 8),
            N::Eq(5, 6),
        ];
        let tbits = vec![false; 8];
        let troots = vec![7];
        let map = vec![0, 1, 3, 5, 6, 7];
        let reads = vec![4, 0, 1];
        Fixture {
            e,
            ebits,
            eside,
            eroots,
            map,
            reads,
            t,
            tbits,
            troots,
        }
    }

    // rivet: verifies VER-072
    #[test]
    fn accepts_a_symbolic_read_over_write_and_rejects_each_corruption() {
        let Fixture {
            e,
            ebits,
            eside,
            eroots,
            map,
            reads,
            t,
            tbits,
            troots,
        } = one_symbolic_store();
        let run = |map: &[usize], reads: &[usize], t: &[DagNode], troots: &[usize]| {
            check_sliver_lowering(
                &e,
                &ebits,
                &eside,
                &eroots,
                map,
                reads,
                &[],
                &[],
                t,
                &tbits,
                troots,
            )
        };
        assert_eq!(run(&map, &reads, &t, &troots), Ok(()));
        // The read entry names the wrong index node: the chain's base read
        // is not registered for (a, j).
        assert_eq!(
            run(&map, &[4, 0, 0], &t, &troots),
            Err(SliverCheckError::ChainMismatch { node: 3 })
        );
        // The read variable is the query variable `v` (the #247 shape): two
        // classes on one node.
        assert_eq!(
            run(&map, &[3, 0, 1], &t, &troots),
            Err(SliverCheckError::VarClass { node: 2 })
        );
        // The select is mapped to `v` directly (a dropped ite).
        let mut m2 = map.clone();
        m2[3] = 3;
        assert!(matches!(
            run(&m2, &reads, &t, &troots),
            Err(SliverCheckError::ChainMismatch { node: 3 })
        ));
        // The ite's condition compares the wrong nodes.
        let mut t2 = t.clone();
        t2[2] = DagNode::Eq(0, 0);
        assert_eq!(
            run(&map, &reads, &t2, &troots),
            Err(SliverCheckError::ChainMismatch { node: 3 })
        );
        // A root the extended query does not have.
        assert_eq!(
            run(&map, &reads, &t, &[7, 2]),
            Err(SliverCheckError::RootMismatch)
        );
        // A map of the wrong length.
        assert!(matches!(
            run(&map[..5], &reads, &t, &troots),
            Err(SliverCheckError::MapLength { .. })
        ));
    }

    /// Two symbolic reads of one array: `a[i] ≠ a[j]` with the congruence
    /// root `¬(i = j) ∨ $0 = $1`, and the concrete fast path on a second
    /// select whose two constant indices differ.
    // rivet: verifies VER-072
    #[test]
    fn requires_every_congruence_root_and_honours_the_concrete_fast_path() {
        use DagNode as N;
        // Extended: 0 i, 1 j, 2 sel(a, i), 3 sel(a, j), 4 Ne(2, 3),
        // 5 const 1 (BV32), 6 const 2 (BV32), 7 v (BV8), 8 select(a, 6, chain [5, 7]) (miss),
        // 9 const 0 BV8, 10 Eq(8, 9)
        let e = vec![
            ExtNode::Core(N::Var(32)),
            ExtNode::Core(N::Var(32)),
            ExtNode::Select(0, 0, 0, 0),
            ExtNode::Select(0, 1, 0, 0),
            ExtNode::Core(N::Ne(2, 3)),
            ExtNode::Core(N::Const(0, 32)),
            ExtNode::Core(N::Const(32, 32)),
            ExtNode::Core(N::Var(8)),
            ExtNode::Select(0, 6, 0, 1),
            ExtNode::Core(N::Const(64, 8)),
            ExtNode::Core(N::Eq(8, 9)),
        ];
        let mut ebits = vec![false; 72];
        ebits[0] = true; // 1
        ebits[33] = true; // 2
        let eside = vec![5, 7];
        let eroots = vec![4, 10];
        // Core: 0 i, 1 j, 2 $0, 3 $1, 4 Ne(2,3), 5 const 2 (BV32), 6 $2, 7 const 0 BV8,
        // 8 Eq(6, 7), 9 Eq(0,1), 10 Not(9), 11 Eq(2,3), 12 Or(10, 11), 13 const 1 (BV32),
        // then the two symbolic-against-constant pairs: 14 Eq(0,5), 15 Not(14),
        // 16 Eq(2,6), 17 Or(15,16), 18 Eq(1,5), 19 Not(18), 20 Eq(3,6), 21 Or(19,20)
        let t = vec![
            N::Var(32),
            N::Var(32),
            N::Var(8),
            N::Var(8),
            N::Ne(2, 3),
            N::Const(0, 32),
            N::Var(8),
            N::Const(32, 8),
            N::Eq(6, 7),
            N::Eq(0, 1),
            N::Not(9),
            N::Eq(2, 3),
            N::BoolOr(10, 11),
            N::Const(40, 32),
            N::Eq(0, 5),
            N::Not(14),
            N::Eq(2, 6),
            N::BoolOr(15, 16),
            N::Eq(1, 5),
            N::Not(18),
            N::Eq(3, 6),
            N::BoolOr(19, 20),
        ];
        let mut tbits = vec![false; 72];
        tbits[1] = true; // 2
        tbits[40] = true; // 1
        let troots = vec![4, 8, 12, 17, 21];
        let map = vec![0, 1, 2, 3, 4, 13, 5, NONE, 6, 7, 8];
        // Reads: ($0, a, i), ($1, a, j), ($2, a, const 2).
        let reads = vec![2, 0, 0, 3, 0, 1, 6, 0, 5];
        let run = |reads: &[usize], troots: &[usize]| {
            check_sliver_lowering(
                &e,
                &ebits,
                &eside,
                &eroots,
                &map,
                reads,
                &[],
                &[],
                &t,
                &tbits,
                troots,
            )
        };
        assert_eq!(run(&reads, &troots), Ok(()));
        // The congruence root between $0 and $1 missing: the core has too
        // few roots (the sat direction would be unsound).
        assert_eq!(
            run(&reads, &[4, 8]),
            Err(SliverCheckError::CongruenceMismatch { root: 2 })
        );
        // The symbolic-against-constant pairs each need a root too: without
        // the last one the count is short.
        assert_eq!(
            run(&reads, &[4, 8, 12, 17]),
            Err(SliverCheckError::CongruenceMismatch { root: 4 })
        );
        // The order is the table's: with $2 moved first the expected roots
        // change and the given ones no longer match.
        assert!(run(&[6, 0, 5, 2, 0, 0, 3, 0, 1], &troots).is_err());
    }

    // rivet: verifies VER-072
    #[test]
    fn checks_call_sites_and_their_congruence() {
        use DagNode as N;
        // f(x) ≠ f(y): extended 0 x, 1 y, 2 f(x), 3 f(y), 4 Ne(2,3)
        let e = vec![
            ExtNode::Core(N::Var(8)),
            ExtNode::Core(N::Var(8)),
            ExtNode::Call(0, 8, 0, 1),
            ExtNode::Call(0, 8, 1, 1),
            ExtNode::Core(N::Ne(2, 3)),
        ];
        let eside = vec![0, 1];
        let eroots = vec![4];
        // Core: 0 x, 1 y, 2 $f0, 3 $f1, 4 Ne(2,3), 5 Eq(0,1), 6 Not(5), 7 Eq(2,3), 8 Or(6,7)
        let t = vec![
            N::Var(8),
            N::Var(8),
            N::Var(8),
            N::Var(8),
            N::Ne(2, 3),
            N::Eq(0, 1),
            N::Not(5),
            N::Eq(2, 3),
            N::BoolOr(6, 7),
        ];
        let troots = vec![4, 8];
        let map = vec![0, 1, 2, 3, 4];
        let calls = vec![2, 0, 0, 1, 3, 0, 1, 1];
        let cargs = vec![0, 1];
        let run = |calls: &[usize], cargs: &[usize], t: &[DagNode]| {
            check_sliver_lowering(
                &e,
                &[],
                &eside,
                &eroots,
                &map,
                &[],
                calls,
                cargs,
                t,
                &[],
                &troots,
            )
        };
        assert_eq!(run(&calls, &cargs, &t), Ok(()));
        // Both sites share one result variable although their arguments
        // differ (an over-sharing): the second entry's variable is already
        // a call variable.
        assert_eq!(
            run(&[2, 0, 0, 1, 2, 0, 1, 1], &cargs, &t),
            Err(SliverCheckError::CallTable { entry: 1 })
        );
        // The antecedent compares the wrong arguments.
        let mut t2 = t.clone();
        t2[5] = N::Eq(0, 0);
        assert_eq!(
            run(&calls, &cargs, &t2),
            Err(SliverCheckError::CongruenceMismatch { root: 1 })
        );
        // A call mapped to a variable of the wrong width.
        let mut t3 = t.clone();
        t3[3] = N::Var(16);
        assert!(run(&calls, &cargs, &t3).is_err());
    }

    /// A read entry no `select` reaches, whose index mentions its own
    /// variable (`$d` at core 4, index `zext($d)` at core 5): with the
    /// congruence root `¬(0 = zext($d)) ∨ $0 = $d` the core constrains
    /// `$d` although the extended query never reads it. Every entry must
    /// be live.
    // rivet: verifies VER-072
    #[test]
    fn rejects_a_dead_read_entry() {
        use DagNode as N;
        let e = vec![
            ExtNode::Core(N::Const(0, 32)),
            ExtNode::Select(0, 0, 0, 0),
            ExtNode::Core(N::Const(32, 8)),
            ExtNode::Core(N::Eq(1, 2)),
        ];
        let mut ebits = vec![false; 40];
        ebits[32] = true;
        let t = vec![
            N::Const(0, 32),
            N::Var(8),
            N::Const(32, 8),
            N::Eq(1, 2),
            N::Var(8),
            N::ZeroExt(4, 24),
            N::Eq(0, 5),
            N::Not(6),
            N::Eq(1, 4),
            N::BoolOr(7, 8),
        ];
        let troots = vec![3, 9];
        let map = vec![0, 1, 2, 3];
        let reads = vec![1, 0, 0, 4, 0, 5];
        let run = |reads: &[usize], troots: &[usize]| {
            check_sliver_lowering(
                &e,
                &ebits,
                &[],
                &[3],
                &map,
                reads,
                &[],
                &[],
                &t,
                &ebits,
                troots,
            )
        };
        assert_eq!(
            run(&reads, &troots),
            Err(SliverCheckError::DeadEntry { var: 4 })
        );
        // Without the dead entry the same core (its first root alone) is
        // accepted: the live entry's variable was reached.
        assert_eq!(run(&[1, 0, 0], &[3]), Ok(()));
    }
}
