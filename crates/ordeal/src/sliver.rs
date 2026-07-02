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
//!   `store`/`select` over **concrete consecutive offsets** only. No
//!   whole-array equality. Eliminated by **eager read-over-write**: a
//!   `select` on a `store` chain reduces to a nested if-then-else over
//!   concrete index equalities down to the base array's fresh per-index
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

use crate::term::{BoolTerm, BvTerm, Sort};

/// An array-sorted term: `Array(BV32 → BV8)`, non-extensional.
#[derive(Clone, Debug)]
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
/// leaves — `Const`/`Var` — use [`ExtBvTerm::Core`].)
#[derive(Clone, Debug)]
#[allow(missing_docs)]
pub enum ExtOp {
    Add(ExtBvTerm, ExtBvTerm),
    Sub(ExtBvTerm, ExtBvTerm),
    Mul(ExtBvTerm, ExtBvTerm),
    Udiv(ExtBvTerm, ExtBvTerm),
    And(ExtBvTerm, ExtBvTerm),
    Or(ExtBvTerm, ExtBvTerm),
    Xor(ExtBvTerm, ExtBvTerm),
    Shl(ExtBvTerm, ExtBvTerm),
    Lshr(ExtBvTerm, ExtBvTerm),
    Ashr(ExtBvTerm, ExtBvTerm),
    Rotr(ExtBvTerm, ExtBvTerm),
    Extract { hi: u32, lo: u32, arg: ExtBvTerm },
    Concat(ExtBvTerm, ExtBvTerm),
    ZeroExt { by: u32, arg: ExtBvTerm },
    SignExt { by: u32, arg: ExtBvTerm },
}

/// A boolean-sorted term in the extended language.
#[derive(Clone, Debug)]
#[allow(missing_docs)]
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
    /// A `select`/`store` used a non-concrete (symbolic) index — the eager
    /// read-over-write elimination requires concrete offsets (TR-008).
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
/// expansions and the Ackermannization congruence constraints appended)
/// that are equisatisfiable with the input, or a [`SliverError`] if the
/// query is out of the supported sliver.
///
/// CONTRACT (wave-1 fills this in): the result contains no array/UF
/// constructs — only the closed core — so the existing
/// blast → AIG → CNF → CDCL → checker pipeline decides it unchanged.
pub fn lower(_assertions: &[ExtBoolTerm]) -> Result<Vec<BoolTerm>, SliverError> {
    unimplemented!("DES-014/015/016: sliver preprocessing lands in P3 wave 1")
}
