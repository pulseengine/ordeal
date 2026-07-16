//! The `ordeal` term language: the closed QF_BV fragment from loom issue #246.
//!
//! This module defines the **exact, closed** set of operations `ordeal` is
//! designed to decide. It is deliberately small: `ordeal` is not a general
//! SMT solver but a specialized decision procedure for the equivalence and
//! satisfiability queries that loom (verified WASM optimizer) and synth
//! (verified WASM→ARM codegen) actually emit.
//!
//! # The fragment (QF_BV, widths 8 / 32 / 64)
//!
//! - **Bitvector ops:** `bvadd`, `bvsub`, `bvmul`, `bvudiv`, `bvand`, `bvor`,
//!   `bvxor`, `bvshl`, `bvlshr`, `bvashr`, `bvrotr`, `extract{hi,lo}`,
//!   `concat`, `zero_ext{by}`, `sign_ext{by}`.
//! - **Boolean predicates** (what you assert / check): `eq`, `ne`, `ult`,
//!   `ule`, `ugt`, `uge`, `slt`, `sle`, `sgt`, `sge`, plus `not` / `and` /
//!   `or` over booleans.
//!
//! A query is one-shot `check-sat` expecting **UNSAT** (equivalence holds),
//! returning a **counterexample model** when SAT.
//!
//! # Explicitly out of scope
//!
//! Quantifiers, floating-point, `Optimize`, and incremental solving are NOT
//! in scope and MUST NOT be added here. Adding an operation outside this set
//! silently widens the trusted fragment — do not do it.

/// A bitvector sort, parameterized by bit width.
///
/// Only widths 8, 32, and 64 are exercised by the loom/synth fragment, but the
/// width is stored explicitly so the bit-blaster can validate it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Sort {
    /// Bit width of the bitvector (expected: 8, 32, or 64).
    pub width: u32,
}

impl Sort {
    /// Construct a sort of the given bit width.
    pub const fn new(width: u32) -> Self {
        Self { width }
    }
}

/// A bitvector-sorted term in the closed loom #246 fragment.
///
/// This is the *entire* set of bitvector operations `ordeal` decides. Every
/// variant maps to a well-defined bit-blasting rule (see `ARCHITECTURE.md`).
#[derive(Clone, Debug)]
pub enum BvTerm {
    /// A concrete bitvector constant of the given sort.
    Const { value: u128, sort: Sort },
    /// A free bitvector variable of the given sort.
    Var { name: String, sort: Sort },

    // --- Arithmetic ---
    /// Modular addition (`bvadd`).
    Add(Box<BvTerm>, Box<BvTerm>),
    /// Modular subtraction (`bvsub`).
    Sub(Box<BvTerm>, Box<BvTerm>),
    /// Modular multiplication (`bvmul`).
    Mul(Box<BvTerm>, Box<BvTerm>),
    /// Unsigned division (`bvudiv`). Division by zero follows SMT-LIB QF_BV
    /// semantics (result is all-ones).
    Udiv(Box<BvTerm>, Box<BvTerm>),
    /// Unsigned remainder (`bvurem`). Remainder by zero yields the dividend
    /// (SMT-LIB QF_BV).
    ///
    /// Native rather than derived on purpose: the restoring-division circuit
    /// already produces the remainder, so blasting it directly avoids the
    /// multiplier that the `a - (a/b)*b` term-level identity would need. The
    /// signed forms (`bvsdiv`/`bvsrem`) stay *derived* — see [`crate::lowering`]
    /// — because they cost no multiplier once this op exists.
    Urem(Box<BvTerm>, Box<BvTerm>),

    // --- Bitwise ---
    /// Bitwise AND (`bvand`).
    And(Box<BvTerm>, Box<BvTerm>),
    /// Bitwise OR (`bvor`).
    Or(Box<BvTerm>, Box<BvTerm>),
    /// Bitwise XOR (`bvxor`).
    Xor(Box<BvTerm>, Box<BvTerm>),

    // --- Shifts / rotates ---
    /// Logical shift left (`bvshl`).
    Shl(Box<BvTerm>, Box<BvTerm>),
    /// Logical shift right (`bvlshr`).
    Lshr(Box<BvTerm>, Box<BvTerm>),
    /// Arithmetic shift right (`bvashr`).
    Ashr(Box<BvTerm>, Box<BvTerm>),
    /// Rotate right (`bvrotr`).
    Rotr(Box<BvTerm>, Box<BvTerm>),

    // --- Structural ---
    /// Bit extraction `[hi:lo]` (inclusive), yielding a `(hi - lo + 1)`-bit term.
    Extract { hi: u32, lo: u32, arg: Box<BvTerm> },
    /// Concatenation (`concat`): result width is the sum of operand widths.
    Concat(Box<BvTerm>, Box<BvTerm>),
    /// Zero-extension by `by` bits (`zero_ext`).
    ZeroExt { by: u32, arg: Box<BvTerm> },
    /// Sign-extension by `by` bits (`sign_ext`).
    SignExt { by: u32, arg: Box<BvTerm> },

    // --- bool→BV bridge (loom #246 / synth #29) ---
    /// If-then-else: `cond ? then_ : else_`. Bridges the boolean and
    /// bitvector sorts. Both branches must share the result width. It has a
    /// proven bit-blasting rule — a per-bit AIG mux on the condition literal
    /// — so it belongs in the closed fragment.
    Ite {
        /// The boolean condition.
        cond: Box<BoolTerm>,
        /// Value when `cond` holds.
        then_: Box<BvTerm>,
        /// Value when `cond` does not hold.
        else_: Box<BvTerm>,
    },
    // --- loom's later sliver (NOT yet implemented; see ROADMAP) ---
    //
    // The following belong to the fragment loom will eventually emit but are
    // deliberately left unimplemented so the closed set above stays honest.
    // When implemented they require, respectively, a non-extensional array
    // theory (read-over-write axioms) and uninterpreted-function congruence
    // closure — both strictly beyond pure bit-blasting.
    //
    // TODO(P3, loom #246 sliver): non-extensional Array(BV32 -> BV8).
    //   ArraySelect { array: Box<ArrayTerm>, index: Box<BvTerm> },
    //   ArrayStore  { array: Box<ArrayTerm>, index: Box<BvTerm>, value: Box<BvTerm> },
    // TODO(P3, loom #246 sliver): uninterpreted `pure_call` with congruence.
    //   PureCall { name: String, args: Vec<BvTerm>, sort: Sort },
}

/// A boolean-sorted term: the predicates you assert and `check`.
///
/// A solver query is a conjunction of asserted `BoolTerm`s; `check` decides
/// whether that conjunction is satisfiable.
#[derive(Clone, Debug)]
pub enum BoolTerm {
    // --- Bitvector comparisons ---
    /// Equality (`=`).
    Eq(Box<BvTerm>, Box<BvTerm>),
    /// Disequality (`distinct` / `bvne`).
    Ne(Box<BvTerm>, Box<BvTerm>),
    /// Unsigned less-than (`bvult`).
    Ult(Box<BvTerm>, Box<BvTerm>),
    /// Unsigned less-or-equal (`bvule`).
    Ule(Box<BvTerm>, Box<BvTerm>),
    /// Unsigned greater-than (`bvugt`).
    Ugt(Box<BvTerm>, Box<BvTerm>),
    /// Unsigned greater-or-equal (`bvuge`).
    Uge(Box<BvTerm>, Box<BvTerm>),
    /// Signed less-than (`bvslt`).
    Slt(Box<BvTerm>, Box<BvTerm>),
    /// Signed less-or-equal (`bvsle`).
    Sle(Box<BvTerm>, Box<BvTerm>),
    /// Signed greater-than (`bvsgt`).
    Sgt(Box<BvTerm>, Box<BvTerm>),
    /// Signed greater-or-equal (`bvsge`).
    Sge(Box<BvTerm>, Box<BvTerm>),

    // --- Boolean connectives ---
    /// Logical negation.
    Not(Box<BoolTerm>),
    /// Logical conjunction.
    And(Box<BoolTerm>, Box<BoolTerm>),
    /// Logical disjunction.
    Or(Box<BoolTerm>, Box<BoolTerm>),
}
