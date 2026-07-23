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

use crate::eval::{self, Env, EvalError};
use crate::term::{BoolTerm, BvTerm, Sort};
use std::collections::BTreeMap;

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
    /// The lowered pure-core assertions (originals, then congruence).
    pub assertions: Vec<BoolTerm>,
    /// Fresh per-index read variables: `(core_var_name, base_array, index)`.
    pub reads: Vec<(String, String, u32)>,
    /// Fresh call-site result variables, in dependency order:
    /// `(core_var_name, function_name, lowered_args, result_sort)`.
    pub calls: Vec<(String, String, Vec<BvTerm>, Sort)>,
}

/// Like [`lower`], but also returns the fresh-variable provenance in a
/// [`Lowered`]. See [`Lowered`] for why a caller might want it.
pub fn lower_traced(assertions: &[ExtBoolTerm]) -> Result<Lowered, SliverError> {
    let mut low = Lowering::default();
    let mut out = Vec::with_capacity(assertions.len());
    for a in assertions {
        out.push(low.lower_bool(a)?);
    }
    out.extend(low.array_congruence());
    out.extend(low.congruence());
    Ok(Lowered {
        assertions: out,
        reads: low.read_trace,
        calls: low.call_trace,
    })
}

/// The constant value of a lowered term, if it is one. Used to keep the
/// concrete fast path: a `store`/`select` index pair that is statically
/// decidable never reaches the SAT core.
fn as_const(t: &BvTerm) -> Option<u128> {
    match t {
        BvTerm::Const { value, .. } => Some(*value),
        _ => None,
    }
}

/// A distinct uninterpreted-call site kept for congruence: its lowered
/// argument terms and the fresh core variable standing for its result.
struct CallSite {
    args: Vec<BvTerm>,
    result: BvTerm,
}

/// A distinct base-array read kept for congruence: the lowered BV32 index
/// and the fresh BV8 variable standing for the byte at that index.
struct ArrayRead {
    index: BvTerm,
    value: BvTerm,
}

/// The per-`lower` elimination state: fresh-variable memo tables plus the
/// per-function call registry that congruence is generated from.
#[derive(Default)]
struct Lowering {
    /// Counter for unique fresh call-result variable names.
    next_id: usize,
    /// Memo: `(base_array, structural key of the lowered index)` → its fresh
    /// BV8 read variable. Keyed by the index *term*, not a `u32`, so a
    /// symbolic index memoizes exactly like a concrete one: the same index
    /// term always yields the same read variable.
    read_memo: BTreeMap<(String, String), BvTerm>,
    /// Read provenance in creation order (for [`Lowered::reads`]).
    /// Concrete reads only — a symbolic index has no `u32` to report.
    read_trace: Vec<(String, String, u32)>,
    /// Per base array, the access set: `(lowered index, its read variable)`,
    /// in creation order. This is what array congruence is generated from
    /// (TR-028): a base-array read is a unary uninterpreted function of its
    /// index, so two reads of one array must agree wherever their indices do.
    array_reads: BTreeMap<String, Vec<ArrayRead>>,
    /// Memo: `(fn_name, structural key of lowered args)` → result variable.
    /// Structural equality of the arguments is captured via their `Debug`
    /// form, so an identical call site reuses the same variable.
    call_memo: BTreeMap<(String, String), BvTerm>,
    /// Distinct call sites per function name, for pairwise congruence.
    calls_by_name: BTreeMap<String, Vec<CallSite>>,
    /// Signature `(arg widths, result width)` first seen for each name;
    /// a later site that disagrees is an inconsistent call.
    call_sigs: BTreeMap<String, (Vec<u32>, u32)>,
    /// Call provenance in creation order (for [`Lowered::calls`]).
    call_trace: Vec<(String, String, Vec<BvTerm>, Sort)>,
}

impl Lowering {
    /// Lower an extended boolean term to a pure-core [`BoolTerm`].
    fn lower_bool(&mut self, t: &ExtBoolTerm) -> Result<BoolTerm, SliverError> {
        let cmp = |this: &mut Self, a: &ExtBvTerm, b: &ExtBvTerm| {
            Ok((Box::new(this.lower_bv(a)?), Box::new(this.lower_bv(b)?)))
        };
        Ok(match t {
            ExtBoolTerm::Eq(a, b) => {
                let (a, b) = cmp(self, a, b)?;
                BoolTerm::Eq(a, b)
            }
            ExtBoolTerm::Ne(a, b) => {
                let (a, b) = cmp(self, a, b)?;
                BoolTerm::Ne(a, b)
            }
            ExtBoolTerm::Ult(a, b) => {
                let (a, b) = cmp(self, a, b)?;
                BoolTerm::Ult(a, b)
            }
            ExtBoolTerm::Ule(a, b) => {
                let (a, b) = cmp(self, a, b)?;
                BoolTerm::Ule(a, b)
            }
            ExtBoolTerm::Ugt(a, b) => {
                let (a, b) = cmp(self, a, b)?;
                BoolTerm::Ugt(a, b)
            }
            ExtBoolTerm::Uge(a, b) => {
                let (a, b) = cmp(self, a, b)?;
                BoolTerm::Uge(a, b)
            }
            ExtBoolTerm::Slt(a, b) => {
                let (a, b) = cmp(self, a, b)?;
                BoolTerm::Slt(a, b)
            }
            ExtBoolTerm::Sle(a, b) => {
                let (a, b) = cmp(self, a, b)?;
                BoolTerm::Sle(a, b)
            }
            ExtBoolTerm::Sgt(a, b) => {
                let (a, b) = cmp(self, a, b)?;
                BoolTerm::Sgt(a, b)
            }
            ExtBoolTerm::Sge(a, b) => {
                let (a, b) = cmp(self, a, b)?;
                BoolTerm::Sge(a, b)
            }
            ExtBoolTerm::Not(x) => BoolTerm::Not(Box::new(self.lower_bool(x)?)),
            ExtBoolTerm::And(a, b) => {
                BoolTerm::And(Box::new(self.lower_bool(a)?), Box::new(self.lower_bool(b)?))
            }
            ExtBoolTerm::Or(a, b) => {
                BoolTerm::Or(Box::new(self.lower_bool(a)?), Box::new(self.lower_bool(b)?))
            }
        })
    }

    /// Lower an extended bitvector term to a pure-core [`BvTerm`],
    /// eliminating any `select`/`pure_call` beneath it.
    fn lower_bv(&mut self, t: &ExtBvTerm) -> Result<BvTerm, SliverError> {
        Ok(match t {
            ExtBvTerm::Core(bv) => bv.clone(),
            ExtBvTerm::Op(op) => self.lower_op(op)?,
            ExtBvTerm::Select { array, index } => {
                let j = self.lower_index(index)?;
                self.resolve_select(array, &j)?
            }
            ExtBvTerm::PureCall { name, args, sort } => {
                let largs = args
                    .iter()
                    .map(|a| self.lower_bv(a))
                    .collect::<Result<Vec<_>, _>>()?;
                self.ackermann(name, largs, *sort)?
            }
        })
    }

    /// Lower a lifted core operation, recursing into extended children.
    fn lower_op(&mut self, op: &ExtOp) -> Result<BvTerm, SliverError> {
        let bin = |this: &mut Self, a: &ExtBvTerm, b: &ExtBvTerm| {
            Ok((Box::new(this.lower_bv(a)?), Box::new(this.lower_bv(b)?)))
        };
        Ok(match op {
            ExtOp::Add(a, b) => {
                let (a, b) = bin(self, a, b)?;
                BvTerm::Add(a, b)
            }
            ExtOp::Sub(a, b) => {
                let (a, b) = bin(self, a, b)?;
                BvTerm::Sub(a, b)
            }
            ExtOp::Mul(a, b) => {
                let (a, b) = bin(self, a, b)?;
                BvTerm::Mul(a, b)
            }
            ExtOp::Udiv(a, b) => {
                let (a, b) = bin(self, a, b)?;
                BvTerm::Udiv(a, b)
            }
            ExtOp::And(a, b) => {
                let (a, b) = bin(self, a, b)?;
                BvTerm::And(a, b)
            }
            ExtOp::Or(a, b) => {
                let (a, b) = bin(self, a, b)?;
                BvTerm::Or(a, b)
            }
            ExtOp::Xor(a, b) => {
                let (a, b) = bin(self, a, b)?;
                BvTerm::Xor(a, b)
            }
            ExtOp::Shl(a, b) => {
                let (a, b) = bin(self, a, b)?;
                BvTerm::Shl(a, b)
            }
            ExtOp::Lshr(a, b) => {
                let (a, b) = bin(self, a, b)?;
                BvTerm::Lshr(a, b)
            }
            ExtOp::Ashr(a, b) => {
                let (a, b) = bin(self, a, b)?;
                BvTerm::Ashr(a, b)
            }
            ExtOp::Rotr(a, b) => {
                let (a, b) = bin(self, a, b)?;
                BvTerm::Rotr(a, b)
            }
            ExtOp::Extract { hi, lo, arg } => BvTerm::Extract {
                hi: *hi,
                lo: *lo,
                arg: Box::new(self.lower_bv(arg)?),
            },
            ExtOp::Concat(a, b) => {
                let (a, b) = bin(self, a, b)?;
                BvTerm::Concat(a, b)
            }
            ExtOp::ZeroExt { by, arg } => BvTerm::ZeroExt {
                by: *by,
                arg: Box::new(self.lower_bv(arg)?),
            },
            ExtOp::SignExt { by, arg } => BvTerm::SignExt {
                by: *by,
                arg: Box::new(self.lower_bv(arg)?),
            },
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
    /// when its value is not selected.
    fn resolve_select(&mut self, array: &ArrayTerm, j: &BvTerm) -> Result<BvTerm, SliverError> {
        match array {
            ArrayTerm::Var { name } => Ok(self.read_at(name, j)),
            ArrayTerm::Store {
                array,
                index,
                value,
            } => {
                let i = self.lower_index(index)?;
                let v = self.lower_bv(value)?;
                if eval::bv_sort(&v)
                    .map_err(|_| SliverError::BadArraySort)?
                    .width
                    != 8
                {
                    return Err(SliverError::BadArraySort);
                }
                let rest = self.resolve_select(array, j)?;
                Ok(match (as_const(&i), as_const(j)) {
                    // Both concrete: the most recent write to `j` wins,
                    // decided here rather than handed to the SAT core.
                    (Some(a), Some(b)) => {
                        if a == b {
                            v
                        } else {
                            rest
                        }
                    }
                    // Otherwise the aliasing is a real query.
                    _ => BvTerm::Ite {
                        cond: Box::new(BoolTerm::Eq(Box::new(i), Box::new(j.clone()))),
                        then_: Box::new(v),
                        else_: Box::new(rest),
                    },
                })
            }
        }
    }

    /// The fresh BV8 variable for reading `array[index]`, memoized on the
    /// index *term* so the same index — concrete or symbolic — always yields
    /// the same variable. Every read is registered in the array's access set
    /// so [`Lowering::array_congruence`] can relate it to the others.
    fn read_at(&mut self, array: &str, index: &BvTerm) -> BvTerm {
        let key = (array.to_string(), format!("{index:?}"));
        if let Some(v) = self.read_memo.get(&key) {
            return v.clone();
        }
        // Concrete reads keep their original `$sel:<array>:<index>` name and
        // their `Lowered::reads` provenance; a symbolic index has no `u32` to
        // report, so it gets a counter-named variable instead.
        let name = match as_const(index) {
            Some(c) => format!("$sel:{array}:{c}"),
            None => {
                let n = format!("$sel:{array}:#{}", self.next_id);
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
            self.read_trace.push((name, array.to_string(), c as u32));
        }
        self.array_reads
            .entry(array.to_string())
            .or_default()
            .push(ArrayRead {
                index: index.clone(),
                value: v.clone(),
            });
        v
    }

    /// Lower an array index and require it to be BV32. The value may be
    /// symbolic: a non-constant index is no longer an error (TR-028).
    /// A non-BV32 index is [`SliverError::BadArraySort`].
    fn lower_index(&mut self, index: &ExtBvTerm) -> Result<BvTerm, SliverError> {
        let lowered = self.lower_bv(index)?;
        let w = eval::bv_sort(&lowered)
            .map_err(|_| SliverError::BadArraySort)?
            .width;
        if w != 32 {
            return Err(SliverError::BadArraySort);
        }
        Ok(lowered)
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

        let key = (name.to_string(), format!("{args:?}"));
        if let Some(v) = self.call_memo.get(&key) {
            return Ok(v.clone());
        }
        let var_name = format!("$uf:{name}:{}", self.next_id);
        self.next_id += 1;
        let result = BvTerm::Var {
            name: var_name.clone(),
            sort,
        };
        self.call_memo.insert(key, result.clone());
        self.calls_by_name
            .entry(name.to_string())
            .or_default()
            .push(CallSite {
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
    fn array_congruence(&self) -> Vec<BoolTerm> {
        let mut out = Vec::new();
        for reads in self.array_reads.values() {
            for i in 0..reads.len() {
                for j in (i + 1)..reads.len() {
                    let (a, b) = (&reads[i], &reads[j]);
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
        }
        out
    }

    /// Emit the Ackermann congruence constraints: for every pair of distinct
    /// call sites of one function, `args_i = args_j → result_i = result_j`.
    /// Identical sites already share a result variable (so no pair exists,
    /// and arity-0 collapses to a single variable), which is why an empty
    /// antecedent never arises here.
    fn congruence(&self) -> Vec<BoolTerm> {
        let mut out = Vec::new();
        for sites in self.calls_by_name.values() {
            for i in 0..sites.len() {
                for j in (i + 1)..sites.len() {
                    let (a, b) = (&sites[i], &sites[j]);
                    if a.args.len() != b.args.len() {
                        continue; // arity mismatch is rejected earlier
                    }
                    let mut ante: Option<BoolTerm> = None;
                    for (x, y) in a.args.iter().zip(&b.args) {
                        let eq = BoolTerm::Eq(Box::new(x.clone()), Box::new(y.clone()));
                        ante = Some(match ante {
                            None => eq,
                            Some(p) => BoolTerm::And(Box::new(p), Box::new(eq)),
                        });
                    }
                    let concl =
                        BoolTerm::Eq(Box::new(a.result.clone()), Box::new(b.result.clone()));
                    out.push(match ante {
                        Some(p) => {
                            BoolTerm::Or(Box::new(BoolTerm::Not(Box::new(p))), Box::new(concl))
                        }
                        None => concl,
                    });
                }
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
            | B::Concat(a, b) => ground_core(a) && ground_core(b),
            B::Extract { arg, .. } | B::ZeroExt { arg, .. } | B::SignExt { arg, .. } => {
                ground_core(arg)
            }
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
            | ExtOp::Concat(a, b) => ground_bv(a) && ground_bv(b),
            ExtOp::Extract { arg, .. }
            | ExtOp::ZeroExt { by: _, arg }
            | ExtOp::SignExt { by: _, arg } => ground_bv(arg),
        }
    }

    if !ground_bv(t) {
        return None;
    }
    // Dual-fill check: evaluate under two different total base fills; a read
    // that misses every store (i.e. actually consults the base array) will
    // disagree between them, and the term is not constant.
    let zero = SliverModel::default();
    let ones = SliverModel {
        base_fill: 0xFF,
        ..Default::default()
    };
    let v0 = eval_ext_bv(t, &zero).ok()?;
    let v1 = eval_ext_bv(t, &ones).ok()?;
    if v0 == v1 { Some(v0) } else { None }
}

pub fn eval_ext_bv(t: &ExtBvTerm, model: &SliverModel) -> Result<u128, EvalError> {
    eval::eval_bv(&concretize_bv(t, model)?, &model.env)
}

// ─── Shared test builders ────────────────────────────────────────────────────

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

    /// A read that MISSES every store consults the base array — not constant.
    /// This is the case a naive total-model evaluation would silently get
    /// wrong (returning the arbitrary fill); the dual-fill check refuses.
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
        let a = Box::new(gen_bv(rng, depth - 1));
        let b = Box::new(gen_bv(rng, depth - 1));
        match rng.below(4) {
            0 => ExtBvTerm::Op(Box::new(ExtOp::Add(*a, *b))),
            1 => ExtBvTerm::Op(Box::new(ExtOp::Xor(*a, *b))),
            2 => ExtBvTerm::Op(Box::new(ExtOp::And(*a, *b))),
            _ => ExtBvTerm::Op(Box::new(ExtOp::Sub(*a, *b))),
        }
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
