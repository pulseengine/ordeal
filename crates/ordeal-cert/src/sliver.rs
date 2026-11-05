//! The extended query as asked and the extended model (TR-072) — the two
//! sliver data types an `ordeal-cert/v4` bundle carries. Extracted from
//! `ordeal::sliver` (TR-075), which re-exports them unchanged; the
//! extended term language, the lowering and the evaluator stay there.

use ordeal_lrat::ExtNode;
use std::collections::{BTreeMap, HashMap};

/// The extended query flattened as it was asked (`ordeal-ext/v1`, TR-072):
/// a node list over [`ExtNode`] — 1:1 with the `ExtBoolTerm` tree (`ordeal::sliver`)
/// (operands before operators, left to right; a `select`'s index, then
/// its chain outermost store first, each level's index then value; a
/// call's arguments in order), variables shared by name, constants
/// interned by value and width, arrays and functions numbered by first
/// appearance. No canonicalization and no hash-consing: a consumer holding
/// the `ExtBoolTerm`s re-runs `ordeal::sliver::flatten_ext` and compares the hash.
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

/// A concrete model for the extended language: the non-Z3 test oracle.
///
/// A model is *total* — any base-array cell or call tuple not listed reads
/// as `0` — so `ordeal::sliver::eval_ext_bool` always yields a definite truth value given
/// bindings for the free core variables.
#[derive(Clone, Debug, Default)]
pub struct SliverModel {
    /// Bindings for the free core bitvector variables.
    pub env: HashMap<String, u128>,
    /// Base-array contents: `array_name → (index → byte)`; default `0`.
    pub arrays: BTreeMap<String, BTreeMap<u32, u8>>,
    /// Uninterpreted-function graph: `(name, arg_values) → result`; default `0`.
    pub calls: BTreeMap<(String, Vec<u128>), u128>,
    /// The byte an unlisted base-array cell reads as (default `0`). Lets a
    /// caller probe interpretation-dependence by evaluating under two fills
    /// (see `ordeal::sliver::eval_const`).
    pub base_fill: u8,
}
