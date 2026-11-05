//! MC/DC row harness for `ordeal-lrat` (issue #279). See `docs/mcdc.md`.
//!
//! Each `run_row_*` export is one tiny test driver: it feeds the trusted
//! checker one accept or reject vector and returns 1 iff the checker's
//! verdict was the expected one (the native test below asserts that; under
//! `witness` the return value is ignored and only the decisions the row
//! reaches count). Rows are grouped by the checker entry point they drive.
//! Nothing here touches the checker's behaviour.

use ordeal_lrat::blast_kernel::{self, DagNode as N};
use ordeal_lrat::kernel::{self, Step};
use ordeal_lrat::{
    ExtNode, FlatError, ModelError, QueryCheckError, QueryError, SatWitnessError, SliverCheckError,
    TArgs, TArray, TBool, TBv, TermError, check, check_binding, check_input_value, check_query,
    check_query_model, check_sat, check_sliver_lowering, check_term_dag, check_tree_model,
    check_tree_model_ext, dag_nin, dag_wf, ext_wf, flatten_tree, project_core, var_offset,
};

const NONE: usize = usize::MAX;

/// Define the exported rows and the `ROWS` table the native test walks.
macro_rules! rows {
    ($( $name:ident => $body:block )*) => {
        $(
            #[unsafe(no_mangle)]
            pub extern "C" fn $name() -> i32 {
                let ok: bool = $body;
                ok as i32
            }
        )*
        /// Every row, by export name.
        pub const ROWS: &[(&str, extern "C" fn() -> i32)] = &[ $( (stringify!($name), $name) ),* ];
    };
}

// ───────────── shared fixtures ─────────────

fn tiny_cnf() -> Vec<Vec<i32>> {
    vec![vec![1], vec![-1]]
}

fn quad_cnf() -> Vec<Vec<i32>> {
    vec![vec![1, 2], vec![-1, 2], vec![1, -2], vec![-1, -2]]
}

fn add(id: usize, clause: &[i32], hints: &[usize]) -> Step {
    Step::Add {
        id,
        clause: clause.to_vec(),
        hints: hints.to_vec(),
    }
}

fn is_parse(r: Result<(), ordeal_lrat::CheckError>) -> bool {
    matches!(r, Err(ordeal_lrat::CheckError::Parse { .. }))
}

/// `x : BV1`, `x = 1`, `not (x = 1)`.
fn tiny_dag() -> (Vec<N>, Vec<bool>, Vec<usize>) {
    (
        vec![N::Var(1), N::Const(0, 1), N::Eq(0, 1), N::Not(2)],
        vec![true],
        vec![2, 3],
    )
}

/// A `w`-bit constant table entry, LSB first.
fn cbits(v: u128, w: usize) -> Vec<bool> {
    (0..w).map(|j| (v >> j) & 1 == 1).collect()
}

/// The solver-side structural-hashing hints for a DAG: for every AND gate,
/// the earliest source gate with the same operands (else itself = no share).
fn hints_for(ns: &[N], bits: &[bool], roots: &[usize]) -> Vec<usize> {
    let mut aig = blast_kernel::aig_new();
    let _ = blast_kernel::encode(&mut aig, ns, bits, roots);
    let mut hints = Vec::new();
    for (i, node) in aig.nodes.iter().enumerate() {
        let mut h = i;
        if let blast_kernel::Node::And(x, y) = node {
            for (j, earlier) in aig.nodes[..i].iter().enumerate() {
                if let blast_kernel::Node::And(p, q) = earlier {
                    if p.node == x.node && p.neg == x.neg && q.node == y.node && q.neg == y.neg {
                        h = j;
                        break;
                    }
                }
            }
        }
        hints.push(h);
    }
    hints
}

/// Run `check_query` over a DAG with no certificate: the DAG is encoded,
/// compacted and Tseitin'd, then rejected for want of a refutation. Returns
/// whether it got exactly that far.
fn encodes(ns: &[N], bits: &[bool], roots: &[usize], hints: &[usize]) -> bool {
    matches!(
        check_query(ns, bits, roots, hints, ""),
        Err(QueryCheckError::Certificate(
            ordeal_lrat::CheckError::NoEmptyClause
        ))
    )
}

/// Two `w`-bit variables `a`, `b`; node 2 is `op(a, b)`; root: `op(a,b) = a`.
fn binop_dag(w: usize, op: fn(usize, usize) -> N) -> (Vec<N>, Vec<usize>) {
    (
        vec![N::Var(w), N::Var(w), op(0, 1), N::Eq(2, 0)],
        vec![3],
    )
}

fn binop_encodes(w: usize, op: fn(usize, usize) -> N) -> bool {
    let (ns, roots) = binop_dag(w, op);
    encodes(&ns, &[], &roots, &[])
}

/// The 1-bit-result comparison `op(a, b)` as a root.
fn cmp_encodes(w: usize, op: fn(usize, usize) -> N) -> bool {
    let ns = vec![N::Var(w), N::Var(w), op(0, 1)];
    encodes(&ns, &[], &[2], &[])
}

// ───────────── term/DAG fixtures ─────────────

type Pair = (
    Vec<N>,
    Vec<bool>,
    Vec<usize>,
    Vec<usize>,
    Vec<N>,
    Vec<bool>,
    Vec<usize>,
);

fn term_and_dag() -> Pair {
    let t = vec![
        N::Var(8),
        N::Var(8),
        N::Add(1, 0),
        N::Const(0, 8),
        N::Const(8, 8),
        N::Mul(3, 4),
        N::Ugt(2, 5),
        N::Eq(0, 1),
    ];
    let mut tbits = cbits(2, 8);
    tbits.extend(cbits(3, 8));
    let troots = vec![6, 7];
    let ns = vec![
        N::Var(8),
        N::Var(8),
        N::Add(0, 1),
        N::Const(0, 8),
        N::Ult(3, 2),
        N::Eq(0, 1),
    ];
    let bits = cbits(6, 8);
    let roots = vec![4, 5];
    let map = vec![0, 1, 2, NONE, NONE, 3, 4, 5];
    (t, tbits, troots, map, ns, bits, roots)
}

fn term_ok(p: &Pair) -> Result<(), TermError> {
    check_term_dag(&p.0, &p.1, &p.2, &p.3, &p.4, &p.5, &p.6)
}

// ───────────── sliver fixtures ─────────────

struct Fixture {
    e: Vec<ExtNode>,
    ebits: Vec<bool>,
    eside: Vec<usize>,
    eroots: Vec<usize>,
    map: Vec<usize>,
    reads: Vec<usize>,
    t: Vec<N>,
    tbits: Vec<bool>,
    troots: Vec<usize>,
}

fn one_symbolic_store() -> Fixture {
    Fixture {
        e: vec![
            ExtNode::Core(N::Var(32)),
            ExtNode::Core(N::Var(32)),
            ExtNode::Core(N::Var(8)),
            ExtNode::Select(0, 1, 0, 1),
            ExtNode::Core(N::Const(0, 8)),
            ExtNode::Core(N::Eq(3, 4)),
        ],
        ebits: vec![false; 8],
        eside: vec![0, 2],
        eroots: vec![5],
        map: vec![0, 1, 3, 5, 6, 7],
        reads: vec![4, 0, 1],
        t: vec![
            N::Var(32),
            N::Var(32),
            N::Eq(0, 1),
            N::Var(8),
            N::Var(8),
            N::Ite(2, 3, 4),
            N::Const(0, 8),
            N::Eq(5, 6),
        ],
        tbits: vec![false; 8],
        troots: vec![7],
    }
}

impl Fixture {
    fn run(&self) -> Result<(), SliverCheckError> {
        check_sliver_lowering(
            &self.e,
            &self.ebits,
            &self.eside,
            &self.eroots,
            &self.map,
            &self.reads,
            &[],
            &[],
            &self.t,
            &self.tbits,
            &self.troots,
        )
    }
}

/// `f(x) != f(y)` with its congruence root.
struct CallFx {
    e: Vec<ExtNode>,
    eside: Vec<usize>,
    eroots: Vec<usize>,
    t: Vec<N>,
    troots: Vec<usize>,
    map: Vec<usize>,
    calls: Vec<usize>,
    cargs: Vec<usize>,
}

fn call_fixture() -> CallFx {
    CallFx {
        e: vec![
            ExtNode::Core(N::Var(8)),
            ExtNode::Core(N::Var(8)),
            ExtNode::Call(0, 8, 0, 1),
            ExtNode::Call(0, 8, 1, 1),
            ExtNode::Core(N::Ne(2, 3)),
        ],
        eside: vec![0, 1],
        eroots: vec![4],
        t: vec![
            N::Var(8),
            N::Var(8),
            N::Var(8),
            N::Var(8),
            N::Ne(2, 3),
            N::Eq(0, 1),
            N::Not(5),
            N::Eq(2, 3),
            N::BoolOr(6, 7),
        ],
        troots: vec![4, 8],
        map: vec![0, 1, 2, 3, 4],
        calls: vec![2, 0, 0, 1, 3, 0, 1, 1],
        cargs: vec![0, 1],
    }
}

impl CallFx {
    fn run(&self) -> Result<(), SliverCheckError> {
        check_sliver_lowering(
            &self.e,
            &[],
            &self.eside,
            &self.eroots,
            &self.map,
            &[],
            &self.calls,
            &self.cargs,
            &self.t,
            &[],
            &self.troots,
        )
    }
}

/// Two symbolic reads of one array plus a concrete miss (the fast path).
struct TwoReads {
    e: Vec<ExtNode>,
    ebits: Vec<bool>,
    eside: Vec<usize>,
    eroots: Vec<usize>,
    map: Vec<usize>,
    t: Vec<N>,
    tbits: Vec<bool>,
    troots: Vec<usize>,
    reads: Vec<usize>,
}

fn two_reads() -> TwoReads {
    let mut ebits = vec![false; 72];
    ebits[0] = true;
    ebits[33] = true;
    let mut tbits = vec![false; 72];
    tbits[1] = true;
    tbits[40] = true;
    TwoReads {
        e: vec![
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
        ],
        ebits,
        eside: vec![5, 7],
        eroots: vec![4, 10],
        map: vec![0, 1, 2, 3, 4, 13, 5, NONE, 6, 7, 8],
        t: vec![
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
        ],
        tbits,
        troots: vec![4, 8, 12, 17, 21],
        reads: vec![2, 0, 0, 3, 0, 1, 6, 0, 5],
    }
}

impl TwoReads {
    fn run(&self) -> Result<(), SliverCheckError> {
        check_sliver_lowering(
            &self.e,
            &self.ebits,
            &self.eside,
            &self.eroots,
            &self.map,
            &self.reads,
            &[],
            &[],
            &self.t,
            &self.tbits,
            &self.troots,
        )
    }
}

// ───────────── tree helpers ─────────────

fn var(n: &str, w: usize) -> Box<TBv> {
    Box::new(TBv::Var(n.as_bytes().to_vec(), w))
}

fn konst(v: u128, w: usize) -> Box<TBv> {
    Box::new(TBv::Const(v, w))
}

fn flat_err(t: TBool) -> Option<FlatError> {
    flatten_tree(&[t]).err()
}

fn eq_t(a: Box<TBv>, b: Box<TBv>) -> TBool {
    TBool::Eq(a, b)
}

rows! {
// ═════════ check: the textual LRAT entry (lib.rs, kernel.rs check_steps) ═════════
run_row_check_accept_two_unit_contradiction => { check(&tiny_cnf(), "3 0 1 2 0").is_ok() }
run_row_check_accept_rup_chain => { check(&quad_cnf(), "5 2 0 1 2 0\n6 0 5 3 4 0").is_ok() }
run_row_check_accept_with_deletion => { check(&quad_cnf(), "5 2 0 1 2 0\n5 d 1 2 0\n6 0 5 3 4 0").is_ok() }
run_row_check_accept_comment_and_blank_lines => { check(&tiny_cnf(), "c a comment\n\n3 0 1 2 0\n").is_ok() }
run_row_check_reject_dropped_hint => { check(&quad_cnf(), "5 2 0 1 2 0\n6 0 5 3 0").is_err() }
run_row_check_reject_wrong_hint_order => { check(&quad_cnf(), "5 2 0 1 2 0\n6 0 3 4 5 0").is_err() }
run_row_check_reject_deleted_clause_reference => { check(&quad_cnf(), "5 2 0 1 2 0\n5 d 3 0\n6 0 5 3 4 0").is_err() }
run_row_check_reject_unknown_id => { check(&tiny_cnf(), "3 0 1 9 0").is_err() }
run_row_check_reject_truncated => { check(&quad_cnf(), "5 2 0 1 2 0").is_err() }
run_row_check_reject_final_clause_non_empty => { check(&tiny_cnf(), "3 1 0 1 0").is_err() }
run_row_check_reject_rat_negative_hint => { check(&tiny_cnf(), "3 0 1 -2 0").is_err() }
run_row_check_reject_garbage => { is_parse(check(&tiny_cnf(), "hello world")) }
run_row_check_reject_non_sequential_id => { check(&tiny_cnf(), "7 0 1 2 0").is_err() }
run_row_check_reject_empty_certificate => { check(&tiny_cnf(), "").is_err() }
run_row_check_reject_zero_id => { is_parse(check(&tiny_cnf(), "0 0 1 2 0")) }
run_row_check_reject_bad_literal_zero_in_hints_id => { is_parse(check(&tiny_cnf(), "3 0 1 0 0")) }
run_row_check_reject_bad_literal_token => { is_parse(check(&tiny_cnf(), "3 x 0 1 2 0")) }
run_row_check_reject_literal_i32_min => { is_parse(check(&tiny_cnf(), "3 -2147483648 0 1 2 0")) }
run_row_check_reject_missing_clause_terminator => { is_parse(check(&tiny_cnf(), "3 1 2")) }
run_row_check_reject_missing_hint_terminator => { is_parse(check(&tiny_cnf(), "3 0 1 2")) }
run_row_check_reject_trailing_after_hints => { is_parse(check(&tiny_cnf(), "3 0 1 2 0 7")) }
run_row_check_reject_bad_hint_token => { is_parse(check(&tiny_cnf(), "3 0 y 2 0")) }
run_row_check_reject_deletion_missing_zero => { is_parse(check(&tiny_cnf(), "3 d 1")) }
run_row_check_reject_deletion_trailing => { is_parse(check(&tiny_cnf(), "3 d 1 0 5")) }
run_row_check_reject_deletion_bad_id => { is_parse(check(&tiny_cnf(), "3 d 0 0")) }
run_row_check_reject_cnf_zero_literal => { check(&[vec![1, 0]], "").is_err() }
run_row_check_reject_cnf_i32_min_literal => { check(&[vec![i32::MIN]], "").is_err() }
run_row_check_reject_unknown_id_in_deletion => { check(&tiny_cnf(), "3 d 9 0\n4 0 1 2 0").is_err() }
run_row_check_reject_double_deletion => { check(&tiny_cnf(), "3 d 1 0\n3 d 1 0").is_err() }
run_row_check_reject_hint_satisfied_not_unit => { check(&[vec![1, 2], vec![1], vec![-1]], "4 0 1 2 3 0").is_err() }
run_row_check_accept_negative_clause_literals => { check(&[vec![-1, -2], vec![1], vec![2]], "4 0 2 3 1 0").is_ok() }
run_row_check_accept_clause_with_repeated_literal => { check(&[vec![1, 1], vec![-1]], "3 0 1 2 0").is_ok() }

// ═════════ kernel::check_steps directly (kernel.rs) ═════════
run_row_steps_accept_two_units => { kernel::check_steps(&tiny_cnf(), &[add(3, &[], &[1, 2])]).is_ok() }
run_row_steps_reject_no_empty_clause => { kernel::check_steps(&[vec![1, 2], vec![-1, 2]], &[add(3, &[2], &[1, 2])]).is_err() }
run_row_steps_reject_non_sequential => { kernel::check_steps(&tiny_cnf(), &[add(5, &[], &[1, 2])]).is_err() }
run_row_steps_reject_dead_hint => { kernel::check_steps(&tiny_cnf(), &[Step::Delete { ids: vec![1] }, add(3, &[], &[1, 2])]).is_err() }
run_row_steps_reject_zero_step_literal => { kernel::check_steps(&tiny_cnf(), &[add(3, &[0], &[1, 2])]).is_err() }
run_row_steps_reject_min_step_literal => { kernel::check_steps(&tiny_cnf(), &[add(3, &[i32::MIN], &[1, 2])]).is_err() }
run_row_steps_reject_exhausted_hints => { kernel::check_steps(&[vec![1, 2], vec![-1, 2], vec![-2, 1]], &[add(4, &[], &[1])]).is_err() }
run_row_steps_reject_delete_unknown => { kernel::check_steps(&tiny_cnf(), &[Step::Delete { ids: vec![99] }, add(3, &[], &[1, 2])]).is_err() }
run_row_steps_reject_delete_zero_id => { kernel::check_steps(&tiny_cnf(), &[Step::Delete { ids: vec![0] }, add(3, &[], &[1, 2])]).is_err() }
run_row_steps_reject_hint_zero_id => { kernel::check_steps(&tiny_cnf(), &[add(3, &[], &[0, 1])]).is_err() }
run_row_steps_reject_cnf_literal_zero => { kernel::check_steps(&[vec![0]], &[]).is_err() }
run_row_steps_accept_add_then_empty => { kernel::check_steps(&quad_cnf(), &[add(5, &[2], &[1, 2]), add(6, &[], &[5, 3, 4])]).is_ok() }
run_row_steps_accept_tautology_clause => { kernel::check_steps(&[vec![1], vec![-1]], &[add(3, &[2, -2], &[1, 2]), add(4, &[], &[1, 2])]).is_ok() }
run_row_steps_reject_conflicting_assumption_literals => { kernel::check_steps(&[vec![1, 2], vec![-1, 2], vec![-2]], &[add(4, &[1, 2], &[3]), add(5, &[], &[4, 3])]).is_err() }

// ═════════ check_sat / check_binding ═════════
run_row_sat_accept_assignment => { check_sat(&[vec![1, 2], vec![-1, 2], vec![-2, 1]], &[true, true]).is_ok() }
run_row_sat_reject_unsatisfied_clause => { matches!(check_sat(&[vec![1, 2], vec![-1, -2]], &[true, true]), Err(SatWitnessError::UnsatisfiedClause { .. })) }
run_row_sat_reject_assignment_too_short => { check_sat(&[vec![3]], &[true]).is_err() }
run_row_sat_accept_lazy_short_assignment => { check_sat(&[vec![1, 3]], &[true]).is_ok() }
run_row_sat_reject_zero_literal => { check_sat(&[vec![0]], &[true]).is_err() }
run_row_sat_reject_min_literal => { check_sat(&[vec![i32::MIN]], &[true]).is_err() }
run_row_sat_accept_negative_literal => { check_sat(&[vec![-1]], &[false]).is_ok() }
run_row_sat_accept_empty_cnf => { check_sat(&[], &[]).is_ok() }
run_row_sat_reject_empty_clause => { check_sat(&[vec![]], &[true]).is_err() }
run_row_binding_accept_positive_bits => { check_binding(&[false, true, false, true], &[1, 2, 3, 4], 0b1010).is_ok() }
run_row_binding_accept_negated_bits => { check_binding(&[false, true, false, true], &[-1, -2], 0b01).is_ok() }
run_row_binding_reject_mismatch => { matches!(check_binding(&[false, true, false, true], &[1, 2, 3, 4], 0b1011), Err(SatWitnessError::BindingMismatch { .. })) }
run_row_binding_reject_short_assignment => { check_binding(&[false, true, false, true], &[9], 0).is_err() }
run_row_binding_reject_zero_literal => { check_binding(&[false, true], &[0], 0).is_err() }
run_row_binding_reject_min_literal => { check_binding(&[false, true], &[i32::MIN], 0).is_err() }
run_row_binding_accept_no_bits => { check_binding(&[], &[], 0).is_ok() }
run_row_binding_reject_negated_mismatch => { check_binding(&[false, true], &[-2], 1).is_err() }
run_row_binding_reject_wide_value_beyond_literals => { check_binding(&[true, true], &[1, 2], 0b100).is_err() }
run_row_binding_reject_over_128_bits => { check_binding(&vec![true; 130], &(1..=130).collect::<Vec<i32>>(), 0).is_err() }

// ═════════ dag_wf / dag_nin / check_query ═════════
run_row_dag_wf_accept_tiny => { let (ns, bits, _) = tiny_dag(); dag_wf(&ns, bits.len()).is_ok() }
run_row_dag_wf_accept_word_ops => {
    let ns = vec![N::Var(8), N::Const(0, 8), N::Add(0, 1), N::Extract(7, 4, 2), N::Concat(3, 0),
        N::ZeroExt(3, 3), N::SignExt(4, 1), N::Ult(0, 1), N::Ite(7, 0, 1), N::BoolAnd(7, 7)];
    dag_wf(&ns, 8).is_ok()
}
run_row_dag_wf_accept_derived_ops => {
    let ns = vec![N::Var(12), N::Var(12), N::BvNot(0), N::Neg(1), N::Rotl(0, 1), N::Sdiv(2, 3), N::Srem(4, 5), N::Eq(5, 6)];
    dag_wf(&ns, 0).is_ok()
}
run_row_dag_wf_reject_zero_width => { dag_wf(&[N::Var(0)], 0).is_err() }
run_row_dag_wf_reject_const_past_table => { dag_wf(&[N::Const(0, 2)], 1).is_err() }
run_row_dag_wf_reject_operand_not_earlier => { dag_wf(&[N::Var(8), N::Add(0, 1)], 0).is_err() }
run_row_dag_wf_reject_first_operand_not_earlier => { dag_wf(&[N::Var(8), N::Add(1, 0)], 0).is_err() }
run_row_dag_wf_reject_width_mismatch => { dag_wf(&[N::Var(8), N::Var(4), N::Add(0, 1)], 0).is_err() }
run_row_dag_wf_reject_extract_hi_past_width => { dag_wf(&[N::Var(8), N::Extract(8, 0, 0)], 0).is_err() }
run_row_dag_wf_reject_extract_lo_gt_hi => { dag_wf(&[N::Var(8), N::Extract(2, 3, 0)], 0).is_err() }
run_row_dag_wf_reject_extract_operand_not_earlier => { dag_wf(&[N::Var(8), N::Extract(1, 0, 5)], 0).is_err() }
run_row_dag_wf_reject_ite_cond_not_bool => { dag_wf(&[N::Var(8), N::Ite(0, 0, 0)], 0).is_err() }
run_row_dag_wf_reject_ite_branch_widths => { dag_wf(&[N::Var(1), N::Var(8), N::Var(4), N::Ite(0, 1, 2)], 0).is_err() }
run_row_dag_wf_reject_ite_operand_not_earlier => { dag_wf(&[N::Var(1), N::Var(8), N::Ite(0, 1, 9)], 0).is_err() }
run_row_dag_wf_reject_not_of_word => { dag_wf(&[N::Var(8), N::Not(0)], 0).is_err() }
run_row_dag_wf_reject_not_operand_not_earlier => { dag_wf(&[N::Var(1), N::Not(3)], 0).is_err() }
run_row_dag_wf_reject_boolean_op_on_word => { dag_wf(&[N::Var(8), N::Var(1), N::BoolAnd(0, 1)], 0).is_err() }
run_row_dag_wf_reject_boolean_op_second_on_word => { dag_wf(&[N::Var(1), N::Var(8), N::BoolOr(0, 1)], 0).is_err() }
run_row_dag_wf_reject_zext_overflow => { dag_wf(&[N::Var(8), N::ZeroExt(0, usize::MAX)], 0).is_err() }
run_row_dag_wf_reject_sext_overflow => { dag_wf(&[N::Var(8), N::SignExt(0, usize::MAX)], 0).is_err() }
run_row_dag_wf_reject_sext_not_earlier => { dag_wf(&[N::Var(8), N::SignExt(4, 2)], 0).is_err() }
run_row_dag_wf_reject_concat_overflow => { dag_wf(&[N::Var(usize::MAX), N::Concat(0, 0)], 0).is_err() }
run_row_dag_wf_reject_concat_not_earlier => { dag_wf(&[N::Var(8), N::Concat(0, 4)], 0).is_err() }
run_row_dag_wf_reject_neg_not_earlier => { dag_wf(&[N::Var(8), N::Neg(1)], 0).is_err() }
run_row_dag_wf_reject_bvnot_not_earlier => { dag_wf(&[N::Var(8), N::BvNot(2)], 0).is_err() }
run_row_dag_wf_reject_sdiv_width => { dag_wf(&[N::Var(8), N::Var(4), N::Sdiv(0, 1)], 0).is_err() }
run_row_dag_wf_reject_srem_width => { dag_wf(&[N::Var(8), N::Var(4), N::Srem(1, 0)], 0).is_err() }
run_row_dag_wf_reject_rotl_not_earlier => { dag_wf(&[N::Var(8), N::Rotl(0, 1)], 0).is_err() }
run_row_dag_wf_reject_comparison_width => { dag_wf(&[N::Var(8), N::Var(4), N::Ult(0, 1)], 0).is_err() }
run_row_dag_wf_reject_eq_not_earlier => { dag_wf(&[N::Var(8), N::Eq(0, 7)], 0).is_err() }
run_row_check_query_reject_no_refutation => { let (ns, bits, roots) = tiny_dag(); matches!(check_query(&ns, &bits, &roots, &[], ""), Err(QueryCheckError::Certificate(_))) }
run_row_check_query_reject_malformed_dag => { let (mut ns, bits, roots) = tiny_dag(); ns[2] = N::Eq(0, 9); matches!(check_query(&ns, &bits, &roots, &[], ""), Err(QueryCheckError::Query(QueryError::NodeNotWellFormed { .. }))) }
run_row_check_query_reject_word_root => { matches!(check_query(&[N::Var(8)], &[], &[0], &[], ""), Err(QueryCheckError::Query(QueryError::BadRoot { .. }))) }
run_row_check_query_reject_root_past_dag => { matches!(check_query(&[N::Var(1)], &[], &[5], &[], ""), Err(QueryCheckError::Query(QueryError::BadRoot { .. }))) }
run_row_check_query_reject_short_const_table => { let (ns, _, roots) = tiny_dag(); check_query(&ns, &[], &roots, &[], "").is_err() }
run_row_check_query_reject_too_large => { check_query(&[N::Var(usize::MAX / 1000), N::Var(usize::MAX / 1000)], &[], &[], &[], "").is_err() }
run_row_check_query_accept_hand_refuted => { let (ns, bits, roots) = tiny_dag(); check_query(&ns, &bits, &roots, &[], "4 0 2 3 0").is_ok() }
run_row_check_query_reject_wrong_root_polarity => { let (ns, bits, _) = tiny_dag(); check_query(&ns, &bits, &[2, 2], &[], "4 0 2 3 0").is_err() }
run_row_check_query_reject_bad_certificate_line => { let (ns, bits, roots) = tiny_dag(); matches!(check_query(&ns, &bits, &roots, &[], "junk"), Err(QueryCheckError::Certificate(_))) }
run_row_check_query_steps_accept_hand_refuted => { let (ns, bits, roots) = tiny_dag(); kernel::check_query(&ns, &bits, &roots, &[], &[add(4, &[], &[2, 3])]).is_ok() }
run_row_check_query_accept_shared_gate_hints => {
    // x = x + x - x style duplicate gates the hint list shares.
    let ns = vec![N::Var(1), N::Add(0, 0), N::Add(0, 0), N::Eq(1, 2), N::Not(3)];
    let hints = hints_for(&ns, &[], &[4]);
    encodes(&ns, &[], &[4], &hints)
}
run_row_check_query_wrong_hints_are_ignored => {
    let ns = vec![N::Var(2), N::Add(0, 0), N::Add(0, 0), N::Eq(1, 2), N::Not(3)];
    encodes(&ns, &[], &[4], &[0, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 1, 0, 3, 2, 5, 4])
}
run_row_check_query_constant_folds => {
    // x & 0, x & 1, x & x, x & !x all fold in `compact`.
    let ns = vec![N::Var(1), N::Const(0, 1), N::Const(1, 1), N::And(0, 1), N::And(0, 2), N::And(0, 0), N::BvNot(0), N::And(0, 6), N::Eq(3, 4), N::Eq(5, 7), N::BoolAnd(8, 9)];
    let bits = vec![false, true];
    encodes(&ns, &bits, &[10], &[])
}

// ═════════ check_query_model / dag_nin ═════════
run_row_model_accept_witness => { let (ns, bits, _) = tiny_dag(); check_query_model(&ns, &bits, &[2], &[true]).is_ok() }
run_row_model_reject_falsified_root => { let (ns, bits, _) = tiny_dag(); matches!(check_query_model(&ns, &bits, &[3], &[true]), Err(ModelError::RootFalse { .. })) }
run_row_model_accept_second_polarity => { let (ns, bits, _) = tiny_dag(); check_query_model(&ns, &bits, &[3], &[false]).is_ok() }
run_row_model_reject_first_of_two_roots => { let (ns, bits, _) = tiny_dag(); check_query_model(&ns, &bits, &[2, 3], &[false]).is_err() }
run_row_model_reject_second_of_two_roots => { let (ns, bits, _) = tiny_dag(); check_query_model(&ns, &bits, &[2, 3], &[true]).is_err() }
run_row_model_accept_surplus_inputs => { let (ns, bits, _) = tiny_dag(); check_query_model(&ns, &bits, &[2], &[true, false, true]).is_ok() }
run_row_model_accept_no_roots => { let (ns, bits, _) = tiny_dag(); check_query_model(&ns, &bits, &[], &[true]).is_ok() }
run_row_model_reject_short_assignment => { let (ns, bits, roots) = tiny_dag(); matches!(check_query_model(&ns, &bits, &roots, &[]), Err(ModelError::ModelTooShort { .. })) }
run_row_model_reject_malformed_dag => { let (mut ns, bits, _) = tiny_dag(); ns[2] = N::Eq(0, 9); check_query_model(&ns, &bits, &[2], &[true]).is_err() }
run_row_model_reject_word_root => { check_query_model(&[N::Var(8)], &[], &[0], &[true; 8]).is_err() }
run_row_model_reject_short_const_table => { let (ns, _, _) = tiny_dag(); check_query_model(&ns, &[], &[2], &[true]).is_err() }
run_row_model_reject_too_large => { check_query_model(&[N::Var(usize::MAX), N::Var(1)], &[], &[], &[]).is_err() }
run_row_dag_nin_counts_var_bits => { dag_nin(&tiny_dag().0) == Ok(1) }
run_row_dag_nin_reject_overflow => { dag_nin(&[N::Var(usize::MAX), N::Var(1)]).is_err() }
run_row_model_accept_add_lt_lsb_first => {
    let ns = vec![N::Var(4), N::Var(4), N::Add(0, 1), N::Const(0, 4), N::Eq(2, 3), N::Ult(0, 1)];
    let bits = vec![true, true, true, false];
    check_query_model(&ns, &bits, &[4, 5], &[true, true, false, false, false, false, true, false]).is_ok()
}
run_row_model_reject_swapped_inputs => {
    let ns = vec![N::Var(4), N::Var(4), N::Add(0, 1), N::Const(0, 4), N::Eq(2, 3), N::Ult(0, 1)];
    let bits = vec![true, true, true, false];
    check_query_model(&ns, &bits, &[4, 5], &[false, false, true, false, true, true, false, false]).is_err()
}

// ═════════ check_term_dag / var_offset / check_input_value ═════════
run_row_term_accept_swap_mirror_fold_shared => { term_ok(&term_and_dag()).is_ok() }
run_row_term_reject_aliased_vars => { let mut p = term_and_dag(); p.3[0] = 1; matches!(term_ok(&p), Err(TermError::VarMismatch { .. })) }
run_row_term_reject_wrong_fold => { let mut p = term_and_dag(); p.5 = cbits(7, 8); matches!(term_ok(&p), Err(TermError::FoldMismatch { .. })) }
run_row_term_reject_fold_of_open_node => { let mut p = term_and_dag(); p.0[5] = N::Mul(0, 4); matches!(term_ok(&p), Err(TermError::FoldMismatch { .. })) }
run_row_term_reject_open_fold_matching_all_false => { let mut p = term_and_dag(); p.0[5] = N::Mul(0, 4); p.5 = cbits(0, 8); matches!(term_ok(&p), Err(TermError::FoldMismatch { .. })) }
run_row_term_accept_ite_const_cond_const_branch => {
    let p = term_and_dag();
    let t2 = vec![N::Var(8), N::Var(8), N::Add(1, 0), N::Const(0, 8), N::Const(8, 8), N::Ult(3, 4), N::Const(16, 8), N::Ite(5, 6, 0), N::Ugt(2, 7), N::Eq(0, 1)];
    let mut tbits2 = p.1.clone();
    tbits2.extend(cbits(6, 8));
    let map2 = vec![0, 1, 2, NONE, NONE, NONE, NONE, 3, 4, 5];
    check_term_dag(&t2, &tbits2, &[8, 9], &map2, &p.4, &p.5, &p.6).is_ok()
}
run_row_term_reject_ite_selected_branch_reads_var => {
    let p = term_and_dag();
    let t3 = vec![N::Var(8), N::Var(8), N::Add(1, 0), N::Const(0, 8), N::Const(8, 8), N::Ult(4, 3), N::Const(16, 8), N::Ite(5, 6, 0), N::Ugt(2, 7), N::Eq(0, 1)];
    let mut tbits2 = p.1.clone();
    tbits2.extend(cbits(6, 8));
    let map2 = vec![0, 1, 2, NONE, NONE, NONE, NONE, 3, 4, 5];
    matches!(check_term_dag(&t3, &tbits2, &[8, 9], &map2, &p.4, &p.5, &p.6), Err(TermError::FoldMismatch { .. }))
}
run_row_term_reject_noncommutative_swap => { let mut p = term_and_dag(); p.0[2] = N::Sub(1, 0); p.4[2] = N::Sub(0, 1); matches!(term_ok(&p), Err(TermError::NodeMismatch { .. })) }
run_row_term_accept_noncommutative_in_order => { let mut p = term_and_dag(); p.0[2] = N::Sub(1, 0); p.4[2] = N::Sub(1, 0); term_ok(&p).is_ok() }
run_row_term_reject_wrong_mirror => { let mut p = term_and_dag(); p.4[4] = N::Ule(3, 2); matches!(term_ok(&p), Err(TermError::NodeMismatch { .. })) }
run_row_term_reject_tampered_map_entry => { let mut p = term_and_dag(); p.3[7] = 4; matches!(term_ok(&p), Err(TermError::NodeMismatch { .. })) }
run_row_term_reject_root_without_image => { let mut p = term_and_dag(); p.3[6] = NONE; matches!(term_ok(&p), Err(TermError::RootMismatch)) }
run_row_term_reject_map_length => { let mut p = term_and_dag(); p.3.truncate(7); matches!(term_ok(&p), Err(TermError::MapLength { .. })) }
run_row_term_reject_map_out_of_range => { let mut p = term_and_dag(); p.3[2] = 99; matches!(term_ok(&p), Err(TermError::MapOutOfRange { .. })) }
run_row_term_reject_const_other_bits => { let mut p = term_and_dag(); p.0.push(N::Const(16, 8)); p.1.extend(cbits(5, 8)); p.3.push(3); matches!(term_ok(&p), Err(TermError::ConstMismatch { .. })) }
run_row_term_reject_malformed_term => { let mut p = term_and_dag(); p.0[2] = N::Add(1, 9); matches!(term_ok(&p), Err(TermError::Term(_))) }
run_row_term_reject_malformed_dag => { let mut p = term_and_dag(); p.4[2] = N::Add(0, 9); matches!(term_ok(&p), Err(TermError::Query(_))) }
run_row_term_reject_extra_dag_root => { let mut p = term_and_dag(); p.6.push(5); term_ok(&p).is_err() }
run_row_term_reject_root_order => { let mut p = term_and_dag(); p.6 = vec![5, 4]; term_ok(&p).is_err() }
run_row_term_reject_var_to_non_var => { let mut p = term_and_dag(); p.3[1] = 2; term_ok(&p).is_err() }
run_row_term_reject_var_width => { let mut p = term_and_dag(); p.4[1] = N::Var(4); term_ok(&p).is_err() }
run_row_term_reject_const_width => { let mut p = term_and_dag(); p.0[3] = N::Const(0, 4); p.0[4] = N::Const(8, 4); term_ok(&p).is_err() }
run_row_term_reject_operator_kind => { let mut p = term_and_dag(); p.4[2] = N::Sub(0, 1); matches!(term_ok(&p), Err(TermError::NodeMismatch { .. })) }
run_row_term_reject_operand_image => { let mut p = term_and_dag(); p.4[5] = N::Eq(0, 0); matches!(term_ok(&p), Err(TermError::NodeMismatch { .. })) }
run_row_var_offset_in_range => {
    let ns = vec![N::Var(3), N::Const(0, 2), N::Var(5), N::Add(0, 0)];
    var_offset(&ns, 0) == Ok(0) && var_offset(&ns, 2) == Ok(3) && var_offset(&ns, 4) == Ok(8)
}
run_row_var_offset_reject_past_end => { var_offset(&[N::Var(3)], 5).is_err() }
run_row_input_value_accept => {
    let inp = [true, false, true, false, true, true, false, true];
    check_input_value(&inp, 0, 3, 0b101) && check_input_value(&inp, 3, 5, 0b10110) && check_input_value(&inp, 8, 0, 0)
}
run_row_input_value_reject_wrong_bits => {
    let inp = [true, false, true, false, true, true, false, true];
    !check_input_value(&inp, 3, 5, 0b10111) && !check_input_value(&inp, 0, 3, 0b100)
}
run_row_input_value_reject_out_of_range => {
    let inp = [true, false, true, false, true, true, false, true];
    !check_input_value(&inp, 3, 6, 0) && !check_input_value(&inp, 9, 0, 0) && !check_input_value(&inp, 0, 129, 0)
}
run_row_input_value_reject_value_wider_than_w => {
    let inp = [true, false, true];
    !check_input_value(&inp, 0, 3, 1 << 3)
}

// ═════════ check_sliver_lowering / ext_wf ═════════
run_row_sliver_accept_symbolic_read_over_write => { one_symbolic_store().run().is_ok() }
run_row_sliver_reject_chain_wrong_index_entry => { let mut f = one_symbolic_store(); f.reads = vec![4, 0, 0]; matches!(f.run(), Err(SliverCheckError::ChainMismatch { .. })) }
run_row_sliver_reject_read_var_is_query_var => { let mut f = one_symbolic_store(); f.reads = vec![3, 0, 1]; matches!(f.run(), Err(SliverCheckError::VarClass { .. })) }
run_row_sliver_reject_select_mapped_to_v => { let mut f = one_symbolic_store(); f.map[3] = 3; matches!(f.run(), Err(SliverCheckError::ChainMismatch { .. })) }
run_row_sliver_reject_wrong_ite_condition => { let mut f = one_symbolic_store(); f.t[2] = N::Eq(0, 0); matches!(f.run(), Err(SliverCheckError::ChainMismatch { .. })) }
run_row_sliver_reject_extra_root => { let mut f = one_symbolic_store(); f.troots = vec![7, 2]; matches!(f.run(), Err(SliverCheckError::RootMismatch)) }
run_row_sliver_reject_map_length => { let mut f = one_symbolic_store(); f.map.truncate(5); matches!(f.run(), Err(SliverCheckError::MapLength { .. })) }
run_row_sliver_reject_map_out_of_range => { let mut f = one_symbolic_store(); f.map[2] = 99; f.run().is_err() }
run_row_sliver_reject_malformed_core => { let mut f = one_symbolic_store(); f.t[5] = N::Ite(2, 3, 99); matches!(f.run(), Err(SliverCheckError::Core(_))) }
run_row_sliver_reject_malformed_ext_operand => { let mut f = one_symbolic_store(); f.e[5] = ExtNode::Core(N::Eq(3, 9)); matches!(f.run(), Err(SliverCheckError::Ext { .. })) }
run_row_sliver_reject_select_index_not_bv32 => { let mut f = one_symbolic_store(); f.e[1] = ExtNode::Core(N::Var(8)); f.run().is_err() }
run_row_sliver_reject_store_index_not_bv32 => { let mut f = one_symbolic_store(); f.e[0] = ExtNode::Core(N::Var(8)); f.run().is_err() }
run_row_sliver_reject_store_value_not_bv8 => { let mut f = one_symbolic_store(); f.e[2] = ExtNode::Core(N::Var(16)); f.run().is_err() }
run_row_sliver_reject_chain_outside_side_table => { let mut f = one_symbolic_store(); f.eside = vec![0]; matches!(f.run(), Err(SliverCheckError::Ext { .. })) }
run_row_sliver_reject_chain_node_not_earlier => { let mut f = one_symbolic_store(); f.eside = vec![0, 9]; matches!(f.run(), Err(SliverCheckError::Ext { .. })) }
run_row_sliver_reject_read_table_bad_var => { let mut f = one_symbolic_store(); f.reads = vec![99, 0, 1]; matches!(f.run(), Err(SliverCheckError::ReadTable { .. })) }
run_row_sliver_reject_read_table_non_bv8_var => { let mut f = one_symbolic_store(); f.reads = vec![0, 0, 1]; f.run().is_err() }
run_row_sliver_reject_read_table_bad_index => { let mut f = one_symbolic_store(); f.reads = vec![4, 0, 99]; f.run().is_err() }
run_row_sliver_reject_read_table_non_bv32_index => { let mut f = one_symbolic_store(); f.reads = vec![4, 0, 3]; f.run().is_err() }
run_row_sliver_reject_read_table_duplicate => { let mut f = one_symbolic_store(); f.reads = vec![4, 0, 1, 3, 0, 1]; matches!(f.run(), Err(SliverCheckError::ReadTable { .. })) }
run_row_sliver_reject_read_table_ragged => { let mut f = one_symbolic_store(); f.reads = vec![4, 0]; f.run().is_err() }
run_row_sliver_reject_var_class_width => { let mut f = one_symbolic_store(); f.t[3] = N::Var(16); f.run().is_err() }
run_row_sliver_reject_var_aliasing => { let mut f = one_symbolic_store(); f.map[1] = 0; f.run().is_err() }
run_row_sliver_reject_var_to_non_var => { let mut f = one_symbolic_store(); f.map[0] = 2; f.run().is_err() }
run_row_sliver_reject_const_image => { let mut f = one_symbolic_store(); f.map[4] = 3; f.run().is_err() }
run_row_sliver_reject_const_image_bits => { let mut f = one_symbolic_store(); f.tbits[0] = true; f.run().is_err() }
run_row_sliver_reject_operator_image => { let mut f = one_symbolic_store(); f.t[7] = N::Ne(5, 6); f.run().is_err() }
run_row_sliver_reject_root_image => { let mut f = one_symbolic_store(); f.troots = vec![2]; f.run().is_err() }
run_row_sliver_reject_dead_read_entry => {
    let e = vec![ExtNode::Core(N::Const(0, 32)), ExtNode::Select(0, 0, 0, 0), ExtNode::Core(N::Const(32, 8)), ExtNode::Core(N::Eq(1, 2))];
    let mut ebits = vec![false; 40];
    ebits[32] = true;
    let t = vec![N::Const(0, 32), N::Var(8), N::Const(32, 8), N::Eq(1, 2), N::Var(8), N::ZeroExt(4, 24), N::Eq(0, 5), N::Not(6), N::Eq(1, 4), N::BoolOr(7, 8)];
    let map = vec![0, 1, 2, 3];
    let dead = check_sliver_lowering(&e, &ebits, &[], &[3], &map, &[1, 0, 0, 4, 0, 5], &[], &[], &t, &ebits, &[3, 9]);
    let live = check_sliver_lowering(&e, &ebits, &[], &[3], &map, &[1, 0, 0], &[], &[], &t, &ebits, &[3]);
    matches!(dead, Err(SliverCheckError::DeadEntry { .. })) && live.is_ok()
}
run_row_sliver_accept_two_reads_and_concrete_miss => { two_reads().run().is_ok() }
run_row_sliver_reject_missing_congruence_root => { let mut f = two_reads(); f.troots = vec![4, 8]; matches!(f.run(), Err(SliverCheckError::CongruenceMismatch { .. })) }
run_row_sliver_reject_missing_last_pair_root => { let mut f = two_reads(); f.troots = vec![4, 8, 12, 17]; matches!(f.run(), Err(SliverCheckError::CongruenceMismatch { .. })) }
run_row_sliver_reject_reordered_read_table => { let mut f = two_reads(); f.reads = vec![6, 0, 5, 2, 0, 0, 3, 0, 1]; f.run().is_err() }
run_row_sliver_reject_wrong_congruence_antecedent => { let mut f = two_reads(); f.t[9] = N::Eq(0, 0); f.run().is_err() }
run_row_sliver_reject_wrong_congruence_consequent => { let mut f = two_reads(); f.t[11] = N::Eq(2, 2); f.run().is_err() }
run_row_sliver_reject_wrong_congruence_shape => { let mut f = two_reads(); f.t[12] = N::BoolAnd(10, 11); f.run().is_err() }
run_row_sliver_reject_wrong_congruence_negation => { let mut f = two_reads(); f.t[10] = N::Eq(9, 9); f.run().is_err() }
run_row_sliver_reject_wrong_const_pair_root => { let mut f = two_reads(); f.t[17] = N::BoolOr(15, 15); f.run().is_err() }
run_row_sliver_reject_too_many_core_roots => { let mut f = two_reads(); f.troots.push(4); f.run().is_err() }
run_row_sliver_accept_call_site_congruence => { call_fixture().run().is_ok() }
run_row_sliver_reject_call_entry_over_shared_result => { let mut f = call_fixture(); f.calls = vec![2, 0, 0, 1, 2, 0, 1, 1]; matches!(f.run(), Err(SliverCheckError::CallTable { .. })) }
run_row_sliver_reject_call_wrong_antecedent => { let mut f = call_fixture(); f.t[5] = N::Eq(0, 0); matches!(f.run(), Err(SliverCheckError::CongruenceMismatch { .. })) }
run_row_sliver_reject_call_wrong_result_width => { let mut f = call_fixture(); f.t[3] = N::Var(16); f.run().is_err() }
run_row_sliver_reject_call_table_bad_var => { let mut f = call_fixture(); f.calls = vec![99, 0, 0, 1, 3, 0, 1, 1]; matches!(f.run(), Err(SliverCheckError::CallTable { .. })) }
run_row_sliver_reject_call_table_arg_past_core => { let mut f = call_fixture(); f.cargs = vec![0, 99]; f.run().is_err() }
run_row_sliver_reject_call_table_duplicate_site => { let mut f = call_fixture(); f.calls = vec![2, 0, 0, 1, 3, 0, 0, 1]; f.run().is_err() }
run_row_sliver_reject_call_table_args_outside => { let mut f = call_fixture(); f.calls = vec![2, 0, 5, 1, 3, 0, 1, 1]; f.run().is_err() }
run_row_sliver_reject_call_table_ragged => { let mut f = call_fixture(); f.calls = vec![2, 0, 0]; f.run().is_err() }
run_row_sliver_reject_call_node_bad_args_range => { let mut f = call_fixture(); f.e[2] = ExtNode::Call(0, 8, 5, 1); matches!(f.run(), Err(SliverCheckError::Ext { .. })) }
run_row_sliver_reject_call_node_zero_width => { let mut f = call_fixture(); f.e[2] = ExtNode::Call(0, 0, 0, 1); matches!(f.run(), Err(SliverCheckError::Ext { .. })) }
run_row_sliver_reject_call_node_arg_not_earlier => { let mut f = call_fixture(); f.eside = vec![9, 1]; matches!(f.run(), Err(SliverCheckError::Ext { .. })) }
run_row_sliver_reject_call_unregistered => { let mut f = call_fixture(); f.calls.clear(); f.run().is_err() }
run_row_sliver_reject_call_arg_image => { let mut f = call_fixture(); f.cargs = vec![1, 0]; f.run().is_err() }
run_row_sliver_reject_call_function_mismatch => { let mut f = call_fixture(); f.e[3] = ExtNode::Call(1, 8, 1, 1); f.run().is_err() }
run_row_ext_wf_accept => { let f = one_symbolic_store(); ext_wf(&f.e, f.ebits.len(), &f.eside).is_ok() }
run_row_ext_wf_reject_bad_node => { let f = one_symbolic_store(); ext_wf(&[ExtNode::Select(0, 7, 0, 0)], 0, &f.eside).is_err() }
run_row_ext_wf_reject_core_node => { ext_wf(&[ExtNode::Core(N::Var(0))], 0, &[]).is_err() }

// ═════════ flatten_tree / project_core / check_tree_model[_ext] ═════════
run_row_flatten_shares_names_and_constants => {
    let t = eq_t(Box::new(TBv::Add(var("x", 8), konst(5, 8))), Box::new(TBv::Add(konst(5, 8), var("x", 8))));
    let f = flatten_tree(&[t]).unwrap();
    project_core(&f.nodes).unwrap() == vec![N::Var(8), N::Const(0, 8), N::Add(0, 1), N::Add(1, 0), N::Eq(2, 3)] && f.roots == vec![4]
}
run_row_flatten_reject_name_at_two_widths => { flat_err(TBool::Ult(var("x", 8), Box::new(TBv::Extract(7, 0, var("x", 32))))) == Some(FlatError::NameWidth) }
run_row_flatten_two_names_unmasked_constants => {
    let t = TBool::Ne(Box::new(TBv::Add(var("ab", 8), konst(0x1FF, 8))), Box::new(TBv::Add(var("a", 8), konst(0xFF, 8))));
    let f = flatten_tree(&[t]).unwrap();
    f.var_node == vec![0, 3] && f.const_node == vec![1, 4]
}
run_row_flatten_select_and_call_sliver_order => {
    let chain = TArray::Store(Box::new(TArray::Var(b"a".to_vec())), var("i", 32),
        Box::new(TBv::Call(b"f".to_vec(), 8, Box::new(TArgs::Cons(var("x", 8), Box::new(TArgs::Nil))))));
    let t = eq_t(Box::new(TBv::Select(Box::new(chain), var("j", 32))), konst(0, 8));
    let f = flatten_tree(&[t]).unwrap();
    f.side == vec![2, 1, 3] && project_core(&f.nodes).err() == Some(FlatError::NotCore)
}
run_row_flatten_reject_function_at_two_widths => {
    let a = eq_t(Box::new(TBv::Call(b"f".to_vec(), 8, Box::new(TArgs::Nil))), konst(0, 8));
    let b = eq_t(Box::new(TBv::Call(b"f".to_vec(), 16, Box::new(TArgs::Nil))), konst(0, 16));
    flatten_tree(&[a, b]).err() == Some(FlatError::FuncWidth)
}
run_row_flatten_reject_select_index_not_bv32 => { flat_err(eq_t(Box::new(TBv::Select(Box::new(TArray::Var(b"a".to_vec())), var("k", 8))), konst(0, 8))) == Some(FlatError::BadArraySort) }
run_row_flatten_reject_store_index_not_bv32 => {
    let chain = TArray::Store(Box::new(TArray::Var(b"a".to_vec())), var("i", 8), konst(0, 8));
    flat_err(eq_t(Box::new(TBv::Select(Box::new(chain), var("j", 32))), konst(0, 8))) == Some(FlatError::BadArraySort)
}
run_row_flatten_reject_store_value_not_bv8 => {
    let chain = TArray::Store(Box::new(TArray::Var(b"a".to_vec())), var("i", 32), konst(0, 16));
    flat_err(eq_t(Box::new(TBv::Select(Box::new(chain), var("j", 32))), konst(0, 8))) == Some(FlatError::BadArraySort)
}
run_row_flatten_accept_two_arrays_two_calls_shared => {
    let sel = |a: &[u8], i: &str| Box::new(TBv::Select(Box::new(TArray::Var(a.to_vec())), var(i, 32)));
    let call = |n: &[u8], x: &str| Box::new(TBv::Call(n.to_vec(), 8, Box::new(TArgs::Cons(var(x, 8), Box::new(TArgs::Nil)))));
    let t1 = eq_t(sel(b"a", "i"), call(b"f", "x"));
    let t2 = eq_t(sel(b"b", "i"), call(b"g", "x"));
    let t3 = eq_t(sel(b"a", "k"), call(b"f", "y"));
    flatten_tree(&[t1, t2, t3]).is_ok()
}
run_row_flatten_reject_width_zero => { flat_err(eq_t(var("x", 0), var("y", 0))) == Some(FlatError::BadWidth) }
run_row_flatten_reject_width_over_128 => { flat_err(eq_t(var("x", 129), var("y", 129))) == Some(FlatError::BadWidth) }
run_row_flatten_reject_operand_width_mismatch => { flat_err(eq_t(var("x", 8), var("y", 9))) == Some(FlatError::BadWidth) }
run_row_flatten_reject_extract_hi_past_width => { flat_err(eq_t(Box::new(TBv::Extract(8, 0, var("x", 8))), var("y", 9))) == Some(FlatError::BadWidth) }
run_row_flatten_reject_extract_lo_gt_hi => { flat_err(eq_t(Box::new(TBv::Extract(2, 3, var("x", 8))), var("y", 1))) == Some(FlatError::BadWidth) }
run_row_flatten_reject_concat_past_128 => { flat_err(eq_t(Box::new(TBv::Concat(var("x", 64), var("y", 65))), var("z", 129))) == Some(FlatError::BadWidth) }
run_row_flatten_reject_zext_past_128 => { flat_err(eq_t(Box::new(TBv::ZeroExt(121, var("x", 8))), var("z", 129))) == Some(FlatError::BadWidth) }
run_row_flatten_reject_sext_past_128 => { flat_err(eq_t(Box::new(TBv::SignExt(121, var("x", 8))), var("z", 129))) == Some(FlatError::BadWidth) }
run_row_flatten_reject_ite_branch_widths => {
    flat_err(eq_t(Box::new(TBv::Ite(Box::new(eq_t(var("c", 1), konst(1, 1))), var("x", 8), var("y", 16))), var("z", 8))) == Some(FlatError::BadWidth)
}
run_row_flatten_accept_ite_extend_concat_extract => {
    let c = eq_t(var("c", 1), konst(1, 1));
    let ite = Box::new(TBv::Ite(Box::new(c), var("x", 8), var("y", 8)));
    let w = Box::new(TBv::Concat(Box::new(TBv::ZeroExt(4, Box::new(TBv::Extract(3, 0, ite)))), Box::new(TBv::SignExt(4, var("s", 4)))));
    flatten_tree(&[eq_t(w, var("z", 16))]).is_ok()
}
run_row_flatten_accept_every_binary_op => {
    let mk: [fn(Box<TBv>, Box<TBv>) -> TBv; 14] = [
        TBv::Add, TBv::Sub, TBv::Mul, TBv::Udiv, TBv::Urem, TBv::And, TBv::Or, TBv::Xor, TBv::Shl, TBv::Lshr, TBv::Ashr, TBv::Rotr, TBv::Rotl, TBv::Sdiv,
    ];
    let mut ok = true;
    for f in mk {
        ok &= flatten_tree(&[eq_t(Box::new(f(var("a", 8), var("b", 8))), var("c", 8))]).is_ok();
    }
    ok &= flatten_tree(&[eq_t(Box::new(TBv::Srem(var("a", 8), var("b", 8))), Box::new(TBv::Neg(Box::new(TBv::BvNot(var("c", 8))))))]).is_ok();
    ok
}
run_row_flatten_accept_every_comparison_and_connective => {
    let cmp: [fn(Box<TBv>, Box<TBv>) -> TBool; 8] = [TBool::Ult, TBool::Ule, TBool::Ugt, TBool::Uge, TBool::Slt, TBool::Sle, TBool::Sgt, TBool::Sge];
    let mut ts: Vec<TBool> = cmp.iter().map(|f| f(var("a", 8), var("b", 8))).collect();
    let and = TBool::And(Box::new(eq_t(var("a", 8), var("b", 8))), Box::new(TBool::Not(Box::new(TBool::Ne(var("a", 8), var("b", 8))))));
    ts.push(TBool::Or(Box::new(and), Box::new(eq_t(var("a", 8), konst(1, 8)))));
    flatten_tree(&ts).is_ok()
}
run_row_flatten_reject_bool_arg_width_in_second_operand => { flat_err(TBool::Ult(var("x", 8), var("y", 4))) == Some(FlatError::BadWidth) }
run_row_flatten_reject_call_arg_bad_width => { flat_err(eq_t(Box::new(TBv::Call(b"f".to_vec(), 8, Box::new(TArgs::Cons(var("x", 0), Box::new(TArgs::Nil))))), konst(0, 8))) == Some(FlatError::BadWidth) }
run_row_flatten_reject_call_result_width_zero => { flat_err(eq_t(Box::new(TBv::Call(b"f".to_vec(), 0, Box::new(TArgs::Nil))), konst(0, 1))) == Some(FlatError::BadWidth) }
run_row_flatten_reject_const_width_zero => { flat_err(eq_t(konst(1, 0), konst(1, 0))) == Some(FlatError::BadWidth) }
run_row_flatten_accept_empty_query => { flatten_tree(&[]).is_ok() }
run_row_flatten_accept_const_width_128 => { flatten_tree(&[eq_t(konst(u128::MAX, 128), konst(0, 128))]).is_ok() }
run_row_project_core_accept_empty => { project_core(&[]).is_ok() }
run_row_project_core_reject_select => { project_core(&[ExtNode::Select(0, 0, 0, 0)]).err() == Some(FlatError::NotCore) }
run_row_project_core_reject_call => { project_core(&[ExtNode::Call(0, 8, 0, 0)]).err() == Some(FlatError::NotCore) }
run_row_tree_model_accept_swapped_images => {
    let ns = [N::Var(8), N::Var(8)];
    let mut inp = vec![false; 16];
    inp[0] = true;
    inp[1] = true;
    for j in 0..8 { inp[8 + j] = (200u128 >> j) & 1 == 1; }
    check_tree_model(&[0, 1], &[8, 8], &[1, 0], &ns, &inp, &[200, 3])
}
run_row_tree_model_reject_wrong_values => {
    let ns = [N::Var(8), N::Var(8)];
    let mut inp = vec![false; 16];
    inp[0] = true;
    inp[1] = true;
    for j in 0..8 { inp[8 + j] = (200u128 >> j) & 1 == 1; }
    !check_tree_model(&[0, 1], &[8, 8], &[1, 0], &ns, &inp, &[3, 200])
}
run_row_tree_model_accept_unmapped_skipped => {
    let ns = [N::Var(8), N::Var(8)];
    let inp = vec![false; 16];
    check_tree_model(&[0, 1], &[8, 8], &[1, NONE], &ns, &inp, &[0, 7])
}
run_row_tree_model_reject_length_mismatch => { !check_tree_model(&[0, 1], &[8, 8], &[1, 0], &[N::Var(8), N::Var(8)], &[false; 16], &[200]) }
run_row_tree_model_reject_width_table_length => { !check_tree_model(&[0, 1], &[8], &[1, 0], &[N::Var(8), N::Var(8)], &[false; 16], &[0, 0]) }
run_row_tree_model_reject_image_not_a_var => { !check_tree_model(&[0], &[8], &[1], &[N::Var(8), N::Const(0, 8)], &[false; 8], &[0]) }
run_row_tree_model_reject_input_block_too_short => { !check_tree_model(&[0], &[8], &[0], &[N::Var(8)], &[false; 4], &[0]) }
run_row_tree_model_accept_reads_declared_width => { check_tree_model(&[0], &[4], &[0], &[N::Var(8)], &[false; 8], &[0]) }
run_row_tree_model_ext_accept => {
    let ns = [N::Var(8), N::Var(8)];
    let mut inp = vec![false; 16];
    inp[0] = true;
    inp[1] = true;
    for j in 0..8 { inp[8 + j] = (200u128 >> j) & 1 == 1; }
    check_tree_model_ext(&[0, 1], &[8, 8], &[1, 0], &[N::Var(8), N::Var(8)], &[0, 1], &ns, &inp, &[200, 3])
}
run_row_tree_model_ext_reject_wrong_values => {
    let ns = [N::Var(8), N::Var(8)];
    let mut inp = vec![false; 16];
    inp[0] = true;
    inp[1] = true;
    for j in 0..8 { inp[8 + j] = (200u128 >> j) & 1 == 1; }
    !check_tree_model_ext(&[0, 1], &[8, 8], &[1, 0], &[N::Var(8), N::Var(8)], &[0, 1], &ns, &inp, &[3, 200])
}
run_row_tree_model_ext_reject_core_image_width => {
    let ns = [N::Var(8), N::Var(8)];
    let inp = vec![false; 16];
    !check_tree_model_ext(&[0, 1], &[8, 8], &[1, 0], &[N::Var(8), N::Var(16)], &[0, 1], &ns, &inp, &[0, 0])
}
run_row_tree_model_ext_reject_core_image_not_var => {
    let ns = [N::Var(8)];
    !check_tree_model_ext(&[0], &[8], &[0], &[N::Const(0, 8)], &[0], &ns, &[false; 8], &[0])
}
run_row_tree_model_ext_reject_core_image_past_end => {
    let ns = [N::Var(8)];
    !check_tree_model_ext(&[0], &[8], &[5], &[N::Var(8)], &[0], &ns, &[false; 8], &[0])
}
run_row_tree_model_ext_accept_unmapped_skipped => {
    let ns = [N::Var(8)];
    check_tree_model_ext(&[0, 1], &[8, 8], &[NONE, 0], &[N::Var(8)], &[NONE], &ns, &[false; 8], &[9, 9])
}
run_row_tree_model_ext_reject_length_mismatch => { !check_tree_model_ext(&[0], &[8], &[0], &[N::Var(8)], &[0], &[N::Var(8)], &[false; 8], &[]) }
run_row_tree_model_ext_reject_width_table_length => { !check_tree_model_ext(&[0, 1], &[8], &[0, 0], &[N::Var(8)], &[0], &[N::Var(8)], &[false; 8], &[0, 0]) }

// ═════════ blast_kernel (through check_query's encode + compact + Tseitin) ═════════
run_row_blast_add_sub_w1 => { binop_encodes(1, N::Add) && binop_encodes(1, N::Sub) }
run_row_blast_add_sub_w5 => { binop_encodes(5, N::Add) && binop_encodes(5, N::Sub) }
run_row_blast_mul_w1 => { binop_encodes(1, N::Mul) }
run_row_blast_mul_w4 => { binop_encodes(4, N::Mul) }
run_row_blast_udiv_urem_w1 => { binop_encodes(1, N::Udiv) && binop_encodes(1, N::Urem) }
run_row_blast_udiv_urem_w4 => { binop_encodes(4, N::Udiv) && binop_encodes(4, N::Urem) }
run_row_blast_sdiv_srem_w1 => { binop_encodes(1, N::Sdiv) && binop_encodes(1, N::Srem) }
run_row_blast_sdiv_srem_w4 => { binop_encodes(4, N::Sdiv) && binop_encodes(4, N::Srem) }
run_row_blast_bitwise_w3 => { binop_encodes(3, N::And) && binop_encodes(3, N::Or) && binop_encodes(3, N::Xor) }
run_row_blast_shifts_pow2_w1 => { binop_encodes(1, N::Shl) && binop_encodes(1, N::Lshr) && binop_encodes(1, N::Ashr) }
run_row_blast_shifts_pow2_w4 => { binop_encodes(4, N::Shl) && binop_encodes(4, N::Lshr) && binop_encodes(4, N::Ashr) }
run_row_blast_shifts_non_pow2_w5 => { binop_encodes(5, N::Shl) && binop_encodes(5, N::Lshr) && binop_encodes(5, N::Ashr) }
run_row_blast_shifts_non_pow2_w3 => { binop_encodes(3, N::Shl) && binop_encodes(3, N::Lshr) && binop_encodes(3, N::Ashr) }
run_row_blast_rotates_pow2_w4 => { binop_encodes(4, N::Rotr) && binop_encodes(4, N::Rotl) }
run_row_blast_rotates_non_pow2_w5 => { binop_encodes(5, N::Rotr) && binop_encodes(5, N::Rotl) }
run_row_blast_rotates_w1 => { binop_encodes(1, N::Rotr) && binop_encodes(1, N::Rotl) }
run_row_blast_unsigned_comparisons_w4 => { cmp_encodes(4, N::Ult) && cmp_encodes(4, N::Ule) && cmp_encodes(4, N::Ugt) && cmp_encodes(4, N::Uge) }
run_row_blast_signed_comparisons_w4 => { cmp_encodes(4, N::Slt) && cmp_encodes(4, N::Sle) && cmp_encodes(4, N::Sgt) && cmp_encodes(4, N::Sge) }
run_row_blast_signed_comparisons_w1 => { cmp_encodes(1, N::Slt) && cmp_encodes(1, N::Sge) }
run_row_blast_eq_ne_w3 => { cmp_encodes(3, N::Eq) && cmp_encodes(3, N::Ne) }
run_row_blast_extract_concat_extend => {
    let ns = vec![N::Var(8), N::Extract(7, 4, 0), N::Extract(3, 0, 0), N::Concat(2, 1), N::ZeroExt(1, 4), N::SignExt(2, 4), N::Eq(3, 0), N::Eq(4, 5)];
    encodes(&ns, &[], &[6, 7], &[])
}
run_row_blast_extend_by_zero_and_full_extract => {
    let ns = vec![N::Var(4), N::ZeroExt(0, 0), N::SignExt(0, 0), N::Extract(3, 0, 0), N::Eq(0, 1), N::Eq(2, 3)];
    encodes(&ns, &[], &[4, 5], &[])
}
run_row_blast_ite_and_boolean_connectives => {
    let ns = vec![N::Var(1), N::Var(4), N::Var(4), N::Ite(0, 1, 2), N::Eq(3, 1), N::Not(4), N::BoolAnd(0, 5), N::BoolOr(6, 4)];
    encodes(&ns, &[], &[7], &[])
}
run_row_blast_unary_derived_ops => {
    let ns = vec![N::Var(5), N::BvNot(0), N::Neg(0), N::Eq(1, 2)];
    encodes(&ns, &[], &[3], &[])
}
run_row_blast_const_operands => {
    let ns = vec![N::Const(0, 4), N::Const(4, 4), N::Add(0, 1), N::Mul(0, 1), N::Udiv(0, 1), N::Eq(2, 3), N::Eq(4, 0)];
    let mut bits = cbits(9, 4);
    bits.extend(cbits(0, 4));
    encodes(&ns, &bits, &[5, 6], &[])
}
run_row_blast_all_hints_shared => {
    let ns = vec![N::Var(1), N::Var(1), N::Add(0, 1), N::Add(0, 1), N::Mul(0, 1), N::Mul(0, 1), N::Ult(2, 3), N::Ult(4, 5), N::BoolOr(6, 7)];
    let hints = hints_for(&ns, &[], &[8]);
    encodes(&ns, &[], &[8], &hints)
}
run_row_blast_stage_count_matches_log2 => {
    // stage_count(w) = (ceil(log2 w), w is a power of two)
    let cases = [(1usize, 0usize, true), (2, 1, true), (3, 2, false), (4, 2, true), (5, 3, false), (8, 3, true), (9, 4, false), (16, 4, true), (17, 5, false)];
    cases.iter().all(|&(w, s, p)| blast_kernel::stage_count(w) == (s, p))
}
run_row_blast_capacity_checks => {
    kernel::encode_fits(0, 0) && kernel::encode_fits(128, 1 << 20) && !kernel::encode_fits(0, usize::MAX)
        && !kernel::encode_fits(usize::MAX / 1000, 1) && !kernel::encode_fits(1 << 16, usize::MAX / 1000)
        && kernel::encode_fits(1, (usize::MAX - 1) / 141) && !kernel::encode_fits(1, (usize::MAX - 1) / 141 + 1)
        && kernel::tseitin_fits(0, 0) && kernel::tseitin_fits((usize::MAX - 2) / 3, 0)
        && !kernel::tseitin_fits((usize::MAX - 2) / 3 + 1, 0) && !kernel::tseitin_fits(0, usize::MAX - 1)
        && kernel::tseitin_fits(0, usize::MAX - 2)
}
run_row_blast_roots_and_widths_helpers => {
    kernel::roots_wf(&[8, 1, 1], &[1, 2]).is_ok() && kernel::roots_wf(&[8, 1], &[1, 0]).is_err()
        && kernel::roots_wf(&[8, 1], &[2]).is_err() && kernel::max_width(&[3, 9, 2]) == 9 && kernel::max_width(&[]) == 0
}
}

#[cfg(test)]
mod tests {
    use super::ROWS;

    /// Every row returns 1: it exercised the vector its name claims, with
    /// the verdict its name claims. Run natively; `witness` does not look
    /// at the return values.
    #[test]
    fn every_row_gets_its_expected_verdict() {
        let mut bad = Vec::new();
        for (name, row) in ROWS {
            if row() != 1 {
                bad.push(*name);
            }
        }
        assert!(bad.is_empty(), "rows with an unexpected verdict: {bad:?}");
    }

    #[test]
    fn row_names_are_unique() {
        let mut names: Vec<&str> = ROWS.iter().map(|(n, _)| *n).collect();
        names.sort_unstable();
        let before = names.len();
        names.dedup();
        assert_eq!(before, names.len());
    }
}
