//! The pure-Rust CDCL SAT core (DES-004) — primary engine on every target.
//!
//! Implements the classic conflict-driven clause-learning loop: two-watched-
//! literal propagation, first-UIP conflict analysis with clause learning,
//! VSIDS-style decision activities with phase saving, and Luby-sequence
//! restarts (conflict-counter based — no wall clock, so the engine runs
//! unchanged on wasm32-wasip2 and is fully deterministic). Learned clauses
//! are never deleted, which also keeps proof-trace indices stable.
//!
//! # Proof trace (the P2 LRAT hook, TR-005)
//!
//! Every learned clause is recorded as a [`LearnedStep`] carrying the
//! antecedent clauses used in its conflict-analysis resolution. Antecedent
//! indices refer to the combined original+learned clause sequence: index
//! `i < n` is `formula.clauses[i]` exactly as passed to [`SatSolver::solve`]
//! (tautologies and duplicate literals included, so original indices line up
//! one-to-one with the input), and index `n + k` is the clause of the `k`-th
//! [`LearnedStep`], where `n = formula.clauses.len()`.
//!
//! The antecedents of each step form a reverse-unit-propagation (RUP) chain:
//! assume the negation of every literal in `clause`, then process the
//! antecedents in order — each becomes unit (propagate its remaining
//! literal) until the last, which becomes falsified. Concretely the order is
//! root-level (level-0) unit reasons in assignment order, then the first-UIP
//! resolution reasons in trail order, then the conflicting clause last. When
//! the result is [`SatResult::Unsat`] the final step's `clause` is empty:
//! that step records the derivation of the empty clause.

use crate::cnf::CnfFormula;
use core::cmp::Ordering;

/// The verdict of a SAT solve.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SatResult {
    /// Satisfiable, with `assignment[v-1]` giving variable `v`'s value.
    Sat(Vec<bool>),
    /// Unsatisfiable.
    Unsat,
}

/// One clause-learning step of the resolution proof (see module docs for
/// the indexing convention and the RUP ordering of `antecedents`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LearnedStep {
    /// The learned clause in DIMACS literals; empty for the final conflict.
    pub clause: Vec<i32>,
    /// Antecedent clause indices into the original+learned sequence.
    pub antecedents: Vec<usize>,
}

/// Internal literal: variable `v` (0-based) is `2v` positive, `2v+1` negated.
type ILit = u32;

/// Sentinel for "assigned by decision / unassigned" in the reason array.
const NO_REASON: usize = usize::MAX;

/// Restart interval unit: restart after `64 * luby(k)` conflicts.
const RESTART_BASE: u64 = 64;

/// VSIDS activity decay factor (activities effectively multiply by this
/// per conflict; implemented by growing the increment).
const VAR_DECAY: f64 = 0.95;

fn ilit(l: i32) -> ILit {
    debug_assert!(l != 0, "DIMACS literals are nonzero");
    ((l.unsigned_abs() - 1) << 1) | u32::from(l < 0)
}

fn ivar(l: ILit) -> usize {
    (l >> 1) as usize
}

fn dimacs(l: ILit) -> i32 {
    let v = (l >> 1) as i32 + 1;
    if l & 1 == 1 { -v } else { v }
}

/// The `i`-th element of the Luby sequence 1,1,2,1,1,2,4,… (0-based).
fn luby(i: u64) -> u64 {
    let (mut size, mut seq, mut x) = (1u64, 0u32, i);
    while size < x + 1 {
        seq += 1;
        size = 2 * size + 1;
    }
    while size - 1 != x {
        size = (size - 1) / 2;
        seq -= 1;
        x %= size;
    }
    1 << seq
}

/// Max-heap over variables ordered by activity, ties broken toward the
/// smaller variable index so decisions are deterministic.
#[derive(Debug, Default)]
struct VarOrder {
    heap: Vec<u32>,
    /// Position of each variable in `heap`, or `usize::MAX` if absent.
    pos: Vec<usize>,
}

fn better(act: &[f64], a: u32, b: u32) -> bool {
    match act[a as usize].partial_cmp(&act[b as usize]) {
        Some(Ordering::Greater) => true,
        Some(Ordering::Equal) => a < b,
        _ => false,
    }
}

impl VarOrder {
    fn reset(&mut self, n: usize) {
        // `heap[i] = i` with all-zero activities already satisfies the heap
        // property (ties break toward the smaller index).
        self.heap = (0..n as u32).collect();
        self.pos = (0..n).collect();
    }

    fn insert(&mut self, act: &[f64], v: u32) {
        if self.pos[v as usize] != usize::MAX {
            return;
        }
        self.pos[v as usize] = self.heap.len();
        self.heap.push(v);
        self.sift_up(act, self.heap.len() - 1);
    }

    /// Restore the heap after `v`'s activity increased.
    fn update(&mut self, act: &[f64], v: u32) {
        let i = self.pos[v as usize];
        if i != usize::MAX {
            self.sift_up(act, i);
        }
    }

    fn pop(&mut self, act: &[f64]) -> Option<u32> {
        let top = *self.heap.first()?;
        self.pos[top as usize] = usize::MAX;
        let last = self.heap.pop().expect("heap is non-empty");
        if !self.heap.is_empty() {
            self.heap[0] = last;
            self.pos[last as usize] = 0;
            self.sift_down(act, 0);
        }
        Some(top)
    }

    fn sift_up(&mut self, act: &[f64], mut i: usize) {
        while i > 0 {
            let parent = (i - 1) / 2;
            if !better(act, self.heap[i], self.heap[parent]) {
                break;
            }
            self.swap(i, parent);
            i = parent;
        }
    }

    fn sift_down(&mut self, act: &[f64], mut i: usize) {
        loop {
            let (l, r) = (2 * i + 1, 2 * i + 2);
            let mut best = i;
            if l < self.heap.len() && better(act, self.heap[l], self.heap[best]) {
                best = l;
            }
            if r < self.heap.len() && better(act, self.heap[r], self.heap[best]) {
                best = r;
            }
            if best == i {
                break;
            }
            self.swap(i, best);
            i = best;
        }
    }

    fn swap(&mut self, i: usize, j: usize) {
        self.heap.swap(i, j);
        self.pos[self.heap[i] as usize] = i;
        self.pos[self.heap[j] as usize] = j;
    }
}

/// The CDCL solver.
#[derive(Debug, Default)]
pub struct SatSolver {
    /// Clause database: input clauses (sorted, deduped) then learned ones.
    /// Index `i` matches the proof-trace convention in the module docs.
    clauses: Vec<Vec<ILit>>,
    /// Number of original clauses (`formula.clauses.len()`).
    n_orig: usize,
    /// For each literal, the clauses currently watching it. A watched
    /// clause keeps its two watched literals at positions 0 and 1.
    watches: Vec<Vec<usize>>,
    assign: Vec<Option<bool>>,
    /// Decision level at which each variable was assigned.
    level: Vec<u32>,
    /// Clause that propagated each variable, or `NO_REASON` for decisions.
    reason: Vec<usize>,
    trail: Vec<ILit>,
    /// Trail length at each decision; `trail_lim.len()` is the current level.
    trail_lim: Vec<usize>,
    /// Propagation queue head (index into `trail`).
    qhead: usize,
    activity: Vec<f64>,
    var_inc: f64,
    order: VarOrder,
    saved_phase: Vec<bool>,
    /// Conflict-analysis scratch: variables already visited.
    seen: Vec<bool>,
    /// Root-support scratch: level-0 variables whose reasons are needed.
    mark: Vec<bool>,
    trace: Vec<LearnedStep>,
    restarts: u64,
    conflicts_since_restart: u64,
}

impl SatSolver {
    /// Create a solver.
    pub fn new() -> Self {
        Self::default()
    }

    /// Decide satisfiability of the formula (unbounded — always a verdict).
    pub fn solve(&mut self, formula: &CnfFormula) -> SatResult {
        self.run(formula, None, None)
            .expect("an unbounded solve always reaches a verdict")
    }

    /// Decide satisfiability under a conflict budget (DES-019).
    ///
    /// Runs the same deterministic CDCL search as [`SatSolver::solve`] but
    /// abandons it once search conflicts exceed `max_conflicts`, returning
    /// `None` — no verdict reached within budget. Any decided verdict (SAT,
    /// or an UNSAT refuted by propagation/root conflict without exceeding the
    /// budget) is returned as `Some`, identical to `solve`, with the proof
    /// trace intact. A `max_conflicts` of 0 admits only queries decided
    /// before the first search conflict.
    pub fn solve_with_budget(
        &mut self,
        formula: &CnfFormula,
        max_conflicts: u64,
    ) -> Option<SatResult> {
        self.run(formula, Some(max_conflicts), None)
    }

    /// Decide satisfiability under a wall-clock deadline (TR-029, issue #71).
    ///
    /// The consumer-facing twin of [`solve_with_budget`]: a translation
    /// validator degrades a slow solve to a fast, safe revert on a
    /// *millisecond* budget, which a conflict count does not map to. Search is
    /// abandoned once `deadline` passes, returning `None` — no verdict. Any
    /// decided verdict is identical to [`solve`], proof trace intact. The
    /// deadline is checked at the same per-conflict site as the budget, so a
    /// query decided by pure propagation is never abandoned.
    ///
    /// [`solve_with_budget`]: SatSolver::solve_with_budget
    /// [`solve`]: SatSolver::solve
    pub fn solve_with_deadline(
        &mut self,
        formula: &CnfFormula,
        deadline: std::time::Instant,
    ) -> Option<SatResult> {
        self.run(formula, None, Some(deadline))
    }

    /// Shared solve entry: `budget` of `None` is unbounded (never `None`
    /// return), `Some(max)` bounds search conflicts and returns `None` on
    /// exhaustion. On any decided path the behaviour is bit-for-bit that of
    /// the original `solve`, so determinism and the proof-trace hook are
    /// unaffected.
    fn run(
        &mut self,
        formula: &CnfFormula,
        budget: Option<u64>,
        deadline: Option<std::time::Instant>,
    ) -> Option<SatResult> {
        // Tolerate literals above `num_vars` by sizing to whichever is larger.
        let n = formula
            .clauses
            .iter()
            .flatten()
            .map(|l| l.unsigned_abs())
            .max()
            .unwrap_or(0)
            .max(formula.num_vars) as usize;
        self.reset(n);
        if !self.load(formula) {
            return Some(SatResult::Unsat);
        }
        if let Some(confl) = self.propagate() {
            self.record_root_conflict(confl);
            return Some(SatResult::Unsat);
        }
        self.search(budget, deadline)
    }

    /// The resolution proof recorded so far: one step per learned clause,
    /// in derivation order. Non-empty exactly when the last solve returned
    /// `Unsat` after at least one conflict; its final step derives the
    /// empty clause. See the module docs for the index convention.
    pub fn proof_trace(&self) -> &[LearnedStep] {
        &self.trace
    }

    fn reset(&mut self, n: usize) {
        self.clauses.clear();
        self.n_orig = 0;
        self.watches = vec![Vec::new(); 2 * n];
        self.assign = vec![None; n];
        self.level = vec![0; n];
        self.reason = vec![NO_REASON; n];
        self.trail.clear();
        self.trail_lim.clear();
        self.qhead = 0;
        self.activity = vec![0.0; n];
        self.var_inc = 1.0;
        self.order.reset(n);
        self.saved_phase = vec![false; n];
        self.seen = vec![false; n];
        self.mark = vec![false; n];
        self.trace.clear();
        self.restarts = 0;
        self.conflicts_since_restart = 0;
    }

    /// Load the clause database, applying input hygiene. Every input clause
    /// is stored (so DB indices match input indices); tautologies are kept
    /// but never watched, duplicate literals are removed, units are enqueued
    /// at level 0. Returns `false` on an immediate root-level contradiction.
    fn load(&mut self, formula: &CnfFormula) -> bool {
        self.n_orig = formula.clauses.len();
        for input in &formula.clauses {
            let mut lits: Vec<ILit> = input.iter().map(|&l| ilit(l)).collect();
            lits.sort_unstable();
            lits.dedup();
            // After sorting, complementary literals of a variable are adjacent.
            let tautology = lits.windows(2).any(|w| w[0] ^ 1 == w[1]);
            let idx = self.clauses.len();
            self.clauses.push(lits);
            if tautology {
                continue;
            }
            match self.clauses[idx].len() {
                0 => {
                    // The input contains the empty clause: trivially Unsat,
                    // certified by the clause itself.
                    self.trace.push(LearnedStep {
                        clause: Vec::new(),
                        antecedents: vec![idx],
                    });
                    return false;
                }
                1 => {
                    let l = self.clauses[idx][0];
                    match self.lit_value(l) {
                        Some(true) => {}
                        Some(false) => {
                            self.record_root_conflict(idx);
                            return false;
                        }
                        None => self.enqueue(l, idx),
                    }
                }
                _ => {
                    let (w0, w1) = (self.clauses[idx][0], self.clauses[idx][1]);
                    self.watches[w0 as usize].push(idx);
                    self.watches[w1 as usize].push(idx);
                }
            }
        }
        true
    }

    /// The CDCL search loop. `budget` bounds the number of search conflicts:
    /// once it is exceeded the search yields `None` (no verdict), otherwise a
    /// verdict is always returned as `Some`. `None` budget is unbounded.
    fn search(
        &mut self,
        budget: Option<u64>,
        deadline: Option<std::time::Instant>,
    ) -> Option<SatResult> {
        let mut conflicts = 0u64;
        loop {
            if let Some(confl) = self.propagate() {
                if self.trail_lim.is_empty() {
                    self.record_root_conflict(confl);
                    return Some(SatResult::Unsat);
                }
                self.conflicts_since_restart += 1;
                conflicts += 1;
                // Budget check before conflict analysis: on exhaustion we
                // abandon search without touching the proof trace.
                if budget.is_some_and(|max| conflicts > max) {
                    return None;
                }
                // Deadline check at the same site: cheap (vDSO clock read)
                // relative to conflict analysis, and never abandons a query
                // decided by propagation alone.
                if deadline.is_some_and(|d| std::time::Instant::now() >= d) {
                    return None;
                }
                let (learnt, bt_level, antecedents) = self.analyze(confl);
                self.trace.push(LearnedStep {
                    clause: learnt.iter().map(|&l| dimacs(l)).collect(),
                    antecedents,
                });
                self.backtrack(bt_level);
                let ci = self.clauses.len();
                if learnt.len() >= 2 {
                    self.watches[learnt[0] as usize].push(ci);
                    self.watches[learnt[1] as usize].push(ci);
                }
                let asserting = learnt[0];
                self.clauses.push(learnt);
                // The learned clause is asserting after backtracking.
                self.enqueue(asserting, ci);
                self.var_inc /= VAR_DECAY;
            } else if self.conflicts_since_restart >= RESTART_BASE * luby(self.restarts) {
                self.restarts += 1;
                self.conflicts_since_restart = 0;
                self.backtrack(0);
            } else {
                match self.pick_branch() {
                    None => return Some(SatResult::Sat(self.model())),
                    Some(l) => {
                        self.trail_lim.push(self.trail.len());
                        self.enqueue(l, NO_REASON);
                    }
                }
            }
        }
    }

    fn lit_value(&self, l: ILit) -> Option<bool> {
        self.assign[ivar(l)].map(|b| b == (l & 1 == 0))
    }

    fn enqueue(&mut self, l: ILit, reason: usize) {
        let v = ivar(l);
        debug_assert!(self.assign[v].is_none());
        self.assign[v] = Some(l & 1 == 0);
        self.level[v] = self.trail_lim.len() as u32;
        self.reason[v] = reason;
        self.trail.push(l);
    }

    /// Two-watched-literal propagation to fixpoint; returns a conflicting
    /// clause index if one is found.
    fn propagate(&mut self) -> Option<usize> {
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            let fl = p ^ 1; // the literal that just became false
            let mut ws = core::mem::take(&mut self.watches[fl as usize]);
            let mut i = 0;
            'clauses: while i < ws.len() {
                let ci = ws[i];
                if self.clauses[ci][0] == fl {
                    self.clauses[ci].swap(0, 1);
                }
                debug_assert_eq!(self.clauses[ci][1], fl);
                let first = self.clauses[ci][0];
                if self.lit_value(first) == Some(true) {
                    i += 1;
                    continue;
                }
                // Look for a replacement watch among the tail literals.
                for k in 2..self.clauses[ci].len() {
                    let q = self.clauses[ci][k];
                    if self.lit_value(q) != Some(false) {
                        self.clauses[ci].swap(1, k);
                        self.watches[q as usize].push(ci);
                        ws.swap_remove(i);
                        continue 'clauses;
                    }
                }
                // No replacement: the clause is unit or conflicting.
                if self.lit_value(first) == Some(false) {
                    self.watches[fl as usize] = ws;
                    return Some(ci);
                }
                self.enqueue(first, ci);
                i += 1;
            }
            self.watches[fl as usize] = ws;
        }
        None
    }

    /// First-UIP conflict analysis. Returns the learned clause (asserting
    /// literal at position 0, a deepest remaining literal at position 1),
    /// the backtrack level, and the RUP-ordered antecedents.
    fn analyze(&mut self, confl: usize) -> (Vec<ILit>, usize, Vec<usize>) {
        let cur_level = self.trail_lim.len() as u32;
        let mut learnt: Vec<ILit> = vec![0]; // slot 0 reserved for the UIP
        let mut chain: Vec<usize> = Vec::new(); // reasons, resolution order
        let mut level0_seeds: Vec<usize> = Vec::new();
        let mut to_clear: Vec<usize> = Vec::new();
        let mut counter = 0usize; // unresolved current-level literals
        let mut idx = self.trail.len();
        let mut c = confl;
        let mut skip_first = false;
        let uip;
        loop {
            // Skip position 0 of reason clauses: it is the propagated
            // (pivot) literal, already accounted for.
            let mut k = usize::from(skip_first);
            while k < self.clauses[c].len() {
                let q = self.clauses[c][k];
                k += 1;
                let v = ivar(q);
                if self.seen[v] {
                    continue;
                }
                if self.level[v] == 0 {
                    // Resolved away against a root-level unit; remember it
                    // so the proof chain can include its reason.
                    if !self.mark[v] {
                        self.mark[v] = true;
                        level0_seeds.push(v);
                    }
                    continue;
                }
                self.seen[v] = true;
                to_clear.push(v);
                self.bump(v);
                if self.level[v] == cur_level {
                    counter += 1;
                } else {
                    learnt.push(q);
                }
            }
            // Next pivot: the most recently assigned marked literal.
            loop {
                idx -= 1;
                if self.seen[ivar(self.trail[idx])] {
                    break;
                }
            }
            let pivot = self.trail[idx];
            counter -= 1;
            if counter == 0 {
                uip = pivot;
                break;
            }
            c = self.reason[ivar(pivot)];
            chain.push(c);
            skip_first = true;
        }
        learnt[0] = uip ^ 1;
        for v in to_clear {
            self.seen[v] = false;
        }
        // Backtrack to the second-highest level; keep one literal of that
        // level at position 1 so it can be watched.
        let bt_level = if learnt.len() == 1 {
            0
        } else {
            let mut deepest = 1;
            for k in 2..learnt.len() {
                if self.level[ivar(learnt[k])] > self.level[ivar(learnt[deepest])] {
                    deepest = k;
                }
            }
            learnt.swap(1, deepest);
            self.level[ivar(learnt[1])] as usize
        };
        // RUP order: level-0 support first, then the resolution reasons in
        // trail (reverse-resolution) order, then the conflicting clause.
        let mut antecedents = self.root_support(&level0_seeds);
        chain.reverse();
        antecedents.extend(chain);
        antecedents.push(confl);
        (learnt, bt_level, antecedents)
    }

    /// Reasons of the given level-0 variables plus, transitively, of the
    /// level-0 variables those reasons mention, in assignment order.
    /// Expects `self.mark` set for the seeds; clears it.
    fn root_support(&mut self, seeds: &[usize]) -> Vec<usize> {
        if seeds.is_empty() {
            return Vec::new();
        }
        let root_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());
        let mut support = Vec::new();
        for i in (0..root_end).rev() {
            let v = ivar(self.trail[i]);
            if self.mark[v] {
                self.mark[v] = false;
                // Every level-0 assignment has a clause reason (there are
                // no decisions below level 1).
                let r = self.reason[v];
                debug_assert_ne!(r, NO_REASON);
                support.push(r);
                for k in 1..self.clauses[r].len() {
                    self.mark[ivar(self.clauses[r][k])] = true;
                }
            }
        }
        support.reverse();
        support
    }

    /// A conflict at decision level 0 refutes the formula: record the
    /// derivation of the empty clause (level-0 unit reasons in assignment
    /// order, then the conflicting clause).
    fn record_root_conflict(&mut self, confl: usize) {
        debug_assert!(self.trail_lim.is_empty());
        let mut seeds = Vec::new();
        for k in 0..self.clauses[confl].len() {
            let v = ivar(self.clauses[confl][k]);
            if !self.mark[v] {
                self.mark[v] = true;
                seeds.push(v);
            }
        }
        let mut antecedents = self.root_support(&seeds);
        antecedents.push(confl);
        self.trace.push(LearnedStep {
            clause: Vec::new(),
            antecedents,
        });
    }

    fn backtrack(&mut self, target_level: usize) {
        if self.trail_lim.len() <= target_level {
            return;
        }
        let end = self.trail_lim[target_level];
        for i in (end..self.trail.len()).rev() {
            let l = self.trail[i];
            let v = ivar(l);
            self.saved_phase[v] = l & 1 == 0;
            self.assign[v] = None;
            self.order.insert(&self.activity, v as u32);
        }
        self.trail.truncate(end);
        self.trail_lim.truncate(target_level);
        self.qhead = end;
    }

    fn bump(&mut self, v: usize) {
        self.activity[v] += self.var_inc;
        if self.activity[v] > 1e100 {
            for a in &mut self.activity {
                *a *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }
        self.order.update(&self.activity, v as u32);
    }

    fn pick_branch(&mut self) -> Option<ILit> {
        while let Some(v) = self.order.pop(&self.activity) {
            let v = v as usize;
            if self.assign[v].is_none() {
                return Some(((v as u32) << 1) | u32::from(!self.saved_phase[v]));
            }
        }
        None
    }

    fn model(&self) -> Vec<bool> {
        // `pick_branch` returned `None`, so every variable is assigned.
        self.assign
            .iter()
            .map(|a| a.expect("full assignment at Sat"))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn formula(num_vars: u32, clauses: &[&[i32]]) -> CnfFormula {
        CnfFormula {
            num_vars,
            clauses: clauses.iter().map(|c| c.to_vec()).collect(),
        }
    }

    /// Brute-force satisfiability of a CNF (≤ 20 vars) — test-only oracle.
    fn brute_sat(f: &CnfFormula) -> bool {
        let n = f.num_vars as usize;
        assert!(n <= 20);
        (0u64..1 << n).any(|bits| {
            let assignment: Vec<bool> = (0..n).map(|i| bits >> i & 1 == 1).collect();
            f.eval(&assignment)
        })
    }

    fn assert_sat_with_model(f: &CnfFormula) -> Vec<bool> {
        match SatSolver::new().solve(f) {
            SatResult::Sat(model) => {
                assert!(model.len() >= f.num_vars as usize);
                assert!(f.eval(&model), "returned model must satisfy the formula");
                model
            }
            SatResult::Unsat => panic!("expected Sat"),
        }
    }

    #[test]
    fn empty_formula_is_sat() {
        assert_sat_with_model(&formula(0, &[]));
        // Unconstrained variables still get values.
        let model = assert_sat_with_model(&formula(3, &[]));
        assert_eq!(model.len(), 3);
    }

    #[test]
    fn empty_clause_is_unsat() {
        let f = formula(2, &[&[1, 2], &[], &[-1]]);
        let mut solver = SatSolver::new();
        assert_eq!(solver.solve(&f), SatResult::Unsat);
        // The trace certifies via the empty input clause itself (index 1).
        assert_eq!(solver.proof_trace().len(), 1);
        assert!(solver.proof_trace()[0].clause.is_empty());
        assert_eq!(solver.proof_trace()[0].antecedents, vec![1]);
    }

    #[test]
    fn chained_unit_propagation() {
        // 1, 1→2, 2→3, …, 9→10 forces every variable true.
        let mut clauses: Vec<Vec<i32>> = vec![vec![1]];
        for v in 1..10 {
            clauses.push(vec![-v, v + 1]);
        }
        let f = CnfFormula {
            num_vars: 10,
            clauses,
        };
        let model = assert_sat_with_model(&f);
        assert!(model.iter().all(|&b| b), "the chain forces all-true");

        // Adding ¬10 closes the chain into a root-level contradiction.
        let mut clauses = f.clauses.clone();
        clauses.push(vec![-10]);
        let g = CnfFormula {
            num_vars: 10,
            clauses,
        };
        let mut solver = SatSolver::new();
        assert_eq!(solver.solve(&g), SatResult::Unsat);
        let trace = solver.proof_trace();
        assert!(!trace.is_empty());
        assert!(trace.last().unwrap().clause.is_empty());
    }

    #[test]
    fn tautology_only_formula_is_sat() {
        let f = formula(3, &[&[1, -1], &[2, 3, -3, 2], &[-2, 1, 2, -1]]);
        assert_sat_with_model(&f);
    }

    struct XorShift(u64);

    impl XorShift {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
    }

    #[test]
    fn random_3sat_agrees_with_brute_force() {
        let mut rng = XorShift(0x9E3779B97F4A7C15);
        let (mut sats, mut unsats) = (0u32, 0u32);
        for round in 0..150 {
            let n = 8 + (rng.next() % 9) as u32; // 8..=16 variables
            let ratio = 3.0 + (rng.next() % 21) as f64 / 10.0; // 3.0..=5.0
            let m = (ratio * f64::from(n)).round() as usize;
            let mut clauses = Vec::with_capacity(m);
            for _ in 0..m {
                let mut lits: Vec<i32> = Vec::with_capacity(3);
                while lits.len() < 3 {
                    let v = 1 + (rng.next() % u64::from(n)) as i32;
                    if lits.iter().any(|l| l.abs() == v) {
                        continue;
                    }
                    lits.push(if rng.next().is_multiple_of(2) { v } else { -v });
                }
                clauses.push(lits);
            }
            let f = CnfFormula {
                num_vars: n,
                clauses,
            };
            let mut solver = SatSolver::new();
            match solver.solve(&f) {
                SatResult::Sat(model) => {
                    assert!(
                        brute_sat(&f),
                        "round {round}: solver said Sat, oracle Unsat"
                    );
                    assert!(f.eval(&model), "round {round}: model must satisfy");
                    sats += 1;
                }
                SatResult::Unsat => {
                    assert!(
                        !brute_sat(&f),
                        "round {round}: solver said Unsat, oracle Sat"
                    );
                    let trace = solver.proof_trace();
                    assert!(!trace.is_empty(), "round {round}: Unsat needs a proof");
                    assert!(trace.last().unwrap().clause.is_empty());
                    unsats += 1;
                }
            }
        }
        // The ratio range straddles the phase transition; both verdicts occur.
        assert!(sats > 0 && unsats > 0, "sats={sats} unsats={unsats}");
    }

    /// PHP(pigeons, holes): every pigeon in some hole, no two share one.
    fn pigeonhole(pigeons: u32, holes: u32) -> CnfFormula {
        let var = |p: u32, h: u32| (p * holes + h + 1) as i32;
        let mut clauses: Vec<Vec<i32>> = Vec::new();
        for p in 0..pigeons {
            clauses.push((0..holes).map(|h| var(p, h)).collect());
        }
        for h in 0..holes {
            for p1 in 0..pigeons {
                for p2 in p1 + 1..pigeons {
                    clauses.push(vec![-var(p1, h), -var(p2, h)]);
                }
            }
        }
        CnfFormula {
            num_vars: pigeons * holes,
            clauses,
        }
    }

    #[test]
    fn pigeonhole_4_3_is_unsat() {
        let f = pigeonhole(4, 3);
        assert_eq!(SatSolver::new().solve(&f), SatResult::Unsat);
        // Sanity: PHP(3,3) is satisfiable.
        assert_sat_with_model(&pigeonhole(3, 3));
    }

    #[test]
    fn budget_matches_unbounded_on_trivially_decidable() {
        // A generous budget must not change a verdict decided within it.
        let sat = formula(3, &[&[1], &[-1, 2], &[-2, 3]]);
        assert_eq!(
            SatSolver::new().solve_with_budget(&sat, 1_000_000),
            Some(SatSolver::new().solve(&sat)),
        );
        let unsat = pigeonhole(4, 3);
        assert_eq!(
            SatSolver::new().solve_with_budget(&unsat, 1_000_000),
            Some(SatResult::Unsat),
        );
    }

    #[test]
    fn budget_exhaustion_returns_none() {
        // PHP(4,3) is UNSAT and needs conflicts; budget 0 admits nothing that
        // requires a search conflict, so it yields None (no verdict).
        let f = pigeonhole(4, 3);
        assert_eq!(SatSolver::new().solve_with_budget(&f, 0), None);
    }

    #[test]
    fn budget_zero_still_decides_pure_propagation() {
        // Decided entirely by unit propagation — no search conflict — so even
        // a zero budget returns a verdict.
        let mut clauses: Vec<Vec<i32>> = vec![vec![1]];
        for v in 1..10 {
            clauses.push(vec![-v, v + 1]);
        }
        let f = CnfFormula {
            num_vars: 10,
            clauses,
        };
        match SatSolver::new().solve_with_budget(&f, 0) {
            Some(SatResult::Sat(model)) => assert!(model.iter().all(|&b| b)),
            other => panic!("expected Sat within a zero budget, got {other:?}"),
        }
    }

    #[test]
    fn unsat_proof_trace_derives_the_empty_clause() {
        let f = pigeonhole(4, 3);
        let mut solver = SatSolver::new();
        assert_eq!(solver.solve(&f), SatResult::Unsat);
        let trace = solver.proof_trace();
        assert!(!trace.is_empty());
        assert!(
            trace.last().unwrap().clause.is_empty(),
            "the final step derives the empty clause"
        );
        // Every step only references clauses that precede it in the
        // combined original+learned sequence (step k has index n_orig + k).
        let n_orig = f.clauses.len();
        for (k, step) in trace.iter().enumerate() {
            assert!(!step.antecedents.is_empty());
            for &a in &step.antecedents {
                assert!(a < n_orig + k, "step {k} references future clause {a}");
            }
        }
    }
}
