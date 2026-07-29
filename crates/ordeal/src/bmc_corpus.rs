//! The TR-031 BMC-shaped benchmark corpus (spar#350 consumer enablement).
//!
//! spar proposes certificate-checked bounded model checking of concurrent
//! AADL behaviour discharged through ordeal: encode the transition relation
//! over small-bit-vector state, unroll to depth `k`, and ask one `check()`
//! per depth — SAT is a replayable counterexample trace, UNSAT arrives with
//! an LRAT certificate the verified checker validated. This module builds
//! query families in exactly those shapes so ordeal can *measure* the
//! practical-`k` envelope (benches/bmc.rs) instead of leaving spar's spike
//! to discover it.
//!
//! Not API. Like [`crate::blast_kernel`], this exists for the benchmark and
//! its tests, not for callers — spar owns the real IR→transition-relation
//! encoding; these are representative shapes, not a modeling framework.
//!
//! # Encoding conventions
//!
//! One bit-vector variable per state component per step (`q_3` is the queue
//! counter after step 3), one scheduler-choice variable per step (`ch_j`,
//! width 8; `Ite` chains give unchosen threads a stutter step). Init pins
//! step-0 state, `T(s_j, ch_j, s_{j+1})` is asserted per step as equalities
//! over `Ite` terms, and the property's negation ("Bad") is asserted at
//! depth `k` (or as a disjunction over all depths where noted). Everything
//! is inside the closed fragment — no ops beyond what loom #246 pinned.

use crate::term::{BoolTerm, BvTerm, Sort};

fn var(name: String, w: u32) -> BvTerm {
    BvTerm::Var {
        name,
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

fn eq(a: BvTerm, bb: BvTerm) -> BoolTerm {
    BoolTerm::Eq(b(a), b(bb))
}

fn and(a: BoolTerm, bb: BoolTerm) -> BoolTerm {
    BoolTerm::And(Box::new(a), Box::new(bb))
}

fn ite(cond: BoolTerm, then_: BvTerm, else_: BvTerm) -> BvTerm {
    BvTerm::Ite {
        cond: Box::new(cond),
        then_: b(then_),
        else_: b(else_),
    }
}

/// Event-port queue overflow (spar#350 shape 1): a producer and a consumer
/// share a bounded queue counter (width 8). Each step the scheduler picks
/// the producer (`ch_j = 0`, enqueue: `q+1`) or the consumer (anything
/// else, dequeue: `q-1` when non-empty, else stutter). Bad: some reachable
/// step exceeds `cap`.
///
/// `cap >= k` is UNSAT within depth `k` (the counter starts at 0 and grows
/// at most 1 per step — but the solver must *prove* that through the `Ite`
/// chains); an undersized `cap < k` is SAT with the all-producer schedule —
/// the seeded-defect direction TR-031's criteria demand.
///
/// The width-8 counter makes the encoding meaningful only for `k <= 255`:
/// past that, modular wraparound would let the count alias zero and the
/// "overflow" property would no longer say what it claims.
pub fn queue_overflow(k: usize, cap: u8) -> Vec<BoolTerm> {
    let w = 8;
    let mut assertions = Vec::with_capacity(k + 2);
    // Init: empty queue.
    assertions.push(eq(var("q_0".into(), w), c(0, w)));
    for j in 0..k {
        let q = var(format!("q_{j}"), w);
        let q_next = var(format!("q_{}", j + 1), w);
        let ch = var(format!("ch_{j}"), 8);
        let is_producer = eq(ch.clone(), c(0, 8));
        let q_nonempty = BoolTerm::Ugt(b(q.clone()), b(c(0, w)));
        // producer: q+1; consumer: q>0 ? q-1 : q (stutter on empty).
        let next = ite(
            is_producer,
            BvTerm::Add(b(q.clone()), b(c(1, w))),
            ite(q_nonempty, BvTerm::Sub(b(q.clone()), b(c(1, w))), q.clone()),
        );
        assertions.push(eq(q_next, next));
    }
    // Bad: overflow at any reached depth (disjunction, folded).
    let mut bad = BoolTerm::Ugt(b(var("q_1".into(), w)), b(c(cap as u128, w)));
    for j in 2..=k {
        bad = BoolTerm::Or(
            Box::new(bad),
            Box::new(BoolTerm::Ugt(
                b(var(format!("q_{j}"), w)),
                b(c(cap as u128, w)),
            )),
        );
    }
    assertions.push(bad);
    assertions
}

/// Two-thread / two-lock deadlock (spar#350 shape 3). Thread state is a
/// 2-bit program counter (0 = idle, 1 = holds first lock & wants second,
/// 2 = holds both, 3 = done/released); lock owners are 2-bit (0 = free,
/// 1 = thread A, 2 = thread B). Thread A acquires lock 1 then lock 2.
/// Thread B acquires in the same order when `inverted` is false (correct
/// discipline — UNSAT: no deadlock reachable) and in the opposite order
/// when true (the classic inversion — SAT at k >= 2 with the interleaving
/// where each grabs its first lock).
///
/// Bad: both threads at pc = 1 while each wanted lock is owned by the
/// other — the circular-wait state itself, which is what "every thread
/// blocked" degenerates to with two threads.
pub fn deadlock(k: usize, inverted: bool) -> Vec<BoolTerm> {
    let w = 2;
    let mut assertions = Vec::new();
    // Init: both idle, both locks free.
    for v in ["pa_0", "pb_0", "l1_0", "l2_0"] {
        assertions.push(eq(var(v.into(), w), c(0, w)));
    }
    // Which lock each thread takes FIRST / SECOND.
    // A: first = l1, second = l2. B: correct → l1 then l2; inverted → l2 then l1.
    for j in 0..k {
        let pa = var(format!("pa_{j}"), w);
        let pb = var(format!("pb_{j}"), w);
        let l1 = var(format!("l1_{j}"), w);
        let l2 = var(format!("l2_{j}"), w);
        let ch = var(format!("ch_{j}"), 8);
        let a_steps = eq(ch.clone(), c(0, 8));

        // Generic per-thread transition, parameterized by (owner-id, first
        // lock, second lock). Returns (pc', first', second') as Ite terms,
        // stuttering when the wanted lock is taken.
        let step = |pc: &BvTerm, first: &BvTerm, second: &BvTerm, me: u128| {
            let at = |n: u128| eq(pc.clone(), c(n, w));
            let free = |l: &BvTerm| eq(l.clone(), c(0, w));
            // pc 0→1 needs first free; 1→2 needs second free; 2→3 releases both.
            let pc_next = ite(
                and(at(0), free(first)),
                c(1, w),
                ite(
                    and(at(1), free(second)),
                    c(2, w),
                    ite(at(2), c(3, w), pc.clone()),
                ),
            );
            let first_next = ite(
                and(at(0), free(first)),
                c(me, w),
                ite(at(2), c(0, w), first.clone()),
            );
            let second_next = ite(
                and(at(1), free(second)),
                c(me, w),
                ite(at(2), c(0, w), second.clone()),
            );
            (pc_next, first_next, second_next)
        };

        // Thread A over (l1, l2); thread B over (l1, l2) or (l2, l1).
        let (pa_n, a_l1, a_l2) = step(&pa, &l1, &l2, 1);
        let (pb_n, b_first, b_second) = if inverted {
            step(&pb, &l2, &l1, 2)
        } else {
            step(&pb, &l1, &l2, 2)
        };
        let (b_l1, b_l2) = if inverted {
            (b_second, b_first)
        } else {
            (b_first, b_second)
        };

        // Scheduler: A steps or B steps; the other thread's pc stutters and
        // the lock owners follow whichever thread stepped.
        assertions.push(eq(
            var(format!("pa_{}", j + 1), w),
            ite(a_steps.clone(), pa_n, pa.clone()),
        ));
        assertions.push(eq(
            var(format!("pb_{}", j + 1), w),
            ite(a_steps.clone(), pb.clone(), pb_n),
        ));
        assertions.push(eq(
            var(format!("l1_{}", j + 1), w),
            ite(a_steps.clone(), a_l1, b_l1),
        ));
        assertions.push(eq(
            var(format!("l2_{}", j + 1), w),
            ite(a_steps, a_l2, b_l2),
        ));
    }
    // Bad at any depth: both at pc=1 (each holding its first lock) while
    // both locks are taken — the circular wait.
    let bad_at = |j: usize| {
        and(
            and(
                eq(var(format!("pa_{j}"), w), c(1, w)),
                eq(var(format!("pb_{j}"), w), c(1, w)),
            ),
            and(
                BoolTerm::Ne(b(var(format!("l1_{j}"), w)), b(c(0, w))),
                BoolTerm::Ne(b(var(format!("l2_{j}"), w)), b(c(0, w))),
            ),
        )
    };
    let mut bad = bad_at(1);
    for j in 2..=k {
        bad = BoolTerm::Or(Box::new(bad), Box::new(bad_at(j)));
    }
    assertions.push(bad);
    assertions
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::{CheckResult, Solver};

    fn check(assertions: &[BoolTerm]) -> CheckResult {
        let mut s = Solver::new();
        for a in assertions {
            s.assert(a.clone());
        }
        s.check()
    }

    /// TR-031 seeded-defect criterion: the undersized queue goes SAT with a
    /// decodable, replayable counterexample — the all-producer schedule.
    #[test]
    fn undersized_queue_overflows_with_replayable_trace() {
        let k = 8;
        let cap = 3u8;
        match check(&queue_overflow(k, cap)) {
            CheckResult::Sat(model) => {
                // Replay: walk the schedule the model chose and confirm the
                // counter really exceeds cap at some step. This is the
                // "counterexample you can replay" leg, independent of the
                // solver's own model self-check.
                let get = |name: &str| {
                    model
                        .assignments
                        .iter()
                        .find(|(n, _)| n == name)
                        .map(|(_, v)| *v)
                        .unwrap_or(0)
                };
                let mut q: u8 = 0;
                let mut overflowed = false;
                for j in 0..k {
                    if get(&format!("ch_{j}")) == 0 {
                        q = q.wrapping_add(1);
                    } else {
                        q = q.saturating_sub(1);
                    }
                    if q > cap {
                        overflowed = true;
                    }
                }
                assert!(overflowed, "model's schedule must actually overflow");
            }
            other => panic!("undersized queue must be SAT, got {other:?}"),
        }
    }

    /// The correctly-sized queue admits no overflow within k — and the
    /// verdict arrives as a checker-validated certificate.
    #[test]
    fn sized_queue_is_unsat_with_certificate() {
        let k = 8;
        match check(&queue_overflow(k, k as u8)) {
            CheckResult::Unsat(cert) => {
                cert.recheck().expect("certificate must re-check offline");
            }
            other => panic!("sized queue must be UNSAT, got {other:?}"),
        }
    }

    /// Correct lock discipline: no deadlock reachable at any depth.
    #[test]
    fn ordered_locks_have_no_deadlock() {
        match check(&deadlock(6, false)) {
            CheckResult::Unsat(cert) => {
                cert.recheck().expect("certificate must re-check offline");
            }
            other => panic!("ordered locks must be UNSAT, got {other:?}"),
        }
    }

    /// The classic inversion: each thread grabs its first lock and the
    /// circular wait is reachable — SAT with a replayable interleaving.
    #[test]
    fn inverted_locks_deadlock() {
        match check(&deadlock(6, true)) {
            CheckResult::Sat(_) => {}
            other => panic!("inverted locks must be SAT, got {other:?}"),
        }
    }

    /// Both backends agree on the corpus (VER-008's parity, on the TR-031
    /// shapes specifically), and the accelerator's UNSAT certificates
    /// re-check offline exactly like the own core's.
    #[cfg(all(feature = "cadical", not(target_family = "wasm")))]
    #[test]
    fn cadical_agrees_on_bmc_shapes() {
        for (assertions, expect_sat) in [
            (queue_overflow(8, 3), true),
            (queue_overflow(8, 8), false),
            (deadlock(6, true), true),
            (deadlock(6, false), false),
        ] {
            let mut s = Solver::new();
            for a in &assertions {
                s.assert(a.clone());
            }
            match (s.check_with_cadical(), expect_sat) {
                (CheckResult::Sat(_), true) => {}
                (CheckResult::Unsat(cert), false) => {
                    cert.recheck().expect("cadical certificate must re-check");
                }
                (got, want) => panic!("cadical disagrees: want sat={want}, got {got:?}"),
            }
        }
    }
}
