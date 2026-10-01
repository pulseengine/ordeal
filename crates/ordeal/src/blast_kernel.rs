//! The bit-blasting rules, the term-DAG encoder, the folding + hashing pass
//! and the Tseitin encoder the solver runs — re-exported from the TRUSTED
//! `ordeal-lrat` crate, where they live since #192 phase 4.
//!
//! Phase 4 moved the proven lowering (`ordeal_lrat::blast_kernel`) next to
//! the checker so that `ordeal_lrat::check_query` can re-encode a
//! certificate's term DAG with the very same code (one source: the solver
//! calls these functions through this module, the trusted re-check calls
//! them directly). This file keeps the solver-side differential tests —
//! they compare the kernel against the shipped `aig.rs` / `cnf.rs`
//! reference implementations, which the trusted crate must not depend on.
//! Everything the solver names as `crate::blast_kernel::*` resolves here.

pub use ordeal_lrat::blast_kernel::*;

#[cfg(test)]
mod tests {
    //! Fidelity differential (the blast_kernel <-> aig.rs link, issue #68;
    //! re-targeted by #192 phase 2).
    //!
    //! The Lean proof (`lean/Blaster*.lean`) establishes: these rules =
    //! BitVec semantics, unbounded, on the append-only reference arena.
    //! Since #192 phase 2 the solver runs these very rules, so there is no
    //! second implementation to compare against. Since phase 3 the solver
    //! lowers through the proven `encode` / `compact` / `tseitin` instead
    //! of the per-rule bridge (`blast/mod.rs`), and the folding + hashing
    //! is proven (`compact_sound`); the bridge is a test harness. These
    //! tests establish, by differential simulation, that BRIDGED
    //! (`blast::*`, replayed with the shipped `Aig::and`'s folding +
    //! hashing) = REFERENCE (this arena, raw): the same operand values
    //! through both, asserting equal outputs. Every rule, exhaustive at
    //! every width 1..=8, seeded-sampled at every width 9..=16 and at a
    //! spread of wide widths up to 128 (issue #185(b)). The chain
    //!   shipped Aig::and (bridge + fold + hash) =(this differential)= rules =(Lean)= BitVec
    //! is bounded test evidence that the shipped `aig::Aig` — the
    //! gate-identity reference `dag::tests` compare `compact` against —
    //! agrees with the rules, stated as such — not smuggled into the
    //! unbounded claim. Every pair — `rotr` included — is compared on the
    //! FULL operand domain at every width (issue #201).

    use super::*;

    /// `stage_count` IS `ceil(log2 w)` as std spells it (`usize::BITS - (w -
    /// 1).leading_zeros()`) and its power-of-two flag IS
    /// `usize::is_power_of_two`, at every width the solver accepts and well
    /// beyond — the two std functions the kernel cannot call (no Aeneas
    /// model) pinned against their std spellings.
    #[test]
    fn stage_count_matches_real_formula_and_is_power_of_two() {
        for w in 1usize..=4096 {
            let real = (usize::BITS - (w - 1).leading_zeros()) as usize;
            assert_eq!(stage_count(w), (real, w.is_power_of_two()), "w={w}");
        }
        for w in [
            usize::MAX / 2,
            usize::MAX / 2 + 1,
            usize::MAX / 2 + 2,
            usize::MAX,
        ] {
            let real = (usize::BITS - (w - 1).leading_zeros()) as usize;
            assert_eq!(stage_count(w), (real, w.is_power_of_two()), "w={w}");
        }
    }

    /// Build two w-bit input words on the reference arena (`word_input`'s shape).
    fn model_inputs(aig: &mut Aig, w: usize) -> (Vec<Lit>, Vec<Lit>) {
        let mut a: Vec<Lit> = Vec::new();
        let mut b: Vec<Lit> = Vec::new();
        let mut i = 0usize;
        while i < w {
            a.push(push_input(aig, i));
            i += 1;
        }
        let mut j = 0usize;
        while j < w {
            b.push(push_input(aig, w + j));
            j += 1;
        }
        (a, b)
    }

    /// One rule instantiated on both sides: the bridged output word
    /// (predicates are 1-literal words) and the reference output word.
    struct DiffPair {
        name: String,
        real: Vec<crate::aig::Lit>,
        model: Vec<Lit>,
    }

    /// Both AIGs with every rule blasted once over shared inputs:
    /// `a` = inputs `0..w`, `b` = inputs `w..2w`, `cond` = input `2w`.
    struct DiffHarness {
        w: usize,
        raig: crate::aig::Aig,
        maig: Aig,
        pairs: Vec<DiffPair>,
    }

    /// `(hi, lo)` extract ranges for width `w`: every range for `w <= 8`,
    /// a representative set (full, top/bottom bit, middle, halves) above.
    fn extract_ranges(w: usize) -> Vec<(usize, usize)> {
        let mut out = Vec::new();
        if w <= 8 {
            for hi in 0..w {
                for lo in 0..=hi {
                    out.push((hi, lo));
                }
            }
        } else {
            for (hi, lo) in [
                (w - 1, 0),
                (w - 1, w - 1),
                (0, 0),
                (w / 2, w / 4),
                (w - 1, w / 2),
                (w / 2 - 1, 0),
                (w - 2, 1),
            ] {
                if !out.contains(&(hi, lo)) {
                    out.push((hi, lo));
                }
            }
        }
        out
    }

    /// Build the harness at width `w`. Every pair, `rotr` included, is
    /// compared on its full operand domain.
    fn build_harness(w: usize) -> DiffHarness {
        use crate::aig as real;
        use crate::blast::{arith, bitwise, muldiv, shift, structural};

        type RealWordOp = fn(&mut real::Aig, &real::Word, &real::Word) -> real::Word;
        type ModelWordOp = fn(&mut Aig, &[Lit], &[Lit]) -> Vec<Lit>;
        type RealPredOp = fn(&mut real::Aig, &real::Word, &real::Word) -> real::Lit;
        type ModelPredOp = fn(&mut Aig, &[Lit], &[Lit]) -> Lit;

        let wu = w as u32;
        let mut raig = real::Aig::new();
        let ra = real::word_input(&mut raig, wu);
        let rb = real::word_input(&mut raig, wu);
        let rc = raig.input();

        let mut maig = aig_new();
        let (ma, mb) = model_inputs(&mut maig, w);
        let mc = push_input(&mut maig, 2 * w);

        let mut pairs: Vec<DiffPair> = Vec::new();
        let mut push = |name: String, real: Vec<real::Lit>, model: Vec<Lit>| {
            assert_eq!(real.len(), model.len(), "{name} w={w}: width mismatch");
            pairs.push(DiffPair { name, real, model });
        };

        let word_ops: [(&str, RealWordOp, ModelWordOp); 9] = [
            ("and", bitwise::blast_and, blast_and),
            ("or", bitwise::blast_or, blast_or),
            ("xor", bitwise::blast_xor, blast_xor),
            ("add", arith::blast_add, blast_add),
            ("sub", arith::blast_sub, blast_sub),
            ("mul", muldiv::blast_mul, blast_mul),
            ("udiv", muldiv::blast_udiv, blast_udiv),
            ("urem", muldiv::blast_urem, blast_urem),
            // Commuted operands exercise the rule asymmetrically.
            (
                "sub(b,a)",
                |g, a, b| arith::blast_sub(g, b, a),
                |g, a, b| blast_sub(g, b, a),
            ),
        ];
        for (name, rf, mf) in word_ops {
            let r = rf(&mut raig, &ra, &rb);
            let m = mf(&mut maig, &ma, &mb);
            push(name.to_string(), r, m);
        }

        let pred_ops: [(&str, RealPredOp, ModelPredOp); 10] = [
            ("ult", arith::blast_ult, blast_ult),
            ("ule", arith::blast_ule, blast_ule),
            ("ugt", arith::blast_ugt, blast_ugt),
            ("uge", arith::blast_uge, blast_uge),
            ("slt", arith::blast_slt, blast_slt),
            ("sle", arith::blast_sle, blast_sle),
            ("sgt", arith::blast_sgt, blast_sgt),
            ("sge", arith::blast_sge, blast_sge),
            ("eq", bitwise::blast_eq, blast_eq),
            ("ne", bitwise::blast_ne, blast_ne),
        ];
        for (name, rf, mf) in pred_ops {
            let r = rf(&mut raig, &ra, &rb);
            let m = mf(&mut maig, &ma, &mb);
            push(name.to_string(), vec![r], vec![m]);
        }

        // udivrem returns both halves; compare each.
        let (rq, rr) = muldiv::blast_udivrem(&mut raig, &ra, &rb);
        let (mq, mr) = blast_udivrem(&mut maig, &ma, &mb);
        push("udivrem.quo".to_string(), rq, mq);
        push("udivrem.rem".to_string(), rr, mr);

        let r = bitwise::blast_ite(&mut raig, rc, &ra, &rb);
        let m = blast_ite(&mut maig, mc, &ma, &mb);
        push("ite".to_string(), r, m);

        // Shifts and rotate: both sides derive the stage count (and the
        // rotr mod-w reduction) from the width themselves.
        let r = shift::blast_shl(&mut raig, &ra, &rb);
        let m = blast_shl(&mut maig, &ma, &mb);
        push("shl".to_string(), r, m);
        let r = shift::blast_lshr(&mut raig, &ra, &rb);
        let m = blast_lshr(&mut maig, &ma, &mb);
        push("lshr".to_string(), r, m);
        let r = shift::blast_ashr(&mut raig, &ra, &rb);
        let m = blast_ashr(&mut maig, &ma, &mb);
        push("ashr".to_string(), r, m);
        let r = shift::blast_rotr(&mut raig, &ra, &rb);
        let m = blast_rotr(&mut maig, &ma, &mb);
        push("rotr".to_string(), r, m);

        // Structural plumbing (gate-free).
        for (hi, lo) in extract_ranges(w) {
            let r = structural::blast_extract(&ra, hi as u32, lo as u32);
            let m = blast_extract(&ma, hi, lo);
            push(format!("extract[{hi}:{lo}]"), r, m);
        }
        push(
            "concat(a,b)".to_string(),
            structural::blast_concat(&ra, &rb),
            blast_concat(&ma, &mb),
        );
        push(
            "concat(b,a)".to_string(),
            structural::blast_concat(&rb, &ra),
            blast_concat(&mb, &ma),
        );
        for by in [0usize, 1, 4, w] {
            push(
                format!("zero_ext({by})"),
                structural::blast_zero_ext(&ra, by as u32),
                blast_zero_ext(&ma, by),
            );
            push(
                format!("sign_ext({by})"),
                structural::blast_sign_ext(&ra, by as u32),
                blast_sign_ext(&ma, by),
            );
        }

        DiffHarness {
            w,
            raig,
            maig,
            pairs,
        }
    }

    /// Simulate one `(a, b, cond)` assignment on both sides and assert
    /// every pair agrees bit-for-bit.
    fn check_diff(h: &DiffHarness, a: u128, b: u128, cond: bool) {
        let w = h.w;
        let mut inputs = vec![false; 2 * w + 1];
        for k in 0..w {
            inputs[k] = (a >> k) & 1 == 1;
            inputs[w + k] = (b >> k) & 1 == 1;
        }
        inputs[2 * w] = cond;
        let rvals = h.raig.simulate(&inputs);
        let mvals = simulate(&h.maig, &inputs);
        for p in &h.pairs {
            let agree = p.real.len() == p.model.len()
                && p.real
                    .iter()
                    .zip(&p.model)
                    .all(|(&r, &m)| h.raig.lit_value(&rvals, r) == eval_lit(&mvals, m));
            if !agree {
                let rbits: String = p
                    .real
                    .iter()
                    .rev()
                    .map(|&l| {
                        if h.raig.lit_value(&rvals, l) {
                            '1'
                        } else {
                            '0'
                        }
                    })
                    .collect();
                let mbits: String = p
                    .model
                    .iter()
                    .rev()
                    .map(|&l| if eval_lit(&mvals, l) { '1' } else { '0' })
                    .collect();
                panic!(
                    "reference/bridged disagree: op={} w={w} a={a:#x} b={b:#x} cond={cond} \
                     reference=#b{mbits} bridged=#b{rbits}",
                    p.name
                );
            }
        }
    }

    fn width_mask(w: usize) -> u128 {
        if w == 128 {
            u128::MAX
        } else {
            (1u128 << w) - 1
        }
    }

    /// xorshift64 — a fixed, dependency-free PRNG for reproducible sampling.
    struct DiffRng(u64);

    impl DiffRng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }

        fn next_u128(&mut self) -> u128 {
            (u128::from(self.next()) << 64) | u128::from(self.next())
        }
    }

    /// `n` seeded cases at width `w`, mixing uniform operands with the edge
    /// amounts shifts and division care about: in-range `b < w`, exactly
    /// `w`, zero, all-ones, and a set sign bit.
    fn sampled_diff(w: usize, n: u32, seed: u64) {
        let h = build_harness(w);
        let mask = width_mask(w);
        let mut rng = DiffRng(seed | 1);
        for case in 0..n {
            let a = rng.next_u128() & mask;
            let raw = rng.next_u128() & mask;
            let b = match case % 8 {
                0 | 1 => raw,
                2 | 3 => raw % w as u128,
                4 => (w as u128) & mask,
                5 => 0,
                6 => mask,
                _ => (1u128 << (w - 1)) | (raw >> 1),
            };
            let cond = rng.next() & 1 == 1;
            check_diff(&h, a, b, cond);
        }
    }

    // rivet: verifies VER-051
    // rivet: verifies VER-056
    /// Issue #185(b): EXHAUSTIVE at every width 1..=8 — every `(a, b)` pair
    /// through every rule on both sides (and/or/xor, add, sub,
    /// ult/ule/ugt/uge, slt/sle/sgt/sge, eq/ne, ite, extract, concat,
    /// zero_ext, sign_ext, shl/lshr/ashr, mul, udiv/urem/udivrem, rotr —
    /// rotr on its FULL amount domain at every width, #201). `ite`'s
    /// condition is exhaustive too: every pair runs under both values.
    #[test]
    fn model_matches_real_blaster_every_op_exhaustive_widths_1_to_8() {
        for w in 1usize..=8 {
            let h = build_harness(w);
            for a in 0u128..(1 << w) {
                for b in 0u128..(1 << w) {
                    check_diff(&h, a, b, false);
                    check_diff(&h, a, b, true);
                }
            }
        }
    }

    // rivet: verifies VER-051
    // rivet: verifies VER-056
    /// Issue #185(b): seeded sampling at every width 9..=16 (exhaustive is
    /// 2^18..2^32 pairs there — infeasible in a debug `cargo test`).
    #[test]
    fn model_matches_real_blaster_every_op_sampled_widths_9_to_16() {
        for w in 9usize..=16 {
            sampled_diff(w, 4096, 0x185B_0900 ^ w as u64);
        }
    }

    // rivet: verifies VER-051
    // rivet: verifies VER-056
    /// Issue #185(b): seeded sampling at wide widths up to 128, power-of-two
    /// and not (the #182 bug class lives at the non-power-of-two ones).
    #[test]
    fn model_matches_real_blaster_every_op_sampled_wide_widths() {
        for w in [17usize, 24, 31, 32, 33, 48, 63, 64, 65, 96, 127, 128] {
            sampled_diff(w, 128, 0x185B_1700 ^ w as u64);
        }
    }

    // ───────────── Gate identity (issue #192 phase 1, F1; phase 2) ─────────────
    //
    // The simulation differential above shows bridged and reference compute
    // the same FUNCTION. Phase 1 of #192 needed more: the same CIRCUIT, so
    // that the reference Tseitin CNF (proven in lean/BlasterTseitin.lean) is
    // the CNF the solver ships. In phase 1 the shipped rules were a second
    // hand-written copy and these tests showed the copy was gate-identical;
    // since phase 2 the shipped rules ARE a replay of this arena through
    // `blast/mod.rs`, and the same two notions now pin the bridge against
    // an independent, test-local replay (`replay` below) — every op, every
    // width 1..=16, each op in its own fresh AIG pair:
    //
    //  * RAW identity — the bridged rule on an `AigOptions::RAW` arena (no
    //    folding, no hashing: one gate per `and` call, like `push_and`)
    //    against the reference rule: the same number of nodes, the same
    //    inputs, gate `i` has the same operand PAIR on both sides, and the
    //    same output literals — the bridge adds and drops nothing. The one
    //    asymmetry: the shipped `Aig::and` stores its two operands
    //    order-normalized (`a.raw() <= b.raw()`, the strash key, applied in
    //    every mode) while the reference stores them as given — so gate
    //    operands are compared as unordered pairs. Everything else is exact.
    //  * REPLAY identity — the reference arena replayed node by node through
    //    a DEFAULT `aig::Aig` (folding + hashing) by the test's own `replay`
    //    is node-identical to the bridged rule on a default arena: the same
    //    `and_gates()` sequence, the same output literals. This is the
    //    statement "shipped = fold_and_hash(reference)" that phase 3's
    //    proven pass `compact` realises (`compact_sound` for the value,
    //    `dag::tests::compact_matches_replay_on_a_shared_query` for the
    //    node-for-node identity with this replay).
    //
    // Result: every op is identical under both notions (`push_xor` was the
    // one phase-1 mismatch — `(x|y)&!(x&y)` vs the shipped `(x&!y)|(!x&y)`
    // — and has the shipped shape since).

    /// Every op, by name: the word ops, the predicates, `udivrem`
    /// (both halves), `ite`, the shifts/rotate, the gate-free plumbing and
    /// the one-bit mux gadget.
    const GATE_IDENTITY_OPS: [&str; 30] = [
        "and", "or", "xor", "add", "sub", "sub(b,a)", "mul", "udiv", "urem", "udivrem", "ult",
        "ule", "ugt", "uge", "slt", "sle", "sgt", "sge", "eq", "ne", "ite", "shl", "lshr", "ashr",
        "rotr", "extract", "concat", "zero_ext", "sign_ext", "mux1",
    ];

    /// Run one op on BOTH sides over fresh inputs `a = 0..w`, `b = w..2w`,
    /// `cond = 2w` (created in that order on both arenas, so the input
    /// variables coincide), returning the output words.
    fn apply_op(
        name: &str,
        w: usize,
        raig: &mut crate::aig::Aig,
        maig: &mut Aig,
    ) -> (Vec<crate::aig::Lit>, Vec<Lit>) {
        use crate::aig as real;
        use crate::blast::{arith, bitwise, muldiv, shift, structural};
        let wu = w as u32;
        let ra = real::word_input(raig, wu);
        let rb = real::word_input(raig, wu);
        let rc = raig.input();
        let (ma, mb) = model_inputs(maig, w);
        let mc = push_input(maig, 2 * w);
        match name {
            "and" => (
                bitwise::blast_and(raig, &ra, &rb),
                blast_and(maig, &ma, &mb),
            ),
            "or" => (bitwise::blast_or(raig, &ra, &rb), blast_or(maig, &ma, &mb)),
            "xor" => (
                bitwise::blast_xor(raig, &ra, &rb),
                blast_xor(maig, &ma, &mb),
            ),
            "add" => (arith::blast_add(raig, &ra, &rb), blast_add(maig, &ma, &mb)),
            "sub" => (arith::blast_sub(raig, &ra, &rb), blast_sub(maig, &ma, &mb)),
            "sub(b,a)" => (arith::blast_sub(raig, &rb, &ra), blast_sub(maig, &mb, &ma)),
            "mul" => (muldiv::blast_mul(raig, &ra, &rb), blast_mul(maig, &ma, &mb)),
            "udiv" => (
                muldiv::blast_udiv(raig, &ra, &rb),
                blast_udiv(maig, &ma, &mb),
            ),
            "urem" => (
                muldiv::blast_urem(raig, &ra, &rb),
                blast_urem(maig, &ma, &mb),
            ),
            "udivrem" => {
                let (rq, rr) = muldiv::blast_udivrem(raig, &ra, &rb);
                let (mq, mr) = blast_udivrem(maig, &ma, &mb);
                (
                    rq.into_iter().chain(rr).collect(),
                    mq.into_iter().chain(mr).collect(),
                )
            }
            "ult" => (
                vec![arith::blast_ult(raig, &ra, &rb)],
                vec![blast_ult(maig, &ma, &mb)],
            ),
            "ule" => (
                vec![arith::blast_ule(raig, &ra, &rb)],
                vec![blast_ule(maig, &ma, &mb)],
            ),
            "ugt" => (
                vec![arith::blast_ugt(raig, &ra, &rb)],
                vec![blast_ugt(maig, &ma, &mb)],
            ),
            "uge" => (
                vec![arith::blast_uge(raig, &ra, &rb)],
                vec![blast_uge(maig, &ma, &mb)],
            ),
            "slt" => (
                vec![arith::blast_slt(raig, &ra, &rb)],
                vec![blast_slt(maig, &ma, &mb)],
            ),
            "sle" => (
                vec![arith::blast_sle(raig, &ra, &rb)],
                vec![blast_sle(maig, &ma, &mb)],
            ),
            "sgt" => (
                vec![arith::blast_sgt(raig, &ra, &rb)],
                vec![blast_sgt(maig, &ma, &mb)],
            ),
            "sge" => (
                vec![arith::blast_sge(raig, &ra, &rb)],
                vec![blast_sge(maig, &ma, &mb)],
            ),
            "eq" => (
                vec![bitwise::blast_eq(raig, &ra, &rb)],
                vec![blast_eq(maig, &ma, &mb)],
            ),
            "ne" => (
                vec![bitwise::blast_ne(raig, &ra, &rb)],
                vec![blast_ne(maig, &ma, &mb)],
            ),
            "ite" => (
                bitwise::blast_ite(raig, rc, &ra, &rb),
                blast_ite(maig, mc, &ma, &mb),
            ),
            "shl" => (shift::blast_shl(raig, &ra, &rb), blast_shl(maig, &ma, &mb)),
            "lshr" => (
                shift::blast_lshr(raig, &ra, &rb),
                blast_lshr(maig, &ma, &mb),
            ),
            "ashr" => (
                shift::blast_ashr(raig, &ra, &rb),
                blast_ashr(maig, &ma, &mb),
            ),
            "rotr" => (
                shift::blast_rotr(raig, &ra, &rb),
                blast_rotr(maig, &ma, &mb),
            ),
            // Gate-free plumbing: every extract range for the width, both
            // concat orders, the four extension amounts — concatenated into
            // one output word per side.
            "extract" => {
                let mut r = Vec::new();
                let mut m = Vec::new();
                for (hi, lo) in extract_ranges(w) {
                    r.extend(structural::blast_extract(&ra, hi as u32, lo as u32));
                    m.extend(blast_extract(&ma, hi, lo));
                }
                (r, m)
            }
            "concat" => (
                structural::blast_concat(&ra, &rb)
                    .into_iter()
                    .chain(structural::blast_concat(&rb, &ra))
                    .collect(),
                blast_concat(&ma, &mb)
                    .into_iter()
                    .chain(blast_concat(&mb, &ma))
                    .collect(),
            ),
            "zero_ext" => {
                let mut r = Vec::new();
                let mut m = Vec::new();
                for by in [0usize, 1, 4, w] {
                    r.extend(structural::blast_zero_ext(&ra, by as u32));
                    m.extend(blast_zero_ext(&ma, by));
                }
                (r, m)
            }
            "sign_ext" => {
                let mut r = Vec::new();
                let mut m = Vec::new();
                for by in [0usize, 1, 4, w] {
                    r.extend(structural::blast_sign_ext(&ra, by as u32));
                    m.extend(blast_sign_ext(&ma, by));
                }
                (r, m)
            }
            // The one-bit mux gadget itself (`aig::mux` vs `push_mux`).
            "mux1" => (
                vec![raig.mux(rc, ra[0], rb[0])],
                vec![push_mux(maig, mc, ma[0], mb[0])],
            ),
            other => panic!("unknown gate-identity op {other}"),
        }
    }

    /// AIGER raw encoding of a model literal: `node << 1 | neg`, the
    /// shipped `aig::Lit::raw`.
    fn model_raw(l: Lit) -> u32 {
        (l.node as u32) << 1 | l.neg as u32
    }

    /// The model arena as `(gate var, operand raw, operand raw)` triples in
    /// node order, exactly what `aig::Aig::and_gates` yields.
    fn model_gates(maig: &Aig) -> Vec<(u32, u32, u32)> {
        maig.nodes
            .iter()
            .enumerate()
            .filter_map(|(i, n)| match n {
                Node::And(x, y) => Some((i as u32, model_raw(*x), model_raw(*y))),
                _ => None,
            })
            .collect()
    }

    fn real_gates(raig: &crate::aig::Aig) -> Vec<(u32, u32, u32)> {
        raig.and_gates()
            .map(|(v, a, b)| (v, a.raw(), b.raw()))
            .collect()
    }

    /// The shipped literal of a model literal under a replay map.
    fn replay_lit(map: &[crate::aig::Lit], l: Lit) -> crate::aig::Lit {
        if l.neg {
            map[l.node].not()
        } else {
            map[l.node]
        }
    }

    /// Replay a model arena through a shipped `aig::Aig` with the given
    /// options, returning the arena and the shipped literal of every model
    /// node.
    fn replay(maig: &Aig, opts: crate::aig::AigOptions) -> (crate::aig::Aig, Vec<crate::aig::Lit>) {
        use crate::aig as real;
        let mut raig = real::Aig::with_options(opts);
        let mut map: Vec<real::Lit> = Vec::with_capacity(maig.nodes.len());
        for n in &maig.nodes {
            let r = match n {
                Node::False => real::Lit::FALSE,
                Node::Input(_) => raig.input(),
                Node::And(x, y) => {
                    let (rx, ry) = (replay_lit(&map, *x), replay_lit(&map, *y));
                    raig.and(rx, ry)
                }
            };
            map.push(r);
        }
        (raig, map)
    }

    // rivet: verifies VER-051
    // rivet: verifies VER-059
    /// Issue #192 phase 1 (F1), RAW identity: the bridged rule on an
    /// unsimplified arena IS the reference arena — node for node, every op,
    /// every width 1..=16 (gate operands as unordered pairs, see the
    /// section comment; everything else exact).
    #[test]
    fn gate_identity_raw_every_op_widths_1_to_16() {
        for w in 1usize..=16 {
            for name in GATE_IDENTITY_OPS {
                let mut raig = crate::aig::Aig::with_options(crate::aig::AigOptions::RAW);
                let mut maig = aig_new();
                let (rout, mout) = apply_op(name, w, &mut raig, &mut maig);
                assert_eq!(
                    raig.num_vars() as usize,
                    maig.nodes.len(),
                    "{name} w={w}: node count"
                );
                assert_eq!(
                    raig.num_inputs() as usize,
                    2 * w + 1,
                    "{name} w={w}: inputs"
                );
                let rg = real_gates(&raig);
                let mg = model_gates(&maig);
                assert_eq!(rg.len(), mg.len(), "{name} w={w}: gate count");
                for (k, (r, m)) in rg.iter().zip(&mg).enumerate() {
                    let rp = if r.1 <= r.2 { (r.1, r.2) } else { (r.2, r.1) };
                    let mp = if m.1 <= m.2 { (m.1, m.2) } else { (m.2, m.1) };
                    assert!(
                        r.0 == m.0 && rp == mp,
                        "{name} w={w}: gate #{k} differs: real {r:?} model {m:?}"
                    );
                }
                let mraw: Vec<u32> = mout.iter().map(|&l| model_raw(l)).collect();
                let rraw: Vec<u32> = rout.iter().map(|l| l.raw()).collect();
                assert_eq!(rraw, mraw, "{name} w={w}: output literals");
            }
        }
    }

    // rivet: verifies VER-051
    // rivet: verifies VER-059
    /// Issue #192 phase 1 (F1), REPLAY identity: the reference arena
    /// replayed through a default `aig::Aig` (constant folding + structural
    /// hashing) by the test's own `replay` is node-identical to the bridged
    /// rule — the same `and_gates()` sequence and the same output literals
    /// — for every op at every width 1..=16.
    #[test]
    fn gate_identity_replay_every_op_widths_1_to_16() {
        for w in 1usize..=16 {
            for name in GATE_IDENTITY_OPS {
                let mut raig = crate::aig::Aig::new();
                let mut maig = aig_new();
                let (rout, mout) = apply_op(name, w, &mut raig, &mut maig);
                let (replayed, map) = replay(&maig, crate::aig::AigOptions::default());
                assert_eq!(
                    replayed.num_inputs(),
                    raig.num_inputs(),
                    "{name} w={w}: inputs"
                );
                let rg = real_gates(&raig);
                let pg = real_gates(&replayed);
                for (k, (r, p)) in rg.iter().zip(&pg).enumerate() {
                    assert_eq!(
                        r, p,
                        "{name} w={w}: gate #{k} differs (real vs replayed model)"
                    );
                }
                assert_eq!(rg.len(), pg.len(), "{name} w={w}: gate count");
                assert_eq!(
                    replayed.num_vars(),
                    raig.num_vars(),
                    "{name} w={w}: node count"
                );
                let mapped: Vec<u32> = mout.iter().map(|&l| replay_lit(&map, l).raw()).collect();
                let rraw: Vec<u32> = rout.iter().map(|l| l.raw()).collect();
                assert_eq!(rraw, mapped, "{name} w={w}: output literals");
            }
        }
    }

    // ───────────── Tseitin differential (issue #192 phase 1) ─────────────

    /// A shipped arena as a model arena, node for node. The shipped `Node`
    /// is private; inputs and gates interleave in creation order, so walk
    /// the variables and classify each by whether `and_gates` names it.
    fn to_model(raig: &crate::aig::Aig) -> Aig {
        let gates: std::collections::BTreeMap<u32, (u32, u32)> = raig
            .and_gates()
            .map(|(v, a, b)| (v, (a.raw(), b.raw())))
            .collect();
        let lit = |raw: u32| Lit {
            node: (raw >> 1) as usize,
            neg: raw & 1 == 1,
        };
        let mut m = aig_new();
        let mut k = 0usize;
        for v in 1..raig.num_vars() {
            match gates.get(&v) {
                Some(&(a, b)) => m.nodes.push(Node::And(lit(a), lit(b))),
                None => {
                    m.nodes.push(Node::Input(k));
                    k += 1;
                }
            }
        }
        assert_eq!(k as u32, raig.num_inputs());
        m
    }

    /// Model `tseitin` vs `cnf::tseitin` on the SAME arena (the shipped one
    /// converted node for node): clause-for-clause equal, same var count.
    fn assert_tseitin_identical(raig: &crate::aig::Aig, routs: &[crate::aig::Lit], what: &str) {
        let maig = to_model(raig);
        let mouts: Vec<Lit> = routs
            .iter()
            .map(|l| Lit {
                node: l.var() as usize,
                neg: l.is_complement(),
            })
            .collect();
        let (real, _map) = crate::cnf::tseitin(raig, routs);
        let model = tseitin(&maig, &mouts);
        assert_eq!(real.num_vars as usize, maig.nodes.len(), "{what}: num_vars");
        assert_eq!(real.clauses.len(), model.len(), "{what}: clause count");
        for (k, (r, m)) in real.clauses.iter().zip(&model).enumerate() {
            assert_eq!(r, m, "{what}: clause #{k} differs");
        }
    }

    /// Model `tseitin` on a MODEL-built arena vs `cnf::tseitin` on its raw
    /// replay: the same up to the shipped arena's per-gate operand
    /// normalization (which swaps the two binary clauses of a gate and the
    /// two negated literals of its ternary clause); clause count and
    /// `num_vars` exact.
    fn assert_tseitin_identical_mod_operand_order(maig: &Aig, mouts: &[Lit], what: &str) {
        let (raw, map) = replay(maig, crate::aig::AigOptions::RAW);
        let routs: Vec<crate::aig::Lit> = mouts.iter().map(|&l| replay_lit(&map, l)).collect();
        let (real, _) = crate::cnf::tseitin(&raw, &routs);
        let model = tseitin(maig, mouts);
        assert_eq!(real.num_vars as usize, maig.nodes.len(), "{what}: num_vars");
        assert_eq!(real.clauses.len(), model.len(), "{what}: clause count");
        let mut k = 0usize;
        while k < model.len() {
            let (r, m) = (&real.clauses[k], &model[k]);
            if r == m {
                k += 1;
                continue;
            }
            // A gate whose operands the shipped arena swapped: the model's
            // (¬o∨a)(¬o∨b)(o∨¬a∨¬b) is the shipped (¬o∨b)(¬o∨a)(o∨¬b∨¬a).
            assert!(
                k + 2 < model.len(),
                "{what}: clause #{k} differs: real {r:?} model {m:?}"
            );
            let (m1, m2, m3) = (&model[k], &model[k + 1], &model[k + 2]);
            let (r1, r2, r3) = (&real.clauses[k], &real.clauses[k + 1], &real.clauses[k + 2]);
            let swapped = m1.len() == 2
                && m3.len() == 3
                && r1 == m2
                && r2 == m1
                && r3 == &vec![m3[0], m3[2], m3[1]];
            assert!(
                swapped,
                "{what}: clauses #{k}..#{} differ beyond operand order: real {r1:?} {r2:?} {r3:?} model {m1:?} {m2:?} {m3:?}",
                k + 2
            );
            k += 3;
        }
    }

    // rivet: verifies VER-051
    // rivet: verifies VER-059
    /// Issue #192 phase 1: the model Tseitin encoder IS `cnf::tseitin` —
    /// clause for clause, in order — on the shipped arena of every
    /// op at every width 1..=16, in each simplification mode (raw, fold
    /// only, fold + hash), asserting every output literal; and, on the
    /// model-built arenas, the same up to the shipped operand normalization.
    #[test]
    fn tseitin_matches_cnf_rs_every_op_widths_1_to_16() {
        for w in 1usize..=16 {
            for name in GATE_IDENTITY_OPS {
                for opts in [
                    crate::aig::AigOptions::RAW,
                    crate::aig::AigOptions::FOLD_ONLY,
                    crate::aig::AigOptions::default(),
                ] {
                    let mut raig = crate::aig::Aig::with_options(opts);
                    let mut maig = aig_new();
                    let (rout, mout) = apply_op(name, w, &mut raig, &mut maig);
                    assert_tseitin_identical(&raig, &rout, &format!("{name} w={w} {opts:?}"));
                    assert_tseitin_identical_mod_operand_order(
                        &maig,
                        &mout,
                        &format!("{name} w={w} (model arena)"),
                    );
                }
            }
        }
    }

    /// A seeded random model circuit over `n_in` inputs with `n_gates`
    /// gates (operands drawn from earlier nodes, random polarity), and a
    /// random output literal.
    fn random_model_circuit(rng: &mut DiffRng, n_in: usize, n_gates: usize) -> (Aig, Lit) {
        let mut maig = aig_new();
        for k in 0..n_in {
            push_input(&mut maig, k);
        }
        for _ in 0..n_gates {
            let n = maig.nodes.len();
            let pick = |rng: &mut DiffRng| Lit {
                node: (rng.next() % n as u64) as usize,
                neg: rng.next() & 1 == 1,
            };
            let (x, y) = (pick(rng), pick(rng));
            push_and(&mut maig, x, y);
        }
        let out = Lit {
            node: maig.nodes.len() - 1,
            neg: rng.next() & 1 == 1,
        };
        (maig, out)
    }

    // rivet: verifies VER-051
    // rivet: verifies VER-059
    /// Issue #192 phase 1: `tseitin` vs `cnf::tseitin` on seeded random
    /// circuits (any operand mix, including constants and repeated
    /// operands, which the op arenas never produce raw).
    #[test]
    fn tseitin_matches_cnf_rs_random_circuits() {
        let mut rng = DiffRng(0x1920_7531);
        for round in 0..200 {
            let (maig, out) = random_model_circuit(&mut rng, 1 + (round % 6), 1 + (round % 40));
            assert_tseitin_identical_mod_operand_order(&maig, &[out], &format!("round {round}"));
            // And exactly, on the replayed (default) arena's conversion.
            let (raig, map) = replay(&maig, crate::aig::AigOptions::default());
            assert_tseitin_identical(
                &raig,
                &[replay_lit(&map, out)],
                &format!("round {round} (replayed)"),
            );
        }
    }

    /// Evaluate a DIMACS clause list under `vals[v-1]`.
    fn cnf_holds(clauses: &[Vec<i32>], vals: &[bool]) -> bool {
        clauses.iter().all(|c| {
            c.iter().any(|&l| {
                let v = vals[(l.unsigned_abs() - 1) as usize];
                if l > 0 { v } else { !v }
            })
        })
    }

    // rivet: verifies VER-051
    // rivet: verifies VER-059
    /// Issue #192 phase 1: the runtime shadow of `tseitin_sat_preserving`
    /// (lean/BlasterTseitin.lean) — for every input assignment under which
    /// the output literal is TRUE, the simulation values (CNF variable
    /// `v + 1` := node `v`'s value) satisfy the model CNF; and when it is
    /// FALSE they do not (the root unit clause fails). Random small
    /// circuits, exhaustive over the inputs.
    #[test]
    fn tseitin_simulation_values_satisfy_cnf_iff_output_true() {
        let mut rng = DiffRng(0x1920_ACE5);
        for round in 0..100 {
            let n_in = 1 + (round % 5);
            let (maig, out) = random_model_circuit(&mut rng, n_in, 1 + (round % 12));
            let cnf = tseitin(&maig, &[out]);
            for bits in 0u32..(1 << n_in) {
                let inputs: Vec<bool> = (0..n_in).map(|k| bits >> k & 1 == 1).collect();
                let vals = simulate(&maig, &inputs);
                assert_eq!(
                    cnf_holds(&cnf, &vals),
                    eval_lit(&vals, out),
                    "round {round} inputs {bits:#b}"
                );
            }
        }
    }
}
