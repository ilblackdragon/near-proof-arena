//! `eval::BlockEval` against the scalar `Tape::eval`, plus a benchmark
//! (`cargo test --release --test eval -- --ignored --nocapture`).

use std::time::Instant;

use npudr::air::{Expr as E, Tape};
use npudr::eval::BlockEval;
use npudr::field::{EF, F, P};
use npudr::toy::{cube_table, cube_trace};
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn f(&mut self) -> F {
        match self.below(8) {
            0 => F::ZERO,
            1 => F::ONE,
            2 => F::NEG_ONE,
            _ => F::new((self.next() % P as u64) as u32),
        }
    }
    fn ef(&mut self) -> EF {
        EF::from_basis_coefficients_fn(|_| self.f())
    }
}

fn rand_expr(r: &mut Rng, width: usize, npub: usize, depth: usize, pool: &mut Vec<E>) -> E {
    if depth == 0 || r.below(5) == 0 {
        return match r.below(10) {
            0 => E::Const(match r.below(4) {
                0 => 0,
                1 => 1,
                2 => (P - 1) as u64,
                _ => r.next() % (1 << 40), // also non-canonical constants
            }),
            1 => E::Pub(r.below(npub as u64) as usize),
            2 => E::IsFirst,
            3 => E::IsLast,
            4 => E::IsTransition,
            5 if !pool.is_empty() => pool[r.below(pool.len() as u64) as usize].clone(),
            _ => E::Col(r.below(width as u64) as usize, r.below(2) == 1),
        };
    }
    let e = match r.below(7) {
        0 | 1 => E::add(rand_expr(r, width, npub, depth - 1, pool), rand_expr(r, width, npub, depth - 1, pool)),
        2 | 3 => E::mul(rand_expr(r, width, npub, depth - 1, pool), rand_expr(r, width, npub, depth - 1, pool)),
        4 => E::neg(rand_expr(r, width, npub, depth - 1, pool)),
        5 => E::sub(rand_expr(r, width, npub, depth - 1, pool), rand_expr(r, width, npub, depth - 1, pool)),
        _ => {
            let s = [E::IsFirst, E::IsLast, E::IsTransition][r.below(3) as usize].clone();
            E::mul(s, rand_expr(r, width, npub, depth - 1, pool))
        }
    };
    if r.below(3) == 0 {
        pool.push(e.clone()); // CSE-shared subexpressions
    }
    e
}

/// Scalar reference: Σ_k α^k C_k(row i).
fn reference(
    tape: &Tape,
    pubs: &[F],
    rows: &[F],
    w: usize,
    next: &[u32],
    sf: &[F],
    sl: &[F],
    apow: &[EF],
    n: usize,
) -> Vec<EF> {
    let mut regs = vec![];
    (0..n)
        .map(|i| {
            let row = &rows[i * w..(i + 1) * w];
            let j = next[i] as usize;
            let nrow = &rows[j * w..(j + 1) * w];
            tape.eval::<F>(&mut regs, |c, nn| if nn { nrow[c] } else { row[c] }, pubs, [sf[i], sl[i], F::ONE - sl[i]]);
            tape.outputs.iter().zip(apow).map(|(o, a)| *a * regs[*o as usize]).sum()
        })
        .collect()
}

fn check(tape: &Tape, pubs: &[F], w: usize, nrows: usize, n: usize, r: &mut Rng) {
    let rows: Vec<F> = (0..nrows * w).map(|_| r.f()).collect();
    let next: Vec<u32> = (0..n).map(|_| r.below(nrows as u64) as u32).collect();
    let sf: Vec<F> = (0..n).map(|_| r.f()).collect();
    let sl: Vec<F> = (0..n).map(|_| r.f()).collect();
    let apow: Vec<EF> = (0..tape.outputs.len()).map(|_| r.ef()).collect();
    let be = BlockEval::new(tape, pubs);
    let mut out = vec![EF::ZERO; n];
    be.eval_combined(&rows, w, &next, &sf, &sl, &apow, &mut out);
    let want = reference(tape, pubs, &rows, w, &next, &sf, &sl, &apow, n);
    assert_eq!(out, want);
}

#[test]
fn random_tapes_match_scalar() {
    let mut r = Rng(0x9e37_79b9_7f4a_7c15);
    for it in 0..300 {
        let w = 1 + r.below(12) as usize;
        let npub = 1 + r.below(4) as usize;
        let pubs: Vec<F> = (0..npub).map(|_| r.f()).collect();
        let mut pool = vec![];
        let nc = 1 + r.below(40) as usize;
        let depth = 1 + (it % 9);
        let cs: Vec<E> = (0..nc).map(|_| rand_expr(&mut r, w, npub, depth, &mut pool)).collect();
        // duplicated constraints (merged coefficients)
        let mut cs2 = cs.clone();
        if r.below(2) == 0 {
            cs2.extend(cs.iter().take(3).cloned());
        }
        let tape = Tape::compile(&cs2);
        let n = 1 + r.below(70) as usize;
        let nrows = n + r.below(20) as usize;
        check(&tape, &pubs, w, nrows, n, &mut r);
    }
}

#[test]
fn many_terms_no_overflow() {
    // all-(p-1) rows and coefficients: maximal u64 accumulation
    let w = 4;
    let mut cs = vec![];
    for k in 0..1000 {
        cs.push(E::col(k % w));
        cs.push(E::mul(E::IsTransition, E::nxt(k % w)));
        cs.push(E::mul(E::col((k + 1) % w), E::IsFirst));
    }
    let tape = Tape::compile(&cs);
    let n = 37;
    let rows = vec![F::NEG_ONE; n * w];
    let next: Vec<u32> = (0..n as u32).map(|i| (i + 5) % n as u32).collect();
    let sf = vec![F::NEG_ONE; n];
    let sl = vec![F::new(5); n];
    let apow = vec![EF::from_basis_coefficients_fn(|_| F::NEG_ONE); cs.len()];
    let be = BlockEval::new(&tape, &[]);
    let mut out = vec![EF::ZERO; n];
    be.eval_combined(&rows, w, &next, &sf, &sl, &apow, &mut out);
    assert_eq!(out, reference(&tape, &[], &rows, w, &next, &sf, &sl, &apow, n));
}

#[test]
fn cube_table_matches_scalar() {
    let t = cube_table(50, 22);
    let tape = Tape::compile(&t.constraints);
    let mut r = Rng(42);
    check(&tape, &[], 50, 300, 256, &mut r);
}

#[test]
#[ignore]
fn bench_cube_3000() {
    let w = 3000;
    let t = cube_table(w, 22);
    let tape = Tape::compile(&t.constraints);
    let chunk = 1024;
    let nrows = chunk + 16;
    let trace = cube_trace(w, 11);
    let rows = &trace.values[..nrows * w];
    let next: Vec<u32> = (0..chunk as u32).map(|i| i + 16).collect();
    let mut r = Rng(7);
    let sf: Vec<F> = (0..chunk).map(|_| r.f()).collect();
    let sl: Vec<F> = (0..chunk).map(|_| r.f()).collect();
    let alpha = r.ef();
    let apow: Vec<EF> = alpha.powers().take(tape.outputs.len()).collect();
    let be = BlockEval::new(&tape, &[]);
    println!(
        "tape ops {} -> {} instructions, {} registers, W = {}",
        tape.ops.len(),
        be.num_instructions(),
        be.num_registers(),
        npudr::eval::W
    );
    let mut out = vec![EF::ZERO; chunk];
    be.eval_combined(rows, w, &next, &sf, &sl, &apow, &mut out);
    let t0 = Instant::now();
    let reps: usize = std::env::var("EVAL_BENCH_REPS").ok().and_then(|s| s.parse().ok()).unwrap_or(5);
    for _ in 0..reps {
        be.eval_combined(rows, w, &next, &sf, &sl, &apow, &mut out);
    }
    let fast = (reps * chunk) as f64 / t0.elapsed().as_secs_f64();
    let n_ref = 512;
    let t0 = Instant::now();
    let want = reference(&tape, &[], rows, w, &next, &sf, &sl, &apow, n_ref);
    let slow = n_ref as f64 / t0.elapsed().as_secs_f64();
    assert_eq!(&out[..n_ref], &want[..]);
    println!(
        "width {w}: BlockEval {fast:.0} rows/s ({:.0} tape-ops/s), scalar {slow:.0} rows/s ({:.0} ops/s), speedup {:.1}x",
        fast * tape.ops.len() as f64,
        slow * tape.ops.len() as f64,
        fast / slow
    );
}

/// Cost breakdown on synthetic tapes (loads + accumulations only; a long
/// multiplication chain with one output).
#[test]
#[ignore]
fn bench_breakdown() {
    let w = 3000;
    let chunk = 1024;
    let nrows = chunk + 16;
    let mut r = Rng(9);
    let rows: Vec<F> = (0..nrows * w).map(|_| r.f()).collect();
    let next: Vec<u32> = (0..chunk as u32).map(|i| i + 16).collect();
    let sf: Vec<F> = (0..chunk).map(|_| r.f()).collect();
    let sl: Vec<F> = (0..chunk).map(|_| r.f()).collect();
    let run = |name: &str, cs: Vec<E>| {
        let tape = Tape::compile(&cs);
        let apow: Vec<EF> = (0..cs.len()).map(|_| EF::from_basis_coefficients_fn(|i| F::new(i as u32 + 3))).collect();
        let be = BlockEval::new(&tape, &[]);
        let mut out = vec![EF::ZERO; chunk];
        let t0 = Instant::now();
        let reps = 10;
        for _ in 0..reps {
            be.eval_combined(&rows, w, &next, &sf, &sl, &apow, &mut out);
        }
        let dt = t0.elapsed().as_secs_f64() / (reps * chunk) as f64;
        println!(
            "{name}: {} instructions, {:.2} ns/row/instruction, {:.0} rows/s",
            be.num_instructions(),
            dt * 1e9 / be.num_instructions() as f64,
            1.0 / dt
        );
    };
    run("load+acc", (0..w).map(E::col).collect());
    run("load+acc next", (0..w).map(E::nxt).collect());
    let mut e = E::col(0);
    for c in 1..w {
        e = E::mul(e, E::col(c));
    }
    run("load+mul", vec![e]);
    let mut e = E::col(0);
    for k in 1..w {
        e = E::mul(E::add(e, E::c(k as u64)), E::col(k % 8));
    }
    run("mul/addk chain", vec![e]);
}
