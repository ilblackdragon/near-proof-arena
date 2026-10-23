//! Prover-latency microbenchmarks (lane/pq-prover-latency).
//!
//! Copied into `openvm-sha384/crates/recursion/examples/` by `../run_bench.sh` so that it links the
//! exact unified backend + SHA-384/Ext12 config the NV prover uses.  Usage:
//!   latency_bench <what> [args]     what = sha | grind | ext | ntt | commit | all
//! Process SHA levers come from env (NEARPROOF_DIGEST_BYTES, NEARPROOF_COSET_LEAF, NEARPROOF_TSTAR).
use std::time::Instant;

use openvm_recursion_circuit::sha384::config::{pow_step, ShaHasher, EF, F};
use openvm_stark_backend::{
    p3_field::{BasedVectorSpace, PrimeCharacteristicRing},
    p3_maybe_rayon::prelude::*,
    prover::{stacked_pcs::{rs_code_matrix_odd, stacked_commit_odd, MerkleTree}, ColMajorMatrix},
};
use sha2::digest::generic_array::GenericArray;

fn threads() -> usize {
    std::env::var("RAYON_NUM_THREADS").ok().and_then(|s| s.parse().ok()).unwrap_or(1)
}

fn sha(nthreads_list: &[usize]) {
    // raw SHA-512 compression function (SHA-384 = same compression, different IV/truncation)
    let per = 1usize << 22;
    for &nt in nthreads_list {
        let t = Instant::now();
        let acc: u64 = std::thread::scope(|s| {
            let hs: Vec<_> = (0..nt)
                .map(|i| {
                    s.spawn(move || {
                        let mut st = [0x6a09e667f3bcc908u64 ^ i as u64, 1, 2, 3, 4, 5, 6, 7];
                        let mut blk = GenericArray::<u8, sha2::digest::consts::U128>::default();
                        for j in 0..per {
                            blk[0..8].copy_from_slice(&(j as u64).to_le_bytes());
                            sha2::compress512(&mut st, std::slice::from_ref(&blk));
                        }
                        st[0]
                    })
                })
                .collect();
            hs.into_iter().map(|h| h.join().unwrap()).fold(0, |a, b| a ^ b)
        });
        let s = t.elapsed().as_secs_f64();
        let rate = (per * nt) as f64 / s;
        println!(
            "SHA512_COMPRESS threads={nt} total={:.2}M/s per_thread={:.2}M/s ns_per={:.1} (x{acc:x})",
            rate / 1e6,
            rate / 1e6 / nt as f64,
            1e9 * s * nt as f64 / (per * nt) as f64
        );
    }
    // multi-block (leaf hashing of long rows): 64 blocks per call
    let blocks = vec![GenericArray::<u8, sha2::digest::consts::U128>::default(); 64];
    let mut st = [0u64; 8];
    let n = 1 << 16;
    let t = Instant::now();
    for _ in 0..n {
        sha2::compress512(&mut st, &blocks);
    }
    let s = t.elapsed().as_secs_f64();
    println!("SHA512_COMPRESS_MULTIBLOCK threads=1 {:.2}M/s ({:.1} MB/s) (x{:x})", (n * 64) as f64 / s / 1e6, (n * 64 * 128) as f64 / s / 1e6, st[0]);
}

fn grind(nthreads: usize) {
    // the honest grind as implemented (T* PoW block, one compression per attempt, via the hasher API)
    let state = [7u8; 48];
    let n1 = 1u32 << 21;
    let t = Instant::now();
    let mut hits = 0u32;
    for w in 0..n1 {
        hits += pow_step(&state, &[w], 64).1 as u32;
    }
    let s = t.elapsed().as_secs_f64();
    println!("GRIND_POW_STEP threads=1 {:.2}M attempts/s ({hits})", n1 as f64 / s / 1e6);
    let n = 1u32 << 26;
    let t = Instant::now();
    let cnt = (0..n).into_par_iter().filter(|&w| pow_step(&state, &[w], 64).1).count();
    let s = t.elapsed().as_secs_f64();
    let rate = n as f64 / s;
    println!(
        "GRIND_POW_STEP threads={nthreads} {:.2}M attempts/s => 2^32 in {:.1} s ({cnt})",
        rate / 1e6,
        (1u64 << 32) as f64 / rate
    );
}

fn ext() {
    let mk = |s: u32| <EF as BasedVectorSpace<F>>::from_basis_coefficients_fn(|i| F::from_u32(s.wrapping_mul(2654435761).wrapping_add(i as u32 * 97 + 1) % 2013265921));
    // throughput: 8 independent chains
    let mut xs: Vec<EF> = (0..8).map(|i| mk(i + 1)).collect();
    let y = mk(99);
    let n = 1 << 22;
    let t = Instant::now();
    for _ in 0..n / 8 {
        for x in xs.iter_mut() {
            *x *= y;
        }
    }
    let s = t.elapsed().as_secs_f64();
    println!("EXT12_MUL threads=1 throughput {:.2}M/s ns_per={:.2} ({:?})", n as f64 / s / 1e6, 1e9 * s / n as f64, <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(&xs[0])[0]);
    // latency: one dependent chain
    let mut x = mk(5);
    let n2 = 1 << 20;
    let t = Instant::now();
    for _ in 0..n2 {
        x *= y;
    }
    let s = t.elapsed().as_secs_f64();
    println!("EXT12_MUL threads=1 latency ns_per={:.2} ({:?})", 1e9 * s / n2 as f64, <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(&x)[0]);
    // ext x base
    let b = F::from_u32(123457);
    let t = Instant::now();
    for _ in 0..n / 8 {
        for x in xs.iter_mut() {
            *x *= b;
        }
    }
    let s = t.elapsed().as_secs_f64();
    println!("EXT12_MUL_BASE threads=1 {:.2}M/s ns_per={:.2}", n as f64 / s / 1e6, 1e9 * s / n as f64);
    // multi-threaded ext mul
    let nt = threads();
    let m = 1usize << 26;
    let t = Instant::now();
    let r: EF = (0..m / 1024)
        .into_par_iter()
        .map(|i| {
            let mut a = [mk(i as u32), mk(i as u32 + 1), mk(i as u32 + 2), mk(i as u32 + 3)];
            for _ in 0..256 {
                for v in a.iter_mut() {
                    *v *= y;
                }
            }
            a[0] + a[1] + a[2] + a[3]
        })
        .sum();
    let s = t.elapsed().as_secs_f64();
    println!("EXT12_MUL threads={nt} throughput {:.2}M/s ({:?})", m as f64 / s / 1e6, <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(&r)[0]);
    // base field (scalar) mul throughput for reference
    let mut bs: Vec<F> = (0..8).map(|i| F::from_u32(i + 3)).collect();
    let t = Instant::now();
    for _ in 0..n / 8 {
        for v in bs.iter_mut() {
            *v *= b;
        }
    }
    let s = t.elapsed().as_secs_f64();
    println!("BABYBEAR_MUL_SCALAR threads=1 {:.0}M/s ({:?})", n as f64 / s / 1e6, bs[0]);
}

fn ntt() {
    use openvm_stark_backend::odd_domain::rs_encode;
    let nt = threads();
    for log in [20usize, 22, 24] {
        let coeffs: Vec<F> = (0..1u32 << (log - 1)).map(F::from_u32).collect();
        // one column, c = 1 (the backend's per-column Radix2DitParallel)
        let t = Instant::now();
        let out = rs_encode::<F, F>(coeffs.clone(), log, 1);
        let s = t.elapsed().as_secs_f64();
        println!("NTT_BB col=1 log={log} c=1 threads={nt} {:.3} s  {:.2} ns/point  {:.1} M points/s ({:?})", s, 1e9 * s / (1u64 << log) as f64, (1u64 << log) as f64 / s / 1e6, out[1]);
        drop(out);
        // batch of 16 columns in parallel (column-level parallelism)
        let w = 16;
        let t = Instant::now();
        let outs: Vec<Vec<F>> = (0..w).into_par_iter().map(|_| rs_encode::<F, F>(coeffs.clone(), log, 1)).collect();
        let s = t.elapsed().as_secs_f64();
        println!("NTT_BB col={w} log={log} c=1 threads={nt} {:.3} s  {:.2} ns/(point*col)  {:.1} M points/s", s, 1e9 * s / (w << log) as f64, (w << log) as f64 / s / 1e6);
        drop(outs);
    }
    // x15 domain: 15 cosets of 2^20 (one column)
    let coeffs: Vec<F> = (0..1u32 << 19).map(F::from_u32).collect();
    let t = Instant::now();
    let out = rs_encode::<F, F>(coeffs, 20, 15);
    let s = t.elapsed().as_secs_f64();
    println!("NTT_BB col=1 log=20 c=15 threads={nt} {:.3} s  {:.2} ns/point (15*2^20 points)", s, 1e9 * s / out.len() as f64);
    // Ext12 NTT (WHIR rounds >= 1 commit Ext12 codewords)
    let coeffs: Vec<EF> = (0..1u32 << 19).map(|i| EF::from(F::from_u32(i))).collect();
    let t = Instant::now();
    let out = rs_encode::<F, EF>(coeffs, 20, 1);
    let s = t.elapsed().as_secs_f64();
    println!("NTT_EXT12 col=1 log=20 c=1 threads={nt} {:.3} s  {:.2} ns/point", s, 1e9 * s / out.len() as f64);
}

fn commit(w: usize, h: usize, b: usize, k: usize, c: usize) {
    let nt = threads();
    let vals: Vec<F> = (0..(w << h) as u32).map(|i| F::from_u32(i.wrapping_mul(2654435761) % 2013265921)).collect();
    let m = ColMajorMatrix::new(vals, w);
    let hasher = ShaHasher;
    let l_skip = 2;
    let t = Instant::now();
    let rs = rs_code_matrix_odd(l_skip, b, c, &m).unwrap();
    let t_rs = t.elapsed().as_secs_f64();
    let pts = rs.values.len();
    let t = Instant::now();
    let tree = MerkleTree::new_with_cosets(&hasher, rs, 1 << k, c).unwrap();
    let t_mk = t.elapsed().as_secs_f64();
    let _ = tree.root().unwrap();
    drop(tree);
    let t = Instant::now();
    let (_root, _data) = stacked_commit_odd(&hasher, l_skip, h - l_skip, b, k, c, &[&m], false).unwrap();
    let t_all = t.elapsed().as_secs_f64();
    let db = std::env::var("NEARPROOF_DIGEST_BYTES").unwrap_or("48".into());
    let cl = std::env::var("NEARPROOF_COSET_LEAF").unwrap_or("0".into());
    println!(
        "COMMIT W={w} h={h} b={b} k={k} c={c} digest={db} coset_leaf={cl} threads={nt} cells={:.3e} rs={t_rs:.2}s ({:.2} ns/cell) merkle={t_mk:.2}s ({:.2} ns/cell, {:.2} ns/byte) stacked_commit_odd={t_all:.2}s ({:.2} ns/cell)",
        pts as f64,
        1e9 * t_rs / pts as f64,
        1e9 * t_mk / pts as f64,
        1e9 * t_mk / (4 * pts) as f64,
        1e9 * t_all / pts as f64
    );
}

/// lane/pq-cpu-prover: streamed commitment of W base-field polynomials of 2^n coefficients on the
/// c * 2^L domain (L = n + b), as the stacked commit of a real NV layer runs it.
fn stream(w: usize, n: usize, b: usize, k: usize, c: usize) {
    use openvm_stark_backend::prover::stream_pcs::stream_commit;
    let coeffs: Vec<Vec<F>> = (0..w)
        .map(|j| (0..(1u32 << n)).map(|i| F::from_u32((i ^ (j as u32 * 7919)).wrapping_mul(2654435761) % 2013265921)).collect())
        .collect();
    let t = Instant::now();
    let tree = stream_commit::<F, F, _>(&ShaHasher, coeffs, n + b, c, 1 << k);
    let s = t.elapsed().as_secs_f64();
    let cells = (w << (n + b)) * c;
    println!(
        "STREAM W={w} n={n} b={b} k={k} c={c} threads={} cells={cells:.3e} secs={s:.2} ({:.2} ns/cell) root0={}",
        threads(),
        1e9 * s / cells as f64,
        tree.root().unwrap()[0]
    );
}

/// lane/pq-cpu-prover: streamed commitment of `w` Ext12 polynomials (the WHIR round codeword
/// shape: d_ext = 12, so the base matrix is 12*w wide). `w=1` reproduces the round-0 commit.
fn stream_ext(w: usize, n: usize, b: usize, k: usize, c: usize) {
    use openvm_stark_backend::prover::stream_pcs::stream_commit;
    let coeffs: Vec<Vec<EF>> = (0..w)
        .map(|j| {
            (0..(1u32 << n))
                .map(|i| {
                    EF::from_basis_coefficients_fn(|q| {
                        F::from_u32((i.wrapping_mul(2654435761) ^ (j as u32 * 7919) ^ (q as u32 * 131)) % 2013265921)
                    })
                })
                .collect()
        })
        .collect();
    let t = Instant::now();
    let tree = stream_commit::<F, EF, _>(&ShaHasher, coeffs, n + b, c, 1 << k);
    let s = t.elapsed().as_secs_f64();
    let cells = (w << (n + b)) * c;
    println!(
        "STREAM_EXT W={w} n={n} b={b} k={k} c={c} threads={} cells={cells:.3e} base_cells={:.3e} secs={s:.2} ({:.2} ns/ext-cell) root0={}",
        threads(),
        cells as f64 * 12.0,
        1e9 * s / cells as f64,
        tree.root().unwrap()[0]
    );
}

/// lane/pq-cpu-prover: coset DFT of a 2^n x w row-major matrix: p3 Radix2DitParallel (as the
/// streamed commit used), p3 Radix2Dit, and the four-step `fast_dft::coset_dft_rows`.
fn dft_bench(w: usize, n: usize) {
    use openvm_stark_backend::prover::fast_dft::coset_dft_rows;
    use openvm_stark_backend::p3_dft::{Radix2Dit, Radix2DitParallel, TwoAdicSubgroupDft};
    use p3_matrix::{bitrev::BitReversibleMatrix, dense::RowMajorMatrix};
    let vals: Vec<F> = (0..(w << n) as u32).map(|i| F::from_u32(i.wrapping_mul(2654435761) % 2013265921)).collect();
    let shift = F::from_u32(7);
    let t = Instant::now();
    let a = Radix2DitParallel::<F>::default().coset_dft_batch(RowMajorMatrix::new(vals.clone(), w), shift).bit_reverse_rows().values;
    let s1 = t.elapsed().as_secs_f64();
    let t = Instant::now();
    let b = Radix2Dit::<F>::default().coset_dft_batch(RowMajorMatrix::new(vals.clone(), w), shift).values;
    let s2 = t.elapsed().as_secs_f64();
    let t = Instant::now();
    let c = coset_dft_rows(&vals, w, shift);
    let s3 = t.elapsed().as_secs_f64();
    let n_ = 1usize << n;
    let same = (0..n_).all(|u| {
        let r = openvm_stark_backend::p3_util::reverse_bits_len(u, n);
        a[r * w..(r + 1) * w] == c[u * w..(u + 1) * w]
    }) && b == c;
    let cells = (w << n) as f64;
    println!(
        "DFT w={w} n={n} threads={} parallel={s1:.3}s ({:.2} ns/cell) dit={s2:.3}s ({:.2}) four_step={s3:.3}s ({:.2}) equal={same}",
        threads(), 1e9 * s1 / cells, 1e9 * s2 / cells, 1e9 * s3 / cells
    );
}

/// lane/pq-cpu-prover: hang hunt - one p3 `Radix2Dit` (spin::RwLock twiddle cache) shared by many
/// rayon tasks, as the early streamed-commit outer path did; a fresh instance per round.
fn dft_share(rounds: usize, tasks: usize, log_n: usize, w: usize) {
    use openvm_stark_backend::p3_dft::{Radix2Dit, TwoAdicSubgroupDft};
    use p3_matrix::dense::RowMajorMatrix;
    use p3_maybe_rayon::prelude::*;
    let base: Vec<F> = (0..(w << log_n) as u32).map(|i| F::from_u32(i % 2013265921)).collect();
    for r in 0..rounds {
        let seq = Radix2Dit::<F>::default();
        let t = Instant::now();
        let s: u64 = (0..tasks)
            .into_par_iter()
            .map(|k| {
                let ev = seq.coset_dft_batch(RowMajorMatrix::new(base.clone(), w), F::from_u32(k as u32 + 3));
                { use p3_field::PrimeField32; ev.values[k % ev.values.len()].as_canonical_u32() as u64 }
            })
            .sum();
        println!("DFT_SHARE round={r} secs={:.2} ({s})", t.elapsed().as_secs_f64());
    }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let what = a.get(1).map(|s| s.as_str()).unwrap_or("all");
    let nt = threads();
    match what {
        "sha" => sha(&[1, 8, 16, 32]),
        "grind" => grind(nt),
        "ext" => ext(),
        "ntt" => ntt(),
        "dftshare" => {
            let p = |i: usize, d: usize| a.get(i).and_then(|s| s.parse().ok()).unwrap_or(d);
            dft_share(p(2, 50), p(3, 64), p(4, 12), p(5, 48))
        }
        "dft" => {
            let p = |i: usize, d: usize| a.get(i).and_then(|s| s.parse().ok()).unwrap_or(d);
            dft_bench(p(2, 82), p(3, 20))
        }
        "stream" => {
            let p = |i: usize, d: usize| a.get(i).and_then(|s| s.parse().ok()).unwrap_or(d);
            stream(p(2, 82), p(3, 20), p(4, 2), p(5, 1), p(6, 15))
        }
        "streamext" => {
            let p = |i: usize, d: usize| a.get(i).and_then(|s| s.parse().ok()).unwrap_or(d);
            stream_ext(p(2, 1), p(3, 19), p(4, 8), p(5, 4), p(6, 15))
        }
        "commit" => {
            let p = |i: usize, d: usize| a.get(i).and_then(|s| s.parse().ok()).unwrap_or(d);
            commit(p(2, 32), p(3, 18), p(4, 3), p(5, 1), p(6, 15))
        }
        _ => {
            sha(&[1, 8, 16, 32]);
            grind(nt);
            ext();
            ntt();
            commit(32, 18, 3, 1, 15);
        }
    }
}
