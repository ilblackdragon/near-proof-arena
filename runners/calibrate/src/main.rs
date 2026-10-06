//! `arena-calibrate` — the judge calibration workload `arena-calibrate-v1`
//! (docs/BENCHMARK_SPEC.md §6.1, bench-spec-v1.6).
//!
//! A fixed, deterministic CPU + memory mix that resembles what candidates
//! spend benchmark time on. Every thread runs the same work on its own data:
//!
//! 1. **hash**: a chained SHA-256 over a 1 MiB buffer, 128 times;
//! 2. **field**: 48 forward NTTs of size 2^16 over the Goldilocks prime
//!    p = 2^64 − 2^32 + 1 (multiply/reduce heavy);
//! 3. **memory**: 2^23 dependent loads through a 16 MiB random cyclic
//!    permutation (latency-bound; with 8 threads it overflows the 96 MiB
//!    L3 of the reference host, so shared memory-bandwidth contention shows up).
//!
//! The time is NOT measured here: the judge times the whole process with the
//! supervisor wall clock (§3.1), exactly like a candidate invocation. The
//! process prints one line, `arena-calibrate-v1 <checksum hex>`. The checksum
//! is identical for every run and thread count; the judge compares it with the
//! value pinned in `measurement.calibration.expected_checksum` (a wrong
//! checksum means a wrong binary or a broken host: INFRA).
//!
//! usage: arena-calibrate [--threads N]     (default 1)

use sha2::{Digest, Sha256};

const P: u64 = 0xffff_ffff_0000_0001;
const LOG_N: u32 = 16;
const NTT_ROUNDS: usize = 48;
const HASH_BYTES: usize = 1 << 20;
const HASH_ROUNDS: usize = 128;
const CHASE_WORDS: usize = 1 << 22; // 16 MiB of u32
const CHASE_STEPS: usize = 1 << 23;

fn splitmix(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

fn mulmod(a: u64, b: u64) -> u64 {
    ((a as u128 * b as u128) % P as u128) as u64
}

fn powmod(mut b: u64, mut e: u64) -> u64 {
    let mut r = 1u64;
    while e > 0 {
        if e & 1 == 1 {
            r = mulmod(r, b);
        }
        b = mulmod(b, b);
        e >>= 1;
    }
    r
}

fn hash_part(seed: u64) -> [u8; 32] {
    let mut s = seed;
    let mut buf = vec![0u8; HASH_BYTES];
    for chunk in buf.chunks_mut(8) {
        chunk.copy_from_slice(&splitmix(&mut s).to_le_bytes()[..chunk.len()]);
    }
    let mut h = [0u8; 32];
    for _ in 0..HASH_ROUNDS {
        buf[..32].copy_from_slice(&h);
        h = Sha256::digest(&buf).into();
    }
    h
}

fn ntt_part(seed: u64) -> u64 {
    let n = 1usize << LOG_N;
    // 7 is a generator of the multiplicative group of the Goldilocks field
    let w = powmod(7, (P - 1) >> LOG_N);
    let mut s = seed;
    let mut a: Vec<u64> = (0..n).map(|_| splitmix(&mut s) % P).collect();
    for _ in 0..NTT_ROUNDS {
        // iterative radix-2 Cooley-Tukey, bit-reversed input order
        let mut j = 0usize;
        for i in 1..n {
            let mut bit = n >> 1;
            while j & bit != 0 {
                j ^= bit;
                bit >>= 1;
            }
            j |= bit;
            if i < j {
                a.swap(i, j);
            }
        }
        let mut len = 2;
        while len <= n {
            let wl = powmod(w, (n / len) as u64);
            for start in (0..n).step_by(len) {
                let mut wk = 1u64;
                for k in 0..len / 2 {
                    let u = a[start + k];
                    let v = mulmod(a[start + k + len / 2], wk);
                    let (sum, carry) = u.overflowing_add(v);
                    a[start + k] = if carry || sum >= P {
                        sum.wrapping_sub(P)
                    } else {
                        sum
                    };
                    a[start + k + len / 2] = if u >= v {
                        u - v
                    } else {
                        u.wrapping_add(P).wrapping_sub(v)
                    };
                    wk = mulmod(wk, wl);
                }
            }
            len <<= 1;
        }
    }
    a.iter().fold(0u64, |x, &y| x.rotate_left(5) ^ y)
}

fn chase_part(seed: u64) -> u64 {
    // Sattolo's algorithm: one cycle through every slot.
    let mut s = seed;
    let mut next: Vec<u32> = (0..CHASE_WORDS as u32).collect();
    for i in (1..CHASE_WORDS).rev() {
        let j = (splitmix(&mut s) % i as u64) as usize;
        next.swap(i, j);
    }
    let mut at = 0u32;
    let mut acc = 0u64;
    for _ in 0..CHASE_STEPS {
        at = next[at as usize];
        acc = acc.wrapping_mul(31).wrapping_add(at as u64);
    }
    acc
}

fn thread_work(t: u64) -> u64 {
    // per-thread data, but the checksum below is thread-count independent
    let _ = t;
    let h = hash_part(1);
    let f = ntt_part(2);
    let c = chase_part(3);
    u64::from_le_bytes(h[..8].try_into().unwrap()) ^ f.rotate_left(17) ^ c.rotate_left(41)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let threads = match args.iter().position(|a| a == "--threads") {
        Some(i) => args
            .get(i + 1)
            .and_then(|v| v.parse::<u64>().ok())
            .filter(|&n| (1..=256).contains(&n))
            .unwrap_or_else(|| {
                eprintln!("arena-calibrate: --threads N (1..=256)");
                std::process::exit(2)
            }),
        None => 1,
    };
    let results: Vec<u64> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..threads)
            .map(|t| sc.spawn(move || thread_work(t)))
            .collect();
        hs.into_iter().map(|h| h.join().expect("thread")).collect()
    });
    if results.windows(2).any(|w| w[0] != w[1]) {
        eprintln!("arena-calibrate: threads disagree (broken host)");
        std::process::exit(1)
    }
    println!("arena-calibrate-v1 {:016x}", results[0]);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ntt_roots_are_right() {
        let w = powmod(7, (P - 1) >> LOG_N);
        assert_eq!(powmod(w, 1 << LOG_N), 1);
        assert_ne!(powmod(w, 1 << (LOG_N - 1)), 1);
    }

    #[test]
    fn deterministic() {
        assert_eq!(thread_work(0), thread_work(5));
    }
}
