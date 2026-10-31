# CPU microbenchmarks (measured 2026-10-31)

Host: AMD Ryzen 9 9950X3D (Zen 5, AVX-512, GFNI/VPCLMULQDQ), one core pinned (CPU 8, 10 or 12),
`RAYON_NUM_THREADS=1`, `-C target-cpu=native`. The box was shared (load average ~12 on 32
threads), so treat these as indicative single runs, not p95s. Plonky3 checkout
`/data/illia/nearproof-deps/Plonky3` at `3acc8b70e68d`. Criterion medians. Script:
`run_benches.sh`. All rows are **M** (measured here) unless marked.

## 1. Hashes

| primitive | measured | per unit | note |
|---|---:|---:|---|
| SHA-512 compression (openssl 3.0.13, 8 KiB blocks) | 953.5 MB/s | **134 ns / 128-B compression** (7.45 M/s) | scalar 64-bit; SHA-384 uses this compression |
| SHA-256 compression (SHA-NI) | 2,140 MB/s | 29.9 ns / 64-B compression (33 M/s) | |
| SHA3-256 (Keccak-f[1600]) | 448.8 MB/s | 303 ns / permutation (136-B rate) | |
| Poseidon2 BabyBear width 16 (AVX-512, 16 lanes) | 917.5 ns / 16 perms | **57.3 ns / perm** (17.4 M/s) | |
| Poseidon2 BabyBear width 24 | 1,426 ns / 16 | 89.1 ns | |
| Poseidon2 KoalaBear width 16 | 701.1 ns / 16 | **43.8 ns** (22.8 M/s) | |
| Poseidon2 KoalaBear width 24 | 1,104 ns / 16 | 69.0 ns | |
| Poseidon2 Mersenne-31 width 16 | 687.9 ns / 16 | 43.0 ns | |
| Poseidon2 Goldilocks width 8 (AVX-512, 8 lanes) | 1,361 ns / 8 | 170 ns | |
| Poseidon2 BN254 width 3 | 5,021 ns | 5,021 ns | |

Per byte absorbed on one CPU core, SHA-512 (953 MB/s) and Poseidon2-KoalaBear-16 at rate 8
(22.8 M x 32 B = 730 MB/s) are about equal. On a GPU they are not: SHA-512 needs ~3,100 INT32
ops per 128 B (hashcat, C), Poseidon2-BabyBear-16 ~5,800 per 32 B (D), so SHA-512 is
~7x cheaper per byte natively. Poseidon2's advantage is only inside circuits.

## 2. NTT (Plonky3 `Radix2Dit`, 256 columns per batch)

| transform | time | per element | per butterfly |
|---|---:|---:|---:|
| BabyBear, 2^16 x 256 | 93.2 ms | 5.56 ns | 0.69 ns |
| BabyBear, 2^20 x 256 | 1.379 s | 5.14 ns | **0.51 ns** |
| Goldilocks, 2^20 x 256 | 2.582 s | 9.62 ns | 0.96 ns (1.9x BabyBear) |
| Goldilocks iDFT, 2^20 x 256 | 2.804 s | 10.4 ns | 1.04 ns |
| BabyBear coset LDE 2^20 -> 2^21 (iDFT + DFT), 256 columns | 5.42 s | 20.2 ns per input | 0.65 ns |

## 3. Binary-field multiplication (Plonky3 `p3-binary-field`, throughput, 10 interleaved chains)

| field | dispatched (CLMUL/GFNI) | portable reference | ratio |
|---|---:|---:|---:|
| GF(2^8) | 0.74 ns | 21.0 ns | 28x |
| GF(2^16) | 2.99 ns | 58.3 ns | 19x |
| GF(2^32) | 9.49 ns | 190.8 ns | 20x |
| GF(2^64) | 6.98 ns | 564.8 ns | 81x |
| GF(2^128) | **18.2 ns** | **1,715 ns** | **94x** |

GPUs have no carry-less multiply. The 94x ratio is an upper bound on the penalty, because a GPU
kernel can use GF(2^16) log/exp tables or bitslicing. It is why `gf128_ops` is the dominant
sensitivity of the binary-field architecture.

## 4. Zero-knowledge overhead of WHIR (Plonky3 `whir/benches/zk_overhead.rs`, HVZK-WHIR, eprint 2026/391)

KoalaBear with a quintic extension, Poseidon2 Merkle, folding 4, starting rate 1/4, 100-bit
target per error term, CapacityBound, `ell_zk = 16`, `mask_log_inv_rate = 5`:

| size | plain proof | ZK proof | ZK - plain | plain prove | ZK prove | ratio |
|---|---:|---:|---:|---:|---:|---:|
| 2^16 | 30,914 B | 103,583 B | **+72,669 B** | 14.58 ms | 25.07 ms | 1.72x |
| 2^18 | 37,490 B | 110,139 B | **+72,649 B** | 52.54 ms | 67.47 ms | 1.28x |

The ZK cost is an **additive ~72.6 KB**, independent of polynomial size, at 100 bits and 31-B
digests. The model scales it to 128 bits linearly (92.9 KB, **D**); 42-B SHA-384 digests would
add more. The same bench's 128-bit octic Johnson-bound configuration **panicked** at
`zk_overhead.rs:88` (a `ZkWhirConfig::new(..).unwrap()`), so there is no 128-bit ZK
measurement. That is the first follow-up experiment.

## 5. Mainnet shard-13 gas distribution (`w13_gas.py` over `tools/d3/claim_outputs.py`)

1,223 replay cases in `/data/illia/nearproof-deps/mainnet-w13/replay-cases/`, header gas field:

| chunks | zero-gas | mean | p50 | p90 | p99 | p99.9 | max |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1,223 | 642 | 1.42 Tgas | 0 | 3.14 Tgas | **18.45 Tgas** | 113.3 Tgas | **115.3 Tgas** |

(The brief quoted p99 = 16 Tgas. The difference is the quantile convention; this file uses
`sorted[int(0.99 n)]`.)

## 6. Scaling the CPU numbers by the model

Model GPU time = model INT32 ops / (16.73 T INT32/s x `eff`). To check the op counts, apply
them to a Zen 5 core. The core's 32-bit lane peak is taken as ~1.66e11 ops/s (5.2 GHz x 2
x 512-bit integer pipes, **A**).

| kernel | model ops | CPU measured | CPU ops-efficiency | H200 at eff 0.35 (D) | = CPU cores |
|---|---:|---:|---:|---:|---:|
| Poseidon2-BB-16 permutation | 5,800 | 17.4 M/s | 61 % | 1.0 G perm/s | ~58 |
| BabyBear butterfly | 10 | 1.95 G/s | 12 % | 585 G/s | ~300 |
| SHA-512 compression | 3,127 (C) | 7.45 M/s (scalar) | — | 1.87 G/s | ~250 |

The butterfly row matters. The CPU NTT spends ~8x more lane-slots than the model's 10 ops,
because of shuffles, twiddle loads and memory traffic. A GPU NTT is bandwidth-bound at
~2e11 elements/s for 2^24 points (3 passes x 8 B at 4.8 TB/s), against a compute bound of
1.4e11/s at 100 % peak. So `bfly_ops` = 10 at `eff` 0.35 is optimistic, not conservative. It
is the second- or third-largest latency sensitivity (README).
