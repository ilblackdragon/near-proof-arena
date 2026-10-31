# H200 SXM hardware model and kernel-efficiency factors

There is no GPU on this host. Every GPU number below is derived from vendor specifications and
published results, then scaled by an explicitly stated efficiency factor `eff`. None is
measured on an H200.

## 1. Specifications (C)

| quantity | value | source |
|---|---|---|
| HBM3e capacity | 141 GB | NVIDIA H200 product page, https://www.nvidia.com/en-us/data-center/h200/ (fetched 2026-10-31; specs marked "preliminary") |
| HBM bandwidth | 4.8 TB/s | same |
| NVLink | 900 GB/s per GPU (bidirectional; 450 GB/s per direction) | same |
| FP32 | 67 TFLOPS (= 132 SMs x 128 FP32 lanes x 1.98 GHz x 2) | same; the SM count and clock are the GH100 SXM configuration that reproduces 67 TF |
| FP64 / FP64 tensor | 34 / 67 TFLOPS | same |
| INT32 | 64 ops/clk/SM for 32-bit IADD, IMAD, LOP3, shifts (cc 9.0) | CUDA C++ Programming Guide, "Arithmetic Instructions" throughput table, https://docs.nvidia.com/cuda/cuda-c-programming-guide/#arithmetic-instructions |
| **INT32 peak (D)** | 132 x 64 x 1.98e9 = **1.673e13 ops/s** | `peak_int32()` |
| TDP | up to 700 W | product page |

Tensor cores are not used. No published prover uses them for 31-bit or binary field arithmetic
at scale, and the model does not credit them.

## 2. Derived primitive rates at 100 % of INT32 peak (`hw_report()`)

Multiply by `eff` for sustained rates.

| primitive | INT32 ops each | peak rate per GPU | basis |
|---|---:|---:|---|
| 31-bit Montgomery multiply (BabyBear/KoalaBear) | 6 | 2.8e12 /s | D: IMAD.LO, IMAD.HI, m = lo·p', IMAD.HI(m, p), subtract, select |
| Goldilocks multiply | ~18 | 9.3e11 /s | D: 64x64 via four 32-bit products (8 IMAD) plus the 2^64 − 2^32 + 1 reduction |
| GF(2^128) multiply | 300 (**A**, range 60–1,200) | 5.6e10 /s | D/A: no carry-less multiply on GPUs; tower over GF(2^16) log/exp tables in shared memory (27 sub-products). CPU portable/CLMUL ratio is 94x (M, `bench/RESULTS.md`) |
| BabyBear^E multiply | 0.75·E²·6 = 450 (E = 10), 288 (E = 8) | — | D (Karatsuba-ish) |
| **SHA-512 compression** (SHA-384) | **3,127** | **5.35e9 /s** | C: hashcat v6.2.6 `-m 1700` SHA2-512 on H100 80 GB SXM, 5,074–5,374 MH/s per device, AWS p5.48xlarge log of 2023-09-18, https://github.com/javydekoning/aws-hashcat/blob/master/p5.48xlarge.v6.2.6.cuda.txt ; ops = peak / rate |
| SHA-256 compression | 1,045 | 1.6e10 /s | C: same log, `-m 1400`, 15.1–16.1 GH/s per device |
| Poseidon2 BabyBear-16 permutation | 5,800 | 2.9e9 /s | D: 8 external rounds x 16 S-boxes (x^7 = 4 multiplies) + 13 internal rounds (S-box + diagonal) = 772 multiplies x 6 + 1,184 adds |
| NTT butterfly (31-bit) | 10 | 1.7e12 /s | D |
| NTT 2^24 points, compute bound | 120 per element | 1.4e11 elements/s | D: 12 butterflies per element |
| NTT 2^24 points, bandwidth bound | 3 passes x 8 B | 2.0e11 elements/s | D: radix-2^8..2^11 passes in shared memory, 4 B read + 4 B write per pass |

The H200 and H100 SXM share the GH100 compute configuration. The H200 differs only in HBM
(141 GB at 4.8 TB/s versus 80 GB at 3.35 TB/s). So the H100 hashcat rates transfer to compute
unchanged (**A**, standard).

## 3. The efficiency factor `eff` and its calibration

`eff` is the sustained fraction of INT32 peak, averaged over every prover kernel (NTT, Merkle
hashing, constraint evaluation, logUp/GKR, sumcheck, FRI/WHIR folding), when cost is counted in
the model's own op counts. The baseline 0.35 is inherited from V3-PERF-DESIGN and is
**A**. The calibration points:

| evidence | what it implies for `eff` | label |
|---|---|---|
| hashcat SHA-512 on H100: 5.35 GH/s | the op count *defines* 100 % for SHA-512. A Merkle kernel reads leaves from HBM, but at 128 B per 3,127 ops it stays compute-bound | C/D |
| NVIDIA cuPQC Poseidon2-BabyBear Merkle tree, 2^24 leaves x 128 elements, **39.14 ms on an RTX PRO 6000 Blackwell**, blog of 2026-04-09, https://nvidia.github.io/cuPQC/blogs/merkle/ | 2^31 elements ≈ 2.85e8 permutations (rate-8 sponge plus nodes) in 39 ms = 7.3e9 perm/s. At 5,800 ops each that is 4.2e13 ops/s against that card's ~6.3e13 INT32 peak (188 SMs x 128 x 2.6 GHz, **A**), i.e. **~0.45–0.67** for a single well-tuned hashing kernel | C/D |
| ZKsync Airbender: **21.8 MHz** RISC-V cycles on one H100 (vendor page, comparison sourced "as of June 2025"), https://zksync.io/airbender ; restated by BlockEden 2026-01-30, https://blockeden.xyz/blog/2026/01/30/zksync-airbender-fastest-risc-v-zkvm-ethereum-proving/ | 16.7e12 / 21.8e6 = 767 k INT32 slots per cycle at 100 %. At ~150–300 k model-ops per cycle that is eff ≈ 0.2–0.4. Airbender is M31, Blake2s, ~100-bit **conjectured**, non-ZK base layer | C/D, uncertain |
| SP1 Hypercube: 99.7 % of 954 L1 blocks under 12 s on **16 RTX 5090**, blog of 2025-11-18, https://blog.succinct.xyz/real-time-proving-16-gpus/ ; earlier ~160 RTX 4090 (May 2025), https://blog.succinct.xyz/sp1-hypercube/ | no cycle counts published, so no direct eff. KoalaBear/Poseidon2, ~100-bit, not PQ-128 proven, non-ZK inner layers | C |
| OpenVM 2.0 beta: p99 7.9 s on 16 GPUs over 7,200 mainnet blocks (Axiom blog, 2026), https://axiom.xyz/blog/openvm-2-beta ; ZisK 9.62 s p99 on 4 RTX 5090 (2026-08, vendor-reported), https://cryptoslate.com/ethereums-12-gpu-proving-problem-just-got-a-4-gpu-answer/ | same caveat: conjectured ~100-bit security, Poseidon2/Blake-class hashes, no common benchmark | C |
| CPU, this host (`bench/RESULTS.md` §6): Plonky3 Poseidon2 reaches 61 % of the lane peak in model ops; the Plonky3 NTT reaches 12 % | the model's NTT op count is light. Treat `bfly_ops` = 10 at eff 0.35 as optimistic | M/D |
| this repo's CPU prover: 18.7 M W_eq/s on 14 threads, ≈ 9 % of AVX-512 peak in model ops (V3-PERF-DESIGN §7) | a production-grade GPU prover needs ~4x the CPU path's efficiency to reach 0.35 | MR |

**Reading.** 0.35 is plausible for a mature, PQ-parameterised GPU prover. 0.6 is the
practical ceiling (single-kernel hashing at ~0.5–0.67). Values above 1.0 are impossible by
definition. Published real-time Ethereum provers reach their numbers at ~100-bit conjectured
security with algebraic or Blake hashes. That is cheaper per cell than SHA-384, 128-bit PQ and
proven bounds by roughly the factors in V3-D3A-STUDY §11.5 (2–4x).

**Cross-check of the verdict against the fastest published GPU prover (D).** Take Airbender's
21.8 MHz per H100 at face value. Give each Wasm operator 1.5–3 RISC-V cycles
(V3-PERF-DESIGN §2.6). The worst-case 1.215e9 Wasm operators are then 1.8–3.6e9 cycles, or
**10–21 s on 8 GPUs**, for the base layer alone, at ~100-bit conjectured security. That is the
same infeasibility the model finds, without any of this model's PQ/SHA-384/ZK factors.

## 4. Memory and interconnect

* **HBM 141 GB per GPU.** Per committed cell, a segment proof holds:
  * the trace, 4 B;
  * the LDE, 4·2^lb B;
  * for GKR architectures, ~16 B of layer data.

  `mem_per_gpu_gb` keeps two segments in flight per GPU. At rate 1/2, 2^24 rows x 160 cells
  is 64 GB/GPU. 2^25 does not fit under the 90 % rule.
* **The single shared-transcript proof does not fit.** V3-PERF-DESIGN P-PERF-4 holds the
  whole chunk's LDE resident until the global challenges. That needs **589 GB per GPU at 8
  GPUs** (78 GB at 32). Spilling to the HGX host's ~2 TB RAM over PCIe 5 (~55 GB/s per GPU)
  costs ~10 s each way. So on 8 GPUs, segment proofs plus aggregation are forced (README §3).
* **NVLink 4** (450 GB/s per direction) carries:
  * segment-proof transfers to aggregation GPUs (tens of MB per proof, < 1 ms);
  * the final wrap split across the 8 GPUs of the node (`wrap_split_eff` = 0.6, **A**).

  It is not a bottleneck in any configuration modelled.
