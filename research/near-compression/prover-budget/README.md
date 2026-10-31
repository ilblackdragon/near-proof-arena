# Prover budget: a PQ-128, zero-knowledge proof of a 1 Pgas NEAR chunk in 3 s on 8 H200?

Status: **research model, 2026-10-31.** No checker, spec or protocol change. No GPU was used:
every GPU time is derived from H200 specifications, cited prover results and an explicit
efficiency factor `eff`.

Labels: **M** = measured here (`bench/RESULTS.md`); **MR** = measured earlier in this repo;
**C** = cited (URL and date in `HARDWARE.md`); **D** = derived; **A** = assumption.

Files:
* `model.py`: the model. One parameter table `P`, three architectures, a design-knob grid
  search, the feasibility frontier and the sensitivity analysis. Override any parameter with
  `--set name=value`. `--prior` re-runs V3-PERF-DESIGN at 8 GPUs.
* `model-output.txt`: the run quoted below.
* `WORKLOAD.md`: PV86 gas table, per-primitive circuit costs, binding worst case, realistic case.
* `HARDWARE.md`: H200 specifications, derived rates, efficiency calibration.
* `bench/`: the CPU microbenchmarks run for this study, their scripts and the mainnet
  gas-distribution script.

Baseline in every architecture (owner decisions, `docs/zk-formal/V3-D3A-STUDY.md` §D):
* **SHA-384 for Merkle trees, the transcript and in-circuit verification** (U-7, 42-B digests per U-10);
* **proven soundness bounds only** (Johnson regime, 260-bit round-by-round target, z = 32 grinding);
* failure ≤ 2^-128 at 2^64 quantum queries (U-6);
* no elliptic curves.

Poseidon2 appears only as a labelled alternative (`--set hash=poseidon2` or `hybrid`) that
would need an owner decision.

## 1. Verdict

Target: worst-case 1 Pgas chunk, proof ready ≤ 3 s after the last receipt, on 8 H200 SXM.
Model defaults: `eff` = 0.35 of INT32 peak, execution 1.2 s per Pgas. Design knobs (segment
size, rates, fan-in, an optional compression layer) are grid-searched per row under the HBM
limit.

| architecture | 1 Pgas worst case: latency after last receipt | margin | total GPU-s (base / aggregation / wrap) | 1 Pgas worst case needs `eff` ≥ | worst case feasible up to | realistic mix | mainnet p99 (18.45 Tgas) |
|---|---:|---:|---|---:|---:|---|---:|
| (a) univariate AIR + WHIR/FRI, BabyBear^10, committed logUp | **16.0 s** | 5.3x over | 128 (51 / 73 / 4.1) | **1.48 (impossible)** | **83 Tgas** | feasible at 1 Pgas (2.4 s) | 0.98 s |
| (b) multilinear zerocheck + LogUp-GKR + stacked WHIR, BabyBear^8 (main-stack shape) | **10.6 s** | 3.5x over | 85 (44 / 38 / 2.4) | **1.01 (impossible)** | **105 Tgas** | feasible at 1 Pgas (1.9 s) | 0.62 s |
| (c) binary field, Binius64-style AND/MUL constraints | **580 s** | 190x over | 4,650 (4,429 / 220 / 0.2) | ≫ 1 | **5 Tgas** | feasible to 284 Tgas | **0.38 s** |

The same three numbers hold for every architecture:

| | value | target | verdict |
|---|---:|---:|---|
| proof size, SHA-384 wrap + HVZK-WHIR | **392,867 B** = 299,967 (MR, non-ZK final layer) + 92,900 (D from M: +72.6 KB measured at 100-bit, scaled to 128) | ≤ 300,000 | **fails by 92.9 KB (24 %)** |
| verify, protocol model (≈ 5–7 k SHA-512 compressions + 3e5 extension multiplications on one core) | **6–7 ms** | < 200 ms | feasible by protocol |
| verify, measured implementation (299,967 B packet) | 1.46 s at 32 threads, 7.65 s on one core (MR) | < 200 ms | **fails by 7.3x**; unprofiled |

**Plain answer: no.**
* No architecture reaches 1 Pgas worst case within 3 s on 8 H200 at any physically possible
  efficiency.
* Even at a perfect 100 % of INT32 peak, (b) misses: it needs 101 %.
* The base layer alone is over budget: 44 GPU-s against ≈ 33 available at `eff` 0.35
  (8 GPUs x (0.9 x 1.2 s + 3 s)).
* At `eff` 0.35 the worst case becomes feasible at **≈ 80–105 Tgas** (architectures a and b).
* **Realistic mainnet chunks are feasible with large margin**: p99 at 0.4–1.0 s, the maximum
  observed (115 Tgas) in 0.9–1.3 s.
* Even a 1 Pgas chunk with the *measured* mix (3.4 % Wasm gas) fits: 1.9–2.4 s.
* **Proof size fails independently of latency**: ZK costs ≈ 93 KB and the non-ZK wrap already
  sits 33 B under the cap.

Frontier by efficiency and GPU count (worst-case Tgas feasible in 3 s, a / b; `model-output.txt`):

| GPUs | eff 0.20 | eff 0.35 | eff 0.60 |
|---:|---:|---:|---:|
| 8 | 21 / 51 | 83 / 105 | 220 / 311 |
| 16 | 46 / 105 | 220 / 318 | 640 / **1,000** |
| 32 | 100 / 211 | 679 / 637 | **1,000 / 1,000** |

1 Pgas worst case needs roughly **16 H200 at 60 %** or **32 H200 at ~40–45 %**. At 32 GPUs the
V3-PERF-DESIGN shared-transcript design is better still: it fits in HBM there, with 1.78 s
after execution at 35 %.

## 2. Binding constraints

1. **Compute throughput, i.e. GPU-seconds. This binds first.**
   * Worst-case 1 Pgas is 2.6–2.9e14 INT32 ops of base proving.
   * That is 44–51 GPU-s at `eff` 0.35, against ≈ 33 GPU-s available in the window
     (execution plus 3 s on 8 GPUs, with streaming).
   * Raising `eff` to the plausible ceiling of 0.6 still leaves aggregation plus base over
     budget.
   * Wasm operators set this. The unaligned `i32.load` chain is 32 main cells and 19
     fractions per op (M), and no gas-priced host primitive is more than 1.05x it per gas
     (WORKLOAD.md §4).
2. **HBM capacity, which forces segmentation, which makes recursion expensive.**
   * The single shared-transcript proof of V3-PERF-DESIGN (P-PERF-4) needs 589 GB per GPU on
     8 GPUs. It does not fit in 141 GB.
   * Streaming segment proofs are therefore forced: 2^23–2^24 rows, 64–75 GB per GPU with two
     in flight.
   * Each segment must then be verified in-circuit. A rate-1/2 child at proven bounds needs
     **610 queries** and **≈ 33 k in-circuit SHA-384 compressions**, ≈ 29 k cells each (MR
     node geometry).
   * Aggregation is therefore **0.9–1.4x the base work** (38–73 GPU-s). HBM is the
     second-largest sensitivity of (b): 80 → 282 GB moves latency 14.8 → 8.0 s.
3. **Proof size at the ZK wrap.**
   * HVZK-WHIR's additive mask oracles cost +72.6 KB at 100-bit (M). No cheaper ZK route is
     measured.
   * The capacity conjecture would roughly halve queries and bytes, but is excluded by U-6.
4. **Verifier implementation**, not the protocol.
   * The protocol needs ≈ 6 ms.
   * The shipped verifier measures 1.46 s and has no time profile (`VERIFY-PROFILE.md`).
5. **Recursion depth and final wrap are not binding** if aggregation uses fan-in 8 at rate 1/4:
   * 2–3 levels;
   * last level 0.2–0.5 s;
   * wrap 0.5–0.9 s split over the node's 8 GPUs;
   * critical path 6.7–8.0 s at 1 Pgas, but **< 1 s** at mainnet sizes.

   A deep binary tree is binding (§4).

## 3. The three cost models (`model.py`)

Shared across all three:
* **Workload** — `adversarial()` takes the gas-free witness/code work (64 MiB witness hashed
  and parsed, 64 MiB of distinct code), then spends the remaining gas on the highest ops/gas
  unit.
* **Timeline** — `evaluate()`:
  1. segments of 2^k rows are proved as execution produces them (streaming, 90 % utilisation
     during the 1.2 s run);
  2. a fan-in tree aggregates them;
  3. one ZK wrap closes it.

  Latency after the last receipt is max(critical path, backlog + last level + wrap). The
  critical path is the last segment, then one node per level, then the wrap.
* **Recursion node cost** — in-circuit hash invocations to verify a child, anchored on the
  measured production node (4,956 SHA-384 compressions per child at 143 queries, lb 6, MR) and
  scaled by query count and tree depth.

Per architecture:

* **(a) univariate AIR + FRI/WHIR**, BabyBear degree-10 extension, committed logUp (k = 2),
  constraint degree 3, two quotient chunks.
  * Per committed cell at rate 1/2, 2^24 rows: ≈ 793 INT32 ops, of which:
    * iDFT + coset NTT: 370;
    * SHA-384 Merkle: 205;
    * DEEP and constraint evaluation: the rest.
  * Per fraction: 4,410 ops.
  * Worst case: 3.65e11 committed cells (main + aux + quotient). The commitment share is 69 %
    and streams during execution.
  * Best design: 2^24-row segments (137 of them), base rate 1/2, nodes at rate 1/4 fan-in 8,
    depth 3. Node times 3.75 / 1.55 / 0.16 s; wrap 0.88 s.
  * With FRI instead of WHIR (`pcs_a=fri`), in-circuit hashing and wrap bytes about double
    (V3-D3A-STUDY §11.4: 0.71–0.88 MB). FRI cannot meet the size cap.
* **(b) multilinear**: zerocheck sumcheck + LogUp-GKR + stacked WHIR, BabyBear degree 8. This
  is the main PQ stack's shape.
  * Only main cells are committed: 6.25e10 in the worst case, versus 3.65e11 in (a).
  * Per cell ≈ 947 ops, including zerocheck and WHIR folding.
  * Per GKR fraction ≈ 8,400 ops. Fractions dominate: the commitment is only 13 % of the work,
    so less work streams.
  * Best design: 2^23-row segments (47), rate 1/2, fan-in 8 at rate 1/4, depth 2. Node times
    6.06 / 0.51 s; wrap 0.52 s.
  * Lowest total of the three: 85 GPU-s.
* **(c) binary field**, Binius64-style, using the repo's Wasm AIR design measured at **1,452
  AND/step** (MR, NPMWASM02), worst op x1.5 (A).
  * Per AND constraint: 1.79 committed 64-bit words (MR) at ≈ 1,090 ops of additive NTT plus
    SHA-384, and **29 GF(2^128)-multiply equivalents of PIOP work**. The 29 is calibrated from
    the measured LaBinius prover stages (0.53 µs per AND on one Zen 5 core, MR) divided by a
    measured 18.2 ns GF(2^128) multiply (M).
  * At 300 INT32 ops per GF(2^128) multiply on a GPU without carry-less multiply (A; range
    60–1,200), that is ≈ 9,800 ops per AND, so **≈ 21 M ops per Wasm step versus ≈ 0.2 M in
    (a)/(b)**.
  * Binary wins only where the work is hashing. In-circuit SHA-512 is ≈ 900 AND versus ≈ 29 k
    cells, which is why (c) has the best mainnet-p99 latency (0.38 s): realistic chunks are
    trie-hashing-dominated.

**Final ZK wrap (all architectures).**
* One layer proves knowledge of a valid root proof. It is made zero-knowledge with HVZK-WHIR:
  masked sumchecks, a zero-evader pad on OOD answers, a randomness budget in the encodings, and
  masked final messages (eprint 2026/391, Plonky3 `p3_whir::pcs::zk`).
* Inner layers need not be ZK: they are witnesses of the wrap and never published.
* Public inputs are exactly the chunk-header outputs plus the claim's trusted facts. No segment
  boundary state leaves the tree.
* Prover cost ×1.5 (M: 1.28–1.72x). Bytes +92.9 KB (D from M).
* Rate 1/64 (lb 6, MR): 85 proven-bound queries per round; the capacity conjecture would give
  ≈ 41. The size and queries rows above use proven bounds.

**Streaming segment size.**
* 2^23–2^24 rows x 160 cells is the largest that keeps two segments per GPU under 90 % of HBM.
* The last segment costs 0.37–0.94 s on one GPU after the last receipt.
* Smaller segments cut that latency but multiply the in-circuit verification work. The grid
  search balances the two.

## 4. Sensitivity (top entries; full lists in `model-output.txt`)

Design knobs are re-optimised at every point.

| rank | (a) 1 Pgas latency, base 16.0 s | (b) 1 Pgas latency, base 10.6 s |
|---|---|---|
| 1 | **`eff`** 0.2 / 0.6: 28.8 / 8.9 s | **`eff`** 0.2 / 0.6: 19.2 / 5.7 s |
| 2 | **`bfly_ops`** (NTT cost) 7 / 14: 13.7 / 19.1 s | **`hbm_gb`** 80 / 282: 14.8 / 8.0 s |
| 3 | **hash** SHA-384 / hybrid: 16.0 / 20.6 s; **`hbm_gb`** 80 / 282: 16.0 / 11.8 s | **`bfly_ops`** 7 / 14: 7.9 / 11.2 s |
| next | `E_a` 8 / 12; `rec_field_overhead`; `sha512_ops`; `proven` (1.75 s) | `rec_field_overhead`; `rec_cells_per_comp` 15 k / 45 k: 9.3 / 12.0 s |

For (c) the top sensitivity is `gf128_ops`: 60 / 1,200 gives 169 / 2,123 s. Even the optimistic
end is 56x over budget.

**Top three for the decision:**
1. **sustained GPU efficiency;**
2. **HBM per GPU**, through segment size and therefore recursion overhead;
3. **NTT kernel cost**, the largest kernel term. The CPU check shows the model's butterfly
   count is light.

The extension degree, grinding, the witness size and the 64 MiB code cap each move the answer
by < 1.2x.

**Poseidon2 (needs an owner decision; would replace U-7).**
* Poseidon2 everywhere: (b) goes 10.6 → 9.8 s and (a) 16.0 → 16.8 s.
* Hybrid (SHA-384 base, Poseidon2 recursion): (a) 20.6 s, (b) 11.8 s.
* Proof 393 → 337 KB.
* So **Poseidon2 does not rescue latency on GPUs**. Natively, SHA-512 is ~7x cheaper per byte
  on a GPU than Poseidon2-BabyBear (C/D, HARDWARE.md), so the commitment cost rises by about
  what recursion saves.
* **Hybrid buys nothing**: the first aggregation level must still verify SHA-384 base paths.

## 5. What changes against `docs/zk-formal/V3-PERF-DESIGN.md`

That design targeted 4 x 8 = 32 H200, ≤ 2 s after execution, no ZK. It found 1.75 s at 35 %
efficiency with P-PERF-1..5 adopted. The P-PERF-1..5 chip costs (M) are reused here unchanged.
At the new constraint (8 H200, 3 s, ZK):

* **4x less compute, only 1.5x more time.** The same design at 8 GPUs gives 7.85 s after
  execution and needs `eff` ≥ 0.75 (`--prior`).
* **P-PERF-4 (one shared-transcript proof) no longer fits HBM**: 589 GB per GPU. This is the
  structural change. The design must become streaming segment proofs plus aggregation, which
  is exactly the tree overhead P-PERF-4 was introduced to avoid. That overhead is now
  0.9–1.4x base.
* **The worst case shifts.** The 64 MiB code-response cap bounds distinct code (V3-PERF-DESIGN
  assumed 0.88 GB). Code loading drops from the worst case to a 7 % add-on. The binding unit
  is the Wasm load chain again, plus the measured RIPEMD AIR, which needs re-layout.
* **ZK is new.** It costs +93 KB, ×1.5 wrap prover time, and nothing in the inner layers.
* **Proof target.** V3-PERF-DESIGN's 0.84 MB FRI final layer is replaced by the WHIR wrap
  (MR 299,967 B). It would be ≈ 393 KB with ZK; the cap is 300 KB.
* What carries over unchanged: register-form Wasm chips, logUp buses, rate 1/2 at the base,
  constraint degree ≤ 3, early PREP of known code, and SHA-384 throughout.

## 6. Implications

**For the main PQ stack** (architecture b):
* The measured production node is 254.1 M cells and 87.1 M interactions, verifying 2 children
  with 8,747 compressions (MR).
* On one H200 at 35 % it would take **0.81 s** at rate 1/64, against 700–904 s measured on
  this CPU. At rate 1/16 it takes 0.30 s.
* A **depth-8 binary tree is therefore 6.7 s of critical path** and cannot meet 3 s.
* Use fan-in ≥ 8, rate 1/4–1/16 nodes and ≤ 3 levels. Keep lb 6 for the wrap only.
* The recursion verifier circuit is ~29 k cells per SHA-384 compression and must shrink:
  * the 18.3 % compression cut already identified (HANDOVER);
  * multi-child sharing of the top Merkle levels;
  * or accumulation (Arc/WARP), which has no QROM proof.
* Separately, **the size gap is now ≈ 93 KB, not 16 KB**, once ZK is required.
* The levers in hand are 26–27-B weak-binding digests (undecided) and a 1-child 2^20 wrap
  schedule (untested). Poseidon2 digests would give −56 KB with an owner decision. None closes
  93 KB alone.

**For the Wasm AIR design** (`tail-architecture/WASM_LADDER.md`):
* **Its semantics are reusable; its backend is not.**
  * 1,452 AND/step on a binary/lattice backend is ≈ 21 M GPU INT32 ops per step without
    carry-less multiply, about 100x the 31-bit Wasm chips' cost (≈ 0.2 M).
  * The running-bank memory (memory steps at ALU cost, measured) and the register-form operand
    channels should be ported to the 31-bit chips (P-PERF-1/5).
* A binary-field backend is worth keeping **only for hash-dominated sub-proofs**: witness/trie
  authentication, receipt hashing, Keccak/RIPEMD hosts. There it is ≈ 7–13x cheaper per
  compression.
* A mixed design would need a cross-field wrap, which nobody has costed.

## 7. Experiments that validate the model cheaply on this CPU host

| # | experiment | what it pins | cost | status |
|---|---|---|---|---|
| 1 | single-core Poseidon2, NTT, SHA-2/3, GF(2^k) and HVZK-WHIR microbenchmarks (`bench/run_benches.sh`) | op counts vs CPU lane peak; native Poseidon2 vs SHA-512 per byte; ZK bytes (+72.6 KB additive); binary-mult penalty (94x) | 25 min | **done** (`bench/RESULTS.md`) |
| 2 | fix the 128-bit octic HVZK-WHIR config (the `unwrap` at `zk_overhead.rs:88`) and rerun with a SHA-384 MMCS | ZK bytes at the real security level and digest width (model assumes 92.9 KB) | 1–2 h | open |
| 3 | `perf record` on the 299,967 B verifier (1 thread) | whether the 7.65 s is setup/vk rebuild or protocol. The model says the protocol needs ≈ 6 ms | 30 min | open |
| 4 | prove one L1 node over a rate-1/2 production child on CPU (main stack, 1 child) | comps/query scaling at lb 1 (model: 32.9 k comps per child, from the lb 6 anchor) | ~1 h CPU | open |
| 5 | Plonky3 `uni-stark` with a SHA-384 MMCS on the spike-4 load-chain AIR, 2^20 rows, 1 thread | measured ns per committed cell vs model ops (calibrates `eff` transfer for arch a) | 2–3 h | open |
| 6 | first H200 hour: hashcat `-m 1700`; a BabyBear 2^24 x 256 NTT; a SHA-384 Merkle build; one segment proof | `eff` per kernel, the dominant sensitivity | 1 GPU-hour | needs hardware |

## 8. Caveats

* Op counts for the GPU are a model. `eff` is the single knob that absorbs everything the
  model omits (memory stalls, launch overhead, imperfect fusion). It is not a measurement.
* Curve/pairing and ML-DSA circuit costs are sketches (±2x). None is within 10x of binding.
* Arch (c)'s PIOP calibration comes from a lattice-backend prover's PIOP stages (LaBinius). A
  hash-based Binius64 prover has a different commitment, but the same PIOP.
* Size is anchored on one measured packet (D0a, opt-baseline-8, `program_part = false`). A
  1 Pgas root's wrap verifies a different child, and per the depth law that adds +0–22 KB.
