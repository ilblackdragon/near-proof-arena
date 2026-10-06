# R1 cost model: one np-udr-stark proof, many segment tables, global buses

Status: research, recursion track checkpoint 1 (`docs/requirements/RECURSION_REQUIREMENTS.md` §6.1:
"R1 cost model calibrated on the existing prover"). Lane `lane/v3-d3`, 2026-10-06.
Tools: `tools/recursion/` (`r1calib` Rust crate linking the `np-udr-stark-fast2` prover and verifier
library, `r1_model.py`, `calib.sh`, `lean_time.sh`). Raw results: `tools/recursion/results/`.

**Labels used below.** **[M]** = measured on this host (Ryzen 9 9950X3D, CCD1 CPUs 8-15, 8 rayon
threads, shared host at load average about 20). **[X]** = exact (byte-for-byte reconstruction of a real
proof). **[F]** = fitted from [M] data and used inside the measured range. **[E]** = extrapolated or
estimated outside the measured range. **[A]** = assumption, stated explicitly.

## 0. Summary

* **Proof size is exactly predictable [X].** The format is fixed by FORMATS.md §5. Given the per-table
  shapes and the query positions, `r1calib breakdown` rebuilds every byte of real proofs: 0 bytes of
  difference on the NEAR max-case proof (3,561,135 B) and on the NEAR fixtures. The closed-form
  expectation over random positions (`r1_model.py`) is within ±1.4% on 33 real proofs [M]: 12 NEAR,
  21 synthetic R1, 0.17% on the max case.
* **R1 is linear in S, and the slope is large.** Every segment table is opened at all 216 query
  positions. Merkle paths, FRI and roots are shared, because the protocol already puts every table in
  one MMCS tree per round. Rows, OOD values and bus finals are not shared. For one segment:
  `Δbytes ≈ 216·(4·w + 32·a + 32·q) + 32·(2w + 2a + q) + 32·f`. The fixed part is about 2.0 MB.
  * Measured slope [M]: 280 KB per segment for the 198-column synthetic segment. It is identical at
    heights 2^12, 2^20 and 2^22.
  * D3 presets [A]: 442 KB (d3-lean, 494 committed base-column equivalents), 785 KB (d3-rich), and
    908 KB (NEAR-AIR density).
* **Caps, for the d3-lean preset (4,194,304 WASM operators = 3.45 Tgas per segment):**

  | cap | binding S | WASM gas | status |
  |---|---|---|---|
  | 8 MiB proof | **14** | **48 Tgas** | size [X], gas per segment [A] |
  | 64 MiB proof (the D0-1 draft cap) | 147 | 507 Tgas | as above |
  | 10 s verify (deployed Lean verifier, 1 core) | 54 | – | [F]/[E] |
  | `Air.wf` bus budget 2^36 (existing verifier rejects beyond it) | ≈50 | – | [A] message length 12 |
  | **600 s prove (8 vCPU)** | **≈3 (1–3)** | ~10 Tgas | [E] from [M] 231 s and 381 s single-segment proofs |
  | 16 GiB RAM, current non-streaming prover | 1 | – | [M]: 11.3 GB for one 2^22 segment |

  * 10^15 gas needs **S = 290**: 124 MiB (d3-lean) to 253 MiB (NEAR density), about 50–92 s Lean
    verify, and 15–60 core-hours ×8 of proving.
  * S = 1000 (1 Tgas segments, as in the requirements' 10^3 upper end): 424–868 MiB.
* **Cost board.** Board: BENCHMARK_SPEC §14; price model: the draft `pm-near-mainnet-2026q4`.
  * R1's marginal cost per segment is 1.5·10^13 fUSD (d3-lean): **75% prove, 20% bandwidth, 5–6%
    verify**.
  * That is **26×** the cost of re-executing the same 3.45 Tgas in the Lean reference verifier
    (5.9·10^11 fUSD).
  * Break-even (score 100) needs a reference whose witness is at least `W*(S)`. W* is 4.6 MiB at S = 1,
    19 MiB at S = 8, and already above nearcore's 64 MiB uncompressed witness limit at S ≈ 30.
    **At mainnet scale R1 cannot break even against re-execution: W*(290) ≈ 600 MiB.**
* **Soundness.** R1 is admissible with the existing protocol and proofs (`stark_romSound_full` is
  stated for any AIR with `NpOk`; multi-table MMCS is already proved). There is one hidden limit:
  `Air.wf` caps the total bus traffic at `busBudget = 2^36` (Air/Basic.lean:216), which binds at
  S ≈ 30–50. Raising it to 2^40 (S ≈ 500–800) is a constant change with slack in `Params`, but it must
  be re-checked (§5).
* **Verdict for the decision memo.** R1 fits **≲ 14 segments ≈ 50 Tgas under 8 MiB**, which is about
  15–50× the single-proof `G_α`. Its **binding constraint is prove time (600 s), not size**. R1 cannot
  reach 10^15 gas under any proposed cap, and it never wins on the cost board. The levers (§6) change
  the constants by at most about 3–4×, not the linear shape.

## 1. Inputs: caps and the cost board

* **Resource caps** (`challenges/chl_17ac2f30…json` `resource_limits`, v1-5; the same values are quoted
  as the D3 placeholder in `D3_WASM_REQUIREMENTS.md` §2.4):
  * proof ≤ 8,388,608 B;
  * verify ≤ 10,000 ms;
  * prove ≤ 600,000 ms;
  * RAM ≤ 16 GiB;
  * 8 vCPUs (`hardware_profile`).

  The chunk-level draft `challenges/drafts/near-chunk-validation-d0-1.draft.json` already uses
  `max_proof_bytes = 67,108,864` (64 MiB), so both 8 MiB and 64 MiB are reported. The prover also
  hard-codes `MAX_PROOF_BYTES = 8 << 20` (`protocol.rs:48`). The verifier rejects before parsing:
  measured, 9.6 MB and 18.6 MB synthetic proofs are rejected in 15–19 ms.
* **Cost board** (`docs/BENCHMARK_SPEC.md` §14.2–14.3):
  `C = c_cpu·v_p·T_prove + N_v·(c_cpu·v_v·T_verify + (c_bw + c_store)·proof_bytes)`, with
  `score = 100·exp(Σ_j w_j·ln(C_base,j/C_cand,j))`. The price model is
  `challenges/price-models/pm-near-mainnet-2026q4.draft.json`:
  * `N_v = 84`, `v_p = v_v = 8`;
  * `c_cpu = 7.61·10^9 fUSD/vCPU-s`, `c_bw = 82,000 fUSD/B`, `c_store = 0`.

  So 1 s of verify costs the same as 742 KB of proof, and 1 s of prove costs the same as 8.8 KB of proof.
* **Break-even (definition).** For a workload class, R1 breaks even when its class score is 100, i.e.
  `C_R1 = C_ref` (§14.2, with a single class). The reference for D3 is re-execution (witness as proof,
  §14.9 "the baseline to beat"):
  * `T_prove ≈ 0`;
  * `proof_bytes = W` (the state witness: code, touched state and the storage proof);
  * `T_verify = G / R`. Here R = 30 Tgas/s, the Lean W3 interpreter speed of the PoC, from
    `near-wasm-strategy.md` §5 ("a 300 Tgas loop in about 10 s") [A].

  Because W does not depend on how much WASM runs, we report **`W*(S)`, the reference witness size at
  which R1 breaks even**:
  `W* = (C_R1(S) − N_v·c_cpu·v_v·G/R) / (N_v·c_bw)`. A larger real witness means R1 wins.
* **Gas → S.** Chunk limit 10^15 gas. `regular_op_cost = 822,756` gas/op, so there are 1.2154·10^6
  ops per Tgas (`RECURSION_REQUIREMENTS.md` §0). A busy real chunk is "maybe 10^7–2·10^8 WASM
  instructions" (`docs/research/checker-recommendations.md` §5.2, an estimate, not a measurement), which
  is 8–165 Tgas of ops. Segment capacity is **2^22 operators per segment** [A], which is 3.45 Tgas.
  This is the top of the "1–3 Tgas per proof" range in `near-wasm-strategy.md` §2.2. It assumes EXEC
  takes 1 row per operator and the 3 sorted-RAM rows per operator go to three 2^22 tables. With 1 Tgas
  segments S is 3.45× larger.

## 2. Proof-size model (np-udr-stark-v1)

Notation per table t:
* `h_t` = log height;
* `w_t` = base columns;
* `a_t` = aux columns (K-valued);
* `q_t` = quotient chunks (K-valued);
* `f_t` = bus finals.

Global quantities:
* `l0 = max h_t + 4`;
* `Q = 216` query positions (duplicates kept).

| constant | value | source |
|---|---|---|
| rate | 1/16 (`LOG_BLOWUP = 4`) | `protocol.rs:44`; DESIGN §8; `Params.lean` (`n = 2^26`, `D = 2^22`) |
| queries Q | 24 chunks × 9 = 216 | `protocol.rs:45-46`; FORMATS §4; `Params.udr2_ok` (207 fail) |
| digest | 64 B (wide hash WH = two SHA-256) | DESIGN R1; FORMATS §2 |
| base / K element | 4 B / 32 B | FORMATS §2 |
| table height | ≤ 2^22, LDE ≤ 2^26 | `protocol.rs:49`; `Table.wf` maxLog ≤ 22 (Air/Basic.lean:199) |
| FRI | binary folds, commitments of arity ≤ 8, final layer 2^5 points, final poly 2 K | `protocol.rs:47,105`; FORMATS §3 |
| aux width | `a_t = Σ_{i: k_i≥2} 2(k_i−1) + #send groups + #recv groups` (auxGroup = 1) | `aux.rs:17,39-66`; FORMATS §3 |
| quotient chunks | `q_t = d_t − 1` (d_t = max(2, constraint degrees, aux degree)) | `air.rs:99`; `aux.rs:85-109` |
| finals | `f_t = #groups` | `aux.rs:67` |
| MMCS | **one** tree per round over **all** tables; a table of LDE log m is injected at level `l0 − m` | FORMATS §5 "MMCS"; `protocol.rs:221` |

**Exact bytes** (`Proof::to_bytes`, `protocol.rs:250`; `mmcs::write_opening`, `mmcs.rs:315`):

```
bytes = 8 + T                                   header (u32 version, u32 numTables, u8 h_t)
      + 3·64 + 64                               root_main/aux/quot, final poly
      + 32·Σ f_t                                bus finals
      + 32·Σ (2w_t + 2a_t + q_t)                OOD values (at z and ωz; quotient at z)
      + 64·C                                    FRI roots (C committed layers)
      + Σ_{tree ∈ main,aux,quot} [ Σ_k U_k·R_k(tree) + 64·Σ_{k≥1} N_k ]       multiproofs
      + Σ_{FRI layer (c,a)} [ Σ_k U_k·32·2^a·[k=0] + 64·Σ_{k≥1} N_k ]
```

In this formula:
* `R_k(main) = 4·Σ_{t: l0−h_t−4=k} w_t`, `R_k(aux) = 32·Σ a_t`, `R_k(quot) = 32·Σ q_t`;
* `U_k` = number of distinct indices at level k;
* `N_k` = number of level-k parents with exactly one known child (each contributes one sibling
  digest).

For uniform positions on `2^L` leaves:
* `E[U_k] = 2^{L−k}·(1 − (1 − 2^{−(L−k)})^Q)`;
* `E[N_k] = 2^{L−k}·2·[(1 − 2^{−(L−k+1)})^Q − (1 − 2^{1−(L−k+1)})^Q]`.

**R1 simplification.** If `2^{l0} ≫ Q`, every table is opened at about 216 distinct rows,
*independent of its height*. A segment table therefore adds

```
Δbytes(t) ≈ 216·(4·w_t + 32·a_t + 32·q_t)  +  32·(2w_t + 2a_t + q_t)  +  32·f_t  + 1
```

* The Merkle siblings (≈ 3,750 × 64 B ≈ 240 KB per tree of depth 26), the FRI layers (≈ 1.26 MB) and
  the roots are paid **once per proof**. This is the amortisation the existing protocol already gives.
* K-valued aux and quotient columns cost **8×** a base column per query (32 B vs 4 B).
* The Lean side (`ZkFormal.Stark.Bcs` MMCS and the multiproof extraction `Bcs/Multiproof.lean`,
  `multiproof_sound`) handles any number of tables of any heights in one tree. **Batching all segments'
  columns into one commitment per round is already the protocol, not a lever.**

Max-case breakdown [X] (`results/breakdown-near-maxcase.txt`):

| component | bytes | % |
|---|---|---|
| main / aux / quot rows | 924,480 / 456,192 / 145,152 | 43% |
| main+aux+quot siblings | 3 × 239,424 | 20% |
| FRI rows + siblings (10 layers) | 287,488 + 966,592 | 35% |
| OOD + finals + roots + header | 73,376 + 2,112 + 832 + 15 | 2% |

## 3. Calibration (model vs measured)

### 3.1 Proof bytes

Sources: `r1_model.py check` (`results/check.txt`) and `r1calib breakdown` (`results/breakdown-*.txt`).

| proof | heights | model (expectation) | measured file | error |
|---|---|---|---|---|
| NEAR max case (gen-max), the real AIR | 22,22,16,17,12,14,13 | 3,567,273 | 3,561,135 | +0.17% |
| NEAR fixtures (11 proofs, judge-verify set) | 2^5–2^16 | – | 1.96–2.62 MB | −1.22% … +0.85% |
| R1 synthetic, 198 cols/segment, h = 12, S = 1/2/4/8/16/32/64 | 12 | 0.84 … 18.52 MB | 0.84 … 18.56 MB | −0.38% … +0.55% |
| same, h = 20, S = 1/2/4 | 20 | 1.69/1.97/2.53 MB | 1.69/1.97/2.53 MB | ≤ 0.35% |
| same, h = 22, S = 1 | 22 | 1,940,123 | 1,927,853 | +0.64% |
| single table, w = 50/450/1350 (h = 12); w = 150 at h = 8/16/18/20 | | | | ≤ 1.4% |

With the transcript's actual query positions the reconstruction is exact: max case 0 B difference; fixture
`example-tierA` 0 B difference. The residual of the expectation is only the randomness of the positions.

Measured per-segment slope [M]:
* (5,048,041 − 2,807,401)/8 = 280,080 B at h = 12;
* (2,532,153 − 1,971,057)/2 = 280,548 B at h = 20.

The model gives 281,092 B. **The slope does not depend on segment height**, as §2 predicts.

### 3.2 Verify time (deployed Lean verifier model)

Measured with `np-lean-verify`: the deployed `(verifier Fp Fp8 A default).toVerifier.deployed`, with the
fast-SHA `@[csimp]`. It ran on 1 core (CPU 9), min of 3 runs, on 23 proofs (`results/lean-verify.tsv`).
On the NEAR max case it takes the same time as the judge-built NEAR `out/verify` (1.65–1.68 s on a loaded
core; 1.30 s in the min-of-3 run; STATUS-L8 reports 1.0 s on a quieter host).

Least-squares fit [F] (`results/fit.txt`):
`t_ms = −112 + 444.6·MB(proof) − 0.059·OOD`. Max residual 44 ms over 0.27–1.77 s.
* **Verify time is ≈ 0.44 s per MB of proof**: hashing plus parsing the List-based proof bytes.
* Column count has no independent effect.
* A `ntables × OOD` term (the verifier's `List.drop`/`getD` per table per query,
  `ZkFormal/Stark/Verifier.lean:210-246`) fits at 0.155 ms per 10^3 table·OOD. It is invisible below
  5 MB, but at S = 1000 it would add up to 280–700 s.
* Both columns are reported. The quadratic one is [E] and is removed by an Array refactor of the verifier
  (implementation only, no soundness change).
* The Rust reference verifier is 30–80× faster: 79 ms on the max case.

### 3.3 Prove time and memory

All measured with the fast2 lowmem prover, AVX2, 8 threads on CPUs 8-15, with `/usr/bin/time` RSS:

| instance | W_eq (= w + 8a + 8q) | prove | peak RSS |
|---|---|---|---|
| NEAR max case, 2^22 (`examples/np-udr-stark-fast2/bench/results/maxcase-avx2-uncontended-2026-10-06.log`) | 995 + small tables | **381 s** | 9.1 GB (11.3 GB in STATUS-L8 runs) |
| R1 toy, 1 segment of 198 cols, **2^22** | 310 | **231 s** | 11.3 GB |
| R1 toy, S = 1/2/4 at 2^20 | 310/seg | 60.7 / 106.5 / 195.0 s | 4.6 / 5.8 / 8.1 GB |
| R1 toy, S = 1…16 at 2^12 | 310/seg | 0.6 … 4.2 s | ≤ 0.14 GB |
| single 150-col table, 2^16/2^18/2^20 | 166 | 3.1 / 11.1 / 41.1 s | |

* Prove time is linear in S: 44.8 s per segment at 2^20, ≈ 4.3× that at 2^22. At 2^22 the cost is
  **0.38 s (NEAR AIR) – 0.75 s (cube toy) per committed base-column equivalent** [F].
* The NEAR anchor is used as central, the toy as the upper bound.
* The current prover holds every table's compact trace. Its RSS grows ≈ 1.2 GB per 2^20 segment
  (≈ 4.7 GB per 2^22 segment), on top of a memory budget it fills anyway (`NPUDR_MEM_GB`, default 11).

## 4. The R1 model

### 4.1 Instance [A]

* **S segments.** Each segment is 2^22 WASM operators and contains these tables, all at height 2^22,
  degree 4 (q = 3) and 1-bit multiplicities, like `nearAir`:
  * **d3-lean:**
    * EXEC: w = 150, 10 interactions (3 RAM, CODE, 4 ALU/range, 2 boundary);
    * three sorted-RAM tables: w = 16, 5 interactions each (permutation receive, 2 range, 2 chain links).

    W_eq = 494, OOD terms 458.
  * **d3-rich:** EXEC w = 300 with 16 interactions; RAM tables w = 24 with 6 interactions; plus an ALU
    limb chip w = 60 with 6 interactions. W_eq = 872.
  * **near-density:** the max case's two 2^22 tables (w = 544 + 163) as the per-segment set: the density
    of an AIR we have actually built. W_eq = 995.
* **Global tables, once per proof:** CODE (2^20 × 24), byte/range providers (2^17, 2^16), io/boundary.
  Lookups are global buses in R1, so providers are not duplicated per segment.
* **Global buses.**
  * The boundary state (pc, frames, gas, budget …) goes from segment s to s+1 as one send/receive
    pair on a global bus. This is the synthetic `seg` instance: 2 interactions on EXEC.
  * RAM is one *global* sorted log cut into 2^22-row tables, with chain links between consecutive
    tables, so there is no per-segment memory image.
  * Only finals and per-table aux columns grow with S. The bus check is `∏ send finals = ∏ receive
    finals` over all tables (FORMATS §3).

### 4.2 What grows and what amortises

| term | growth in S | note |
|---|---|---|
| opened rows: 216·(4w + 32a + 32q) per table | **linear** | 85–95% of Δbytes |
| OOD values 32·(2w + 2a + q), finals 32·f, header 1 B per table | linear | 4–5% |
| Merkle siblings (main/aux/quot), FRI layers, roots, final poly | **constant** (≈ 2.0 MB) | one tree per round, shared positions |
| verify: proof hashing/parsing | linear (0.44 s/MB) | [F] |
| verify: per-table List walks | quadratic (deployed List code) | removable [E] |
| verify: ALI at z, final bus product | linear, small | |
| prove: LDE/commit/quotient/DEEP per segment | linear | FRI (one 2^26 batched codeword) is amortised |
| peak memory, streaming two-pass prover | ≈ constant | [E] see 4.4 |

### 4.3 S-curves

Sources: `r1_model.py curves` and `results/curves.txt`. Bytes are [X-model] (formula, ±1.4%), verify
[F→E], prove [F→E], RSS of the current prover [E].

**d3-lean** (`bytes = 1,995,991 + 442,275·S`):

| S | WASM gas | proof | Lean verify (linear fit) | Lean verify (+List term) | prove (8 vCPU) | RSS, current prover |
|---|---|---|---|---|---|---|
| 1 | 3.45 Tgas | **2.33 MiB** | 0.93 s | 0.94 s | 3.1–6.1 min | 11 GB (M: 11.3) |
| 8 | 28 Tgas | **5.28 MiB** | 2.1 s | 2.1 s | 0.42–0.82 h | 64 GB |
| 64 | 221 Tgas | 28.9 MiB | 11.6 s | 12.5 s | 3.4–6.6 h | 485 GB |
| 290 (10^15 gas) | 1,000 Tgas | 124 MiB | 50 s | 72 s | 15–30 h | 2.2 TB |
| 512 | 1,767 Tgas | 218 MiB | 88 s | 160 s | 27–52 h | 3.9 TB |
| 1000 | 3,451 Tgas | 424 MiB | 170 s | 450 s | 53–102 h | 7.5 TB |

**d3-rich** (`1.996 MB + 785 KB·S`) and **near-density** (`1.996 MB + 908 KB·S`):

| S | d3-rich proof / verify / prove | near-density proof / verify / prove |
|---|---|---|
| 1 | 2.65 MiB / 1.1 s / 6–11 min | 2.77 MiB / 1.1 s / 6.5–12 min |
| 8 | 7.90 MiB / 3.1 s / 0.75–1.5 h | 8.83 MiB (over the cap) / 3.3 s / 0.85–1.7 h |
| 64 | 49.8 MiB / 19 s / 6–12 h | 57.3 MiB / 21 s / 7–13 h |
| 512 | 385 MiB / 150 s / 48–92 h | 445 MiB / 163 s / 54–105 h |
| 1000 | 751 MiB / 293 s / 93–180 h | 868 MiB / 317 s / 106–206 h |

What is measured at the S-points [M], against the corresponding model rows:
* proof bytes at S = 1/8/64 (h = 12, 198-col segment) and at S = 1 (h = 22);
* Lean verify at S = 1/8 (h = 12) and S = 1 (h = 22);
* prove at S = 1 (h = 22) and S = 1/2/4 (h = 20).

Everything else is model.

### 4.4 Peak memory: the streaming two-pass prover [E]

The requirements assume "peak ≈ one segment". The existing protocol allows it, but the leaf hash of
row j concatenates **all** tables' rows j. A segment-streaming prover therefore has to keep the
following:

* **Per-leaf SHA-256 states for the tree being built.** That is 2 × 32 B × 2^26 = 4 GiB, provided each
  segment's row bytes are padded to a multiple of 64 B, so no partial block is carried. The current
  prover already streams column chunks into per-leaf states over groups of positions
  (`lmcommit.rs`); R1 would iterate segments inside a group or keep all 2^26 states.
* **The DEEP accumulator** over the 2^26-point FRI domain: 2 GiB.
* **One segment's working set:** 9–11 GB measured with the default budget; the budget can be lowered.

The total is ≈ 15–17 GB, at the 16 GiB cap. Each phase re-executes every segment, for 5–6 passes:
* main commit;
* aux, after `α_fp`, `γ`;
* quotient, after `α_c`;
* OOD, after `z` (from H values);
* DEEP;
* openings, which need rows at about 216 × 2^KEEP positions for the recomputed low Merkle levels.

Re-execution itself is cheap next to the LDE work, so prove(S) ≈ S × (single-segment prove).

There is one more cost: the global sorted RAM needs an external sort of the whole access log, about
3.6·10^9 × ~16 B ≈ 58 GB on disk at 10^15 gas.

## 5. Soundness side conditions (existing L2/L3 proofs)

* `ZkFormal/Assembly/RomFull.lean:27` `stark_romSound_full (A : Air) …` is stated for **any** AIR with
  `NpOk A prm` (Udr/Np/Statements.lean:38: per-table constraint count ≤ 2^20, numBuses < 2^30) and
  `NVu A prm ≤ 2^30`. `NVu` depends only on `schedBound` (log of the batch size) and the fixed parameters
  (Stark/Statements.lean:49-64), so it grows only logarithmically with S.
* Multi-table, mixed-height MMCS extraction is proved (`Bcs/Multiproof.lean`, `multiproof_sound`). One
  tree per round over all tables is the deployed format. R1 is therefore "the same protocol with more
  tables", as the requirements state. New Lean work: the segmentation semantics and the boundary-bus
  balance across segments (requirements §3.1, §3.4).
* **The hidden limit.** `headerOk` (Stark/Protocol.lean:145-150) requires `A.wf`. `Air.wf` requires
  `fpBound ≤ busBudget = 2^36` and `multBound ≤ 2^36` (Air/Basic.lean:201-219), where
  `fpBound = Σ_t 2^maxLog_t·#interactions_t·(max msg len + 1)`.
  * nearAir uses 2^32.1 of that budget.
  * An R1 AIR with 2^22-row segment tables adds `2^22·I_seg·(L+1)` per segment.
  * At `I_seg` = 25 and L + 1 = 13 [A]: **S ≤ 50** (d3-lean), 31 (d3-rich), 41 (near-density). Above
    that, every proof is rejected by `headerOk`.
  * The budget enters the commit-phase term `qCommit·commitBad/2^256` with
    `commitBad = 2^36·3^8` (Params.lean:33). That term is 2^-143.3 today against a query term of
    ≈ 2^-133, so about 2^10–2^14 of slack exists.
  * busBudget = 2^40 allows S ≈ 500–800, with the commit term at ≈ 2^-139.
  * Changing it touches `busBudget`/`badBudget`/`commitBad` and requires re-running the kernel `Params`
    checks. **Not verified here.**

## 6. Dominant terms and levers

Dominant per-segment terms for d3-lean at 216 queries:
* main rows: 4 × 198 = 792 B/query;
* aux: 32 × 25 = 800 B/query;
* quotient: 32 × 12 = 384 B/query.

K-valued aux and quotient columns are 60% of the slope. In cost terms the prover is 75% of the marginal
segment cost.

| lever | effect on the linear term | needs | verdict |
|---|---|---|---|
| Batch all segments into one tree per round, share positions | already done (amortises the 2 MB) | – | no further gain |
| **Lower blowup, bigger tables** (rate 1/8 → tables 2^23, ≈ 243 queries; 1/4 → 2^24, ≈ 297; 1/2 → 2^25, ≈ 477, at the same LDE 2^26) | bytes per operator ×0.56 / ×0.34 / ×0.28 (queries ↑, segments ↓ 2/4/8×); prove per operator ↓ (fewer LDE cells per row) | new `Params` kernel checks (`n`, `D`), `Air.wf (2^logBlowup)` degree ≤ blowup (degree-4 tables need blowup ≥ 4), L3 instantiation at the new rate; DESIGN R7 2-adicity allows LDE 2^27 | **largest structural lever, ≈ 3×** |
| Higher rate (1/32, 1/64) | UDR gives ≤ 1 bit per query: 216 → ≈ 207 → ≈ 202 queries, and tables shrink 2–4× | – | **counter-productive** |
| Pack interactions (`auxGroup` > 1; a `Params` field, Stark/Protocol.lean:150) | aux 25 → 13 K-cols (−83 KB/segment) but degree 2 + 2g raises q_t (+55 KB) | Params change; NpOk currently pins `Params.default` | small (≈ 5–10%) |
| Fewer, wider tables (fold the RAM tables into EXEC rows) | −3 quotient chunk sets = −62 KB/segment (−14%) | AIR layout | modest |
| Global providers (CODE, ranges) instead of per-segment copies | avoids `+Σ` provider widths per segment (already assumed) | R1 design | assumed in presets |
| Array-based Lean verifier | removes the quadratic List term (S = 1000: 450 s → 170 s) | implementation only | needed for any S ≳ 100 |
| Faster prover (AVX-512 build 1.6× on STATUS-L8's SSE2 comparison; GPU) | prove only | engineering | needed: prove cap binds at S ≈ 1–3 |

Even with every lever, R1 is ≥ ~140 KB per 3.45 Tgas (rate 1/4, packed). At 10^15 gas that is
≥ 40 MiB plus about 30 s of verify and hours of prove. **R1 is not succinct in S, and no lever changes
that.**

## 7. Measured vs assumed

* **Measured / exact.**
  * The proof-size formula and all its constants (exact reconstruction; ±1.4% for the expectation on
    33 proofs).
  * The per-segment byte slope (280 KB at 198 columns, height-independent).
  * Lean verify ≈ 0.44 s/MB on 23 proofs up to 5 MB.
  * Single-segment prove time (231 s toy, 381 s NEAR, both at 2^22) and linear S-scaling at 2^20
    (S ≤ 4).
  * Peak RSS of the current prover.
  * The 8 MiB rejection.
* **Assumed.**
  * D3 table widths and interaction counts (presets d3-lean / d3-rich, plus the NEAR-density anchor).
  * 2^22 operators per segment.
  * Max bus message length 12.
  * Lean re-execution at 30 Tgas/s.
  * Busy-chunk gas of 8–165 Tgas (an estimate in `checker-recommendations.md` §5.2).
  * The draft price model.
* **Extrapolated.**
  * Verify beyond 5 MB (> 8 MiB is not even accepted today).
  * Prove beyond S = 4.
  * Streaming-prover memory (§4.4: designed, not built).
  * The busBudget headroom (§5).

Reproduce:

```
cd tools/recursion/r1calib && RUSTFLAGS="-C target-cpu=x86-64-v3 -C target-feature=+sha,+aes" \
  CARGO_TARGET_DIR=<scratch> taskset -c 8-15,24-31 /data/illia/nearproof-deps/bin/heavy cargo build --release --offline
R1CALIB=<bin> LV=<np-lean-verify> WORK=<scratch> tools/recursion/calib.sh <tag> "1 2 4 8 16" 12 150,16,16,16 8
tools/recursion/lean_time.sh results/lean-verify.tsv <air.json> <pub.bin> <claim.bin> <proof.bin> <label>
python3 tools/recursion/r1_model.py check | fit | curves | detail
```

`np-lean-verify` used: `/data/illia/nearproof-wt/zk-L8d-l6/examples/np-udr-stark/conformance/.lake/build/bin/np-lean-verify`.
It accepts every honest synthetic proof, and its timing on the max case equals the judge-built
`out/verify` (`c82117cb…`).
