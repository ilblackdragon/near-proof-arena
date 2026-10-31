# E2E: real D0a chunks → final PQ proof → fresh-process verification (2026-10-31)

Status: **research run, owner's relaxed targets of 2026-10-31.** `security_established=false`,
`zero_knowledge_established=false` in every RESULT.json. No GPU was used; GPU latencies are
model projections only (`../prover-budget/model.py`). No Lean spec or checker change.

## 1. Verdict against the relaxed targets

| target (2026-10-31) | result here | met? |
|---|---|---|
| real chunk, witness → final proof → fresh-process verify | 3 corpus D0a chunks (with 1–4 receipts), see §2 | **yes** (D0a scope) |
| SHA-384 throughout, proven bounds, no curves | SHA-384/42 B Merkle + T* transcript; Johnson-regime list decoding, 268-bit RBR target, z = 32; no curves | **yes**, with the A-IC recursion assumption (U-11/U-12) still unproven |
| 128-bit PQ | every component ≥ 268 RBR bits (§4) ⇒ ≤ 2^-140 at 2^64 quantum queries per CMS19 t²ε, hash 2^-144 | **parameters yes; `security_established` stays false** (HANDOVER obligations open) |
| zero knowledge, public = header outputs + trusted facts | **not implemented**; leakage inventory, construction, simulation sketch and measured HVZK-WHIR cost in `ZK-ARGUMENT.md` | **no** |
| proof ~400 KB with ZK | non-ZK packets **306,839–307,427 B**; HVZK-WHIR measured at 128-bit Johnson, rate 1/64 adds **+222 KB (2^18, z=30) to +312 KB (2^20, z=20)**; + salts ≈ 11 KB (estimate) ⇒ ≈ 540–630 KB | **no** (projected, ZK not built) |
| verify < 200 ms | **104–111 ms single core**, 105–114 ms at 16 threads (full CLI, fresh process, incl. `statepublic` and setup pin; 56 MB RSS). Same binary on the delivered v1 packet: 8.8 s / 2.4 s | **yes** |
| ≤ 3 s at ~100 Tgas, ~10 s at 1 Pgas on 8 H200 | model: 100 Tgas worst case 2.38 s (arch b), 1 Pgas worst case 10.56 s, realistic mix 0.84 / 1.89 s; this chain as run ≈ 0.66 s on 8 H200 (§5) | 100 Tgas **yes (model)**; 1 Pgas worst case **5.6 % over (model)** |

## 2. Results table

Three D0a-domain chunks from `/data/illia/nearproof-deps/corpora` (accepted by `statedump d0a`
and by the Lean reference checker `nearspec-v3-check`), each proved from witness to final packet
and verified in a fresh process. Host: shared 32-core Zen 5, 16 threads on CPUs 8-15,24-31,
`HEAVY_MEM=32G`; other tenants were active (load 17–25), so CPU times are as measured, not best case.
Chain geometry `ns19/lb6`, `NEARPROOF_TAPE_EVAL=1`, 268-bit RBR target, SHA-384/42 B.

| | d1/00-h10006-s3 | d1/00-h10007-s0 | d2/05-h10042-s3 | delivered `opt-baseline-8` (ref.) |
|---|---:|---:|---:|---:|
| receipts / witness B / public msgs / hint B | 1 / 3,100 / 671 / 16 | 4 / 3,945 / 814 / 155 | 2 / 5,114 / 1,358 / 16 | 0 / 1,532 / – / 16 |
| witness gen (`statedump`) s / peak GiB | 11.4 / 1.40 | 12.7 / 1.39 | 12.4 / 1.40 | – |
| base proof B / prove s / peak GiB | 511,990 / 340.2 / 9.0 | 513,000 / 347.2 / 8.8 | 514,820 / 472.8 / 9.0 | 459,984 / 77.9 / 1.0 |
| L1 … L_n proof B | 361,923; 358,185; 356,505; 356,337 | 363,267; 358,479; 357,429; 356,673 | 363,141; 358,101; 356,967; 357,219; 358,563 | ≈ 373 KB × 5 |
| L1 … L_n prove s | 576; 469; 515; 491 | 734; 590; 562; 434 | 516; 429; 425; 496; 526 | 462–582 |
| FINAL prove s | 494.3 | 489.6 | 465.2 | ≈ 520 |
| chain wall s (L1..FINAL) / peak GiB | 2,628.6 / 16.9 | 2,904.8 / 16.9 | 2,929.1 / 16.9 | 3,065.7 / 13.3 |
| **total CPU wall, witness → packet** | **≈ 2,980 s** | **≈ 3,265 s** | **≈ 3,414 s** (fresh base) | ≈ 3,145 s |
| **packet B** (proof + hint + base point u + framing) | **306,839** | **307,314** | **307,427** | 299,967 |
| final proof B / WHIR queries | 305,891 / [46,41,31,25] | 306,227 / same | 306,479 / same | 299,935 / [41,38,29,23] |
| **verify, fresh process, 1 thread** | **104–112 ms** | **104–137 ms** | **105–111 ms** | 8.8–9.6 s (same new binary) |
| verify, 16 threads | 105–108 ms | 106–146 ms | 113–137 ms | 2.4–2.5 s |
| verifier peak RSS | 56 MB | 56 MB | 56 MB | 365 MB |
| negatives (fresh verifier per case) | 23/23 pass | 23/23 pass | 23/23 pass | 6/6 (earlier) |
| 8×H200 latency, this chain (model) | ≈ 0.66 s | ≈ 0.66 s | ≈ 0.66 s | |

Bases of the first two chunks were proved by `run.sh` at 07:35–07:50 (`runs/…/base.log`, reused and
re-validated against the AIR + public TAPE by `validate-base`); their base times overlap other work.
Every proof level is natively re-verified and statement-checked before the next level starts.
Prove times include those checks. Per-run numbers: `results/<run>.json`; sha256 manifests:
`results/<run>.manifest.json`; logs: `logs/<run>/`.

Negatives (`scripts/negatives.py`, each a fresh `verify` process): claim bytes flipped at 2/25/50/75/98 %;
the claim of another chunk; hint byte; base-point `u` bytes; proof bytes at 0/10/33/50/66/90 % and
the last byte; trailing byte; truncations; an untrusted setup pin; and a **wrong witness**: one
constrained cell of the `head` trace flipped, the prover's precheck disabled
(`NEARPROOF_NEGATIVE_SKIP_PRECHECK=1`), so the base proof is produced and the **verifier** rejects it
(`BatchConstraintError(SumClaimMismatch)`); with precheck on, the prover refuses
(`head: constraint 38 fails on row 9`). One claim mutation per chunk (bytes 4491 / 6290 / 5952) leaves
the public inputs unchanged and is *accepted by the Lean reference checker with the same witness*,
so the statement is still true and the proof correctly accepts it; the harness takes the expected
verdict from the reference checker. Side finding (`scripts/precheck_mutations.py`): `head` column 72
on the last active row is unconstrained (its only constraint is a transition into the inactive row);
a witness-malleability don't-care, not a statement change.

## 3. What changed in the stack (and why)

1. **TAPE bound by evaluation, not by commitment** (`patches/e2e-verify.patch`, lever
   `NEARPROOF_TAPE_EVAL=1`). The verifier spent 99 % of its time (15.2 s of 15.3 s single-core on the
   delivered packet) recomputing the base proof's cached TAPE commitment from the public claim: a
   rate-1/1920 codeword of 15·2^23 = 126 M points (1,920 coset DFTs of 2^16, 31.5 M SHA-384 leaves +
   31.5 M nodes). That is a prover-scale computation with a floor of ≈ 2 core-seconds of hashing
   alone, so no implementation tuning reaches 200 ms on one core. Instead:
   * L1's NV circuit (the in-circuit verifier of the base proof) now folds into the statement digest
     `H(u, y)`, where `u` is the base stacked-reduction point (squeezed *after* the TAPE root is
     observed) and `y` the TAPE commitment's stacked opening at `u`, which the same circuit's WHIR
     check proves against the root. The root itself leaves the digest.
   * The packet (v2, `NPQCH02`) carries `u` (19 × 48 B = 916 B with framing).
   * The verifier evaluates the stacked public TAPE (≈ 43 k non-zero cells) at `u` — 2^16 eq weights,
     not a commitment.
   * Soundness: if the committed TAPE T* ≠ the public T, then T*(u) = T(u) with probability
     ≤ (l_skip + n_stack)/|EF| ≈ 2^-367 per transcript, so ≤ 2^-303 against 2^64 grinding
     attempts; binding of `y` to the root is the base proof's own WHIR soundness, verified in-circuit.
   * ZK caveat: `u` is a deterministic function of the base commitments; see `ZK-ARGUMENT.md` Z6.
2. **Program check reuses the batch point** of the verification just performed instead of re-running
   GKR + zerocheck verification, and evaluates the program MLE over the program's 2^m prefix with
   pre-folded weights (`vd.rs`): 26.5 → ≈ 7 ms single-core.
3. **`NEARPROOF_CHAIN_GEOM=ns19lb6`** for every recursion layer: corpus chunks with receipts have a
   512–515 KB base proof whose in-circuit verification needs a 2^21-row SHA AIR (L1 failed at the
   delivered `ns18/lb7`: `LayoutHeightExceeded{21,20}`). `2 + 19 + 6 = 27` keeps the BabyBear
   domain; queries [48,38,29,23] (non-final). The base layer is unchanged.
4. Measurement: `verify` prints `VERIFY_PROFILE_MS`; `verify-bench` splits stages; `soundness`
   prints per-component bits from a vk.

## 4. 128-bit: concrete bits per component

`nearproof-chunk-e2e soundness <vk>` (stark-backend `SoundnessCalculator::calculate_from_vk`,
round-by-round bits, proven Johnson-regime list decoding m = 64, z = 32 query-phase grinding);
`results/soundness-*.txt`:

| component | base (ns18, lb7) | L1–L5 (ns19, lb6) | FINAL (ns19, lb6, k_first 1) |
|---|---:|---:|---:|
| LogUp α/β | 321.4 | 321.9 | 321.9 |
| GKR sumcheck / batching | 369.3 / 370.9 | 369.3 / 370.9 | 369.3 / 370.9 |
| zerocheck sumcheck | 355.0 | 355.0 | 355.0 |
| constraint batching | 349.4 | 350.8 | 350.8 |
| stacked reduction | 346.8 | 351.5 | 351.5 |
| WHIR query (binding) | 269.6 | 269.2 | **268.2** |
| WHIR proximity gaps / fold | 280.1 | 281.6 | 283.1 |
| WHIR OOD / γ batching / μ batching | 329.0 / 347.8 / – | 329.0 / 348.3 / – | 329.0 / 348.7 / 283.6 |
| **min (RBR bits)** | **269.6** | **269.2** | **268.2** |
| tape-eval binding (new, §3) | – | ≥ 367 (SZ, deg 21 / |EF| ≈ 2^371) | – |

PQ reading (U-6, V3-D3A-STUDY §11.2): with RBR error ε ≤ 2^-268 per round and t = 2^64 quantum
queries, the CMS19 bound gives ≈ t²ε = 2^-140 per layer; Merkle binding t³/2^336 = 2^-144 (U-10);
union over 7 layers ≈ 2^-137. This is the *parameter* claim. It rests on A-IC (U-11/U-12) for the
in-circuit SHA-384 in recursion, and on the open HANDOVER obligations (single-database NodeOK,
concrete family-QROM instantiation, WHIR transfer), so **`security_established` stays `false`**.

## 5. GPU projection (model only)

`scripts/project.py` → `results/projection.json` (model defaults: eff 0.35, 8 H200, ZK wrap ×1.5).

| chunk | arch (b) worst case | (b) realistic mix | arch (a) worst / realistic |
|---|---:|---:|---:|
| these D0a chunks (no Wasm gas; model floor) | 0.67 s | 0.53 s | 1.04 / 0.89 s |
| mainnet p99 (18.45 Tgas) | 1.26 s | 0.62 s | 1.68 / 0.98 s |
| **100 Tgas** | **2.38 s** (≤ 3 s) | 0.84 s | 3.57 / 1.29 s |
| **1 Pgas** | **10.56 s** (≈ 10 s allowed: 5.6 % over) | 1.89 s | 16.0 / 2.36 s |

The table is the model's optimal design (segments + fan-in-8 tree + one ZK wrap), not the code
that ran. The chain as run (base + 5–6 one-child NV levels at ns19/lb6, the last ×1.5 for ZK) is
3.15 GPU-s serial on one H200, **≈ 0.66 s** with each proof split over 8 GPUs at 60 % efficiency
(`measured_chain_projection`). CPU → GPU: the measured CPU chain is ≈ 2,600–2,900 s on 16 Zen 5
threads, i.e. the model assumes ≈ 4,000× from GPUs plus kernel work; that ratio is unvalidated
until the first H200 hour (prover-budget §7 #6).

## 6. Verifier profile and fixes

Before (delivered packet, `perf` on one core, `vprof/base`): 32.5 % `fast_dft::dif_rows`, 17.5 %
`sha384_x16`, 16.5 % coset-twist closure, 10.5 % memmove, 3 % `stream_commit` — all inside the
re-commitment of the base's TAPE (`STREAM_COMMIT width=1 c=15 log_domain=23`, 1,920 sub-cosets).
Phase split, single core: TAPE re-commitment 15,180 ms (contended) / 8,270 ms (idle) of the total;
everything else 125 ms. GKR/zerocheck/stacking/WHIR (`engine.verify`) was 18–24 ms; the program
check re-ran zerocheck verification and built a 2^18 eq table (26.5 ms).

After (`results/verify-bench.txt`, idle cores, median of 7):

| stage (1 thread) | before | after | fix |
|---|---:|---:|---|
| TAPE binding | 8,270–15,180 ms | **≈ 0.5 ms eval** (+ ≈ 32 ms AIR JSON parse and TAPE build, shared with the old path) | statement binds (u, TAPE(u)); verifier evaluates 2^16 eq weights |
| `engine.verify` (GKR, zerocheck, stacking, WHIR) | 18–24 ms | 14–15 ms | unchanged code; 1 fewer commitment on this geometry |
| program check | 26.5 ms | ≈ 6 ms | reuse the batch point; prefix eq table with pre-folded weights |
| `statepublic` subprocess (claim + hint → public inputs) | 32–52 ms | 32 ms | unchanged (separate trusted tool) |
| setup read + pin + parse (3.8 MB JSON) | 8–16 ms | 8 ms | unchanged |
| proof decode | 0.2 ms | 0.2–1.4 ms | – |
| **total CLI wall** | **7.65 s (1 thr), 1.46 s (32 thr)** | **104–112 ms (1 thr)** | |

More threads do not help now: the remaining work is sequential parsing and a 15 ms protocol check.
The next 60 ms would come from a binary setup/AIR encoding (JSON parse ≈ 35 ms) and running the
public-input preparation in-process.

## 7. What blocks extending this from D0a to general chunks

In order of how soon they bite:

1. **Relation coverage.** The base AIR is the 25-table D0a fixture AIR (`near-air-v3.json`): state
   witness/trie authentication, receipts, header outputs. No Wasm execution, no D1/D2 tiers, no D3
   state/Wasm join in this pipeline. A general chunk needs the Wasm chips and the join as base
   tables (or as separate segment proofs).
2. **Height wall at every layer.** The base is limited to `n_stack ≤ 18` at rate 1/128
   (`2 + 18 + 7 = 27`, BabyBear's two-adicity), i.e. one 2^20-row stacked commitment. Already the
   receipt-carrying D0a chunks here need `ns19/lb6` at L1 because the in-circuit verification of a
   512 KB base proof needs a 2^21-row SHA AIR. Any chunk with real gas exceeds one base proof and
   needs segment proofs plus aggregation: the production-target aggregation nodes exist
   (depth 2/3, 316–322 KB) but only over Fibonacci fixture leaves, not real segments.
3. **Per-shape trusted setup.** `SETUP.json` (final vk + program, ≈ 3.7 MB) is run-specific: the vk
   depends on trace heights and the converged program on the committed tight heights. A deployable
   verifier needs one setup per shape class (padding to classes) or a uniform recursion layer.
4. **Zero knowledge** (`ZK-ARGUMENT.md`): Z1–Z6 unimplemented; ≈ 100–300 KB of HVZK-WHIR overhead
   measured at the PCS level, so the ~400 KB budget is tight on top of a 300+ KB non-ZK packet.
5. **Security obligations** (HANDOVER "Recursion/security"): A-IC for in-circuit SHA-384 (U-11/U-12),
   single-database NodeOK, family-QROM instantiation, WHIR transfer — `security_established=false`.
6. **Prover time.** ≈ 1 CPU-hour per tiny chunk on 16 threads (§2). The 6-level linear chain exists
   for program-binding convergence, not for the statement; a GPU deployment wants base segments + a
   fan-in-8 tree + one ZK wrap (§5), which is the model's design, not this code's.

## 8. Reproduction

```sh
# deps: pinned cpu-fast tree + patches/e2e-verify.patch, then build (8 jobs, CPUs 8-15,24-31)
research/near-compression/e2e/scripts/setup_e2e.sh /data/illia/nearproof-deps/pq-e2e-zk
NEARPROOF_PQ_DEPS=/data/illia/nearproof-deps/pq-e2e-zk research/near-compression/native/pq-chunk-e2e/build.sh
# one chunk end to end (witness, public inputs, base, L1..L5, FINAL, fresh-process verify)
research/near-compression/e2e/scripts/e2e_case.sh OUT /data/illia/nearproof-deps/corpora/d1run/d1/00-h10006-s3
# the three chunks of this run
research/near-compression/e2e/scripts/batch3.sh /data/illia/nearproof-deps/pq-e2e-zk/e2e
# negatives (fresh verifier process per case) + collection
python3 research/near-compression/e2e/scripts/negatives.py OUT CASE OTHER_CASE --wrong-witness
python3 research/near-compression/e2e/scripts/collect.py OUT research/near-compression/e2e/results
# verifier timing: stage split, and the full CLI at 1 / 16 threads
NEARPROOF_PQ_DEPS=... research/near-compression/e2e/scripts/time_verify.sh OUT 1 15
# HVZK-WHIR overhead (Plonky3 3acc8b7 + patches/plonky3-zk128-example.patch)
research/near-compression/e2e/scripts/zk128_sweep.sh
# 8xH200 projection
python3 research/near-compression/e2e/scripts/project.py > research/near-compression/e2e/results/projection.json
```

Evidence: `results/<run>.json` (numbers), `results/<run>.manifest.json` (sha256 of packet, setup,
proofs, logs, tools), `logs/` (copied stage logs).
