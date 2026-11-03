# E2E: real D0a chunks → final PQ proof → fresh-process verification (2026-10-31, ZK update 2026-11-03)

Status: **research run, owner's relaxed targets of 2026-10-31.** `security_established=false`,
`zero_knowledge_established=false` in every RESULT.json. No GPU was used; GPU latencies are
model projections only (`../prover-budget/model.py`). No Lean spec or checker change.

## 0. Update 2026-11-03, milestone D-2 (lane E2E-D): full zero-knowledge masking of the FINAL proof

The FINAL layer now runs `NEARPROOF_ZK_FINAL=5`. That is the PCS-level hiding of §0b plus PIOP
masking: masked GKR, masked batch sumcheck with column masks, and masked stacking reduction
(`ZK-ARGUMENT.md` §4, `native/recursion/patches/zk-piop.patch`). It also uses the
slice-splitting packing, which is now fixed. For each of the 3 D0a chunks, the FINAL layer was
re-proved from the existing L4 checkpoint (`scripts/run_zk4.sh zk5`). The base (`zk = 1`) and
L1–L4 are not affected by FINAL-only masking. Every packet was then verified in fresh
processes. `zero_knowledge_established=false` (reason below).

| target (owner, 2026-11-03) | result | met? |
|---|---|---|
| mask the core proof steps of FINAL | built, see the list below | **yes** |
| one simulator plus a concrete hiding error | `ZK-ARGUMENT.md` §6: ε_ZK ≤ 2^-185 + ε_D + ε_E, where ε_D and ε_E are two composition lemmas (base-field cells absorbing extension-field functionals) that are argued but not proved | **written; not established** |
| two-witness test, witness-guessing distinguisher | `zk = 2` packet: the right witness matches 287/287 openings; full-ZK packet: 0/287 for both witnesses (§0.3) | **passes** |
| split packing (`zk = 3`) | fixed. FINAL layout is 68 stacked columns (`zk = 4` would be 98; non-ZK 53 + 15 mask columns), with 1,537 slices | **yes** |
| proof ≤ ~400 KB with ZK | **319,695 / 320,464 / 319,779 B** | **yes** |
| verify < 200 ms, one core | **40–50 ms** fresh process, 5 runs per chunk, host load 13–19; the FINAL check itself is 24–26 ms | **yes** |
| 128-bit PQ | minimum 268.2 bits per round, unchanged (`results/zk5/*/soundness.txt`) | parameters yes; `security_established=false` |

What is masked:
* **Masked GKR.** A root sumcheck replaces the upstream messages for the two half sums and for
  `q_0`, the product of all denominators. Off-cube level masks are added, and every layer
  sumcheck gets a Libra mask.
* **Masked batch sumcheck.** It has a Libra mask and last-variable column masks, and the per-AIR
  LogUp terms are no longer sent. The public program columns stay unmasked, because V_d checks
  them.
* **Masked stacking reduction.** Sparse mask claims plus a committed-column Libra mask.

### 0.1 Results (full ZK, `zk = 5`)

| | d1/00-h10006-s3 | d1/00-h10007-s0 | d2/05-h10042-s3 |
|---|---:|---:|---:|
| **packet B (full ZK)** | **319,695** | **320,464** | **319,779** |
| packet B, PCS-ZK only (`zk = 2`, §0b) | 325,613 | 324,534 | 326,243 |
| packet B, non-ZK (10-31) | 306,839 | 307,314 | 307,427 |
| FINAL sections: gkr / relations / stacking / whir | 42,828 / 24,436 / 5,440 / 243,960 | 42,828 / 24,436 / 5,440 / 244,590 | 42,828 / 24,436 / 5,440 / 244,044 |
| FINAL prove, including 2 self-verifications, s (10 threads, load 13–19) | 637 | 528 | 763 |
| verify, fresh process, 1 thread (min–max of 6) | 40.3–50.0 ms | 41.3–50.4 ms | 41.0–41.9 ms |
| of which the FINAL protocol check | 23.9–24.7 ms | 25.3–26.1 ms | 24.5–24.8 ms |
| negatives (fresh verifier each) | 21/21 | 21/21 | 21/21 |

Where the bytes went, relative to `zk = 2`:
* GKR +5.2 KB: the masked root, plus per layer the Libra sum, `p_xi_1` (no longer derived) and
  two more last-round evaluations.
* Relations −0.3 KB: the per-AIR terms are gone; one round gains extra evaluations.
* Stacking and WHIR −12.7 KB: 68 instead of 95 stacked columns. The split packing removes the
  30-column packing loss, and the 3 PIOP mask columns are added back.

Relative to non-ZK, full ZK costs +12.4 to +13.2 KB. Raw logs: `results/zk/zk5/`, with sha256
manifests of each packet, proof and setup. Verify now runs public-input preparation in process
(see §0.4).

### 0.2 Sizes at 268 and 274 bits per round (FINAL layer)

Chunk 1, full ZK, same L4 (`results/zk/zk5`, `zk5b`, `zk5r274`, `zk5-extra.log`):

| FINAL per-round target | WHIR queries | min bits | packet B | verify, 1 thread |
|---|---|---:|---:|---:|
| 268 (pinned) | [46, 41, 31, 25] | 268.2 | 319,695 (second proof of the same L4: 318,813) | 40–50 ms |
| 274 (`NEARPROOF_FINAL_RBR=274`) | [47, 43, 31, 25] | 274.0 | **325,051** (+5.4 KB) | 39 ms |

Only the FINAL layer was re-targeted; the inner levels and the base stay at 268. The two
268-bit proofs differ by 0.9 KB because Merkle multiproof deduplication depends on the query
positions.

### 0.3 Hiding tests

* **Same witness, fresh randomness.** `results/zk/zk-diff-zk5-same-witness.txt` compares two
  full-ZK FINAL proofs of the same L4. Every value field differs, except the shape, the public
  values, the PoW witness of a fixed-zero-bit grind, and structural zeros: `q0_claim`, the empty
  slots of layer 0, Gruen-derived zero evaluations, and the zero last evaluation of the doubled
  batch round. On 11-03 morning (`zk = 2`) the GKR, zerocheck and opening values also changed,
  but only through their challenges: they were still deterministic in (witness, challenges).
* **Witness-guessing distinguisher and two-witness test** (`results/zk/zk-guess.txt`, method in
  ZK-ARGUMENT.md §8.2). Each candidate witness is the FINAL trace regenerated from an L4
  checkpoint. The distinguisher recomputes all 287 masked column openings, plus the 4 public
  program openings, at the proof's own batch point.

  | packet (chunk 1) | right witness (chunk 1) | wrong witness (chunk 2) |
  |---|---|---|
  | `zk = 2` (PCS-ZK only) | **287/287** match: the proof identifies its witness | 20/287 (columns equal across chunks) |
  | `zk = 5` (full ZK) | **0/287** (public program 4/4) | 0/287 (program 0/4) |

  With masking, the right witness is no more consistent with the proof than the wrong one. This
  is the test the 11-02 log called "only meaningful after PIOP masking", and it now passes. It is
  a necessary condition, not a proof of ZK (§0 table).

### 0.4 Verify in process (sub-agent)

`statepublic` is now a library call, and the TAPE evaluation is folded.
`results/zk/verify-inprocess.txt` has 32–34 ms on the `zk = 2` packets. The FINAL protocol check
is 16–18 ms with `zk = 2` and 24–26 ms with `zk = 5`.

## 0b. Update 2026-11-03 (lane E2E-D, D-1): PCS-level ZK lever on

Owner targets (2026-11-03): 128-bit PQ, SHA-384, proven bounds; ZK with only the chunk-header
outputs plus trusted facts public; proof **~400 KB accepted with ZK**; verify < 200 ms.

| target | result (`NEARPROOF_ZK=1`, 3 chunks re-run end to end) | met? |
|---|---|---|
| verifier patch reviewed, argued, in the patch stack | `VERIFIER-PATCH.md` (TAPE binding ≤ 2^-289.5 at 2^64 queries under list decoding; reused batch point equivalent, hardened); `native/recursion/patches/e2e-verify.patch` via `setup_e2e_verify_deps.sh`; clean-checkout build OK; v1 path kept, deprecated | **yes** |
| zero knowledge | **partial**: PCS layer of FINAL hidden (root, WHIR, opened rows, stacked openings) and the published base point `u` simulatable (`zk-pcs.patch`); the FINAL PIOP layer (GKR, batch zerocheck, stacking sumcheck, column openings) is **not** masked yet (`ZK-ARGUMENT.md` §4) | **no** — `zero_knowledge_established=false` |
| proof ≤ ~400 KB with ZK | packets 325,613 / 324,534 / 326,243 B with the PCS-ZK layer (+17.2 to +18.8 KB over non-ZK, of which ≈ 13 KB is a packing loss; the splitting fix does not work yet); PIOP masking estimated +6–12 KB ⇒ **≈ 330–340 KB projected with full ZK** | **yes (projected)**: measured for what is built, estimated for the rest |
| verify < 200 ms | 129–283 ms single core on a host at load 20–22 (5 fresh processes per chunk); the FINAL protocol check is 20–48 ms of it, the rest is `statepublic` (45–118 ms) and claim/TAPE preparation, both unchanged by ZK. 10-31 idle-host figure for the same pipeline: 104–112 ms | **yes on an idle host; no under the current contention for 2 of 3 chunks** (the ZK lever adds ≈ 1–5 ms) |
| 128-bit PQ, proven bounds | unchanged: min 268.2 RBR bits (FINAL WHIR query); the ZK lever adds no round, challenge or claim (`results/zk/soundness-final-zk2.txt`) | parameters yes; `security_established=false` |

### 0b.1 Results table (ZK lever on)

| | d1/00-h10006-s3 | d1/00-h10007-s0 | d2/05-h10042-s3 |
|---|---:|---:|---:|
| base proof B (zk = 1) / prove s | 512,410 / 766 | 513,042 / 387 | 515,954 / 434 |
| L1 … L4 proof B | 362,217; 355,959; 357,009; 356,673 | 360,873; 357,555; 355,077; 358,143 | 364,023; 357,429; 357,975; 358,605 |
| L1 … L4 prove s | 1,118; 1,225; 618; 859 | 1,101; 1,540; 1,100; 570 | 799; 863; 678; 745 |
| FINAL (zk = 2) prove s | 1,250 | 556 | 806 |
| chain wall s / peak GiB | 5,234 / 15.3 | 4,952 / 15.1 | 4,072 / 15.1 |
| **packet B with PCS-ZK** | **325,613** | **324,534** | **326,243** |
| packet B non-ZK (10-31) / Δ | 306,839 / +18.8 KB | 307,314 / +17.2 KB | 307,427 / +18.8 KB |
| FINAL proof sections: gkr / relations / stacking / whir | 37,592 / 24,772 / 6,736 / 255,366 | 37,592 / 24,772 / 6,736 / 254,148 | 37,592 / 24,772 / 6,736 / 255,996 |
| verify, fresh process, 1 thread (5 runs, host load 20–22) | 171–203 ms | 194–283 ms | 129–137 ms |
| of which FINAL protocol check (`final_verify`) | 20–42 ms | 21–48 ms | 20–21 ms |
| verify at 10 threads (in-run) | 133 ms | 98 ms | 102 ms |
| verifier peak RSS | 57 MB | 57 MB | 57 MB |
| negatives (fresh verifier each, incl. wrong-witness base) | 23/23 | 23/23 | 23/23 |

10 threads (CPUs 8-15,24-25), `HEAVY_MEM=32G`, host shared with three sibling lanes (load 20–50
during the runs), so CPU times are as measured. Every level natively re-verified before the next.
Per-run numbers `results/zk/<run>.json`, sha256 manifests `results/zk/<run>.manifest.json`.

### 0b.2 ZK size levers measured

| lever | FINAL packet | Δ vs non-ZK (306,839 B, same chunk) | source |
|---|---:|---:|---|
| HVZK-WHIR (eprint 2026/391, Plonky3) at 128-bit Johnson, rate 1/64 — PCS overhead alone | ≈ 529–619 KB (projected) | +222 to +312 KB | `results/zk128-sweep.txt` (10-31) |
| **random-codeword batching** (Ligero/Aurora-style: 12 uniform mask columns make WHIR's batched polynomial a one-time pad; reserved random rows per column; mask columns double as leaf salts) — `zk = 2`, measured | **325,403 / 325,571** (two replays) | **+18.6 KB** | `results/zk/replay-*` |
| … of which packing loss (first-fit with reserved rows cannot put two 2^20 slices in one column: 30 extra stacked columns) | | ≈ +14 KB | stacking openings 95 vs 53 |
| … of which mask columns + their openings (12 × 4 B × 92 opened rows + 12 × 48 B) | | ≈ +5 KB | arithmetic |
| slice-splitting packing (`zk = 3`) | not obtained | expected ≈ +5 KB (−14 KB) | `zk = 3` fails the stacking reduction final-sum check (`results/zk/replay-zk3-split-FAILED.txt`); open |
| PIOP masking (Libra masked sumchecks, low-degree column masks, ZK-GKR), not built | estimate | +6 to +12 KB | `ZK-ARGUMENT.md` §4 |

Grinding on mask spot checks and fewer HVZK masks were the 10-31 candidates for cutting the
HVZK-WHIR overhead; they are moot: the batching construction has no mask oracles and no extra
queries, so its cost is the width of the opened rows, not a security-level-dependent query count.

### 0b.3 Per-round soundness of the ZK wrap (FINAL, pinned), and the 274-bit variant

`results/zk/soundness-final-zk2.txt` (pinned FINAL, `zk = 2`): LogUp 321.9, GKR sumcheck 369.3,
GKR batching 370.9, zerocheck 355.0, constraint batching 350.8, stacked reduction 351.5, WHIR
query/shift **268.2**, proximity/fold 283.1, sumcheck 353.8, OOD 329.0, γ 348.7, μ 283.6 bits ⇒
**min 268.2 bits per round**, queries [46, 41, 31, 25], query grinding 32 bits. The ZK lever leaves
every term unchanged (no new round, challenge or claim).

At a 274-bit per-round target (`NEARPROOF_FINAL_RBR=274`; lane E's budget
`docs/zk-formal/E2E-SOUNDNESS-BUDGET.md` asks ≥ ≈ 274 bits/round if the single-database QROM theorem
is not instantiated): queries [47, 43, 31, 25], min **274.0** bits, FINAL packet **329,505 B** vs
325,613 B at 268 (same chunk, same L4): **+3.9 KB, not material** (`results/zk/replay-zk2-rbr274.txt`).
Only the FINAL layer was re-targeted here; the inner levels and the base stay at 268.

### 0b.4 Hiding checks run

* `zk-diff` of two FINAL proofs from the same L4 (same witness, fresh randomness):
  `results/zk/zk-diff-replay-same-witness.txt`. Root, every WHIR field, stacked openings differ; the
  shape (trace heights) and public values are identical. The PIOP fields also differ, but only
  because their Fiat–Shamir challenges change with the root; they remain deterministic functions of
  (witness, challenges), i.e. a witness-guessing distinguisher still works (open, `ZK-ARGUMENT.md` §4).
* `zk-diff` of two `zk = 1` base proofs of the same witness: `results/zk/zk-diff-base-same-witness.txt`
  (the root, hence `u`, differs).
* This is not the "two witnesses, no distinguishing field" test the owner asked for: that test can
  only pass once the PIOP masking of §4 exists.


## 1. Verdict against the relaxed targets (2026-10-31 run, non-ZK)

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
# deps: cpu-fast tree + native/recursion/patches/{e2e-verify,zk-pcs}.patch (setup_e2e_verify_deps.sh), then build
research/near-compression/e2e/scripts/setup_e2e.sh /data/illia/nearproof-deps/pq-e2e-d
NEARPROOF_PQ_DEPS=/data/illia/nearproof-deps/pq-e2e-d research/near-compression/native/pq-chunk-e2e/build.sh
# 2026-11-03 ZK run (NEARPROOF_ZK=1 is the driver default; =0 reproduces 10-31): replay pair + 3 chunks + negatives
research/near-compression/e2e/scripts/run_zk_batch.sh
# levers: zk=3 split packing, 274-bit FINAL, second zk base; then 1-thread verify timing + collection
research/near-compression/e2e/scripts/run_zk_levers.sh; research/near-compression/e2e/scripts/bench_zk_verify.sh
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
