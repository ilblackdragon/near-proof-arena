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
| proof ~400 KB with ZK | non-ZK packets TBD; + HVZK-WHIR ≈ TBD + salts ≈ 11 KB (estimate) | TBD |
| verify < 200 ms | TBD single core / TBD 16 threads (was 7.65 s / 1.46 s) | TBD |
| ≤ 3 s at ~100 Tgas, ~10 s at 1 Pgas on 8 H200 | model: 100 Tgas worst case 2.38 s (arch b), 1 Pgas worst case 10.56 s, realistic mix 0.84 / 1.89 s; this chain as run ≈ 0.66 s on 8 H200 (§5) | 100 Tgas **yes (model)**; 1 Pgas worst case **5.6 % over (model)** |

## 2. Results table

TBD

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
   511–… KB base proof whose in-circuit verification needs a 2^21-row SHA AIR (L1 failed at the
   delivered `ns18/lb7`: `LayoutHeightExceeded{21,20}`). `2 + 19 + 6 = 27` keeps the BabyBear
   domain; queries [48,38,29,23] (non-final). The base layer is unchanged.
4. Measurement: `verify` prints `VERIFY_PROFILE_MS`; `verify-bench` splits stages; `soundness`
   prints per-component bits from a vk.

## 4. 128-bit: concrete bits per component

TBD

## 5. GPU projection (model only)

TBD

## 6. Verifier profile and fixes

TBD

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
