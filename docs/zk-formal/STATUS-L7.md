# STATUS — lane L7 (completeness and assembly)

Branch `lane/zk-L7`. Lean: `zk-formal/ZkFormal/{Assembly,Prover,Toy,NearAssembly}/`, toy spec
`zk-formal/ZkToySpec/`. All proved items: no sorry/axiom/native_decide; axioms ⊆
{propext, Classical.choice, Quot.sound} (numeric checks: none or propext/Quot.sound).

## 1. Parameters (`Assembly/Params.lean`, `Assembly/Budget32.lean`) — proved, kernel

| theorem | content |
|---|---|
| `g2_5_dom`, `g2_8_dom`, `g3_5_dom` | concrete `G = chunkGood agree lo` dominates `agree(2^q)^9·2^(256−9q)` for every `q ∈ [lo, 26]` |
| `udr2_K26_ok` | 26 chunks (234 queries), every admissible domain: query term ≤ 2^-129 |
| `udr2_K24_min8_ok` | 24 chunks (216 queries), domains ≥ 2^8 |
| `udr2_K24_q5_fails`, `udr2_K24_q7_fails` | **24 chunks fail at domains 2^5..2^7** (R-L7-1) |
| `udr3_K40_ok`, `udr3_K39_fails` | fallback radius (n−D)/3: 40 chunks (360 queries) suffice, 39 do not |
| `badAnswers_le` | commit-phase `bad = 2^36 · 2·3^8 ≤ 2^50` |
| `full_ok`, `full_K26`, `full_K24_min8`, `full_K40_udr3` | `bcsNum … · 2^128 ≤ 2^(256K)` at 2^64 hash / 2^40 prover queries |
| `Bcs.budget32` | L2's `budget` with honest-prover budget `NPu ≤ 2^32` (R-L7-3) |
| `np_romSound` (`Assembly/RomBound.lean`) | judge's `RomSound` for `verifier Fp Fp8 A prm` from L3's `RbrWith` + prover budgets, all verifier-side hypotheses discharged (L4c facts, `schedOk`, `hdec_deployed`) |

## 2. Prover model and completeness (`Prover/*`)

Defined: `proveTree V pr pub cb` (BCS compilation of an honest IOP prover `pr`: MMCS trees
`buildTree`, multiproof stream `multiproofBytes`, transcript identical to the verifier's
`chain`), `npProver S A traceOf : TreeProver S`, `npVerifier S A` (claim guard ∘ L4 verifier).

| theorem | state |
|---|---|
| `np_proverComplete` (ProverComplete, every `H`) | **proved from** `BcsCompleteStmt`, `SizeStmt`, `NpIopCompleteStmt` |
| `np_prover_unit` (2^32), `np_prover_chunk` (numChunks) | **proved from** `ProverQStmt`+`NpProverQStmt`, `ProverChunkStmt` |
| `ProverChunkStmt`, `ProverQStmt` | **proved** `prover_chunk`, `prover_unit` (L7-bcs) |
| `BcsCompleteStmt`, `SizeStmt` | **false as stated** for `H` with non-32-byte answers (R-L7-bcs-1); proved for 32-byte `H` (+ `0 < numChunks, posPerChunk`): `bcs_complete32`, `size32`. Needs L4's `fit32` fix in `Stark.H`, after which the general statements follow |
| `NpIopCompleteStmt`, `NpProverQStmt` | open — sub-lane `lane/zk-L7-iop` |
| `VerifierComplete` | from `np_proverComplete` at `H = sha256(roTag ‖ ·)` (in `np_admission`) |
| proof-size bound | `sizeBound` (formula); toy: `toy_size` ≤ 8 MiB proved (467 KB at height 16); NEAR: `L6Facts.size` open |

## 3. Assembly

| theorem | content |
|---|---|
| `Assembly.romSound_guard`, `inLang_of_guard` | claim-canonicality guard (R-L7-2) |
| `Assembly.np_admission` | **`AdmissionStatement ch art`** for any ROM challenge and AIR from the open statements, L3 `RbrWith`, AIR soundness/completeness, numerics — proved |
| `Toy.toy_admission` (M2) | `AdmissionStatement` for the DEMO toy challenge (`ZkToySpec`, byte square root) — proved from `ToyPending` |
| `Toy.toy_sound`, `toy_holds`, `toy_header`, `toy_size`, `toy_NVu` | toy AIR semantics and numerics — proved |
| `NearAssembly.near_admission` (M5 skeleton) | `AdmissionStatement` for `NearSpec.TransferV1.challengeParamsWith …` from `NearPending` + `L6Facts` — proved |

Open inputs of `toy_admission` / `near_admission` (`ToyPending`/`NearPending`): the six
prover statements above; L3's `RbrFacts (Iop.verifier Fp Fp8 A default) (AirLang Fp A)
Fp8.all 2^36 (agreeUdr 4)` (L3's `Np.rbr_of` from its open `Msg*/Chal*/Query/Shaped/ScheduleAlt`
statements); `QueryOk Params.default.numChunks g2_5`, **false for the current default (24)**,
true once R-L7-1 is applied (`numChunks := 26`). NEAR additionally: `L6Facts` (L6) and the
size bound at every admissible NEAR header.

## Findings (REQUESTS.md)

* **R-L7-1** 216 queries do not give 2^-128 when the query domain is 2^5..2^7 (adversary picks
  the header). Fix: 26 chunks (recommended) or require `queryLog ≥ 8`.
* **R-L7-2** `pubOf` cannot distinguish `cb` from `cb ++ [0]`; honest proofs exist for
  non-decodable claims. Fixed L7-side by the claim guard in the deployed model.
* **R-L7-3** honest prover ≈ 2^30 + O(1) queries; `budget32`.

## M5 trusted-tree pinning

`challenges/drafts/near-transfer-receipt-v1-4.draft.json` (unsigned; `arena-admin check` OK,
id `chl_53e1d8d00479c527c6f555e8dcca769a`): supersedes v1-3 (`chl_fefb6bc7…`), pins
ArenaCore/NearSpec at `e4088761` (formal-core with `sha256Fast`, `9f1adc7`), tree digest
`sha256:35fbd260…`; everything else as v1-3.

## M2: real formal-checker run (2026-10-05, dev bwrap sandbox, tier_cap demo)

Run: `formal-check` (rebuilt from this tree) with the native-lean route, model
`ZkFormal.Toy.Model.verifier`, and certificate `ToyCandidate.certificate : ArenaExpectedInst.expectedType`
(`:= toy_admission pending …`). The trusted inputs were formal-core (ArenaCore) and the toy spec
(`ZkToySpec`). The Expected template was rendered with the validity-classical-128 values (2^64/2^40,
8 MiB) and `sha256(publicBin)`. The scratch tree differs from this branch in two ways: `pending`
discharges `ToyPending` with `sorry` (bcs, size, proverQ, proverChunk, npIop, npProverQ, rbr), and
`query := udr2_K26_ok` holds only after a local `numChunks := 26` patch (R-L7-1). Neither change is
committed.

Result:
* **ARTIFACT_BINDING PASS.** The judge built the native verifier from the model
  (`sha256:3fae6e3c…`, reproducible). The certificate type matched the expected statement:
  neither audit reported THEOREM_TYPE_MISMATCH or SHADOWED_DEFINITION.
* **Every formal gate FAILs**, for exactly two reasons:
  * `SORRY_FOUND`: the 7 open obligations above, as expected;
  * `RECHECK_FAILED`: lean4lean hit a deterministic timeout on L1's `p_prime` (R-L7-4).
* leanchecker accepted all 111 modules (43 s), and nanoda accepted the 8 239-declaration export
  (9 s). Candidate elaboration took 30 s in total, with no module over 1.3 s.
