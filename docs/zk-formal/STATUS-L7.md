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
| **`stark_romSound_full`** (`Assembly/RomFull.lean`) | L3 `Udr.Np.rbrWith` ∘ L2 `stark_romSound_rbr` ∘ L4 facts ∘ L7 numerics: `RomSound` at 2^-128 from `NpOk A prm` (decidable), `QueryOk prm.numChunks g` + domination, `NVu ≤ 2^30`, prover budgets — proved; `stark_romSound_full'` fixes `g = g2_5` |
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

Open inputs of `toy_admission` / `near_admission` (`ToyPending`/`NearPending`): the
prover statements above (L3 is now closed: `toy_npOk` proved, soundness via `stark_romSound_full`); `QueryOk Params.default.numChunks g2_5`, **false for the current default (24)**,
true once R-L7-1 is applied (`numChunks := 26`). NEAR additionally: `L6Facts` (L6) and the
size bound at every admissible NEAR header.

## Findings (REQUESTS.md)

* **R-L7-1** 216 queries do not give 2^-128 when the query domain is 2^5..2^7 (adversary picks
  the header). Fix: 26 chunks (recommended) or require `queryLog ≥ 8`.
* **R-L7-2** `pubOf` cannot distinguish `cb` from `cb ++ [0]`; honest proofs exist for
  non-decodable claims. Fixed L7-side by the claim guard in the deployed model.
* **R-L7-3** honest prover ≈ 2^30 + O(1) queries; `budget32`.

## M5 trusted-tree pinning

`challenges/drafts/near-transfer-receipt-v1-zk.draft.json` (unsigned; `arena-admin check` OK,
id `chl_bdbfc8082737c592d3fe3d46992c7868`): supersedes v1-3 (`chl_fefb6bc7…`), pins
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

## M2 rerun with L4d's `@[csimp]` fast verifier (lane/zk-int d6e3a90; toy `maxLog` 16)

Real checker, dev sandbox. Deployed default parameters (24 chunks), so the judge binary matches the
Rust prover. Pending obligations: `bcs`, `size`, `npIop`, `npProverQ`, and `query` (false at 24, R-L7-1)
are `sorry` in the scratch tree only. `proverQ`/`proverChunk` are the proved `prover_unit`/`prover_chunk`.
* Same verdict as before: ARTIFACT_BINDING PASS. The formal gates FAIL only on SORRY_FOUND and
  the lean4lean `p_prime` timeout (R-L7-4). leanchecker accepted 196 modules (66 s), nanoda accepted
  11 092 declarations, and candidate elaboration took 81 s in total.
* **Candidate `@[csimp]` on the native-lean route:** accepted. The audit has no rule for it either
  way, and the judge's native build applies it. The judge-generated `Stark/Bcs.c` calls
  `takeF`/`mpLeavesF`/`readInjF` at every call site; `take?` appears only as its own definition.
  The trusted `ArenaCore/Interp.c` calls `ArenaCore_sha256Fast`.
* **Timing of the judge-built binary** (`sha256:65512c09…`), honest toy proofs from the L8 Rust
  prover (`sqprove`, scratch): 2 KB 3 ms, 33 KB 13 ms, 365 KB 82 ms, **927 KB 208 ms**. That is
  linear and matches L4d's 1.00 MB / 230 ms; the old path took ~20 s at 0.8 MB. Rejections (exit 1)
  on a wrong claim, a non-canonical claim `[b, 0]` (the guard), and a 1-bit proof mutation.
* **But see R-L7-5:** csimp lemmas are not audited, so a `sorry` csimp passes every gate and
  redirects the judge binary (reproduced).


## Prover sub-lanes merged (L7-bcs `918a308`, L7-iop `cfe6701`)

* Proved: `prover_chunk : ProverChunkStmt`, `prover_unit : ProverQStmt`,
  `Np.npIopComplete' : NpIopCompleteStmt'` (honest np IOP prover `npProver`: LDE, aux, quotient,
  OOD, DEEP batch, FRI; well-formed, perfectly complete for every challenge sequence),
  `Np.npProverQ : NpProverQStmt'`, `bcs_complete32`, `size32`.
* The original statements are false, and the composition now uses the corrected ones:
  * `NpIopCompleteStmt` needs `A.tables.length < 2^32` (for 2^32 trivial tables no prover is
    well-formed). That is now a hypothesis of `np_admission`: `by decide` for the toy, an
    `L6Facts` field for NEAR.
  * `NpProverQStmt` needs `NVu ≤ 2^30` (unbounded width ⇒ unbounded batching slots), which
    the assembly already assumes.
  * `BcsCompleteStmt`/`SizeStmt` are false for `H` with non-32-byte answers (R-L7-bcs-1). They are
    proved for 32-byte `H`. **Still open**, and they close once L4 normalises answers (`fit32`).
* `np_admission` (and so `toy_admission`, `near_admission`) is now proved from **only**
  `BcsCompleteStmt`, `SizeStmt` and `QueryOk numChunks g2_5`, plus the AIR inputs. `ToyPending`
  = {bcs, size, query}.

## Lead decisions applied (2026-10-05)

* **R-L7-1 → (b):** 24 chunks, admissible headers require `queryLog ≥ 8`. Toy and NEAR use
  `lo = 8`, `g = g2_8`, and `QueryOk 24 g2_8 = udr2_K24_min8_ok` (kernel). The new input is `min8`
  (admissible ⇒ `8 ≤ queryLog`); it comes from L4's new `headerOk` (lane/zk-L4e). The toy's honest
  trace now has height 16 (LDE 2^8).
* `ToyPending` = {`bcs`, `size` (L4e: hash answers normalised to 32 bytes), `min8` (L4e)}.
* ZK challenge draft renamed to `near-transfer-receipt-v1-zk` (`chl_bdbfc808…`, unsigned).


## M2 certificate CLOSED (after merging lane/zk-L4e and lane/zk-int with L1b)

`Toy.toy_admission` now has **no hypotheses beyond the judge's literals**: it is the full
`AdmissionStatement` for the DEMO toy challenge. Axioms: propext, Classical.choice, Quot.sound.
* L4e (`fit32`): the BCS evaluation lemmas restate wide hashes with `fit32`, and the hash-length
  hypotheses become `(fit32 (H m)).length = 32`, which holds for every `H`. So `bcs_complete32`/`size32`
  apply to every `H`, and `np_proverComplete` uses them directly.
* L4e (`minQueryLog = 8`): every boundary statement (IOP completeness, prover budget, size, `hlo`) is
  over the IOP verifier's admissible headers (`(Vd A).headerOk`). `lo = 8` comes from
  `verifier_headerOk`, and the query bound is `udr2_K24_min8_ok` (24 chunks).
* `np_admission` hypotheses: AIR soundness/completeness, header fit, non-empty and < 2^32 tables,
  size bound, `maxProofBytes`, profile facts, `lo`/`g` domination + `QueryOk`, `NpOk`, `NVu`.
  `near_admission` needs only `L6Facts`.

### M2 real checker run on the closed certificate (`535b0c7`; dev bwrap sandbox, tier_cap demo)

Certificate `ToyCandidate.certificate := toy_admission _ … rfl (by decide) (by decide) (by decide +kernel)`.
There is **no sorry** anywhere. Model `ZkFormal.Toy.Model.verifier`; trusted: formal-core (`ArenaCore`) + `ZkToySpec`.

**All six gates PASS**: FORMAL_SEMANTIC_SOUNDNESS, FORMAL_SEMANTIC_COMPLETENESS, FORMAL_CRYPTO_SOUNDNESS,
FORMAL_IMPL_CONNECTION, AXIOM_AUDIT and ARTIFACT_BINDING. There are no findings and no warnings.
* Rechecks: leanchecker accepted 231 modules (74 s), lean4lean accepted 231 modules (84 s; the L1b
  Pocklington `p_prime` fixed the timeout), nanoda accepted (20 s); arena-audit and the NDJSON audit (12 767 decls) accepted.
* Candidate elaboration took 111 s; the whole pipeline took 324 s.
* Judge-built verifier `sha256:f703a5a2…`, run on honest proofs from L8's Rust prover:

  | proof | exit code | time |
  |---|---|---|
  | height 2: 2 KB | 1 (query domain 2^5 < 2^8, correctly inadmissible) | 2 ms |
  | 33 KB | 0 | 14 ms |
  | 365 KB | 0 | 104 ms |
  | 927 KB | 0 | 237 ms |

  Wrong claim, non-canonical claim and a 1-bit mutation are all rejected.
* Caveat: `lane/fc-csimp` (R-L7-5) has not landed. AXIOM_AUDIT does not yet cover the `@[csimp]`
  lemmas. L4d's three lemmas use only propext/Quot.sound, so the verdict should not change.
