# Lean chunk-transition gap census — 2026-10-25

Measured, not asserted. Every figure below was recomputed from the pinned corpora in this
session against the built `nearspec-v3-check-successor` binary on `main` at `705ee41b5`
(binary mtime 2026-10-24 23:58, newer than every `.lean` source in `spec/lean/v3`).

> **Scope note.** This census is a snapshot at `705ee41b5`. Its §2/§3 figures (2,581 accept / 8
> reject / 549 out-of-domain) are **superseded** for current work by the remeasurement in
> [LEAN_CHUNK_COMPLETION_WORKPLAN.md §Status](../../requirements/LEAN_CHUNK_COMPLETION_WORKPLAN.md):
> 2,743 / 8 / 387 on the binary `3ad82706…` committed with the status table. The 162-case difference
> is 73 gas-key promise hosts, 86 warm-cache pre-state contracts now served by the deploy tracker,
> and 3 `c.segment` cases. The §3.1 argument (that `c.segment` is a prover size bound and a Gate B
> violation) and §6's open items still stand and are not affected by the remeasurement.

## 1. Selection predicate and totals

The plan's gap set is: a case where the pinned validator says the chunk is valid, but Lean
refuses to decide it. The concrete predicate used is

    meta.json: nearcore == "ok"  ∧  expected_rel_d3 == false

over corpora `d3c7`–`d3c10`: **3,138 cases** (2,969 `out_of_domain`, 169 mutants).
All 3,138 carry `expected_rel == true`, so "Lean refuses" here always means Lean declines a
chunk the validator accepted.

Full-corpus context: 235,716 cases total; 76,431 have `nearcore == "ok"`
(39,942 honest + 36,489 surviving mutants). The 3,138 are 4.1% of the nearcore-valid corpus.

## 2. Verdicts per tier on the 3,138 cases

| tier | accept | reject | out_of_domain |
|---|---|---|---|
| signed … runtimeLimits (rank 0–6) | 0 | 0 | 3,138 |
| storageResolution | 2,354 | 8 | 776 |
| globalActions | 2,339 | 8 | 791 |
| completeCodeGlobal | 2,263 | 170 | 705 |
| curveHosts | 2,354 | 8 | 776 |
| resharding | 2,354 | 8 | 776 |
| **allFeatures** | **2,581** | **8** | **549** |

`allFeatures` is the only tier whose *domain* (the set of inputs it decides, accept ∪ reject)
contains every other wide tier's domain. Verified by set inclusion over all 3,138 cases:
`domain(globalActions) ⊆ domain(allFeatures)`, and likewise for `curveHosts`, `resharding`.
`domain(completeCodeGlobal) ⊄ domain(allFeatures)` — 86 cases outside, all of the form
"completeCodeGlobal rejects, allFeatures excludes".

The 86 are *not* a monotonicity defect in `allFeatures`: `completeCodeGlobal` **rejects**
86 chunks that nearcore accepts (its complete-code witness policy demands raw code for
pre-state execution). `allFeatures` uses the cold-partial policy and declines to decide them
(`pre-state contract served only by the in-chunk compiled-contract cache`). So both tiers are
wrong on those 86 in different ways; neither is an ancestor of the other in the accept
direction. The source comment at `Config.lean:363` calling `completeCodeGlobal` "narrower" is
correct only about *accepts* (2,263 ⊆ 2,581), not about domain.

The 8 rejects are identical across every deciding tier and are **disagreements**, not
exclusions: Lean reports `invalid: MissingTrieValue (contract code)` on 8 mutants whose
`meta.json` records `nearcore: ok` under `verdict_source: nearcore(cold)`. The matching base
(honest) cases accept, so the mutation trips a code-availability path where Lean's cold-store
model and the recorded cold verdict diverge.

## 3. Remaining exclusion families under `allFeatures` (549 cases)

| n | reason | reachable at PV86? | Lean-side blocker |
|---|---|---|---|
| 266 | `w.shape: ML-DSA-65 public key` | **yes** — `PublicKey::MLDSA65`, `Signature::MLDSA65` verified by `UnparsedPublicKey::new(&ML_DSA_65, …)` at `core/crypto/src/signature.rs:1125-1128` | `D2/Types.lean:51` (`pPk`) and `:336` (sig tag 2) throw; ML-DSA verify **not implemented** anywhere in Lean |
| 86 | `e.wasm-α: pre-state contract served only by the in-chunk compiled-contract cache` | yes (warm-cache chunks) | `Successor/CodeResolution.lean:81`, `D3/FunctionCall.lean:271` |
| 80 | `w.shape: non-ED25519 transaction key` | **yes** — SECP256K1 and MLDSA65 transactions both valid | `D2/TxD2.lean:46`, `Successor/GlobalCodecs.lean:150`, `TxD1.lean:84` |
| 73 | `e.wasm-α: unmodeled host function promise_batch_action_add_gas_key_with_full_access` | yes | host **is implemented** (`Wasm/Host.lean:1130`) but gated out by `Exec.realOodHosts:67-74`; `globalPromiseHosts:76-82` lifts only the 7 global/state-init names |
| 41 | `e.secp: SECP256K1 delegate signature verification` | yes | `D2/Actions.lean:401` throws; `Secp256k1.recover` exists but delegate needs ECDSA *verify* (different function, not present) |
| 3 | `c.segment` | **yes — but blocked only by a prover size bound** | `RuntimeCore.lean:122` etc.: `c.blocks.length ≤ 32`; these cases have `n_blocks` = 41, 43, 43 |

### 3.1 The 3 `c.segment` cases are a Gate B violation, not a semantic gap

`c.segment` is inherited from the D0 design and is documented as a **size bound**
(`spec/near-chunk-validation-v0.md:180`, reason column literally "size bound"). It exists so the
AIR's public-segment and table heights stay bounded — exactly the kind of prover-derived bound
Gate B forbids ("no `G_α` or other bound derived from one prover's table height, width,
recursion shape or performance budget"). The three cases are honest, `nearcore: ok`,
`n_blocks` 41/43/43, and fail *only* on this guard. Lifting it on a successor tier needs no new
semantics: the pipeline already walks an arbitrary `c.blocks` list.

### 3.2 Crypto feasibility differs sharply by family

* **SECP256K1** — field/group arithmetic, `checkSigValues` and `recover` already exist in
  `NearSpecV3/Secp256k1.lean` (161 nearcore vectors tested). ECDSA *verify* is a short
  addition over the same primitives: `u1 = z·s⁻¹`, `u2 = r·s⁻¹`, `R = u1·G + u2·Q`,
  accept iff `R.x ≡ r (mod n)` and `R ≠ ∞`.
* **ML-DSA-65** — no implementation in Lean at all. Verification is a lattice computation
  (NTT over `q = 8380417`, `k=6, l=5`, `η=4`, `γ1`, `γ2`, `τ`); this is a substantial
  implementation, not a wiring change. The current exclusion reason ("their trie handle is a
  SHA3-256 hash, which is not formalized", `D2/Types.lean:20`) is **inaccurate**: Keccak-f[1600]
  is formalized in `Wasm/Crypto.lean:34-78`, and SHA3-256 is the same sponge with pad byte
  `0x06` instead of `0x01` (a one-constant change at `:65`).

## 4. What "accept" does and does not mean

`MainSuccessor.lean:40-48` maps the checker's `Except` result to a verdict. `accept` means
`checkSuccessor` returned `.ok ()`. Reading `checkD2Core` (`ChunkValidationD2.lean:114-270`),
that is *not* merely internal witness consistency: the tail checks computed values against the
validator-attested header fields —

    H.prevStateRoot == root, H.prevOutcomeRoot == outcomeRootD1 out.outcomes,
    H.prevGasUsed == out.gasUsed, H.prevBalanceBurnt == out.balanceBurnt,
    H.prevOutgoingReceiptsRoot == outgoingReceiptsRootD2 L out.outgoing,
    H.congestion == out.congestion, H.txRoot == merklizeBorsh …, H.encodedMerkleRoot == emr

so an `accept` binds Lean's computed roots, outcome root, gas, receipts and tx root to the
endorsed header. That is output agreement with the pinned validator, per chunk, for those
fields — but only for fields the header commits to. Logs, return data and emitted-receipt
bodies are covered only indirectly (through the outcome/receipts roots), and no per-receipt
`action_results` comparison is made here. Lane 5 must state this boundary explicitly rather
than claim full output agreement.

## 5. Independent verification commands

    B=spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor
    $B --tier allFeatures <case-dir>            # one JSON verdict line per case

    # regenerate the tier table (writes matrix.json + per-reason case lists)
    python3 /tmp/opencode/tier_matrix.py /tmp/opencode/ood-valid2.txt /tmp/opencode/matrix-out 24

Note `tier_matrix.py` runs 12 tiers × ⌈3138/40⌉ batches; a single serial full run exceeds a
20-minute timeout, so keep the thread pool ≥ 20.

## 6. Open items this census does not settle

* The 8 `MissingTrieValue` disagreements: whether Lean's cold-store model or the recorded
  `nearcore(cold)` verdict is at fault. Needs the base/mutant witness pair diffed at the code
  lookup, not a tier change.
* Whether lifting `c.segment` on a successor tier changes any non-`c.segment` verdict. It
  should be purely additive, but that needs a full-corpus rerun to establish, not a sample.
* The `w.size` 4,000,000-byte storage-proof bound (`ChunkValidationD2.lean:236-237` and
  `Successor/RuntimeCore.lean:55`) is the same class of prover-derived restriction as
  `c.segment`. It is **not** in this gap set only because no corpus case exceeds it: measured
  zero `w.size` failures among the 549 `allFeatures` exclusions. It will bite protocol-scale
  chunks; Gate B should treat it as a known open exclusion even though zero current cases fail
  on it. The same applies to `c.layout` (0 cases) and `e.g_alpha` (0 cases at the protocol-gas
  cap, which is why the `protoGas` tier moves no cases in this set).
