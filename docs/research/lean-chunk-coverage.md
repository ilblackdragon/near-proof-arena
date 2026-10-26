# Lean chunk-transition coverage inventory (L0)

Integration note (2026-10-23): the counts and lane descriptions below are the L0 analysis snapshot. The regenerated JSON now includes L2 float implementation and L3 partial crypto progress; see [combined checkpoint](../logs/lean-chunk-integration-2026-10-23.md). Remaining exclusions are not closed by merging additive modules.

Readable summary of [`lean-chunk-coverage.json`](lean-chunk-coverage.json), the L0 deliverable in
[`../requirements/LEAN_CHUNK_TRANSITION_PLAN.md`](../requirements/LEAN_CHUNK_TRANSITION_PLAN.md) §4.
Owner **L0**; worktree `/data/illia/nearproof-wt/lean-chunk-L0`, branch `lane/lean-chunk-L0`, base
`833f3311c`. Nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4), PV 86.

**What this is.** Two layers, in one row set:

1. a *static reconciliation* of the pinned nearcore surface against the Lean dispatch tables
   (`action`, `host`, `instruction`, `domain_guard`, `boundary` families);
2. an *execution/boundary analysis* of every rejection and domain guard of the D3 checker, the
   oracle marks, the called-vs-imported host trap, the exclusion classification and the unresolved
   boundary questions (`d2-core`, `d3-hook`, `wasm-*`, `claim-fact`, `evidence` families).

It is **not** execution evidence for the static rows, a differential test or a proof. `implemented`
means the Lean spec has a dispatch arm or guard; `validated` means the branch is both present and
exercised by the recorded 115,284-case D3 run. Neither is a conformance claim on its own.

Regenerate or verify (the file is generated, never hand-edited):

```
python3 tools/d3/lean_chunk_coverage.py --repo . \
    --nearcore /data/illia/nearproof-deps/nearcore --output docs/research/lean-chunk-coverage.json
python3 tools/d3/lean_chunk_coverage.py --repo . \
    --nearcore /data/illia/nearproof-deps/nearcore --check docs/research/lean-chunk-coverage.json
```

Exit status 1 means the inventory drifted from source. `--check` also covers the execution-analysis
rows: `tools/d3/lean_chunk_coverage_l0.py` holds their generator, and its Lean-source hashes are in
`source_sha256`.

## Pins and provenance

| | |
|---|---|
| nearcore commit | `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4) |
| protocol version | 86 |
| base commit | `833f3311c26baa3144a1aece84f0c9d0f25d4f08` |
| source extraction | git objects only, never a dirty checkout |
| Lean side | `spec/lean/v3/NearSpecV3`, per-file hash in `source_sha256` |
| checker | `oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3`, sha256 `b4154b212fc482af99fafd4a1c4d5cf6b1157f4e26c154fc1a66e907312ce5d8` |
| corpora | `/data/illia/nearproof-deps/corpora/d3c{7,8,9,10}`, 33,248 / 49,490 / 15,995 / 16,551 |
| recorded run | `var/d3-runs/report-d3-full.json` (lean-chunk-transition-plan worktree), not re-run by L0 |

The host-import extractor was cross-validated against the pre-existing
[`near-wasm-boundary-inventory.json`](near-wasm-boundary-inventory.json): both independently yield
the same 92 `env` imports with no set difference. That agreement is the reason to trust the row set;
it is not evidence about behaviour.

## Headline numbers

| | count |
|---|---|
| inventory rows | 222 |
| implemented | 147 |
| validated | 36 |
| partial | 9 |
| missing | 19 |
| impossible-at-boundary | 11 |
| nearcore `env` imports | 92 |
| Lean host dispatch arms | 75 |
| nearcore action tags | 15 |
| Lean-decoded action tags | 10 (+3 delegate via `pAct`) |
| Lean numeric opcode bytes | 134 |
| distinct oracle `d3_violations` strings | 11 |
| unresolved boundary questions | 17 |

## By family

| family | implemented | validated | partial | missing | impossible-at-boundary |
|---|---|---|---|---|---|
| action | 12 | 0 | 0 | 3 | 0 |
| host | 75 | 0 | 2 | 12 | 3 |
| instruction | 2 | 0 | 0 | 0 | 0 |
| domain_guard | 6 | 0 | 0 | 0 | 0 |
| boundary | 0 | 0 | 1 | 1 | 0 |
| d2-core | 29 | 23 | 3 | 3 | 0 |
| d3-hook | 10 | 4 | 1 | 2 | 0 |
| wasm-prepare | 5 | 3 | 0 | 0 | 0 |
| wasm-exec | 5 | 1 | 0 | 1 | 0 |
| wasm-domain | 1 | 0 | 2 | 0 | 0 |
| claim-fact | 0 | 0 | 0 | 0 | 8 |
| evidence | 0 | 4 | 0 | 0 | 0 |

Counts here are regenerated from the JSON in this commit; the previous table was a hand-maintained
snapshot and had drifted from its own generator (it read 137 implemented against a JSON holding 143).
Treat the JSON as authoritative and regenerate both together.

`validated` rows are the D2/D3 guards with an exercised corpus path; `d2-core` carries most of them
because the saved verdicts contain 85–14,246 discriminating rejects per guard.

## Missing / partial by lane

| lane | missing | partial | implemented | validated | impossible-at-boundary |
|---|---|---|---|---|---|
| L0 | 0 | 1 | 49 | 35 | 0 |
| L1 | 0 | 4 | 0 | 0 | 0 |
| L2 | 0 | 0 | 7 | 0 | 0 |
| L3 | 13 | 2 | 0 | 0 | 0 |
| L4 | 5 | 0 | 87 | 0 | 3 |
| L5 | 0 | 1 | 0 | 0 | 0 |
| L6 | 1 | 1 | 4 | 1 | 0 |
| L7 | 0 | 0 | 0 | 0 | 0 |
| L8 | 0 | 0 | 0 | 0 | 8 |
| L9 | 1 | 0 | 0 | 0 | 0 |

Counts regenerated from the JSON. L6's seven rows: the genesis main transition (`partial`),
`c.same_layout` and `c.no_split_gate` (`implemented`), plus the three D2-core guard rows they lift —
`L0-D2-012`/`L0-D2-019` now `implemented`, `L0-D2-027` now `validated` — with the actual shard-layout
transition (`L0-resharding`) still `missing`. L4's large `implemented` count is the additive codec/host surface; only five rows remain
missing and none is enabled in the signed chunk dispatch.

The semantic gap is concentrated, not diffuse. Of the 19 `missing` rows: **12 curve hosts**
(`alt_bn128_*` 3, `bls12381_*` 9), **3 action tags** (9/10/11, codec present but not dispatched),
**2 `d3-hook`** and **1 `wasm-exec`** rows on L4/L3, **1 resharding transition** on L6. (The two L6 `d2-core` guard rows and the L9 genesis row are no
longer missing: L6's additive modules moved them to `implemented`/`validated`.) Float/prepare is no longer in this list: all five
`wasm-prepare` rows and both `instruction` rows are implemented, so the earlier "5 float/prepare"
figure is obsolete. The two capacity caps (`G_α`, `n_blocks ≤ 32`) are separate from these rows.

## Guards per module

Decision sites counted from comment-stripped source (`check`/`checkK`, `throw`, `.error`), plus
`out of domain` and `unmodeled` string sites.

| module | check | throw | .error | decision sites | `out of domain` | `unmodeled` |
|---|---|---|---|---|---|---|
| `ChunkValidationD1.lean` | 46 | 13 | 1 | 60 | 13 | 0 |
| `ChunkValidationD1a.lean` | 9 | 5 | 4 | 18 | 9 | 0 |
| `ChunkValidationD2.lean` | 51 | 15 | 1 | 67 | 11 | 0 |
| `ChunkValidationV0.lean` | 47 | 10 | 2 | 59 | 14 | 0 |
| `ChunkValidationV0a.lean` | 8 | 9 | 5 | 22 | 8 | 0 |
| `D2/Actions.lean` | 0 | 16 | 1 | 17 | 2 | 0 |
| `D2/Queues.lean` | 0 | 39 | 3 | 42 | 1 | 0 |
| `D2/Receipts.lean` | 0 | 25 | 4 | 29 | 0 | 0 |
| `D2/TxD2.lean` | 0 | 6 | 0 | 6 | 2 | 0 |
| `D2/Types.lean` | 0 | 19 | 0 | 19 | 6 | 0 |
| `D3/FunctionCall.lean` | 0 | 29 | 9 | 38 | 2 | 22 |
| `Layout.lean` | 0 | 3 | 0 | 3 | 1 | 0 |
| `PrepD0.lean` | 35 | 20 | 4 | 59 | 17 | 0 |
| `RuntimeD0.lean` | 0 | 16 | 4 | 20 | 11 | 0 |
| `RuntimeD1.lean` | 0 | 9 | 3 | 12 | 6 | 0 |
| `Wasm/ChunkStorage.lean` | 0 | 0 | 1 | 1 | 0 | 1 |
| `Wasm/Decode.lean` | 0 | 1 | 0 | 1 | 0 | 0 |
| `Wasm/DomainD3.lean` | 0 | 0 | 0 | 0 | 0 | 0 |
| `Wasm/Exec.lean` | 0 | 4 | 9 | 13 | 1 | 31 |
| `Wasm/FiniteWasm.lean` | 0 | 10 | 0 | 10 | 1 | 0 |
| `Wasm/Host.lean` | 0 | 9 | 2 | 11 | 0 | 3 |
| `Wasm/InstrSize.lean` | 0 | 0 | 0 | 0 | 0 | 0 |
| `Wasm/Machine.lean` | 0 | 0 | 3 | 3 | 0 | 4 |
| `Wasm/Prepare.lean` | 0 | 7 | 9 | 16 | 0 | 11 |
| `Wasm/Segment.lean` | 0 | 0 | 0 | 0 | 0 | 1 |
| `Wasm/Syntax.lean` | 0 | 0 | 0 | 0 | 0 | 0 |
| `Wasm/TrieAccounting.lean` | 0 | 0 | 6 | 6 | 0 | 0 |
| `Wasm/TrieStore.lean` | 0 | 0 | 3 | 3 | 0 | 1 |
| `Wasm/Validate.lean` | 0 | 40 | 3 | 43 | 2 | 0 |
| `Wire.lean` | 0 | 21 | 1 | 22 | 8 | 0 |

Totals: **600 decision sites**, **115 `out of domain` sites**, **74 `unmodeled` sites**.

Reading notes:

* `Wasm/Validate.lean` has 40 `throw`s because wasmparser validation is one error per rule; they all
  collapse to `PrepareError::Deserialization` (`Prepare.lean:392`).
* `D3/FunctionCall.lean` has 29 `throw`s but only 2 `out of domain` literals: the `unmodeled`
  action-log paths are lifted to `out of domain (e.wasm-α)` by `functionCallD3` (`:367`).
* `Wasm/DomainD3.lean` has zero decision sites: its `noResharding`/`contractInD3α` predicates are
  **not called by `checkD3`** (UQ-010).
* `Wasm/Exec.lean:462-464` is the only *import*-triggered exclusion, and it is guarded by
  `real.isNone` — the state-free harness only, never the chunk checker.

## Called vs imported hosts (the trap)

**Answer: under `checkD3`, exclusion triggers on a call, not on an import.**

| where | gate | under `checkD3`? |
|---|---|---|
| `Wasm/Exec.lean:72` (`callHost`) | `s.real.isSome && realOodHosts.contains name` | yes, on a call |
| `Wasm/Exec.lean:78` (`callHost`) | `hostCall name = none` (curve families) | yes, on a call |
| `Wasm/Exec.lean:462-464` (`runCall`) | `real.isNone && imports any curveHost` | **no** — harness only |
| `D3/FunctionCall.lean:277` (`contractOOD`) | `prepare` result (floats/compile) | yes, at preparation |
| `D3/FunctionCall.lean:51` (`oodHosts`) | *unused*; the live list is `Wasm.realOodHosts` | n/a |

`oodHosts` (`D3/FunctionCall.lean:51-59`) duplicates `Wasm.realOodHosts` (`Exec.lean:62-70`) and
nothing references it. nearcore links imports at instantiation (`wasmtime_runner/mod.rs:1127-1155`)
and only a call executes `External` code, so call-triggering is correct.

Evidence: `d3c7/d3/00-h10027-s2` imports an excluded family and calls nothing → Lean accept,
nearcore ok; `d3c9/ood/00-h10006-s2` calls `ecrecover` → `out of domain (e.wasm-α)`. Of the 192
import-only cases, 167 accept, 25 leave the domain for an unrelated guard (`e.g_alpha`/`w.shape`),
and none is excluded for the import.

## Oracle marks

Distinct `d3_violations` strings across `d3c{7,8,9,10}/{d3,mutants,ood}/*/meta.json`: **11**
(`d3c9` alone: 10 — no `c.segment`). Counts are oracle-tagged cases; a case may carry several tags.

| tag | d3c7 | d3c8 | d3c9 | d3c10 | total | mapping | Lean guard |
|---|---|---|---|---|---|---|---|
| `c.no_resharding` | 333 | 495 | 159 | 140 | 1127 | mapped-with-defect | ChunkValidationD2.lean:140 `out of domain (c.same_layout): resharding` |
| `c.not_genesis` | 39 | 60 | 19 | 19 | 137 | mapped | ChunkValidationD2.lean:176 `out of domain (c.not_genesis)` |
| `c.segment` | 1 | 2 | — | — | 3 | mapped | ChunkValidationD2.lean:144 `out of domain (c.segment)` |
| `e.code_cache` | 92 | 125 | 31 | 31 | 279 | mapped | D3/FunctionCall.lean:271 `out of domain (e.wasm-α): pre-state contract served only by the in-chunk compiled-contract cache` |
| `e.eth_implicit_local` | 69 | 95 | 24 | 35 | 223 | mapped | D3/FunctionCall.lean:238 `ETH-implicit account with a local contract (legacy wallet resolution)` |
| `e.float` | 35 | 80 | 26 | 19 | 160 | mapped | Wasm/Prepare.lean:315 `out of domain (e.wasm-α): float type or operator in a function body` (via D3:277) |
| `e.g_alpha` | 302 | 428 | 149 | 131 | 1010 | mapped | ChunkValidationD2.lean:240 `out of domain (e.g_alpha): chunk function-call gas … > G_α …` |
| `e.mldsa_key` | 28 | 60 | 14 | 16 | 118 | mapped | D2/Types.lean:34 `out of domain (w.shape): ML-DSA-65 public key` (D2:46 pPk) |
| `e.ood_host` | 142 | 197 | 70 | 71 | 480 | mapped | Wasm/Exec.lean:72-73 `out-of-domain host function {name} called` (realOodHosts: state-init/global/gas-key) |
| `e.secp` | 10 | 19 | 8 | 4 | 41 | mapped | D2/Actions.lean:399 `out of domain (e.secp): SECP256K1 delegate signature verification` |
| `w.shape` | 77 | 155 | 34 | 51 | 317 | mapped | D2/Types.lean:36-39 (DeployGlobalContract/UseGlobalContract/DeterministicStateInit/GlobalContractDistribution) |

**Unmapped/mismapped: 1 of 11 — `c.no_resharding`**, and the mismatch hides a coverage hole:

* all 1,127 tagged claims have one byte-identical shard layout (274 one epoch, 850 two epochs,
  3 with 3–4 epochs) and none carries a split gate;
* 700 of the 1,127 are `accept` in Lean, Python and nearcore; the rest leave the domain for another
  reason (`c.not_genesis` 137, `e.g_alpha` 147, …);
* the recorded difftest still reports 0 disagreements because it compares verdicts, not tags.

**Consequence:** the corpus contains **no resharding case at all**, so `c.same_layout`
(`ChunkValidationD2.lean:140`) and `c.no_split_gate` (`:156`) have zero coverage despite 1,127 marks
claiming otherwise. Fix the oracle classifier before L6 measures progress. The other 10 tags map 1:1
with small pre-emption counts.

Per-tag Lean verdicts (saved `lean.jsonl`, all cases): `e.float` 160/160 OOD, `e.secp` 41/41,
`e.mldsa_key` 118/118, `w.shape` 317/317, `e.eth_implicit_local` 223/223, `e.g_alpha` 1010/1010,
`e.code_cache` 279/279, `c.not_genesis` 137/137, `e.ood_host` 480/480, `c.segment` 3/3; only
`c.no_resharding` splits 700 accept / 427 OOD.

## Exclusion classification

`impossible-at-boundary` is used only where the **pinned validator** cannot exhibit the condition for
a claim about the pinned target. On that test **none of the semantic exclusions is impossible**;
every one is a live PV86 path that nearcore accepts today.

| exclusion | classification | why (source) | owner |
|---|---|---|---|
| `e.float` | **unimplemented** | PV86 contracts may contain floats: wasmparser features enable MVP floats and saturating float-to-int (`runtime/near-vm-runner/src/features.rs:47-59`, `SATURATING_FLOAT_TO_INT=true`). Lean rejects them at preparation (`Wasm/Prepare.lean:205,234,315`). 160 protocol-valid cases excluded. | L2 |
| `e.secp` | **unimplemented** | SECP256K1 is a live key type and Delegate signature scheme at PV86 (`core/crypto/src/signature.rs:250-257`; `KeyType::SECP256K1`). Lean throws at `D2/Actions.lean:399`; 41 protocol-valid cases excluded. | L3 |
| `e.mldsa_key` | **unimplemented** | ML-DSA-65 is enabled at PV85 (`core/primitives-core/src/version.rs:414,567`; `85.yaml` adds `ml_dsa_65_verification_cost`). Lean treats ML-DSA keys/signatures as `w.shape` (`D2/Types.lean:34-35,46`); 118 protocol-valid cases excluded. | L3 |
| `w.shape` | **unimplemented** | Global contracts, deterministic state init and gas keys are live at PV83/85 (`Action` tags 9-11, `core/primitives/src/action/mod.rs:349-370`; `version.rs:553-562`; `GlobalContractDistributionNonce`, `GasKeys`). Lean rejects them at `D2/Types.lean:36-39,300-302` and `D3/FunctionCall.lean:248`; 317 protocol-valid cases excluded. | L4 |
| `e.eth_implicit_local` | **unimplemented** | Legacy ETH-wallet resolution is deterministic given `chain_id` (`runtime/runtime/src/contract_code.rs:56-76`, `eth_wallet_global_contract_hash`), not random. Lean conservatively excludes it (`D3/FunctionCall.lean:236-239`); 223 protocol-valid cases excluded. | L4 |
| `c.no_resharding` | **guards implemented; the transition itself unimplemented** | Dynamic resharding is enabled at PV85 (`version.rs:342,564`); the validator has a resharding transition path (`chain_validation.rs:258-308`, `ImplicitTransitionParams::Resharding` at :702-733, `reassign_outgoing_receipts_for_resharding`) and mainnet genesis sets `dynamic_resharding: true` (`utils/mainnet-res/res/mainnet_genesis.json`). L6 states both guards against the validator and proves the exclusion argument: `c.same_layout` (`ChunkValidationD2.lean:140`) ⇒ consecutive-epoch layouts equal ⇒ `get_resharding_transition`'s layout-difference conjunct false (`sameLayout_forbids_resharding`); `c.no_split_gate` (:156) as `noSplitGate_iff` plus `splitGate_excludes_nonempty`. But **an actual layout transition remains unimplemented**, and the split gate is genuinely reachable at PV86 (mainnet PV85 has `dynamic_resharding_config`), so D3 declining such claims is an exclusion, not a proven impossibility. The 1,127 oracle marks are a stale multi-epoch classifier: all have one layout and 700 are accepted. No genuine resharding case is in the corpus. | L6 |
| `c.not_genesis` | **implemented additively by L6** | The genesis main transition is a first-class validator branch (`chain_validation.rs:403-413`, `MainTransition::Genesis`, `Chain::genesis_chunk_extra`) and claim-v3 T14 carries `genesis_chunk_extra`. The signed `checkD2Core` still excludes it (`ChunkValidationD2.lean:176`); L6's additive `checkD3G` (`NearSpecV3/GenesisD3.lean`) decides all 137 recorded genesis-`B2` cases instead. The remaining L9 obligation is wiring the genesis path into the signed successor's chunk dispatch and closing UQ-017's header comparison set. | L6 + L9 |
| `e.g_alpha` | **capacity choice, not a boundary condition** | `G_α` is a prover table-size cap (`D3/FunctionCall.lean:389`, `D3_WASM_REQUIREMENTS.md` §2.4), not a nearcore condition; nearcore accepts all 1,010 tagged chunks. A chunk above `G_α` is protocol-valid. | L1 |
| `e.code_cache` | **partly impossible-at-boundary, partly unimplemented** | nearcore's verdict depends on the compiled-contract cache (`oracle/v3-d3/src/d3judge.rs` ColdCache; `function_call.rs:355-393` records the access, `pipelining.rs:323-374` may reuse a preparation). For a *rolled-back* in-chunk deploy the verdict is genuinely cache-dependent, so no cache-independent relation can decide it. For a *committed* deploy the deploy tracker serves the code deterministically (`contract.rs:42-131`), so those 169 cold-accepted cases are decidable; Lean's blanket rule (`D3/FunctionCall.lean:268-275`) excludes them anyway. | L1 + L7 |
| `c.segment` | **arena-format bound, not a validator condition** | The 32-block bound is a claim-size budget (`spec/claim-v3.md` §5 `max_claim_bytes`), not a nearcore rule; the validator's backward walk (`chain_validation.rs:144-253`) has no such limit. Three protocol-valid claims have 41/41/43 blocks and are excluded by `ChunkValidationD2.lean:144`. | L1 |

Reading:

* **Floats are not impossible**: wasmparser at PV86 enables MVP floats and saturating float-to-int
  (`features.rs:47-59`); Lean rejects them at preparation (`Prepare.lean:205,234,315`). 160 corpus
  chunks execute float contracts and nearcore accepts them.
* **secp256k1 and ML-DSA-65 are not impossible**: both are live key types
  (`core/crypto/src/signature.rs:250-257`); ML-DSA is enabled at PV85 (`version.rs:414,567`).
* **Global contracts / state-init / gas keys are not impossible**: `Action` tags 9–11 exist
  (`action/mod.rs:349-370`) and are gated on at PV83/85 (`version.rs:553-562`).
* **ETH-implicit legacy wallet is not impossible**: resolution is deterministic from `chain_id`
  (`contract_code.rs:56-76`), so it is a finite enumeration.
* **Resharding and genesis are not impossible**: both have first-class validator branches
  (`chunk_validation.rs:258-308`, `:403-413`), and mainnet genesis sets `dynamic_resharding: true`.
  Genesis is now *decided* by L6's additive `checkD3G` rather than refused; resharding transitions
  are still refused, with only the guard-level exclusion argument in place.
* **`e.code_cache` is the one genuinely boundary-dependent item, and only partly**: for a
  *rolled-back* in-chunk deploy the verdict depends on the compiled-contract cache, so no
  cache-independent relation can decide it; for a *committed* deploy the tracker serves the code
  deterministically (`contract.rs:42-131`), so the 169 cold-accepted cases are decidable.
* **`G_α` and `n_blocks ≤ 32` are capacity/format choices**, not validator conditions: 1,010 chunks
  exceed `G_α` and 3 claims exceed 32 blocks, all accepted by nearcore.

Honest headline for Gate B: **11 semantic families and 2 capacity caps** stand between D3α and the
full PV86 transition. D3α is sound (never accepts what nearcore rejects) but not complete. L6's
genesis branch removes one of those families from the exclusion list (`c.not_genesis`) without
touching the signed `checkD2Core`; its non-genesis tail is delegated to `checkD2Core` itself, so the
extension cannot drift the existing relation. The first draft did not delegate and wrongly accepted
307 header mutants — measured over the corpus, not inferred.

## Unresolved boundary questions

Gate B cannot pass with any of these open; each names an owner lane.

| id | question | owner |
|---|---|---|
| `UQ-001` | Must `Rel_D3` be cache-independent, and is the cold-cache statement the one the arena admits? | L1 |
| `UQ-002` | Can `e.code_cache` be narrowed to rolled-back deploys (committed deploys are served by `ContractsTracker`)? | L1 + L7 |
| `UQ-003` | Which NaN payload/sign semantics does the pinned Wasmtime produce, and is that stable across validator architectures? | L2 |
| `UQ-004` | Are the curve host-function gas schedules fully pinned at PV86 (there is no `86.yaml`)? | L3 |
| `UQ-005` | Is the ML-DSA-65 trie key handle (SHA3-256 of the pubkey) part of the pinned claim/trie model? | L3 |
| `UQ-006` | Which global-contract / state-init receipts can appear in `source_receipt_proofs` at PV86, and are `GlobalContractDistribution` receipts ever in a chunk witness? | L4 |
| `UQ-007` | Is the `LegacyEthWallet` branch still reachable at PV86 after `EthImplicitGlobalContract` (83), and which wallet hashes must be enumerated? | L4 |
| `UQ-008` | Which witness carries a resharding transition, and must `retain_split_shard` / child congestion info be modelled per child shard? | L6 |
| `UQ-009` | May a valid segment reference a PV85 epoch (a protocol-version activation boundary), and does the pinned target require both PV85 and PV86 runtime configs? | L9 + L6 |
| `UQ-010` | Which predicate is the statement of record: `checkD3` (implementation) or `Wasm.DomainD3.noResharding`/`contractInD3α` (unused, and stricter on curve imports)? | L1 |
| ↳ `UQ-010` record (2026-10-26) | **Decided by the user:** `checkD3`/`RelD3` is the named statement of record (W00 §3.1), and its 37 SECP256K1 delegate verdict moves are **accepted as a signed-statement strengthening**. The moves: 35 `out_of_domain → accept` on the 3,138-case gap census (2,438/700 → 2,403/735), plus 2 high-s `reject → accept` (`k6151 00-h10075-s1`, `k1618 00-h10077-s1`). nearcore accepts all 37. Population, reproduction command and reason: [owner map §3.2](lean-chunk-w00-owner-map.md#32-uq-010-decision-record--the-secp256k1-delegate-strengthening-2026-10-26). The UQ's `DomainD3` reconciliation stays open. | L1 |
| `UQ-011` | Does Gate B require removing the arena claim-size bounds (`c.segment` 32 blocks, `w.size` 4 MB/8 MiB), or is a larger versioned claim format acceptable? | L1 + L8 |
| `UQ-012` | Does Gate B require unbounded chunk function-call gas (segmented proof), or is a stated `G_α` capacity contract acceptable? | L1 |
| `UQ-013` | What admission contract binds the trusted facts (`chain_id`, validators, `minimum_stake`, `tx_valid`, RS params, `genesis_chunk_extra`) to the verifier's own chain state? | L8 |
| `UQ-014` | Are the Wasmtime `LoadingError` / `WasmUnknownError` / resource `LinkError` branches (H2/H9/H10) truly absent at PV86, or must they be modelled? | L7 |
| `UQ-015` | Is `Σ|values| + 2000·R ≤ 4 000 000` a sound upper bound on `recorded_storage_size_upper_bound` when contract-storage removals are present? | L5 |
| `UQ-016` | Is the mock action log equivalent to nearcore's `ReceiptManager` for every reachable promise/yield/gas-key shape, or does it silently OOD a valid shape? | L4 |
| `UQ-017` | For the genesis main transition, which header comparisons apply and is `tx_valid` all-1? | L9 |

## Claim facts (trusted values)

`Rel` cannot authenticate `chain_id`, epoch validators, `minimum_stake`, `tx_valid`, RS parameters,
`validator_update` contents, `split_gate`, or `genesis_chunk_extra` (claim-v3 §2.4 T3/T4/T8/T10/T11/
T13/T14). Those rows (`L0-CLAIM-001…008`) are `impossible-at-boundary` in the precise sense that *no
relation over claim+witness can check them*; they must be bound by the arena's admission contract
(L8). A proof alone is not a validated chunk.

## What this inventory does NOT establish

* It does not show that an `implemented` row behaves like nearcore; that needs plan §5's directed
  and generated comparisons.
* The opcode count (134) is *syntactic*: bytes the decoder accepts, not semantic branches.
* Domain guards are recorded as present, not re-derived as complete.
* `validated` rows rest on the recorded 115,284-case run, which L0 did **not** re-execute.

## Next step for L0

The inventory settles the boundary questions it can settle and names the rest. The blocking items
for other lanes are UQ-001 (cache-independent statement), UQ-010 (`checkD3` vs `DomainD3` as the
statement of record), the oracle `c.no_resharding` classifier fix, and a real resharding corpus.
Everything else maps to a lane in the missing/partial table above.
