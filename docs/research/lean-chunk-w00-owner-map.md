# W00 owner map — 28 missing/partial rows and 17 UQs

Owner: **L0** (integration owner for the successor API). Worktree
`/data/illia/nearproof-wt/lean-chunk-L0`, branch `lane/lean-chunk-L0`, base tip
`46ddb874692225cbafdd7bc5cac9baa3834ae2b6` (unchanged by this work — all new files are untracked).
Nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4), protocol version 86.

Companions: [`lean-chunk-coverage.json`](lean-chunk-coverage.json) (generated inventory, 222 rows),
[`lean-chunk-coverage.md`](lean-chunk-coverage.md) (readable summary), the successor API at
`spec/lean/v3/NearSpecV3/Successor/`, and the lane log
[`../logs/lean-chunk-L0-2026-10-24.md`](../logs/lean-chunk-L0-2026-10-24.md).

**What this document is.** The reconciliation W00 owes the workplan: for every inventory row that is
`missing` or `partial`, and for every recorded unresolved boundary question, one row naming the owner,
the disposition, the source justification and the test obligation. It also states, per interface, which
Lean module publishes the contract and where the row's obligation now lives.

**What this document is not.** It is not new evidence. Every "source" column here points at an
existing generator row or an existing Lean declaration; nothing is re-derived. Status words
(`missing`/`partial`) are copied from the generated inventory, not re-judged. **No row changes status
because this document names an owner**: naming an owner is not implementing a row, and the workplan is
explicit that "unresolved implementation work cannot disappear by relabelling an exclusion."

## 0. How to read the disposition column

| disposition | meaning |
|---|---|
| **open — implementation** | The behaviour is not modelled in Lean and no successor module models it. An owner must implement it. |
| **open — proof** | The behaviour *is* modelled but a theorem or premise is unproved. An owner must prove or discharge it. |
| **open — decision** | A modelling or policy choice is unmade. An owner must decide and record it. |
| **modelled, unvalidated** | A successor module now provides a signature/semantics; no differential evidence exists yet. W13/W14 must validate. |
| **boundary — stays excluded** | The row is an arena-format bound or a validator condition, not a modelling gap. It stays an exclusion in every tier. |
| **successor-only** | The signed checker excludes it by design; the successor admits it. The row's status in the *signed* inventory is correct and stays. |

Interface owner of record for all seven published interfaces: **L0**. The module that publishes each
interface is named in §1. Every row's *semantic* owner stays as the generated inventory records it.

## 1. Interfaces published by W00 and where each row's obligation lives

| # | Interface | Module | Signed statement untouched? | Row families it carries |
|---|---|---|---|---|
| 1 | Canonical checker and tiers | `Successor/Config.lean` | yes — `checkSuccessor_signed` is `rfl` | `boundary` genesis rows, all tier predicates |
| 2 | Wasm host dispatch | `Successor/HostDispatch.lean` | yes — `signedTable` is `hostCall` | all 14 missing/partial `host` rows, plus the implemented ones it names |
| 3 | Actions and receipts | `Successor/ActionsReceipts.lean` | yes — `ActV.d2` delegates to `D2.pAct` | `action-09/10/11`, distribution receipts, key forms |
| 4 | Contract resolution | `Successor/Resolution.lean` | yes — resolution is not in `checkD3` | `L0-D3-006`, `L0-D3-008`, `L0-D3-009`, UQ-002/UQ-007 |
| 5 | Trie recorder | `Successor/TrieRecorder.lean` | yes — recorder is witness-side | `L0-D2-040`, `L0-D2-041`, soft-limit state |
| 6 | Boundary facts | `Successor/BoundaryFacts.lean` | yes — facts are witness-side | genesis/epoch/layout/split rows, UQ-008/UQ-013/UQ-017 |
| 7 | Differential result | `Successor/Differential.lean` | yes — no checker change | every test lane's comparison vocabulary |

Aggregator: `NearSpecV3/Successor.lean` (module name `NearSpecV3.Successor`), which imports all seven
and states the cross-interface facts (`signedChecker_eq_checkD3`, the exclusion owner list).

## 2. Missing/partial rows — 28 rows, one disposition each

Generated inventory status is quoted verbatim in *status*. *Lean symbol now* records what this work
added; `none` means the row still has no Lean representation.

### 2.1 Action rows (3) — family `action`

| Row | Status | Owner | Lean symbol now | Disposition | Source justification | Test obligation |
|---|---|---|---|---|---|---|
| `L0-action-09` | missing | L4 | `ActV.deployGlobal`, `pActV` tag 9, `ActionTag.deployGlobalContract` | successor-only | `core/primitives/src/action/mod.rs:DeployGlobalContract = 9`; `D2/Types.lean` rejects tag 9 as `w.shape` | 1 valid + 1 invalid whole-chunk case (tag 9) |
| `L0-action-10` | missing | L4 | `ActV.useGlobal`, `pActV` tag 10, `ActionTag.useGlobalContract` | successor-only | same, `UseGlobalContract = 10` | 1 valid + 1 invalid whole-chunk case (tag 10) |
| `L0-action-11` | missing | L4 | `ActV.stateInit`, `pActV` tag 11, `ActionTag.deterministicStateInit` | successor-only | same, `DeterministicStateInit = 11` | 1 valid + 1 invalid whole-chunk case (tag 11) |

**What changed and what did not.** The three actions now have a *decoder* (`pActV`) whose tag 9/10/11
branches are proved to reach the `L4` decoders (`pActV_tag9/10/11`), and an `ActionHandler` dispatch
(`ActionTag.handler`). They do **not** have whole-chunk *execution* semantics in Lean: `L4`'s
`DeployGlobal`/`UseGlobal`/`Dsi` records and their costs are in `D3/GlobalContract.lean`, but no
chunk-level execution path consumes them. The row stays `missing` for execution; the decoder half is
done. **L4 owns closing it.**

### 2.2 Host rows (14) — family `host`

Fourteen `host` rows are missing/partial: twelve `missing` curve hosts and two `partial`
(`ecrecover`, `p256_verify`). The successor host table names every one with an explicit store
requirement, gas order and error class, and declares the implemented subset.

| Row | Status | Owner | Lean symbol now | Disposition |
|---|---|---|---|---|
| `L0-host-alt_bn128_g1_multiexp` | missing | L3 | `implementedContracts`? no — `unimplementedHosts` entry | open — implementation |
| `L0-host-alt_bn128_g1_sum` | missing | L3 | `unimplementedHosts` entry | open — implementation |
| `L0-host-alt_bn128_pairing_check` | missing | L3 | `unimplementedHosts` entry | open — implementation |
| `L0-host-bls12381_g1_multiexp` | partial | L3 | `NearSpecV3.Wasm.CryptoHost.bls12381_g1_multiexp` (successor table); D3α: none | implemented in successor domain; D3α still excludes it — open — validation |
| `L0-host-bls12381_g2_multiexp` | partial | L3 | `NearSpecV3.Wasm.CryptoHost.bls12381_g2_multiexp` (successor table); D3α: none | implemented in successor domain; D3α still excludes it — open — validation |
| `L0-host-bls12381_map_fp2_to_g2` | partial | L3 | `NearSpecV3.Wasm.CryptoHost.bls12381_map_fp2_to_g2` (successor table); D3α: none | implemented in successor domain; D3α still excludes it — open — validation |
| `L0-host-bls12381_map_fp_to_g1` | partial | L3 | `NearSpecV3.Wasm.CryptoHost.bls12381_map_fp_to_g1` (successor table); D3α: none | implemented in successor domain; D3α still excludes it — open — validation |
| `L0-host-bls12381_p1_decompress` | partial | L3 | `NearSpecV3.Wasm.CryptoHost.bls12381_p1_decompress` (successor table); D3α: none | implemented in successor domain; D3α still excludes it — open — validation |
| `L0-host-bls12381_p1_sum` | partial | L3 | `NearSpecV3.Wasm.CryptoHost.bls12381_p1_sum` (successor table); D3α: none | implemented in successor domain; D3α still excludes it — open — validation |
| `L0-host-bls12381_p2_decompress` | partial | L3 | `NearSpecV3.Wasm.CryptoHost.bls12381_p2_decompress` (successor table); D3α: none | implemented in successor domain; D3α still excludes it — open — validation |
| `L0-host-bls12381_p2_sum` | partial | L3 | `NearSpecV3.Wasm.CryptoHost.bls12381_p2_sum` (successor table); D3α: none | implemented in successor domain; D3α still excludes it — open — validation |
| `L0-host-bls12381_pairing_check` | partial | L3 | `NearSpecV3.Wasm.CryptoHost.bls12381_pairing_check` (successor table); D3α: none | implemented in successor domain; D3α still excludes it — open — validation |
| `L0-host-ecrecover` | partial | L3 | `implementedContracts` entry (`.ecrecover`); `successorTable` dispatch via `cryptoHostCall` | modelled, unvalidated |
| `L0-host-p256_verify` | partial | L3 | `implementedContracts` entry (`.p256Verify`); `successorTable` dispatch | modelled, unvalidated |

Source justification for all 14: `runtime/near-vm-runner/src/imports.rs:354-368` (curve host table);
`signedTable` reports them out of domain (`Wasm/Exec.lean:462-464` import gate), `successorTable` admits
the two implemented ones and leaves the rest unimplemented. Test obligation for each: positive/negative
host vector plus exact gas through a real chunk. **L3 owns all 14.**

The generated inventory's host family has 14 missing/partial rows: the twelve `missing` curve hosts
above plus the two `partial` ones (`ecrecover`, `p256_verify`). `L0-W-015` — also a curve-host row — is
filed under family `wasm-exec`, not `host`, and is counted in §2.5.

### 2.3 Boundary rows (2) — family `boundary`

| Row | Status | Owner | Lean symbol now | Disposition | Source justification | Test obligation |
|---|---|---|---|---|---|---|
| `L0-genesis-main-transition` | partial | L6 | `checkD3G` (existing), `ProtocolCfg.genesisMainTransition`, `Tier.genesis`, `BoundaryInputs.genesis` | open — proof | `chunk_validation.rs:403-413 MainTransition::Genesis`; non-genesis delegation argued by construction over 115,284 cases but not proved as a rewrite theorem | genesis B2 with nonempty witness + genesis header negative |
| `L0-resharding` | missing | L6 | `ShapeExclusion.resharding`, `EpochInputs.layouts`, `SplitInputs` | open — implementation | `validate_chunk_state_witness: layout transitions`; `Wasm.DomainD3.noResharding` is the stated exclusion | validator fixture crossing a real layout boundary |

**What changed.** The genesis row now has an *explicit configuration flag* (`genesisMainTransition`) and a
boundary-inputs record (`GenesisInputs.genesisChunkExtra`, `EpochInputs.layoutsOf`, `splitGatesOf`), so a
lane can state which genesis facts it consumed. It still has **no** rewrite theorem from the genesis
branch to the non-genesis branch — that stays L6's proof obligation. The resharding row now has typed
layout/split-gate inputs and an owner-list entry; **no** layout-transition semantics exists.

### 2.4 d2-core partials (3)

| Row | Status | Owner | Lean symbol now | Disposition | Source justification | Test obligation |
|---|---|---|---|---|---|---|
| `L0-D2-015` | partial | L1 | `ChunkAccounting` (soft/per-receipt limits) — *not* the `c.segment` bound | boundary — stays excluded | `ChunkValidationD2.lean:144` `c.segment` (n_blocks ≤ 32) vs `chunk_validation.rs:144-253` backward walk with no 32-block limit | extend the claim-size budget and replay the 41/43-block cases |
| `L0-D2-040` | partial | L5 | `ChunkAccounting.receiptExceeded`, `trieRecorderContract` | open — proof | `runtime/src/lib.rs:838-845`; `recorded_storage_counter.rs:27`; per-receipt limit 4,000,000 | construct a chunk where a receipt's recorded-size delta exceeds Σ values + 2000R but stays under 4e6 |
| `L0-D2-041` | partial | L0 | `ProtocolCfg.gasCap`, `ChunkAccounting.softLimitReached` | open — decision | `G_α` is a prover cap (`D3/FunctionCall.lean:389`), not a nearcore condition; 1,010 corpus chunks exceed it and nearcore accepts them | raise the cap and replay; compare with nearcore |

Family totals for the 28: `host` 14, `action` 3, `d2-core` 3, `d3-hook` 3, `boundary` 2,
`wasm-domain` 2, `wasm-exec` 1. §2.6 lists the exact IDs.

### 2.5 d3-hook (3), wasm-exec (1) and wasm-domain (2) rows — 6 total

| Row | Status | Owner | Lean symbol now | Disposition | Source justification | Test obligation |
|---|---|---|---|---|---|---|
| `L0-D3-006` | missing | L4 | `ContractIdentifier` (`Rci`), `IdentifierKind.ethWallet`, `ethWallet_kind_unreachable` | open — implementation | `contract_code.rs:56-76`; with `eth_implicit_global_contract` on, the legacy path becomes `Global{eth_wallet_global_contract_hash(chain_id)}` | replay `d3.call_eth_implicit_local` with the wallet hash enumerated |
| `L0-D3-008` | missing | L4 | `ResolutionEnv.resolveCodeHash`, `ResolutionEnv.codeOf`, `deployedCode?` | modelled, unvalidated | `contract_code.rs:39-95 RuntimeContractIdentifier::resolve` | replay `UseGlobalContract` / `GlobalByAccount` cases |
| `L0-D3-009` | partial | L1 | `CacheMode`, `CacheEnv`, `committedCache`, `validatorCache_not_admitted` | open — proof | `contract.rs:104-131`; `contract.rs:42-69 ContractsTracker`; `function_call.rs:355-393`; 169/279 code-cache cases are cold-validator accepts | split 279 cases by committed vs rolled-back deploy; replay cold validator |
| `L0-W-015` | missing | L3 | `unimplementedHosts` (curve host table) | open — implementation | `imports.rs:354-368` | replay `d3curve` run/cb |
| `L0-W-016` | partial | L1 | `Tier.domainPredicate` (verdict-form predicate) | **closed 2026-10-29 — retired (§3.4)**: `Wasm/DomainD3.lean` deleted; `noResharding` kept in `ReshardingD3.lean` as the legacy core's guards, which the statement of record no longer requires | (was `DomainD3.lean:23-39`) | — |
| `L0-W-017` | partial | L1 | `Tier.domainPredicate` | **closed 2026-10-29 — retired (§3.4)**: `contractInD3α` deleted; it excluded curve-host *imports*, which no checker does | (was `DomainD3.lean:57-62`) | — |

### 2.6 The exact 28 rows

Generated, not hand-typed. Reproduce with:

```
python3 - <<'PY'
import json
d = json.load(open('docs/research/lean-chunk-coverage.json'))
print([r['id'] for r in d['rows'] if r['status'] in ('missing','partial')])
PY
```

The set is: `L0-action-09`, `L0-action-10`, `L0-action-11`, `L0-host-alt_bn128_g1_multiexp`,
`L0-host-alt_bn128_g1_sum`, `L0-host-alt_bn128_pairing_check`, `L0-host-bls12381_g1_multiexp`,
`L0-host-bls12381_g2_multiexp`, `L0-host-bls12381_map_fp2_to_g2`, `L0-host-bls12381_map_fp_to_g1`,
`L0-host-bls12381_p1_decompress`, `L0-host-bls12381_p1_sum`, `L0-host-bls12381_p2_decompress`,
`L0-host-bls12381_p2_sum`, `L0-host-bls12381_pairing_check`, `L0-host-ecrecover`,
`L0-host-p256_verify`, `L0-genesis-main-transition`, `L0-resharding`, `L0-D2-015`, `L0-D2-040`,
`L0-D2-041`, `L0-D3-006`, `L0-D3-008`, `L0-D3-009`, `L0-W-015`, `L0-W-016`, `L0-W-017`.

Counts by `owner` field in the generated JSON: L3 = 15 (14 host + `L0-W-015`), L4 = 5 (3 actions +
`L0-D3-006` + `L0-D3-008`), L1 = 4 (`L0-D3-009`, `L0-W-016`, `L0-W-017`, `L0-D2-015`), L6 = 2,
L5 = 1 (`L0-D2-040`), L0 = 1 (`L0-D2-041`). Total 28. **The authoritative per-row owner is the
generated JSON's `owner` field; §2.1–2.5 quote it.**

## 3. Unresolved boundary questions — 17, one disposition each

All 17 remain **open**. None is closed by this work: this work publishes *contracts and vocabulary*,
not decisions. The column "where it now surfaces in Lean" is the interface at which a lane meets the
question.

| UQ | Owner | Question (abridged) | Disposition | Where it now surfaces in Lean | Blocking |
|---|---|---|---|---|---|
| `UQ-001` | L1 | Must `Rel_D3` be cache-independent; is cold-cache the admitted statement? | **resolved 2026-10-29 (W08)** — the relation is the cold-cache statement; accepts and non-missing-code rejects are cache-independent for every hash-consistent cache, missing-code rejects stay rejects ([w08](../evidence/lean-chunk-completion/w08-warm-cache/README.md), `tools/d3/check_cache_independence.py`) | `Resolution.CacheMode`, `CacheEnv.determinedByClaim`, `coldCache_independent`, `validatorCache_not_independent` | Gate B |
| `UQ-002` | L1 + L7 | Can `e.code_cache` narrow to rolled-back deploys only? | **resolved 2026-10-29** — on allFeatures only the preparation-pipeline race remains cache-dependent; 279 `e.code_cache` cases 0 disagreements ([open-uqs](../evidence/lean-chunk-completion/open-uqs/README.md)) | `Resolution.CacheEnv`, `committedCache`, `validatorCache_not_admitted` | Gate B |
| `UQ-003` | L2 | Which NaN payload/sign semantics does pinned Wasmtime produce; stable across architectures? | **resolved 2026-10-29** — results are the positive canonical NaN; 5,920 calls bit-identical x86_64/aarch64(QEMU)/Lean ([open-uqs](../evidence/lean-chunk-completion/open-uqs/README.md)) | `Config.ProtocolCfg.floats` (L2's float kernel) | Gate B |
| `UQ-004` | L3 | Are curve host gas schedules fully pinned at PV86 (no `86.yaml`)? | **resolved 2026-10-29** — PV86 uses the config stored at 85; 32/32 values agree Lean/YAML/snapshot ([open-uqs](../evidence/lean-chunk-completion/open-uqs/README.md)) | `HostDispatch.GasOrder`, `HostContract.gasOrder` | Gate B |
| `UQ-005` | L3 | Is the ML-DSA-65 trie key handle part of the pinned claim/trie model? | **resolved 2026-10-26** — the SHA3-256 handle (`PublicKey.handle`, tag 3) matches `core/crypto/src/signature.rs`; ML-DSA-65 keys and signatures are verified on every entry path and agree with nearcore on 533 honest chunks and 3,886 mutants ([mldsa-fixtures](../evidence/lean-chunk-completion/mldsa-fixtures/README.md)) | `ActionsReceipts.KeyForm.mlDsa65Handle`, `KeyForm.expectedLength` | Gate B |
| `UQ-006` | L4 | Which global-contract/state-init receipts appear in `source_receipt_proofs` at PV86; are distribution receipts in a chunk witness? | **resolved 2026-10-26** — distribution receipts do reach witnesses (incoming, delayed and buffered, including across a split); they are executed and routed, including to the child of a split target (`Successor/Routing.lean`) ([global-cache](../evidence/lean-chunk-completion/global-cache-fixtures/README.md), [resharding-2](../evidence/lean-chunk-completion/resharding-fixtures-2/README.md)). An obsolete target under a V2 layout stays out of domain (unreachable at PV86, see UQ-009) | `ActionsReceipts.GcdBody`, `DistReceipt`, `ShapeExclusion.globalContractDistribution` | Gate B |
| `UQ-007` | L4 | Is `LegacyEthWallet` still reachable at PV86 after `EthImplicitGlobalContract` (83)? | **resolved 2026-10-29** — unreachable at PV86; 7/7 wallet hashes match ([open-uqs](../evidence/lean-chunk-completion/open-uqs/README.md)) | `Resolution.ethWallet_kind_unreachable`, `IdentifierKind` | Gate B |
| `UQ-008` | L6 | Which witness carries a resharding transition; per-child-shard congestion info? | **resolved 2026-10-26** — the first child chunk carries `ImplicitTransitionParams::Resharding`; per-child congestion and `retain_split_shard` are modelled (`ReshardCore`, `TrieSplit`) and match nearcore on 2,920 real-split witnesses ([resharding](../evidence/lean-chunk-completion/resharding-fixtures/README.md), [resharding-2](../evidence/lean-chunk-completion/resharding-fixtures-2/README.md)) | `BoundaryFacts.EpochInputs.layouts`, `SplitInputs`, `ShapeExclusion.resharding` | Gate B |
| `UQ-009` | L9 + L6 | May a valid segment reference a PV85 epoch; both PV85/PV86 configs required? | **resolved 2026-10-26** — no: mainnet goes PV84 → PV86 directly (archival blocks 207,762,733 / 207,762,734), and `Successor/LayoutReach.lean` proves a layout change between PV86 epochs is a dynamic (V3) split; PV86-only configs suffice for the pinned target ([resharding-2](../evidence/lean-chunk-completion/resharding-fixtures-2/README.md)) | `Config.ProtocolCfg.protocolVersion`, `checkSuccessor_unsupported_pv` | Gate B |
| `UQ-010` | L1 | Which predicate is the statement of record: `checkD3` or `Wasm.DomainD3`? | `checkD3`/`RelD3` is the record (§3.1); `DomainD3` **retired 2026-10-29** and item-6 completeness moves recorded (§3.4); the `witness.bin` domain bound awaits a challenge decision (§3.4 (c)) | `Config.Tier.domainPredicate` (verdict-form, on the statement of record) | Gate B |
| `UQ-011` | L1 + L8 | Must Gate B remove the arena claim-size bounds, or is a larger versioned claim format acceptable? | **resolved for `allFeatures` 2026-10-26** — `c.segment`, `w.size` (8 MiB) and `c.layout` are lifted; nearcore's 64 MiB decode limit is kept and its 48 MiB compressed limit is approximated by the `w.compressed_size` exclusion (> 50,000,000 B). Narrower tiers keep their caps ([gate-b-caps](../evidence/lean-chunk-completion/gate-b-caps/README.md)) | `BoundaryFacts.ShapeExclusion.claimSize/witnessSize`, `permanentExclusions` | Gate B |
| `UQ-012` | L1 | Unbounded chunk function-call gas or a stated `G_α` capacity contract? | **resolved for `allFeatures` 2026-10-26** — `gasCap := none`: the 1 Pgas figure was nearcore's per-call `max_gas_burnt`, not a chunk rule; 1.8 Pgas chunks accept and match nearcore. Narrower tiers keep the cap (tier design) ([gate-b-caps](../evidence/lean-chunk-completion/gate-b-caps/README.md)) | `Config.ProtocolCfg.gasCap`, `ChunkAccounting.softLimitReached` | Gate B |
| `UQ-013` | L8 | What admission contract binds the trusted facts to the verifier's chain state? | **resolved 2026-10-30 by user decision: admission contract A1** — a proof for `claim.bin` is admitted only by a verifier that rebuilds the claim's trusted section (and `epoch_id`, `protocol_version`, `chain_id`) from its own chain state for `prev_block_hash` and finds it byte-identical; no relation change ([open-uqs](../evidence/lean-chunk-completion/open-uqs/README.md) §UQ-013) | `BoundaryFacts.FactAuthentication`, `BoundaryFact.obligation`, `genesisChunkExtra_requires_auth` | Gate B |
| `UQ-014` | L7 | Are Wasmtime `LoadingError`/`WasmUnknownError`/`LinkError` branches absent at PV86 or must they be modelled? | open — proof | `HostDispatch.HostErrorClass`, `HostContract.errorClass` | Gate B |
| `UQ-015` | L5 | Is `Σ|values| + 2000·R ≤ 4 000 000` sound when contract-storage removals are present? | **resolved 2026-10-29** — the bound is sound: recorded items come only from `base_state`; signed tier accepts no nearcore reject on 88 storage-limit fixtures ([open-uqs](../evidence/lean-chunk-completion/open-uqs/README.md)) | `TrieRecorder.ChunkAccounting.receiptExceeded`, `recorder_size_record_ge` | Gate B |
| `UQ-016` | L4 | Is the mock action log equivalent to `ReceiptManager` for every reachable shape? | **resolved 2026-10-29** — static check of all 30 action-log write sites; no unmodeled-log exclusion in 5,358 verdicts ([open-uqs](../evidence/lean-chunk-completion/open-uqs/README.md)) | `ActionsReceipts.ActV.raw`, `pActV_fallsThrough` | Gate B |
| `UQ-017` | L9 | For genesis main transition, which header comparisons apply; is `tx_valid` all-1? | **resolved 2026-10-29** — the genesis main transition uses the non-genesis header comparison set; 266/266 genesis-main chunks accept/accept ([open-uqs](../evidence/lean-chunk-completion/open-uqs/README.md)) | `Config.ProtocolCfg.genesisMainTransition`, `BoundaryFacts.GenesisInputs` | Gate B |

Every UQ's full text and "why" are in the generated JSON (`unresolved_boundary_questions`); this table
abridges the question and adds the disposition and Lean surface. **No UQ's disposition changed.**

### 3.1 UQ-010 — which predicate is the statement of record

The workplan asks W00 to "resolve which checker/predicate is the statement of record: `Wasm.DomainD3`
contains predicates disconnected from or stricter than actual dispatch." The inventory records the
question (`UQ-010`, owner L1). W00 makes the *API-level* call below and leaves L1's semantic
reconciliation open; this is a stated decision with sources, not a silent pick.

**Statement of record: `D3.checkD3` / `D3.RelD3`.** The executable definition is the statement, not the
`Wasm.DomainD3` predicates. Reasons, each with a source:

1. **It is the term the signed statement names and the proofs consume.**
   `checkD3` is defined at `spec/lean/v3/NearSpecV3/D3/FunctionCall.lean:400-401` as
   `checkD2Core (d3Hooks Wasm.pv86) true … (some gAlpha)`, and `RelD3 c w := checkD3 c w = .ok ()`
   (same file, line 403). The `Decidable` instance and the D3 proofs (`zk-formal` `Join/Fold.lean`,
   `Join/Coverage.lean`) consume *that* definitional form (`relD3_iff_acceptsD3`, same file).
2. **`Wasm.DomainD3` is not in `checkD3`'s import closure at all.**
   `D3/FunctionCall.lean:1-3` imports `D2.Receipts`, `ChunkValidationD2`, `Wasm.Exec` — never
   `Wasm.DomainD3`. `grep -rln "import NearSpecV3.Wasm.DomainD3"` over the tree returns only
   `NearSpecV3/ReshardingD3.lean`. So the `DomainD3` predicates cannot constrain the checker by
   construction; they are a parallel, unconnected statement.
3. **The actual domain guards are inline in `checkD2Core`.** The resharding exclusion the checker
   really applies is `c.same_layout` (`ChunkValidationD2.lean:140`) and `c.no_split_gate`
   (`ChunkValidationD2.lean:156`) — these are dispatch-time guards, not `noResharding`.
4. **`noResharding` is redundant, not contradictory.** `noResharding_iff_guards`
   (`ReshardingD3.lean:150-152`) proves `Wasm.DomainD3.noResharding c = true ↔ (sameLayout c ep ∧
   noSplitGate c)` whenever `ep ∈ c.epochs`; `checkD2Core` *requires* that membership via
   `c.epochs.find? (·.epochId == c.epochId)` (`ChunkValidationD2.lean:134`). So on in-domain claims
   the two agree; `checkD3 ⇒ noResharding` is a provable obligation (`L0-W-016`), not a conflict.
5. **`contractInD3α` *is* genuinely stricter — and the checker's reading wins.**
   `contractInD3α` (`DomainD3.lean:57-62`) rejects a contract that merely *imports* a curve host.
   Actual dispatch rejects curve hosts only when *called*: `contractOOD` decides floats at
   preparation and defers curve hosts to the run (`D3/FunctionCall.lean:63-69`), and `Wasm.runCall`
   states "under the trie-backed `External` (RuntimeD3) only *calling* one is" (`Wasm/Exec.lean:514-516`).
   So an import-only curve contract is accepted by `checkD3` and rejected by `contractInD3α`. The
   witness obligation is the import-only curve case (`L0-W-017`), and the fix direction is to
   *narrow* `contractInD3α` to "called", **not** to widen `checkD3` — widening would change the
   signed statement, which this work may not do.

**Consequence for the API.** `Config.Tier.domainPredicate` is stated on the *verdict* of the tier's
checker (`Successor/Config.lean:227-228`), i.e. on the statement of record, and its docstring records
that it is not proved equal to the `DomainD3` predicates. The two `DomainD3`-derived rows
(`L0-W-016`, `L0-W-017`) keep their `open — proof` disposition and L1 ownership; this subsection
supplies the direction each must be discharged in. It does **not** change either row's status, and it
does **not** edit `Wasm.DomainD3`, `checkD3`, `RelD3`, `gAlpha` or the oracle pins.

### 3.2 UQ-010 decision record — the SECP256K1 delegate strengthening (2026-10-26)

**Decision (user, recorded 2026-10-26): accepted.** The statement of record `D3.checkD3` / `D3.RelD3`
(§3.1) now verifies SECP256K1 delegate signatures, and the user accepts the resulting verdict moves
as a **strengthening of the signed statement**. Of the two options in the HANDOVER/workplan, this is
option (a). Option (b), re-isolating the signed layer behind its own delegate decoder, is not
pursued. Accepting the moves does not edit `checkD3`, `RelD3`, the oracle pins or any challenge. It
records that the term already on main (`4ae27c76e` and the high-s fix after it) *is* the signed
statement.

Why it moved: `D2.actDelegate` is shared by the signed and successor checkers (`checkD3 =
checkD2Core (d3Hooks …)` reaches `applyAction … .delegate d => actDelegate …`). The pre-widening
`e.secp` exclusion was that arm's `throw`, not an entry in `signedExclusions`. So verifying the secp
pair in that arm changes `checkD3`'s meaning.

**Population: 37 signed-tier verdict moves, all toward nearcore.**

| Moves | Population | Before → after (`--tier signed`) | nearcore |
|---|---|---|---|
| 35 `out_of_domain → accept` | the 3,138-case gap census: `nearcore == "ok" ∧ expected_rel_d3 == false` over `d3c7`–`d3c10` (898 / 1,376 / 429 / 435, from `d3/`, `mutants/` and `ood/`). All 35 lie in the 41-case SECP256K1 delegate set. | 2,438 OOD / 700 accept → **2,403 / 735** | `ok` for all 35 (it is the population filter) |
| 2 `reject → accept` | the two high-s secp256k1 delegate chunks of the key-family fixtures: `k6151 00-h10075-s1` (committed as `docs/evidence/lean-chunk-completion/key-family-fixtures/cases/00-h10075-s1`) and `k1618 00-h10077-s1`. They moved with the `s < n/2` fix in `Secp256k1.verify`. | `reject` (`invalid: MissingTrieValue (access key)`) → `accept`. Over the 2,925 selected key-family cases, signed went 572 / 636 / 1,717 → 574 / 636 / 1,715 (accept / OOD / reject): 2 moves, 0 other changes (`replay/full-signed-{main,fix}.json`). | cold nearcore accepts both |

**Reason: nearcore accepts all 37.** Every move goes from "not accepted" to "accepted" on a chunk the
pinned nearcore 2.13.4 validator accepts. None goes in the unsound direction (Lean accepts, nearcore
rejects), and no verdict on either population moves the other way.

**Reproduce the 35** (pinned corpora, read-only; run from the repository root after
`lake build nearspec-v3-check-successor` in `spec/lean/v3`):

```sh
python3 - <<'PY' > /tmp/gap3138.txt
import json, os
R = '/data/illia/nearproof-deps/corpora'
for c in ['d3c7', 'd3c8', 'd3c9', 'd3c10']:
    for sub in ['d3', 'mutants', 'ood']:
        for x in sorted(os.listdir(f'{R}/{c}/{sub}')):
            try: m = json.load(open(f'{R}/{c}/{sub}/{x}/meta.json'))
            except Exception: continue
            if m.get('nearcore') == 'ok' and m.get('expected_rel_d3') is False:
                print(f'{R}/{c}/{sub}/{x}')
PY
wc -l /tmp/gap3138.txt     # 3138
python3 tools/d3/replay_successor.py --tier signed --cases-file /tmp/gap3138.txt \
  --out /tmp/gap3138-signed --jobs 4
# current tree: {"verdicts": {"accept": 735, "out_of_domain": 2403}}
```

The "before" side (2,438 / 700) is the same command on a tree whose `actDelegate` secp arm is
restored to the `throw` and rebuilt. The committed pair is
`key-family-fixtures/replay/signed-gap3138-{before,after}.json`; across the high-s fix both read
2,403 / 735. **Reproduce the 2:** regenerate the `k6151`/`k1618` runs and select the cases as in
`key-family-fixtures/README.md` ("Generation"), then run `replay_successor.py --tier signed` over the
2,925 selected cases. Alternatively, replay the committed
`key-family-fixtures/cases/00-h10075-s1` alone.

Consequence: wherever a document says the widening is "successor-only" or "the signed tier is
unchanged", read it as superseded by this record.

### 3.3 Signed-tier valid-reject fixes 2026-10-27

**Decision (user, recorded 2026-10-27): accepted as a strengthening of the signed statement.** Before
this change, `D3.checkD3` / `D3.RelD3` (`--tier signed`) rejected four chunks that pinned nearcore
accepts and `allFeatures` accepts. A reject of a valid chunk on the statement of record is a bug.
This change edits Lean definitions on `checkD3`'s path. `oracle/v3-d3/src/**`, `challenges/**` and
the oracle pins are unchanged (`make pin-check` ok). Evidence:
[signed-valid-rejects](../evidence/lean-chunk-completion/signed-valid-rejects/README.md).

Two root causes. In both, the fix reuses the rule the successor tiers already apply:

1. **V3 bandwidth parent chaining** (`InvalidBandwidthRequests`, 1 case: `resharding-fixtures`
   `seed11-02-h10077-s2`). nearcore chains the buffer to `get_parent_shard_id(to_shard)` before the
   shard's own buffer (`runtime/runtime/src/congestion_control.rs:545-554`). That call always
   succeeds for a V3 layout (`shard_layout/mod.rs:253-272`, `shard_layout/v3.rs:344-354`). The legacy
   `D2.bandwidthRequests` now dispatches a V3 layout to `bandwidthRequestsV3`. `Logged.R_bandwidthRequestsV3`
   proves that it evaluates to what the recorder engine's `bandwidthRequestsV3L` (the `allFeatures`
   rule, now shared from `Logged/D2Queues.lean`) evaluates to. V2 layouts keep the previous body.
   Until this change, workplan item 4 recorded this case as a stated restriction of the signed
   statement. It is no longer one.
2. **Instance loading** (`main transition post state root`, 3 cases: `runtime-chunks-209`
   `runtime-above-43`, `runtime-mixed-71`, `runtime-targeted-1703`). The pooling allocator refuses a
   module whose instance exceeds 1 MiB (`near-vm-runner/src/wasmtime_runner/mod.rs:481-495`,
   `:744-745`), and the runtime turns that into a zero-gas failed call
   (`runtime/runtime/src/function_call.rs:328-330`). `Wasm.pv86` now sets `loadingLimits := true`,
   which is the same `runCallWithLimits` rule `allFeatures` runs. `checkD3`'s text is unchanged, and
   `signedCfg := { loadingLimits := true }` keeps `checkSuccessor_signed` and `signed_tier_rel_iff`
   definitional.

**Population and moves (`--tier signed`, before `b65fe05c…` on `b6b01df77`, after `87d7e13e…`).**

| Population | Before (accept / OOD / reject) | After | Moves | nearcore |
|---|---|---|---|---|
| 3,138-case gap census (§3.2) | 735 / 2,403 / 0 | unchanged | 0 | — |
| 577 committed fixture cases | 112 / 320 / 145 | 116 / 320 / 141 | 4 `reject → accept`: the four cases above | `ok` for all four |
| 235,716-case corpus (six corpora) | 73,577 / 2,758 / 159,381 | unchanged (verdict and reason) | 0 | — |

All four moves go toward nearcore. None goes in the unsound direction, and no out-of-domain count
changes. No corpus case has either root cause. The remaining signed rejects of nearcore-`ok`
corpus chunks are the 206 `d2corpus.v2` code-less witnesses (`MissingTrieValue (contract code)`),
an unrelated known population. Every narrower tier built from `signedCfg` inherits both fixes, as do
the legacy adapters (`checkD3F`, `checkD3Proto`, `checkD3G`, `checkD3Global`) and `checkD2` (bandwidth
only). `.runtimeLimits` and `.genesisFloatsProtoGas` now coincide.

**Reproduce** (from the repository root, after `lake build nearspec-v3-check-successor` in
`spec/lean/v3`):

```sh
B=spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor
E=docs/evidence/lean-chunk-completion
$B --tier signed $E/resharding-fixtures/cases/seed11-02-h10077-s2 \
  $E/runtime-chunks-209/cases/{runtime-above-43,runtime-mixed-71,runtime-targeted-1703}   # 4 x accept
$B --tier signed --ablate-loading-limits $E/runtime-chunks-209/cases/runtime-targeted-1703  # reject (control)
python3 tools/d3/replay_successor.py --tier signed --cases-file /tmp/gap3138.txt --out OUT --jobs 16
```

The "before" side is the same commands on `b6b01df77`.

**Follow-up, same day: V2 layouts with a parent map (soundness).** nearcore's
`get_parent_shard_id` also succeeds on a V2 layout that carries `shards_parent_map`
(`shard_layout/v2.rs:285-301`). On such a layout every request chains the parent's buffer, so an
unsplit shard requests its own buffer twice. Lean's V2 decoder dropped the map, so both engines
used the own-buffer rule. The case is reachable at PV86. Mainnet's static layouts from PV75 to PV81
are V2 with a parent map (`res/epoch_configs/mainnet/75.json`–`81.json`), and under the PV85/86
dynamic config an epoch without a split keeps the previous layout
(`chain/epoch-manager/src/lib.rs:693-707`). The decoder now keeps the map (`Layout.v2ParentMap`),
and both engines apply the rule (`bandwidthRequestsV2P` / `bandwidthRequestsV2PL`, related by
`Logged.R_bandwidthRequestsV2P`). A map without an entry for a layout shard is a named exclusion.
On a generated V2 parent-map chain (`yield-congestion-v2parent`, seed 102, 2,301 cases) the fix moves
21 (`signed`) / 24 (`allFeatures`) honest chunks from `reject` to `accept`, and 21 / 24
own-buffer-only header mutants from **`accept`** to `reject`: the pre-fix checker accepted chunks
nearcore rejects. No case of the census, the fixtures or the corpus carries a V2 parent map
(`tools/d3/claim_layout.py --summary`: 235,716 / 577 / 3,138 V2 without a map, or V3), and none moves.
[Evidence](../evidence/lean-chunk-completion/signed-valid-rejects/v2-parent-map/README.md).

### 3.4 UQ-010 signed-tier completeness, workplan item 6 (2026-10-29)

**Decision in force (user, 2026-10-27).** A signed-tier reject or exclusion of a valid chunk is fixed
as a strengthening of `checkD3`/`RelD3`, not kept as a stated restriction. This section records each
move made under that decision for workplan item 6. Evidence:
[signed-completeness](../evidence/lean-chunk-completion/signed-completeness/README.md).
`oracle/**` Rust sources, `challenges/**` and the oracle pins are unchanged (`make pin-check` ok, no pin
update needed: the pins cover the Rust oracle trees, not the Lean statement).

**The structural change.** The old body of `checkD3` is now `D3.checkD3Core` (`D3/FunctionCall.lean`).
`D3.checkD3` (`D3/Signed.lean`) is that core, except that a core *error* outside the core's two stated
preconditions is decided by the recorder engine that `allFeatures` uses (`checkReshardCore` /
`StorageExecution`), at the signed feature set (`Wasm.pv86`, `G_α`, clear `near-arena-witness-v3`,
8 MiB state witness, `c.segment`, `c.layout`; no floats, curve hosts or global actions). The two
preconditions are:

1. one shard layout and no split check: `c.same_layout` (both forms) and `c.no_split_gate`;
2. the storage-proof limits never trigger: the core's `w.size` storage-proof exclusion, or any core
   error on a witness whose values and code exceed 4,000,000 bytes (the core cannot accept such a
   witness, so its error is a premature exclusion).

Proved (only `propext`, `Classical.choice`, `Quot.sound`): `D3.checkD3_of_core_ok` (every core accept
is kept) and `D3.checkD3_cases` (`checkD3` is the core's result unless the core returned an error on
which the hand-over fires). `checkSuccessor signedRecordCfg = D3.checkD3` and
`checkSuccessor signedCfg = D3.checkD3Core` are both `rfl`. The narrower legacy tiers (`floats`,
`protoGas`, `genesis`, …) keep the core and its exclusions. The `TierMono` pairs that started at
`.signed` (`relSuccessor_protoGas_mono`, `relSuccessor_genesis_mono`,
`relSuccessor_signed_genesisProtoGas`) now start at `checkD3Core`, because the signed tier is wider
than `.protoGas`/`.genesis` on resharding claims. ChallengeChunkV3.lean gains one import line
(`D3.Signed`), because `RelChunkV3` names `D3.RelD3`; its text is otherwise unchanged.

| Sub-item | Disposition | Moves (all toward nearcore) |
|---|---|---|
| (a) resharding: layout change, buffer to a split parent, pre-split gate | **fixed** (hand-over, precondition 1) | 593 committed fixtures: 26 `OOD → accept`, 25 `OOD → reject` (nearcore rejects), 1 `OOD → OOD (e.g_alpha)`. Raw split runs (1,173 PV86 cases, 6 chains): 159 `OOD → accept`, 72 `OOD → reject`, 8 `OOD → OOD` (other exclusions). No case in any population reaches the buffer-to-split-parent form, so that form is covered by the rule and the proof, not by a fixture |
| (b) eval-time fuel | **fixed**: the signed engine uses `wasmFuel` (`Wasm/Fuel.lean`); `successorFuel_moves_only_exhausted` applies | 10 committed `fuel exhausted` fixtures: 6 `OOD → accept`, 4 `OOD → OOD (e.g_alpha)` |
| (c) `witness.bin` completeness bound (`ChallengeChunkV3.maxWitnessChunk`) | stopped 2026-10-29; **done 2026-10-30 by user decision**: `maxWitnessChunk` = 75,497,501 (`maxWitnessChunk_eq`); the v3.1 draft (`near-chunk-v3-1`, built by the item-11 builder with `spec/tools/near_chunk_v3_uq010.py`) raises `max_witness_bytes` and drops `c.same_layout`, `c.no_split_gate`, `e.secp` and the storage-proof clause of `w.size`; pin-check covers it. No published or signed file changed | — |
| (d) `Wasm.DomainD3` | **retired**: file deleted; `noResharding` moved to `ReshardingD3.lean` as a description of the core's guards; `contractInD3α` dropped (it excluded curve-host *imports*, which no checker does) | — |
| (e) found here: 26 valid-chunk **rejects** on `storage-limit-fixtures` (`MissingTrieValue`) | **fixed** (hand-over, precondition 2) | 26 `reject → OOD (e.g_alpha)` and 18 `OOD (w.size) → OOD (e.g_alpha)`: the chunks exceed `G_α`, a prover-capacity exclusion outside item 6. Regenerated storage-limit chains (3 shapes, 4,500 honest): 66 `reject → OOD`, 130 `OOD → OOD`; chain 0's 501 mutants: 55 valid `reject → OOD`, 4 `OOD → reject`, and 88 correct rejects → OOD (above `G_α`). **2026-10-30, user decision: `G_α` is lifted on the hand-over path** (`withReshardHandover` runs the recorder with no gas cap; the legacy core keeps it). Now every storage-limit fixture and mutant verdict matches nearcore: the 501 mutants are 99 accept / 402 reject, all agreeing, with 0 `reject → OOD` against the pre-item-6 checker; on 4 seeds (generator now honours `--seed`), 4 × 65 honest chunks move `OOD (e.g_alpha) → accept` |

Unchanged: the 3,138-case census (735 accept / 2,403 OOD before and after), shard 13 (944 / 279,
the 279 are floats), the corpus (235,716: 73,783 / 2,758 / 159,175 before and after, 0 moves). No population has a Lean accept of a nearcore reject,
before or after.

**(c), stopped.** The signed `near-chunk-v3` challenge (`chl_497bbbf1…`, trusted tree `66bba27e` at
`85adc6c0`) fixes the completeness domain in `ChallengeChunkV3.lean` as `∃ w, RelTier t c w ∧ |w| ≤
maxWitnessChunk = 67,108,864`, and its JSON caps a request witness at `max_witness_bytes =
12,582,912`. After this change an accepted signed witness can be `(4+21) + (4 + 8,388,608) +
67,108,864 = 75,497,501` bytes (8 MiB state witness plus a full 64 MiB `ContractCodeResponse`), so
the bound can exclude a code-heavy valid chunk from the completeness promise (soundness is not
affected). Proposed, not made: `maxWitnessChunk := 75497501` (or a per-tier bound, with
`Successor.allFeaturesWitnessBound` for `allFeatures`), and a new challenge version whose
`max_witness_bytes` is at least that bound and whose restriction list drops `c.same_layout`,
`c.no_split_gate`, the storage-proof clause of `w.size` and `e.secp`.

**Remaining signed exclusions of valid chunks, outside item 6** (3,138 census, after): `e.g_alpha`
847, ML-DSA keys 260, curve hosts (`ecrecover`) 245, legacy ETH wallet 210, in-chunk code cache 169,
floats 150, `c.not_genesis` 137, global-contract and state-init shapes ~303, non-ED25519 transaction
keys 79, `c.segment` 3. On mainnet shard 13, 279 of 1,223 chunks are excluded for floats. These are
recorded, not changed here.

**Move (f), 2026-10-30 (W12 O4): precondition 2 counts ContractData removals.** Found by the
`removal-soft` ground truth (`../evidence/lean-chunk-completion/tier-refinement-w12/README.md` §14.1,
§15): nearcore charges 2,000 B per ContractData removal in `main_storage_proof_size_soft_limit`, so
removals alone can make it defer receipts while the witness's values stay under 4,000,000 B; the core
then ran the deferred receipt and rejected the valid chunk (`MissingTrieValue`). Precondition 2 is now
`storageCrossed c w`: the witness's values and code **plus 2,000 · R** exceed 4,000,000 B, where `R =
recorderRemovals c w` is the ContractData removal count of the main transition of the signed recorder
engine run on the same claim and witness (`0` if that run stops earlier). `R` is a function of `(c, w)`
alone, independent of the core's result (no circularity), and is evaluated only on a core error whose
merged size alone does not decide. The narrower legacy tiers' `withStorageExclusion` uses the same
condition, so `.signed ⊑ .runtimeLimits/.floats/.genesisFloatsProtoGas` etc. keep holding (re-proved;
`checkD3_of_core_ok`, `checkD3_cases` unchanged in form, `handover` now takes the claim). The v3.1
draft's `w.size` restriction text says so. Removal-soft (7,296 cases, 4 seeds): 624 signed
`reject → accept` moves, all nearcore-valid; 956 nearcore rejects keep `reject` with the recorder's
reason; no Lean accept of a nearcore reject, no `reject → OOD`. Corpus, census, shard 13 and fixtures:
W12 README §15.

### 3.5 Rung decision record — `Rel_Dk := RelD3 ∧ InDk` (2026-10-30)

**Finding.** `D1 ⊂ D2` (and `D0 ⊂ D3`, `RelD1a ⊂ RelD3`) is false: D0/D1 never compare the
`epoch_start_after` flags with the headers, D2/D3 require `!isGenesis || flag = 1`
(`NearSpecV3.Examples.not_d1_sub_d2`, `not_d1a_sub_d3`, kernel-checked;
`docs/evidence/lean-chunk-completion/proof-debt/d1-genesis-flag/`). Not a nearcore-reject accept
(the witness is valid; the flag is a false trusted claim fact), but it made `WitnessLift` unprovable.

**Decision (owner, option 1).** The rungs of the `near-chunk-v3` statement are restrictions of the
top relation: `RelRungDk := RelD3 ∧ InRungDk` (`spec/lean/v3/NearSpecV3/RungsDefs.lean`), with
`InRungDk` the cumulative domain of the rung's own checker (no `out of domain …` verdict). The
statement is `NearSpecV3.RelChunkV3R` (`ChallengeChunkV3R.lean`, `relChunkV3R_iff : ↔ RelD3`), in
the **new draft** `challenges/drafts/near-chunk-v3-1.draft.json` (judge config
`runners/formal-checker/challenges/near-chunk-v3-1.json`, templates `spec/lean/judge/ExpectedChunkV3R*`).
The v3.0 draft, its module and every signed file are unchanged.

**What is proved.** `D0 ⊂ D1 ⊂ D2 ⊂ D3` for the rungs (projections, `rung_chain`); `WitnessLift`
over the D1a rung (`ZkFormal.PQ.Join.witnessLift`); the fast checkers are admitted by
`rungD2_of_checkD2` (alone) and `rungD{0,0a,1,1a}_of_checks` (with a `checkD2` accept). Checker-level
`D0 ⊂ D1` (`relD0_relD1`) and `D2 ⊂ D3` (`Successor.relD2_relD3`) stay; checker-level `D1 ⊂ D2` is
false (`not_d1_sub_d2`).

**Names kept.** `RelD0`, `RelD0a`, `RelD1`, `RelD1a`, `RelD2` keep their meaning (checker
acceptance): they are the statements of the separate D0/D0a/D1 challenges (the signed
`near-chunk-validation-d0` declares `NearSpecV3.RelD0`) and of the zk-formal D0a/D1a stacks, whose
soundness theorems are about the checkers. Redefining those names would change a signed statement's
meaning and those theorems' content; the rung relations are new names instead.

## 4. The schema decision W00 owes

The workplan asks for "a schema decision states which existing claim fields suffice, which need a
versioned extension, and how external facts are authenticated."

### 4.1 Existing `Claim` fields that suffice

`Claim` (`ClaimV3.lean:67`) already carries: `protocolVersion`, `chainId`, `epochId`, `chunkInner`,
`blocks`, `rsDataParts`, `rsTotalParts`, `epochs`, `epochStartAfter`, `applyFacts`, `txValid`,
`genesisChunkExtra`. Of these, the successor API reads — without extension:

| Fact | Claim field | Boundary-fact name |
|---|---|---|
| chain id | `chainId` | `BoundaryFact.chainId` |
| epoch validators | `epochs[].validators` | `BoundaryFact.epochValidators` |
| minimum stake | `applyFacts[].minimumStake` | `BoundaryFact.minimumStake` |
| tx validity flags | `txValid` | `BoundaryFact.txValid` |
| RS parameters | `rsDataParts`, `rsTotalParts` | `BoundaryFact.rsParams` |
| validator updates | `applyFacts[].validatorUpdate` | `BoundaryFact.validatorUpdate` |
| split gate | `applyFacts[].splitGate` | `BoundaryFact.splitGate` |
| genesis chunk extra | `genesisChunkExtra` | `BoundaryFact.genesisChunkExtra` |

`BoundaryInputs.ofClaim` (`BoundaryFacts.lean:185`) projects exactly these and is proved to preserve the
chain id, the epoch table and the *absence* of a lifted genesis extra (`ofClaim_chainId`,
`ofClaim_epochs`, `ofClaim_genesis_extra_absent`).

### 4.2 Fields needing a versioned extension

| Extension | Why | Owner |
|---|---|---|
| Global-contract identifier on action tags 9/10/11 | `Claim.applyFacts` has no global-contract field; the identifier lives in the *action*, decoded by `pActV` | L4 |
| Global-contract distribution body | `GcdBody` is not in the claim; UQ-006 leaves its witness representation open | L4 |
| ML-DSA-65 public-key handle | `D2/Types.lean:18` says the handle is not formalized; `KeyForm.mlDsa65Handle` types it but no claim field carries it | L3 / L5 |
| Resharding layout transition | no claim field carries a *transition*; `epochs[].shardLayout` carries per-epoch layouts only | L6 |
| Epoch protocol version ≠ 86 | `epochs[].protocolVersion` exists but `ChunkValidationD2.lean:125,139` require 86 for every epoch (UQ-009) | L9 |

**None of these extensions is added by this work.** They are named so a lane knows which claim field or
versioned extension it must add. Adding one is a claim-schema change and needs its own review.

### 4.3 How external facts are authenticated

`BoundaryFact` (`BoundaryFacts.lean:51`) splits facts into `external` and `computed`.
`BoundaryFact.obligation` gives each external fact a claim-v3 authentication obligation id, and
`obligation_nonempty` proves no obligation string is empty. `FactAuthentication` pairs a fact with its
obligation and `genesisChunkExtra_requires_auth` proves the genesis extra is external, i.e. it must be
authenticated rather than computed.

**No computed transition output is admitted as a fact**: `BoundaryFact.kind` marks `stateRoot`,
`outcomeRoot`, `gasUsed`, `balanceBurnt`, `outgoingReceiptsRoot`, `congestionInfo`, `bandwidthRequests`
and `validatorProposals` as `computed`, and `stateRoot_computed` proves it for the state root. The
authentication contract *ids* are typed; the admission contract itself is UQ-013 (L8) and stays open.

## 5. Success criteria — status against the workplan's four W00 criteria

| # | Criterion | Status | Evidence |
|---|---|---|---|
| 1 | Every inventory row and UQ has an owner, disposition, source justification and test obligation; unknown answers explicitly open and blocking Gate B | **partial — owner and disposition done for all 28+17; test obligations copied from the generated inventory; "blocks Gate B" stated per row** | §2, §3; generated JSON |
| 2 | The API contracts are written and compile with existing float/gas/genesis adapters | **met for signatures; NOT met for the default build target** | `lake build NearSpecV3.Successor` → 96 jobs green; but `lake build` (defaultTargets) does **not** reach the modules — see §6 |
| 3 | A schema decision states which claim fields suffice, which need an extension, how external facts authenticate; no computed result admitted as a fact | **met as a decision document; no schema change made** | §4 |
| 4 | The inventory generator's drift check passes and IDs are unique; static status and evidence distinguished; no relabelling | **met** | `--check` exit 0; no row status edited; no JSON written |

## 6. Verification-integrity finding: the default build does not cover these modules

This is a discrepancy W00 must report rather than hide. The workplan's verification step is
`cd spec/lean/v3 && lake build` and "must be green". It **is** green — but it is green *without compiling
the new modules*.

Measured facts (all reproducible):

1. `lakefile.toml` sets `defaultTargets = ["NearSpecV3", "nearspec-v3-check", "nearspec-v3-leaftest"]`.
   The first entry resolves to the *module* `NearSpecV3.lean`, not to the library's module glob.
2. `NearSpecV3.lean` imports 25 modules; its transitive closure is 74 modules. It does not import
   `NearSpecV3.Successor`.
3. `lake build` reports 184 jobs both before and after the eight modules were added.
4. **Injected-error test**: appending `#check thisDoesNotExistAtAll_xyz` to
   `Successor/Differential.lean` (and separately to `Successor/Config.lean`) and running `lake build`
   exited **0** with "Build completed successfully (184 jobs)". Deleting
   `Successor/Config.olean` and running `lake build` did **not** regenerate it. Both prove the default
   target does not reach the modules.
5. `lake build NearSpecV3.Successor` builds them: 96 jobs, exit 0. `lake build NearSpecV3.Successor.<M>`
   builds one module.
6. Pre-existing: 45 of 119 library modules have no `.olean` under the default build — this is not new
   and not caused by W00. The new modules are in good company, but that does not make the default
   build's green a verification of them.

**Consequence.** A CI gate that only runs `lake build` will not catch a regression in
`NearSpecV3/Successor/*.lean`. Until `lakefile.toml`'s `defaultTargets` changes (which W00 must not do —
it is integration-owner territory per the hard constraints), the honest verification command for these
modules is:

```
cd spec/lean/v3 && lake build NearSpecV3.Successor
```

**Exact edit needed, if the integration owner wants the default build to cover them** (W00 does not make
this edit): in `spec/lean/v3/lakefile.toml`, add `"NearSpecV3.Successor"` to `defaultTargets`, i.e.

```toml
defaultTargets = ["NearSpecV3", "NearSpecV3.Successor", "nearspec-v3-check", "nearspec-v3-leaftest"]
```

That is a one-line change to an integration-owner file. The alternative — importing
`NearSpecV3.Successor` from `NearSpecV3.lean` — is also integration-owner territory and would put the
successor in the signed root module's closure, which the hard constraints discourage. The
`defaultTargets` edit is the narrower one.

## 7. Axiom closure

Every `#print axioms` check point in the eight modules reports a subset of
`{propext, Classical.choice, Quot.sound}`. None reports `sorryAx` and none reports a custom axiom.
Twenty-one declarations are printed. **Five** depend on no axioms at all: `ActionTag.ofCode_code`,
`distReceipt_encode_layout`, `coldCache_lookup_none`, `permanentExclusions_eq`, `signedExclusions_covers`.
**Three** depend on `[propext]` only: `pActV_tag9`, `ethWallet_kind_unreachable`,
`signedExclusions_owner_consistent`. **One** depends on `[propext, Quot.sound]`: `summarise_complete`.
The remaining **12** add `Classical.choice` as well. 5 + 3 + 1 + 12 = 21; every set is within the allowed
`{propext, Classical.choice, Quot.sound}`.

No module uses `sorry`, `admit`, or `native_decide`. The grep hits for "sorry"/"admit" in the modules are
prose in docstrings, not tactic terms; `grep -n "sorryAx" ` over a clean rebuild of all eight modules
returns zero.

## 8. Next executable steps

1. **Integration owner**: decide the `defaultTargets` edit in §6 so CI covers the modules.
2. **L4**: close `L0-action-09/10/11` execution (decoders are done); close `L0-D3-006`, `L0-D3-008`.
3. **L3**: close the 14 unimplemented curve hosts and validate `ecrecover`/`p256_verify`.
4. **L1/L5/L6/L9**: discharge the proof/decision UQs each row names in §3.
5. **W13/W14**: consume `Differential.DiffResult`/`DiffSummary` so no lane can report agreement with a
   skipped or invalid case.
