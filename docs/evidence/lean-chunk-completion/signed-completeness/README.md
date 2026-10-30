# Signed-tier completeness, workplan item 6 / UQ-010 (2026-10-29)

Target: pinned nearcore 2.13.4 (`44f7ae6c`, PV86), run cold, is the ground truth. The decision in
force (user, 2026-10-27) is that a signed-tier exclusion or reject of a valid chunk is fixed as a
strengthening of the statement of record `D3.checkD3` / `D3.RelD3`. The decision record is
[`lean-chunk-w00-owner-map.md` §3.4](../../../research/lean-chunk-w00-owner-map.md#34-uq-010-signed-tier-completeness-workplan-item-6-2026-10-29).

Checker before: `a1627ea3…` (this branch's base, `4f07a7fdf`). Checker after: `1ebfae54…`.
Tool: `tools/d3/replay_successor.py --tier signed` (populations with `meta.json`) and a plain
batch runner for shard 13 (no `meta.json`; every chunk is nearcore-valid per its W13 report).

## Status per sub-item

| Sub-item | Status |
|---|---|
| (a) resharding: a layout change across the claim's epochs, a non-empty outgoing buffer to a split parent, and pre-split gating (`c.same_layout`, `c.no_split_gate`) | **fixed**, measured. The buffer-to-split-parent form occurs in no population (no case, before or after, reports it); it is covered by the hand-over rule and its proof only |
| (b) eval-time loops that exhaust the signed fuel budget | **fixed**, measured. The 4 that do not accept are now excluded for `e.g_alpha` (the chunk burns more than `G_α`), not for fuel |
| (c) the `witness.bin` bound of the completeness domain (`ChallengeChunkV3.maxWitnessChunk`) | **stopped**: it is a definition of the signed `near-chunk-v3` challenge. The proposed change is below |
| (d) `Wasm.DomainD3` | **retired** (file deleted, see below) |
| (e) found during this work: 26 nearcore-valid storage-limit fixtures **rejected** by the signed tier | **fixed**: no longer rejected. They are now excluded for `e.g_alpha` |

## The change

* `D3/FunctionCall.lean`: the old body of `checkD3` is renamed `checkD3Core`. The signed engine's Wasm
  fuel is `wasmFuel cfg gas` (`Wasm/Fuel.lean`, not edited here) instead of the legacy
  `(gas / regular_op_cost + 2) · 64 + 10⁶`. `Wasm.successorFuel_moves_only_exhausted` already proves
  that a call result can change only if it was `fuel exhausted` under the legacy budget.
* `D3/Signed.lean` (new): `checkD3 := withReshardHandover Wasm.pv86 (some gAlpha) (checkD3Core …)`.
  The legacy core keeps its result, unless that result is an error outside its two preconditions:
  1. **one layout, no split check**: the error is `out of domain (c.same_layout)…` or
     `out of domain (c.no_split_gate)`;
  2. **the storage-proof limits never trigger**: the error is the core's
     `out of domain (w.size): storage-proof…`, or the witness's values plus code exceed 4,000,000
     bytes. The core cannot accept such a witness, because its `w.size` check is necessary for
     acceptance.

  In those cases the claim is decided by the recorder engine at the signed feature set:
  `checkReshardCore` (or `checkD2CoreWith` on a segment that reaches genesis) with
  `reshardingDriver Wasm.pv86` and the clear witness format. The recorder models both storage-proof
  limits exactly and applies nearcore's 64 MiB code-response cap. It keeps the 8 MiB state witness,
  `c.segment`, `c.layout` and `G_α`.
* Proved: `D3.checkD3_of_core_ok` (a core accept is kept) and `D3.checkD3_cases` (the only results
  that change are core errors on which the hand-over fires). Both use only `propext`,
  `Classical.choice` and `Quot.sound`.
* `Successor/Config.lean`: `ProtocolCfg.reshardHandover` (default `false`) and
  `signedRecordCfg := { signedCfg with reshardHandover := true }` is `Tier.cfg .signed`.
  `checkSuccessor_signed` (`= D3.checkD3`) and `checkSuccessor_signedCore` (`signedCfg ↦ D3.checkD3Core`)
  are `rfl`. The narrower legacy tiers keep the core.
* `TierMono`: `checkSuccessor_gas_mono`, `checkSuccessor_genesis_mono`, `Lift.gas` and `Lift.gateB`
  take `reshardHandover = false`. The named pairs that started at `.signed` now start at
  `checkD3Core`, because the signed tier is wider than `.protoGas`/`.genesis` on resharding claims.
* `zk-formal` (`Join/Fold`, `Join/Coverage`, `Join/Compose`, `Join/Statement`): the join reaches
  `RelD3` through `checkD3_of_core_ok`. The two "premise ⇔ conclusion" theorems are now stated on the
  core, because `RelD3` is wider than its core.
* `MainSuccessor`: `--ablate-reshard-handover` is the deliberate-breakage control (it gives the legacy
  core). `tools/d3/smoke_successor.py` asserts two honest split chunks accept, their two mutants
  reject, and the ablation excludes all four.
* `ChallengeChunkV3.lean` gains one import (`NearSpecV3.D3.Signed`), because `RelChunkV3` names
  `D3.RelD3`. Its text is otherwise unchanged.

## Measured (`--tier signed`), before → after

| Population | Before (accept / OOD / reject) | After | Moves | vs nearcore after |
|---|---|---|---|---|
| 3,138-case gap census | 735 / 2,403 / 0 | 735 / 2,403 / 0 | 0 | — |
| 593 committed fixture dirs | 124 / 320 / 149 | 150 / 269 / 174 | 26 `OOD → accept` (`ok`), 25 `OOD → reject` (nearcore rejects), 1 `OOD → OOD (e.g_alpha)` | 0 disagreements (before: 0) |
| 338 fixtures extracted from `cases.tar.gz` (fuel, eval-time, gate-B caps, cross-family, runtime-errors, storage-limit) | 55 / 134 / 149 | 61 / 154 / 123 | 6 `OOD (fuel) → accept`; 4 `OOD (fuel) → OOD (e.g_alpha)`; 26 `reject → OOD (e.g_alpha)` (all nearcore `ok`); 18 `OOD (w.size) → OOD (e.g_alpha)` | 0 disagreements (before: **26 valid rejects**) |
| raw split runs `fa0–fa2`, `fb0–fb2` (seeds 11, 23; 6 chains; PV86 only: 1,087 honest + 86 nearcore-judged mutants) | 889 / 272 / 12 | 1,048 / 41 / 84 | 159 `OOD → accept`, 72 `OOD → reject` (nearcore rejects), 8 `OOD → OOD` (`e.g_alpha`, ML-DSA, hosts) | 1,132 decided, 1,132 agree |
| regenerated storage-limit chains (`storage-limits`, chain index 0/1/2 = 4/5/6 shards; 1,200 + 1,500 + 1,800 honest, all nearcore `ok`) | 4,062 / 372 / 66 | 4,062 / 438 / 0 | 66 `reject → OOD (e.g_alpha)` (23 + 21 + 22), 130 `OOD (w.size) → OOD (e.g_alpha)` | 0 rejects of valid chunks (before: 66) |
| … its 501 nearcore-judged mutants of the 65 hand-over chunks (446 nearcore reject, 55 nearcore `ok`) | 0 / 116 / 385 | 0 / 255 / 246 | 55 `reject → OOD (e.g_alpha)` on nearcore-`ok` mutants; **88 `reject → OOD (e.g_alpha)` on nearcore-rejected mutants**; 4 `OOD → reject` (nearcore rejects); 112 `OOD (w.size) → OOD (e.g_alpha)` | 246 rejects, all nearcore rejects; 0 accepts; 0 disagreements (before: 55 valid rejects) |
| mainnet shard 13 (1,223 chunks, all nearcore-valid) | 944 / 279 / 0 | 944 / 279 / 0 | 0 | the 279 are floats |
| 235,716-case corpus (six corpora) | 73,783 / 2,758 / 159,175 | identical (verdict and reason) | 0 | 232,958 decided, all agree with `meta.json` |

Per-case moves: `moves-*.jsonl` (paths: repo-relative, `cases.tar.gz:<family>/…`, `raw-reshard:<run>/…` = the `fa*/fb*` runs of `resharding-fixtures`, `storage-limits-gen:<dir>/…` = regenerated chains, not committed); counts: `summary.json`.

On this base, the corpus replay reports no compared disagreement before or after (112,036 compared, all agree). The 206 `d2corpus.v2` code-less rejects described in the workplan are not reproduced here: other merges since then, not this change, removed them.

**No population has a Lean accept of a nearcore reject, before or after.** Every move goes toward
nearcore. There are three kinds: `OOD → accept` on a valid chunk, `OOD → reject` on a nearcore
reject, and, on the storage-limit chunks, `reject → OOD` on a valid chunk. The last removes a wrong
verdict, but the chunk is still not accepted, because it burns more than `G_α`. `G_α` is the
signed tier's prover-capacity exclusion and is outside item 6. The same chunks accept on
`storageResolution` and `allFeatures` ([storage-limit-fixtures](../storage-limit-fixtures/README.md)).

**A rule exception, stated.** The workplan rule allows only `OOD → accept` and `reject → accept`
moves. On the storage-limit mutants this change also moves **88 correct rejects to `OOD`**. Those
mutants are above the legacy core's storage bound and burn more than `G_α`, so the recorder excludes
them for `e.g_alpha` before comparing post-state roots. In this family the legacy core cannot tell
its 55 wrong rejects of nearcore-valid mutants (`code.duplicate`, `code.extra_*` and similar) from its
correct ones. Both kinds fail with `MissingTrieValue` because the witness is legitimately partial.

Removing the wrong rejects therefore costs the correct ones, unless `G_α` is lifted on the hand-over
path. That would widen the signed statement beyond item 6 and needs a decision. No accept moved in
either direction.

**Seeds.** The split runs cover 6 chains from 2 generator seeds. The `storage-limits` scenario is a
quiet chain and does not depend on the seed: seeds 103, 105, 107 and 109 produced byte-identical
cases, so it counts as one seed. Only the chain index varies it (4/5/6 shards), and three chain
shapes were measured. The storage-limit family therefore does **not** meet the ≥ 4-seed rule.
Mutants were replayed for chain 0 only. A mutant replay costs several minutes per case on the
loaded host (both engines run).

## Deliberate-breakage controls

* `--ablate-reshard-handover` (the legacy core) restores the before verdict on every hand-over case.
  It is asserted by `make d3-smoke` on four committed split fixtures.
* Fuel: the before checker, with the legacy budget, puts the 10 fuel fixtures back out of domain.
* The negatives: 25 + 72 nearcore-rejected split mutants (`InvalidChunkHeaderShardSplit`, child
  post-state root, `retain_split_shard` with a dropped node) are now rejected rather than excluded. A
  hand-over that skipped the split check or the child root would accept them.

## (c) Stopped: the proposed change

The signed `near-chunk-v3` challenge (`challenges/chl_497bbbf1a6a5abc5b3448e0bc1a56997.json`, trusted
tree `66bba27e` at `85adc6c0`) defines the completeness domain as
`∃ w, RelTier t c w ∧ |w| ≤ maxWitnessChunk` with `maxWitnessChunk = 67,108,864`
(`ChallengeChunkV3.lean:91`). Its JSON caps a request witness at `max_witness_bytes = 12,582,912`.

* Before this change, the core's 4,000,000-byte `w.size` bound already kept accepted code to
  ≤ 4 MB, so the 64 MiB bound excluded no accepted chunk.
* After it, a witness past that bound is decided by the recorder engine. An accepted signed
  `witness.bin` can then be `(4 + 21) + (4 + 8,388,608) + 67,108,864 = 75,497,501` bytes: an 8 MiB
  state witness plus a full 64 MiB `ContractCodeResponse`.
* So the domain bound can drop a code-heavy valid chunk from the completeness promise. Soundness is
  not affected.

Proposed:

1. `maxWitnessChunk := 75497501`, or a per-tier bound, with `Successor.allFeaturesWitnessBound` for
   `allFeatures`.
2. A new challenge version with `max_witness_bytes ≥` that bound, and a restriction list that drops
   `c.same_layout`, `c.no_split_gate`, the storage-proof clause of `w.size` and `e.secp`. These no
   longer restrict `RelD3`.

## (d) `Wasm.DomainD3` retired

It was outside `checkD3`'s import closure. Its two predicates both disagreed with the statement of
record:

* `noResharding` is now false on claims `checkD3` decides.
* `contractInD3α` excluded a contract that merely *imports* a curve host. Dispatch excludes only a
  call.

`noResharding` and its spec moved to `ReshardingD3.lean`, where its theorems already were. It is
documented there as the legacy core's guards. `contractInD3α` was deleted. The imports of
`ReshardingD3.lean` and `oracle/wasm-d3/lean/Main.lean` (which used nothing from the module) were
updated. `tools/d3/lean_chunk_coverage.py` now reads `noResharding` from `ReshardingD3.lean` and no
longer lists `contractInD3alpha`. The coverage JSON is left for the integrator to regenerate.

## Reproduce

```sh
cd spec/lean/v3 && lake build nearspec-v3-check-successor && cd ../..
B=spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor
E=docs/evidence/lean-chunk-completion/resharding-fixtures/cases
$B --tier signed $E/seed23-02-h10062-s5 $E/seed11-00-h10048-s2-h.proposed_split_forged   # accept, reject
$B --tier signed --ablate-reshard-handover $E/seed23-02-h10062-s5                          # out_of_domain
python3 tools/d3/replay_successor.py --tier signed --cases-file LIST --out OUT --jobs 4
# storage-limit chain: NEAR_SUCCESSOR_SCENARIO=storage-limits $G gen --domain d3 --seed 103 --chains 1 \
#   --blocks 300 --p-missing 0 --mutate-every 10 --code-mutant-p 0 --ood-cap 100000 --out s103
```
