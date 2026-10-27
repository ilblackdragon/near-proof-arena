# Signed-tier valid-reject fixes (2026-10-27)

Before this change the statement of record (`D3.checkD3` / `D3.RelD3`, `--tier signed`) rejected four
chunks that pinned nearcore 2.13.4 (`44f7ae6c`, PV86) accepts and that `--tier allFeatures` accepts.
A reject of a valid chunk on the signed statement is a completeness bug. Both root causes are now
fixed by reusing the rule `allFeatures` already applies. The decision record is
[`lean-chunk-w00-owner-map.md` §3.3](../../../research/lean-chunk-w00-owner-map.md#33-signed-tier-valid-reject-fixes-2026-10-27).

| Case | Before (`signed`) | After | nearcore | Root cause |
|---|---|---|---|---|
| `resharding-fixtures/cases/seed11-02-h10077-s2` | `invalid: InvalidBandwidthRequests` | accept | ok | V3 bandwidth parent chaining missing in the legacy engine |
| `runtime-chunks-209/cases/runtime-above-43` | `invalid: main transition post state root` | accept | ok | instance-loading rule (`LoadingError`) missing from `Wasm.pv86` |
| `runtime-chunks-209/cases/runtime-mixed-71` | same | accept | ok | same |
| `runtime-chunks-209/cases/runtime-targeted-1703` | same | accept | ok | same |

## Root causes

To isolate each cause, the tiers were run one flag at a time. `genesisFloatsProtoGas → runtimeLimits`
differ only in `loadingLimits`, and that step moves the three runtime chunks from reject to accept.
`runtimeLimits → storageResolution` differ only in the engine (legacy `applyNewChunkD2` against the
recorder `StorageExecution.run`), and that step moves the resharding chunk.

1. **Bandwidth requests on a V3 layout.** nearcore's `generate_bandwidth_request`
   (`runtime/runtime/src/congestion_control.rs:526-566`) chains the buffer to
   `shard_layout.get_parent_shard_id(to_shard)` ahead of the shard's own buffer (`:545-554`). For a V3
   layout `get_parent_shard_id` always succeeds (`core/primitives/src/shard_layout/mod.rs:253-272`;
   `ShardLayoutV3::try_get_parent_shard_id`, `shard_layout/v3.rs:344-354`). It returns the split
   parent for a child of the latest split and the shard itself otherwise, so every other shard
   requests its own buffer twice. The recorder engine already modelled this rule
   (`bandwidthRequestsV3L`, added for the resharding fixtures). The legacy `D2.bandwidthRequests`,
   which `checkD3` uses, did not.
2. **Instance loading.** The pinned validator configures Wasmtime's pooling allocator
   (`runtime/near-vm-runner/src/wasmtime_runner/mod.rs:481-495`, 1 MiB core instance size) and maps
   a module that does not fit to `VMRunnerError::LoadingError` (`:744-745`). The runtime turns that
   into a zero-gas failed call (`runtime/runtime/src/function_call.rs:328-330`, `nop_outcome`). Lean
   models this as `Wasm.runCallWithLimits` under `NearCfg.loadingLimits`, and every tier from
   `runtimeLimits` up set it, but `Wasm.pv86` (and so `checkD3`) did not. The signed checker
   therefore ran a module nearcore refuses to load, and the post-state root diverged.

## The change (Lean only; `oracle/v3-d3/src/**` and `challenges/**` are untouched)

* `D2/Queues.lean`: `bandwidthRequests` dispatches on `layout.lastSplit`. A V3 layout gets the new
  `bandwidthRequestsV3`, the recorder rule written in the legacy monad. A V2 layout gets
  `bandwidthRequestsV2`, the previous body, unchanged.
* `Logged/D2Queues.lean`: `bufferSizesL` and `bandwidthRequestsV3L` moved here verbatim from
  `Successor/StorageExecution.lean`, so the recorder (`bandwidthRequestsR`) and the logged legacy
  mirror (`bandwidthRequestsL`) call the same definition. The recorder's behaviour is unchanged:
  the moved definitions are identical, and the only edit is the rename of its V2 branch.
* `Logged/D2QueuesSpec.lean`: `R_bufferSizes`, `R_bandwidthRequestsV2` and `R_bandwidthRequestsV3`
  are proved. `R_bandwidthRequestsV3` states that the signed engine's V3 rule evaluates to exactly
  what the recorder's `bandwidthRequestsV3L` evaluates to on the same state (`R`, `Logged/LM.lean:65`).
  `R_bandwidthRequests` re-proves the full dispatch.
* `Wasm/Prepare.lean`: `pv86 := { loadingLimits := true }`. The text of `checkD3`
  (`checkD2Core (d3Hooks Wasm.pv86) …`) is unchanged, so the `zk-formal` join proofs that name
  `Wasm.pv86` need no edit. `Successor/Config.lean`: `signedCfg := { loadingLimits := true }`, so
  `checkSuccessor_signed` and `signed_tier_rel_iff` stay `rfl` / `Iff.rfl`. The rule is the same
  function, `runCallWithLimits`, with the flag `allFeatures` sets.
* `Wasm/Exec.lean`: the old `runCallWithLimits_signed` (`rfl`, "loading checks absent from the signed
  configuration") is false now. It is replaced by `runCallWithLimits_noLimits` (with the flag off,
  the function is `runCall`) and `pv86_loadingLimits`.
* `MainSuccessor.lean`: `--ablate-loading-limits` switches the rule off. It is a deliberate-breakage
  control only, because no tier lacks the rule any more. `tools/d3/smoke_successor.py` uses it in
  place of `genesisFloatsProtoGas`, and also asserts that `signed` accepts the four runtime chunks.

Side effects, all in the same direction: every tier built from `signedCfg` (`floats`, `protoGas`,
`floatsProtoGas`, `genesis`, `genesisFloatsProtoGas`) inherits both fixes, so `runtimeLimits` and
`genesisFloatsProtoGas` are now the same configuration. The legacy adapters `checkD3F`,
`checkD3Proto`, `checkD3G` and `checkD3Global` inherit them too. `checkD2` (D2's `applyNewChunkD2`)
inherits the bandwidth fix.

**Follow-up (same day): V2 layouts with a parent map.** nearcore applies the same parent chaining
on a V2 layout that carries `shards_parent_map`. Lean dropped the map, so both engines accepted
own-buffer-only headers that nearcore rejects (a soundness bug). This is fixed in both engines and
measured on a generated V2 parent-map chain in [v2-parent-map/](v2-parent-map/README.md).

## Measured (`--tier signed`, `tools/d3/replay_successor.py --jobs 16`)

Before: `b65fe05c…` (main `b6b01df77`). After: `87d7e13e…`. Full counts are in `summary.json`, and
the four moved fixture rows are in `fixture-moves.jsonl`.

| Population | Before (accept / OOD / reject) | After | Moved | Direction |
|---|---|---|---|---|
| 3,138-case gap census | 735 / 2,403 / 0 | 735 / 2,403 / 0 | 0 | — |
| 577 committed fixtures | 112 / 320 / 145; 4 compared-disagree | 116 / 320 / 141; 0 compared-disagree | 4 (`reject → accept`, all nearcore `ok`) | toward nearcore |
| 235,716-case corpus | 73,577 / 2,758 / 159,381 | identical | 0 (verdict and reason string) | — |

The out-of-domain counts did not change on any population. No other valid-chunk reject in the
corpus has either root cause. The only signed rejects of nearcore-`ok` corpus chunks are 206
`d2corpus.v2` cases with `invalid: MissingTrieValue (contract code)`: witnesses that carry no
code, whose `ok` is the producer's verdict. That is the same population `allFeatures` rejects
(224), with an unrelated cause.

## Reproduce

```sh
cd spec/lean/v3 && lake build nearspec-v3-check-successor && cd ../..
B=spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor
E=docs/evidence/lean-chunk-completion
$B --tier signed $E/resharding-fixtures/cases/seed11-02-h10077-s2 \
  $E/runtime-chunks-209/cases/runtime-above-43 $E/runtime-chunks-209/cases/runtime-mixed-71 \
  $E/runtime-chunks-209/cases/runtime-targeted-1703            # 4 x accept
$B --tier signed --ablate-loading-limits $E/runtime-chunks-209/cases/runtime-targeted-1703   # reject
# populations (case lists: the gap census as in owner-map §3.2; fixtures = every committed case dir)
python3 tools/d3/replay_successor.py --tier signed --cases-file LIST --out OUT --jobs 16
```

Gates: `lake build` (default targets and exes), `make d3-smoke`, `make pin-check`, the coverage
check (regenerated: three source digests), `pytest oracle/tools tools/mainnet-replay`, and the
kernel non-vacuity `lake build NearSpecV3.Examples.RealCaseD3` (274 s, 20.7 GB peak; `RelD3` and
`Tier.rel .allFeatures` on the honest chunk and both negations on the mutant).
