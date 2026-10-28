# Signed-tier completeness (item 6): the statement of record on the successor engine (2026-10-27)

Workplan item 6 listed four ways the signed tier (`--tier signed`, then `checkD3`/`RelD3`) excluded
valid chunks: (a) resharding (`c.same_layout`, `c.no_split_gate`), (b) eval-time loops that
exhausted the signed fuel budget, (c) the 64 MiB `witness.bin` bound of `ChallengeChunkV3`, and
(d) `DomainD3` reconciliation. The user decided (2026-10-27) that signed-tier rejects and
exclusions of valid chunks are fixed, not kept as restrictions. Measuring the signed tier on every
committed fixture before starting also found **26 signed rejects of nearcore-accepted chunks**
(`storage-limit-fixtures`: `StorageInconsistentState(MissingTrieValue)`, `MissingTrieValue
(promise yield timeout)`, `MissingTrieValue (account)`). They come from the legacy engine, which
has no model of nearcore's storage-proof limits, and were not on the item-6 list.

Target: nearcore 2.13.4 (`44f7ae6c`), PV86. Checker before: `a1627ea3…` (main `7c94cbd3d`).
Checker after: `checker-after2` of this branch (`summary.json` has every sha256). The decision
record is [`lean-chunk-w00-owner-map.md` §3.4](../../../research/lean-chunk-w00-owner-map.md#34-the-statement-of-record-moves-to-the-successor-engine-2026-10-27).

## The change

* **`RelD3S`, the statement of record** (`Successor/Record.lean`). The D3α feature set on the
  engine the successor tiers already use: the recorder runtime (`StorageExecution.run`),
  `ReshardCore` for every non-genesis segment, and the genesis-capable shell otherwise. The Wasm
  configuration is `Wasm.pv86` with the pinned loading rule. The D3α feature exclusions stay
  declared exclusions: floats, curve hosts, global actions, ML-DSA and non-ED25519 keys, the `G_α`
  per-chunk gas bound, the 32-block segment, the 8 MiB in-the-clear witness and 64 shards. The
  witness can be in the clear or compressed as distributed, with nearcore's 48 MiB / 64 MiB limits
  and the code-response cap, exactly as on `allFeatures`.
* **Config.** `signedCfg := { d3aCfg with storageResolution := true, resharding := true }`, and
  `checkSuccessor_signed : checkSuccessor signedCfg = checkD3S` is `rfl`. The previous
  configuration is `d3aCfg`, which is `Tier.d3a` (`--tier d3a`) with `checkSuccessor_d3a :
  … = D3.checkD3` (`rfl`). The narrow tiers are still built from `d3aCfg`, so they do not move.
* **Challenge** (`ChallengeChunkV3.lean`). A new rung `.d3s` (rank 6), with `RelTier .d3s =
  RelD3S` and `RelD3S` as a fifth disjunct of `RelChunkV3`. `.d3a` is still `RelD3`, unchanged, so
  the `zk-formal` joins, `Examples/RealCaseD3` and the reexec artifact (which states
  `RelTier .d3a = RelD3` by `rfl`) are untouched.
* **(b) fuel.** `D3.functionCall` (and its logged mirror) uses `Wasm.wasmFuel` in place of the
  legacy `64·` budget. `Wasm/Fuel.lean` proves that this moves only fuel-exhausted results. The
  recorder engine of `RelD3S` already used `wasmFuel`.
* **(c) witness bound (signed encoding change).** `maxWitnessChunk` = 26 + 4 + 50,331,648 +
  67,108,864 = **117,440,542** (was 67,108,864): the framing, the 48 MiB encoded witness and the
  64 MiB code response. `Successor.Config` proves `maxWitnessChunk = allFeaturesWitnessBound`. The
  D3 tiers' proof cap is `maxProofBytesChunkV3 .d3a/.d3s = maxWitnessChunk`. The other tiers keep
  `maxProofBytesV3` = 64 MiB, so the D1a decision P-D1-5 and `zk-formal` `ModelTier` are
  unaffected. The draft `challenges/drafts/near-chunk-v3.draft.json` carries the new bound in
  `claim_encoding.max_witness_bytes` and `resource_limits.max_proof_bytes`, and adds the D3S
  coverage tier. `make pin-check` is ok and needed no new pin: it pins the generator specs and
  oracle sources, and neither changed.
* **(d) `DomainD3`.** `contractInD3α` no longer excludes a contract that only *imports* a curve
  host. No checker does that: a curve host is excluded when it is called, at run time
  (`contractInD3α_iff`). `noResharding` is documented as the `.d3a` rung's guard
  (`ReshardingD3.noResharding_iff_guards`); `RelD3S` has no resharding exclusion.
* **Deliberate-breakage control.** `--ablate-output-checks` (signed only) runs `checkD3SAblated`,
  which skips every comparison against a produced value.

## Measured (`tools/d3/replay_successor.py --tier signed`)

| population | before (accept / OOD / reject) | after | moved | to accept (all nearcore `ok`) | Lean accept of a nearcore reject | accept lost |
|---|---|---|---|---|---|---|
| 931 fixtures (every committed case dir and case tarball) | 179 / 454 / 298 | **216 / 418 / 297** | 113 | 37 | **0** | 0 |
| 3,138 gap census | 735 / 2,403 / 0 | **1,082 / 2,056 / 0** | 379 | 347 | **0** | 0 |
| resharding raw runs, 1,700 PV86 cases (seeds 11, 23, 37, 41, 51) | 1,251 / 431 / 18 | **1,494 / 52 / 154** | 398 | 243 | **0** | 0 |

What moved, on the fixtures (`fixture-moves.jsonl`):

| before | after | cases | nearcore |
|---|---|---|---|
| OOD `c.same_layout` / `c.no_split_gate` | accept | 26 | ok |
| OOD `c.same_layout` / `c.no_split_gate` | reject (`InvalidChunkHeaderShardSplit`, split post root, `retain_split_shard`) | 25 | reject |
| OOD `fuel exhausted` | accept | 6 | ok |
| OOD `fuel exhausted` | OOD `e.g_alpha` (300 Tgas calls) | 4 | ok |
| OOD ETH-implicit with a local contract | accept | 5 | ok |
| **reject** `MissingTrieValue` (storage-limit fixtures) | OOD `e.g_alpha` | 26 | ok |
| OOD `w.size` storage-proof overestimate | OOD `e.g_alpha` | 18 | ok |
| OOD `c.no_split_gate` / ETH-implicit local contract | OOD `e.g_alpha` | 2 | ok |
| reject `slot count` | reject `shard not in layout` | 1 | reject |

After the change no fixture has a signed reject of a nearcore-accepted chunk; before, 26 did. The
26 storage-limit chunks and 18 more are now excluded only by the declared D3α gas bound `G_α`
(chunk function-call gas above 3.45 Tgas), which is a prover-capacity bound of the D3α feature set.
In the gap census the 347 new accepts are 178 ETH-implicit accounts with a local contract and 169
pre-state contracts served by an in-chunk deploy (the recorder engine's resolution, as on
`storageResolution`).

**Resharding raw runs.** The runs were regenerated with the `reshard` generator: seeds 11 and 23
(three chains each, as in `resharding-fixtures`), 51 (the threshold gates `t1` and `t2` of
`resharding-fixtures-2`), and 37 and 41 (single splits, variants 1 and 2). Each run's cases are
nearcore cold verdicts; the generator's own split and layout mutants are included. Several runs
were cut short by the host's load; every case they wrote is complete and cold-judged. After the
change: 1,494 of the 1,544 honest chunks are accepted, and the other 50 are D3α feature
exclusions (31 `G_α`, 10 `ecrecover`, 4 ML-DSA keys, 3 promise-action hosts, 2 floats). 154 of the
156 mutants are rejected; the other 2 are `G_α` exclusions. There are 0 disagreements.

**Control.** With `--ablate-output-checks` all 18 `w.split_child_post_root` mutants are
*accepted* (nearcore rejects them), and every honest verdict is unchanged. So the mutants detect a
missing produced-value check. The other mutants are still caught by independent checks
(`InvalidChunkHeaderShardSplit`, layout and retention).

**`d3a` (the old signed checker with `wasmFuel`).** On the fixtures it moves only the 10
fuel-exhausted cases (6 to accept, 4 to `G_α`). Everything else is identical to the old signed
tier.

## Corpus

See `summary.json` (`corpus`, when present) and owner map §3.4 for the 235,716-case run.

## Reproduce

```sh
cd spec/lean/v3 && lake build nearspec-v3-check-successor && cd ../..
B=spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor
python3 tools/d3/replay_successor.py --binary $B --tier signed --cases-file LIST --out OUT --jobs 12
$B --tier signed --ablate-output-checks CASE...     # breakage control
$B --tier d3a CASE...                               # the D3α rung (RelD3)
near-arena-oracle-v3-successor reshard --seed 11 --chains 1 --first-chain {0,1,2} --blocks 80 --out fa$i
near-arena-oracle-v3-successor reshard --seed 23 --split-k 2 --chains 1 --first-chain {0,1,2} --blocks 80 --out fb$i
near-arena-oracle-v3-successor reshard --seed 37 --chains 1 --first-chain 0 --variant 1 --blocks 80 --out c37
near-arena-oracle-v3-successor reshard --seed 41 --chains 1 --first-chain 0 --variant 2 --blocks 80 --out c41
near-arena-oracle-v3-successor reshard --seed 51 ... (t1, t2: resharding-fixtures-2 README)
```
