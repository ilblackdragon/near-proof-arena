# Full computed observables against nearcore (W01), 2026-10-26

The successor checker now emits, per chunk, every execution outcome, every outgoing receipt and the
committed storage changes it computed. Each is compared field by field with nearcore's own values.
On 17,338 distinct graded chunks (generator runs plus 1,223 mainnet shard-13 chunks), **0 fields
mismatch**. **38,061 of 38,061** wrong-observable controls are reported as mismatches.

## 1. What Lean emits (`--emit-full` / `--blind-full`)

`nearspec-v3-check-successor --tier T --blind-full CASE...` (and `--emit-full`, which keeps every
header comparison on) prints a row with `"outputsVersion": 2`. The row's `outputs` holds every
version-1 key unchanged, plus the keys below. `--emit` / `--blind` are unchanged, so
`blind_inputs.py`, `blind_corpus.py` and `shard_replay.py` read the same rows as before.

| key | per item | source in Lean |
|---|---|---|
| `outcomes` | `id`, `executor`, `status` (`value` + return bytes / `receipt` + id / `failure`), `gasBurnt`, `tokensBurnt`, `logs`, `receiptIds`, `leaf` | `MainOutD2.outcomes`, the list `outcomeRootD1` merklizes |
| `outgoingReceipts` | `id`, `predecessor`, `receiver`, `kind`, `hash` = sha256(borsh body), `refund` (predecessor `system`) | the list the outgoing-receipts root commits to (post-reassignment across a split) |
| `stateChanges` | `key`, `valueHash`, `valueLen` (`null` = deleted), ascending raw key | `sortKV` of the main transition's committed `TrieUpdate` overlay at `finalize`, so rolled-back changes are absent |
| `computeUsage` | chunk total | the runtime's compute accumulator (`RS.compute`) |

Every value is computed by the checker. The claim and witness carry no per-outcome data. Under
`--blind-full` the produced header fields and the witness post-state roots are also zeroed
(`blind_inputs.blind_case`).

**Internal assertion.** `detailSelfCheck` (`MainSuccessor.lean`) recomputes from the emitted lists
the outcome root, Σ gas, the concatenated logs and the receipt count, and checks each against the
computed header-level value. A failure turns the row into `internal_error` and the exit code into 2.
None occurred. The comparator also recomputes, independently in Python, each outcome's leaf and the
merkle root from the *emitted* JSON fields of both sides. Lean's list and nearcore's list each hash
to the witness header's `prev_outcome_root` in every graded case (`recompute_failures` is empty in
every report).

**Lean edits.** These are observation only, and no check reads them:

* `Observable` gains four defaulted fields.
* `MainOutD2` gains `committed` / `compute`, both `Option`, `none` for the D2 runtime.
* `StorageExecution.applyNewChunkD2` fills them.
* The four `Observable` constructions fill them: `checkD2CoreObs`, the logged D2 checker,
  `checkD2CoreWithObs` and `checkReshardCoreObs`. They are kept syntactically parallel so that
  `legacy_core_eq` / `legacy_genesis_eq` stay `rfl`.

## 2. Expected values (nearcore)

* **Generator runs.** With `NEAR_SUCCESSOR_OBSERVABLES=1`, `oracle/v3-successor` (`gen` and
  `reshard`) writes `nearcore-observables-<chain>.jsonl` (`src/observables.rs`). Its own cold
  validator runtime pre-validates each honest witness with the needed code blobs and calls
  `apply_new_chunk(ValidateChunkStateWitness)`. Records hold the `ApplyChunkResult` outcomes
  (including `compute_usage`), outgoing receipts (reassigned with
  `ChainStore::reassign_outgoing_receipts_for_resharding` when the layouts differ, as
  `validate_chunk_state_witness_impl` does), `trie_changes.state_changes()` with every change's
  cause, and the producer's stored outcome ids. Records are bound to cases by
  sha256(`claim.bin`) and sha256(`witness.bin`). The variable does not touch the RNG: seed 7,
  30 blocks, `--mutate-every 10` gives byte-identical output with and without it. Signed sources
  are unchanged; `make pin-check` passes.
* **Mainnet shard 13.** `rpc-full-chunks` holds a single block of chunk views and no outcomes. The
  stopped capture node's database *does* retain them. It tracks shard 13 under a schedule, so
  `save_tx_outcomes` defaults on (`is_rpc`), and `save_state_changes` defaults on.
  `near-arena-oracle-v3-successor mainnet-observables` (`src/mainnet_obs.rs`) opens it read-only
  and reads, for each capture's main-transition block, `OutcomeIds` + `TransactionResultForBlock`,
  `OutgoingReceipts` and `StateChanges`. All 1,223 stored outcome lists hash to the witness
  header's outcome root. `compute_usage` is `#[borsh(skip)]` and not persisted, so mainnet has no
  compute comparison.

## 3. Results

Comparator: `tools/mainnet-replay/full_observables.py` (tests: `test_full_observables.py`). Lean
checker sha256 `09cf9944d47a078ddfb0f6447f4f844e509c083747998f03487397fc881c318a`, tier
`allFeatures`. Oracle binaries: `01e8df7bab730568ecda0639f1a73d0454782fbe0661b3bd2fd3da1263c98f33`
for the D3 runs and `mainnet-observables`; `bfb2ff485b6f592b18ab46455732bd74cdc46ccbf64d08fd07556dcc9f6c1591`
for the resharding runs (it adds the reassignment). Per-population reports: `reports/*.json`;
aggregate: `summary.json`.

**Per field**, over the 17,338 distinct graded chunks (the `regen_*` populations plus `mainnet`):

| field | compared | mismatched |
|---|---|---|
| outcome id / executor / status / return data / status receipt id / gas burnt / tokens burnt / logs / receipt ids | 592,845 each | 0 |
| outcome count, receipt count, refund count, state-change key set, chunk outcome root / gas / balance burnt | 17,338 each | 0 |
| outgoing receipt id / predecessor / receiver / kind / body hash / refund flag | 439,552 each | 0 |
| storage change (final value hash + length, or deletion) | 617,303 | 0 |
| chunk compute usage | 16,115 (mainnet has none) | 0 |

The header-level comparison (`blind_inputs.COMPARED`, 11 fields) also has no differences.

Matched chunks exercising each kind: 7,815 contain a failed outcome, 4,348 logs, 2,111 non-empty
return data, 12,775 refund receipts, 13,830 outgoing receipts, and 17,338 storage changes.

**Per population** (`cases_bound` = case directories bound to a nearcore record by hash):

| population | bound | match | mismatch | Lean out of domain | genesis main | not blindable | outcomes | receipts | storage changes | controls detected |
|---|---|---|---|---|---|---|---|---|---|---|
| mainnet shard 13 | 1223 | 1223 | 0 | 0 | 0 | 0 | 1,075 | 1,112 | 3,905 | 723/723 |
| regen d3c10 (seed 10, 4 chains) | 3226 | 3207 | 0 | 0 | 19 | 0 | 94,338 | 66,079 | 103,911 | 1703/1703 |
| regen d3c9 (seed 9, 4 chains) | 3228 | 3209 | 0 | 0 | 19 | 0 | 98,421 | 71,702 | 102,144 | 1705/1705 |
| regen curve 4242 / 31337 | 358 / 441 | 354 / 436 | 0 | 0 | 4 / 5 | 0 | 29,042 | 19,398 | 19,957 | 3386/3386 |
| regen keys 1618 / 6151 | 974 / 966 | 964 / 956 | 0 | 6 / 6 | 4 / 4 | 0 | 77,585 | 53,514 | 59,592 | 3417/3417 |
| regen yield 4242 / 1729 | 970 / 1074 | 966 / 1069 | 0 | 0 | 4 / 5 | 0 | 67,795 | 47,082 | 52,630 | 3414/3414 |
| regen storage-limits 99 / 101 | 1200 / 1500 | 1196 / 1495 | 0 | 0 | 4 / 5 | 0 | 1,202 | 486 | 4,669 | 1258/1258 |
| regen global-cache 2718 / 31415 | 477 / 501 | 473 / 497 | 0 | 0 | 4 / 4 | 0 | 39,003 | 26,689 | 32,094 | 3436/3436 |
| regen global-promise 1618 | 211 | 207 | 0 | 0 | 4 | 0 | 2,118 | 1,605 | 2,500 | 1703/1703 |
| regen reshard fa0-2 / fb0-2 | 1,933 | 1,086 | 0 | 822 | 24 | 1 | 182,266 | 151,885 | 235,901 | 9421/9421 |

The committed fixture sets and the pinned corpora are subsets of those runs, bound by byte identity.
They are reported separately: curve 87/87, global-cache 28/28, global-promise 2/2, keys 36/36 (+1
Lean out of domain), yield 74/74, storage-limit 64/64, resharding 19/19 (+1 not blindable), d3c10
83 and d3c9 81 (+19 genesis each). All match.

* *Lean out of domain*: the PV85 epochs of the resharding chains (`c.pv86`, excluded as in
  `resharding-fixtures/README.md`) and 12 key-scenario chunks. The latter are an ML-DSA-signed
  transaction and the other key exclusions documented in `key-family-fixtures`.
* *genesis main*: the main transition is the stored `genesis_chunk_extra`, so `--blind` does not run
  it (as in `corpus-blind-and-pipeline`).
* *not blindable*: a split case whose sibling child's chunk header in the segment carries the same
  outcome root (already documented in `corpus-blind-and-pipeline`).

**Wrong-observable controls.** For up to 100 matching cases per population, the comparator re-runs
the comparison against the expected record with one field mutated. The mutations are: gas +1,
tokens +1, executor, id, an extra log, one log byte, a dropped outcome, a dropped receipt id, return
data, failure↔value, receipt body hash, receiver, a dropped receipt, a refund unmarked, a storage
value hash, a write turned into a delete, a dropped storage change and compute +1. Each must be
reported as a mismatch of exactly the mutated field: 38,061/38,061 were (`controls` in each
report).

## 4. Differences found and resolved (encoding, not semantics)

Both are documented in the comparator, and each has a test.

1. **Compute of `GlobalContractDistribution` receipts.** nearcore adds
   `deploy_global_contract_execution_base + per_byte · len` (20 Tgas + 250 Mgas/byte at PV86) to the
   chunk's compute total, but produces no outcome (`runtime/src/lib.rs:1506-1516`,
   `global_contracts.rs:223-268`). Σ outcome `compute_usage` therefore falls short of the total that
   Lean reports. The first run showed 12 global-cache chunks off by exactly 20,086,250,000,000
   (code length 345). The expected total now adds that term for each `GlobalContractCode` change
   with cause `ReceiptProcessing` in nearcore's own state changes (`expected_compute`,
   `test_distribution_compute_has_no_outcome`).
2. **Outgoing receipts across a split.** `ApplyChunkResult.outgoing_receipts` is the parent's list.
   The validator reassigns it to the lowest child before hashing (`chunk_validation.rs:640-651`), and
   Lean emits the reassigned list. One `split.right` case had 0 vs 1 receipts. The collector now
   applies nearcore's own `reassign_outgoing_receipts_for_resharding` and keeps the pre-reassignment
   list as `outgoing_receipts_before_reassignment`.

No Lean bug was found. Some storage-limit chunks need more than 600 s of checker time on this loaded
host; the timeout is now 3,600 s.

## 5. What is not covered

*2026-10-30:* failure kinds, per-receipt state-change attribution, per-outcome compute and the
d1run / d2corpus.v2 expected values are now covered by [w01-observables-v3](../w01-observables-v3/README.md).

* **Failure kind.** Lean's `OStatus.failure` carries no error kind. The outcome hash commits only to
  the `Failure` tag (`PartialExecutionStatus`). The nearcore records keep `Failure(<error>)` for
  reference, but only the tag is compared.
* **Postponed receipts and data receipts** produce no outcome in nearcore or in Lean. The equal
  outcome lists (`outcomes.count`, `id`) show that both sides postpone the same receipts. Their
  storage effect (`PostponedReceipt`, `ReceivedData` keys) is in the compared storage changes.
* **Per-receipt state-change attribution.** Lean emits the chunk's committed overlay (final value
  per key, rollbacks applied), not per-receipt causes. nearcore's per-change causes are kept in the
  records.
* **Per-outcome compute** is not modelled in Lean (`OutD1` has no compute). Only the chunk total is
  compared.
* **Pinned corpora.** The current generator does not reproduce the pinned d3c7–d3c10 chains. Its
  crafted-injection traffic differs: at seed 10 chain 0 the first difference is at height 10007,
  where the pinned case carries `x.gas_nonce_*` injections. Only 102 (d3c10) and 100 (d3c9) pinned
  cases are bound byte-for-byte. The regenerated runs use the same seeds and parameters
  (`oracle/v3-d3/scripts/gen-d3-corpus.sh`: 200 blocks, `--mutate-every 20 --code-mutant-p 0.25
  --ood-cap 25 --drop-cap 48`, seed 10 with `--min-gas-price 100000000`); they are fresh
  populations of the same shape. d3c7/d3c8 were not regenerated (host load). d1run and
  d2corpus.v2 come from the D1/D2 generator (`oracle/v3-d1`), which has no collection hook, so they
  have no per-outcome expected values.

## 6. Verdict movement

The emission fields are read by no check. The 3,138-case gap census (`nearcore == ok ∧
expected_rel_d3 == false` over d3c7–d3c10), run on `allFeatures` with the checker built from
`5c60547b3` (sha256 `29bf5217…`) and with this checker: 3,138 accept before, 3,138 accept after,
0 rows differ.

## Files

* `summary.json`: per-population and aggregate counts.
* `reports/<population>.json`: the comparator's full report, including per-field counts, controls,
  identities and the hash of the expected file.
* `expected/*.jsonl.gz`: the nearcore records bound to the committed fixture sets, the pinned-corpus
  cases and mainnet. Change causes are stripped except for `GlobalContractCode` keys; nothing compared
  is removed.
* `cases/*.txt`: the bound case directories. Storage-limit cases are inside
  `storage-limit-fixtures/cases.tar.gz`.

Reproduce (committed fixtures, for example yield):

```
python3 tools/mainnet-replay/full_observables.py --binary spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor \
  --cases docs/evidence/lean-chunk-completion/full-observables/cases/yield.txt \
  --expected docs/evidence/lean-chunk-completion/full-observables/expected/yield.jsonl.gz --out OUT
```

Generator runs: the README commands of each fixture set with `NEAR_SUCCESSOR_OBSERVABLES=1`. The
regenerated d3c9/d3c10 chains use `gen-d3-corpus.sh`'s parameters with the successor binary. Then
`mainnet-observables --home mainnet-w13/home --exports mainnet-w13/exports --cases
mainnet-w13/replay-cases --out FILE`.
