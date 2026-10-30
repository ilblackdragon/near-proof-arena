# W01 observables v3: failure kinds, per-receipt storage attribution, per-outcome compute (2026-10-30)

Workplan item 9. [full-observables](../full-observables/README.md) compared every outcome, outgoing
receipt and committed storage change with nearcore, but left out three things (its §5): the
failure kind of a failed outcome, which receipt caused which storage change, and per-outcome compute.
It also had no nearcore per-outcome values for `d1run` and `d2corpus.v2`. This lane closes all four
and prepares the corpus CI gate for a provisioned runner.

Ground truth: pinned nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4, PV86), run cold.
Lean computes everything. The checker runs on blinded inputs (`--blind-full`), and no nearcore value
is a Lean input.

**Result.** 28,070 graded chunk rows over 24 populations match on every compared field. The committed
fixture sets overlap their same-seed runs, so the distinct chunks are fewer.
including 46,673 failure kinds, 1,098,587 per-outcome compute values and 894,074 per-receipt attribution
entries (1,352,063 keys). There are 0 mismatches. Wrong-observable controls detect
26,421/26,421 mutations. A deliberately broken checker (B1–B3) is detected in every
population that exercises the broken path. Verdicts do not move: census 3,138/3,138 accept before (recorded) and after; 928 committed fixture cases, 0 verdict or reason moves.

## 1. Lean (observation only)

`--emit-full` / `--blind-full` set `ProtocolCfg.observeDetail` → `NearCfg.observeDetail`. The
successor driver (`Successor/StorageExecution.lean`) then records `D2.ObsDetail` in its `Recording`
state and returns it in `MainOutD2.detail` → `Observable.detail`. No check reads it. With the flag off
(every other mode, every tier proof) nothing is recorded. The row is `outputsVersion: 3`. It adds:

| emitted | what | source |
|---|---|---|
| `outcomes[].status.error` (failed outcomes) | failure kind | VM failures: the VM's own error, the string `Exec.runCall` returns (`FunctionCallError(<e>)`). Other action failures: `Successor/FailureKinds.lean` `actionKind`. Transactions: `txKind`. Storage-stake failure after the actions: `ActionError[None].LackBalanceForState`. New-receipt validation: `NewReceiptValidationError`. |
| `outcomes[].computeUsage` | the outcome's compute | the `cu` that `processWithTotals` adds to `RS.compute`; for a transaction, the delta of `RS.compute` across `processTxD2L` |
| `receiptStateChanges[]` | per processed transaction / receipt: `ids`, the committed keys whose value it changed, and their final values | `committedDiff` of the overlay's committed list before and after the step |

**How failure kinds are obtained.** The action and transaction code (`D2/Actions`, `Logged/D2Actions`,
`Logged/D2Runtime`) returns only `ok = false`. Threading a kind through it would change the signed
D2/D3 definitions and the `Logged ↔ D2` relational proofs. Instead, `FailureKinds.lean` re-evaluates
the failed action's conditions on the state *before* the action, in nearcore's order (each condition
cites its pinned source line), and names the first that fails. It runs only after the real code
reported a failure. Its answer is checked against nearcore on every failed outcome below. It is a
derived observation, not a statement that the action code computes the kind.

**Unknown pre-state values.** A step can write a key it never read, for example the first access key
of a new account, or a global contract code key re-committed by a repeated distribution. The witness
then records only the key's value reference, not its bytes, so the checker cannot tell whether the
write changed the value. Such keys are emitted in a companion entry with `preKnown: false`. The
comparator requires that nearcore committed that key in the same entry with the same final value,
changed or not.

Other Lean edits: the `Observable` / `MainOutD2` fields (four parallel constructions, so
`legacy_core_eq` stays `rfl`), `ObsDetail` (`D2/Types.lean`), and the `observeDetail` flag
(`Wasm/Prepare.lean`, `Successor/Config.lean`). The full default build (`lake build`, 313 jobs)
passes. Its axiom report lists only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`.

## 2. nearcore expected values

* **Per-change detail.** `observables.rs` `change_detail_json` (generator runs) and `mainnet_obs.rs`
  (mainnet node store) now record, for every changed key, every committed change in order with its
  `StateChangeCause` and value hash and length. They also record the key's pre-state value
  reference (`Trie::get_optimized_ref`). For generator runs this comes from the witness's recorded
  pre-state nodes and the applied chunk's `prev_state_root`; for mainnet, from the witness's base
  state and the applied chunk header's `prev_state_root` read from the stopped node. There were 0
  pre-state lookup errors.
* **d1run / d2corpus.v2** (`observe-d1` / `observe-d2`, `oracle/v3-successor/src/d12obs.rs`,
  `tools/d3/observe_d12.sh`). The original D1/D2 generator chains run *unchanged*: the shared
  `oracle/v3-d1` sources, compiled into this crate with the original parameters
  (`regen-fixtures-v3.sh:38`, `gen-d2-corpus.sh`). The output goes to scratch. This crate's `judge`
  is the shared `oracle/v3/src/judge.rs` re-exported unchanged plus a thread-local hook
  (`judge_hook.rs`). No other command installs the hook. For each honest witness the generator
  judges, the hook looks up sha256(Borsh `ChunkStateWitness`) among the corpus cases of that chain.
  On a hit it runs `observables::observe` with a **cold** validator runtime (empty compiled-contract
  cache, its own runtime and epoch manager handle over the client's store) and the code blobs the
  corpus `witness.bin` carries. The record is bound to the corpus case by sha256 of `claim.bin` and
  `witness.bin`.

  | corpus | cases (honest) | observed (byte-identical regeneration) | `ok` records | genesis main transition |
  |---|---|---|---|---|
  | d1run (12 chains) | 7,039 | 7,039 | 6,979 | 60 |
  | d2corpus.v2 (14 chains) | 10,927 | 10,927 | 10,858 | 69 |

  `oracle/v3-d1/src` is unchanged, so `make pin-check` passes. The first D1 attempt did not
  regenerate 21 cases of chain 9 (heights ≥ 10145) or 399 of chain 11 (heights ≥ 10038). Both
  chains were then re-run unchanged and regenerated every case. The D1 TestEnv replay is therefore
  not reliably deterministic under host load (load average ~170 during the first attempt); the
  byte-identity check catches this, and a non-identical case is never bound. Mutants
  (`d1run/mutants` 46,009, `d2corpus.v2/mutants` 56,457) are nearcore-rejected. Their asserted
  outcome is the cold verdict in `meta.json`; a rejected chunk has no outputs to compare.
* **Fresh generator runs** with the per-change collector, honest chunks only: yield 4242, global-cache
  2718, keys 1618 and the D3 baseline seed 10 chain 0 (`--min-gas-price 100000000`). Commands are in
  `generation.json`.
* **Item-10 runs** (`../remaining-shapes`): their records predate the per-change collector. They are
  compared for failure kinds and compute only.

## 3. Comparator

`tools/mainnet-replay/full_observables.py` (version 3) and `failure_kinds.py`, with tests in
`test_full_observables.py` and `test_failure_kinds.py` (21 tests).

* **Failure kinds.** Both sides are reduced to a dotted variant path with the action index and no
  payloads: `ActionError[0].FunctionCallError.HostError.GasExceeded`,
  `InvalidTxError.InvalidAccessKeyError.RequiresFullAccess`, `ActionError[None].LackBalanceForState`.
  nearcore collapses VM errors into `FunctionCallError::ExecutionError(<Display>)`
  (`runtime/src/conversions.rs:74-90`). The Display text is mapped back to the variant with a table
  transcribed from `near-vm-runner/src/logic/errors.rs:458-636`. Every nearcore failure in every
  population resolved; none stayed `ExecutionError`. `NewReceiptValidationError` is compared at its
  own name (Lean does not classify the receipt-validation error inside it). `ActionsValidation`
  subkinds *are* compared.
* **Attribution.** A cause naming a transaction or receipt (`TransactionProcessing`,
  `ActionReceiptProcessingStarted`, `ActionReceiptGasReward`, `ReceiptProcessing`,
  `PostponedReceipt`; ids decoded from base58) is mapped to the Lean entry for that id. A
  `PostponedReceipt{h}` cause goes to the entry that postponed h. Every other cause goes to the
  entry whose outcome is h; a receipt postponed and completed in one chunk has two entries. For each
  entry, a key counts when its value after the entry differs from its value before (pre-state
  reference, or the previous change). Chunk-level causes (`UpdatedDelayedReceipts`,
  `ValidatorAccountsUpdate`, `BandwidthSchedulerStateUpdate`, …) are not attributed on either side.
  A nearcore change attributed to an id with no Lean entry is reported as `attrib.unattributed`.
* **Outgoing-buffer keys excluded from attribution** (`TrieKey` columns 13, 14, 16, 17). nearcore
  commits the receipt (`runtime/src/lib.rs:963`, `ReceiptProcessing`) and only then forwards or
  buffers its new receipts (`lib.rs:1109`). Those writes are therefore logged under the *next*
  commit's cause (the next receipt's `ActionReceiptProcessingStarted`, or `UpdatedDelayedReceipts`).
  This is bookkeeping order, not state. The first run showed exactly this on 20 of 966 yield chunks
  and 56 of 501 global-cache chunks, and nothing else. The final values of these keys stay compared
  chunk-wide (`stateChange.value`).

## 4. Results (`reports/`, `summary.json`)

Lean checker `nearspec-v3-check-successor` sha256 `eba960d0573a6fc9642fc544b9b21c849f5b72d036c98382e6fb739ac8b8ca3a` (built at `4f52dac49`), tier `allFeatures`, `--blind-full`.

| population | source | match | mismatch | other | failure kinds | outcome compute | attribution entries | attribution keys | controls |
|---|---|---|---|---|---|---|---|---|---|
| d1run | cold re-capture, 12 chains | 6979 | 0 | nearcore_genesis 60 | 5,813 | 438,980 | 438,980 | 647,167 | 1793/1793 |
| d2corpus | cold re-capture, 14 chains | 10858 | 0 | nearcore_genesis 69 | 21,645 | 365,132 | 365,682 | 582,282 | 1959/1959 |
| mainnet | shard 13, node store, per-change detail | 1223 | 0 | — | 43 | 0 | 1,204 | 2,731 | 810/810 |
| regen_y4242 | yield, fresh run | 966 | 0 | nearcore_genesis 4 | 1,431 | 30,540 | 30,849 | 41,669 | 2063/2063 |
| regen_g2718 | global-cache, fresh run | 501 | 0 | nearcore_genesis 4 | 594 | 11,534 | 11,704 | 16,125 | 2088/2088 |
| regen_k1618 | keys, fresh run | 988 | 0 | nearcore_genesis 4 | 1,513 | 19,245 | 19,507 | 26,241 | 2099/2099 |
| regen_d10 | D3 baseline seed 10, fresh run | 696 | 0 | nearcore_genesis 4 | 1,363 | 25,868 | 26,148 | 35,848 | 2077/2077 |
| yield | committed fixtures (2026-10-26 records) | 74 | 0 | — | 132 | 3,982 | 0 | 0 | 959/959 |
| curve | committed fixtures (2026-10-26 records) | 87 | 0 | — | 146 | 3,855 | 0 | 0 | 949/949 |
| keys | committed fixtures (2026-10-26 records) | 37 | 0 | — | 50 | 2,838 | 0 | 0 | 704/704 |
| globalcache | committed fixtures (2026-10-26 records) | 28 | 0 | — | 50 | 2,457 | 0 | 0 | 541/541 |
| globalpromise | committed fixtures (2026-10-26 records) | 2 | 0 | — | 4 | 14 | 0 | 0 | 37/37 |
| storage | committed fixtures (2026-10-26 records) | 64 | 0 | — | 16 | 142 | 0 | 0 | 899/899 |
| resharding | committed fixtures (2026-10-26 records) | 19 | 0 | error 1 | 4 | 3,912 | 0 | 0 | 289/289 |
| pin_d3c9 | pinned corpus subset (2026-10-26 records) | 81 | 0 | nearcore_genesis 19 | 62 | 1,636 | 0 | 0 | 866/866 |
| pin_d3c10 | pinned corpus subset (2026-10-26 records) | 83 | 0 | nearcore_genesis 19 | 65 | 826 | 0 | 0 | 892/892 |
| item10_se701 | item-10 run (no per-change records) | 234 | 0 | nearcore_genesis 4 | 364 | 12,417 | 0 | 0 | 922/922 |
| item10_se702 | item-10 run (no per-change records) | 295 | 0 | nearcore_genesis 5 | 773 | 13,132 | 0 | 0 | 930/930 |
| item10_se703 | item-10 run (no per-change records) | 360 | 0 | nearcore_genesis 6 | 403 | 7,338 | 0 | 0 | 880/880 |
| item10_se704 | item-10 run (no per-change records) | 228 | 0 | nearcore_genesis 4 | 338 | 11,089 | 0 | 0 | 938/938 |
| item10_mb1618 | item-10 run (no per-change records) | 1055 | 0 | nearcore_genesis 4 | 2,276 | 25,787 | 0 | 0 | 940/940 |
| item10_mb2718 | item-10 run (no per-change records) | 1038 | 0 | nearcore_genesis 4 | 3,932 | 40,169 | 0 | 0 | 931/931 |
| item10_cy601 | item-10 run (no per-change records) | 972 | 0 | nearcore_genesis 4 | 2,134 | 29,745 | 0 | 0 | 930/930 |
| item10_cy602 | item-10 run (no per-change records) | 1202 | 0 | nearcore_genesis 5 | 3,522 | 47,949 | 0 | 0 | 925/925 |

`nearcore_genesis` = the main transition is the stored genesis chunk extra, so nearcore applies
nothing and there is nothing to compare (as before). The one resharding error is the known
not-blindable split case (`corpus-blind-and-pipeline`).

### Wrong-observable controls (comparator)

For up to 100 matching cases per population, the expected record is mutated in one field and must
be reported as a mismatch of that field. Earlier mutations are kept. New ones: a different failure
kind (`outcome.failureKind`), per-outcome compute +1 (`outcome.computeUsage+1`), a flipped final
value of an attributed key (`attrib.value`), and an attributed change moved to an unknown receipt
(`attrib.cause`). The `attrib.cause` control is drawn only from changes that alter the value; moving
a same-value rewrite is unobservable by definition. In the first runs (yield, global-cache), 8 + 5
such draws were missed before this restriction. In d1run, one `outcome.failureKind` draw turned
`Expired` into `Expired`; the mutation now always picks a different canonical kind. These three
populations were re-run (`fo3`), and every control in the table is detected.

### Deliberate-breakage control (checker)

`lean-ctl` is the same tree with three bugs (patch: `generation.json` `control_patch`):

* **B1**: the stake classifier tests `TriesToUnstake` before `TriesToStake`, and the transaction
  classifier reports `NonceTooLarge` for every nonce failure.
* **B2**: a transaction outcome reports compute + 1.
* **B3**: every key first committed in a step counts as changed (no pre-state comparison).

Checker sha256 `20ff40b3…`. Every report below fails (`reports/ctl-*.json`
):

| population | chunks flagged | failure kinds wrong (B1) | outcome compute wrong (B2) | attribution entries / keys wrong (B3) |
|---|---|---|---|---|
| yield 4242 (fresh run) | 887 / 966 | 31 / 1,431 | 9,304 / 30,540 | 1,006 / 30,849 entries, 1,396 / 43,063 keys |
| pin d3c9 | 74 / 81 | 3 / 62 | 1,372 / 1,636 | — (2026-10-26 records, no causes) |
| pin d3c10 | 71 / 83 | 1 / 65 | 526 / 826 | — |
| keys (committed) | 36 / 37 | 1 / 50 | 709 / 2,838 | — |

Every B1 hit is the nonce half (`NonceTooLarge` reported for nearcore's `InvalidNonce`, 36 outcomes).
The stake half reorders `TriesToStake`/`TriesToUnstake`, which differ only when both conditions
hold. No compared chunk has that, so this half was not exercised.

## 5. Verdict movement

The emission is read by no check, and the flag is off outside `--emit-full`/`--blind-full`.

`allFeatures` verdicts. "Before" is the checker built from the base commit `4f07a7fdf` (sha256
`a1627ea3…`, built by the item-10 lane from an unchanged Lean tree). "After" is this branch's
checker (`eba960d0…`).

| population | before | after (plain) | after (`--emit-full`, `observeDetail` on) |
|---|---|---|---|
| 3,138-case gap census (list sha256 `cd6a89a8…`, as recorded) | 3,138 accept (recorded in `mldsa-fixtures/replay/census-3138.json`) | 3,138 accept | 3,001 accept + 137 out of domain |
| 928 committed fixture cases (every unpacked `cases/` dir plus the cross-family, remaining-shapes and storage-limit tarballs) | 556 accept / 371 reject / 1 io_error | identical, 0 verdict or reason moves | not run |
| d1run + d2corpus.v2 honest cases (graded above) | — | — | 17,837 accept + 129 genesis claims |

The 137 census cases under `--emit-full` are `out of domain (c.not_genesis): resharding walk reaches
the genesis block`. The observable path (`checkSuccessorObs`) has never handled genesis-reaching
resharding claims. The base checker's `--emit` returns the same 137 out-of-domain rows
(`census-ood137-base-emit`), so `observeDetail` causes none of them. The io_error is
`resharding-fixtures-2/cases/seed61-00-h10061-s5`, a case directory without a `witness.bin`, on
both checkers. The full corpus was not re-run: the plain verdict path is unchanged code apart from
fields it never reads, and the sample above shows no movement. The eval-time and fuel-termination
fixtures (worst-case loops) were not re-run.

## 6. Corpus CI gate (prepared, not enabled)

`corpus-content-gates` (`.github/workflows/ci.yml`) now runs on a self-hosted runner labelled
`near-corpora`. Its step is `tools/d3/fetch_corpora.sh`: corpora already mounted, rsync from
`NEAR_CORPORA_SOURCE`, or per-family tarballs from `NEAR_CORPORA_URL`. In every mode the corpora are
accepted only if `corpus_manifest.py --verify` reproduces the committed manifest. The job then runs
the comparator self-tests. Runbook: `tools/d3/CORPUS_RUNNER_RUNBOOK.md`.

Local dry run on this host (`NEAR_CORPORA_DIR=/data/illia/nearproof-deps/corpora`): 17 of 18
families verify. `d2corpus.v2/ood` differs (bytes 10,095,608 → 10,449,976). Commit `c8b2aeccd`
(branch `worktree-agent-a103b9b4017fa3668`, not on `main`) replaced those 224 cases in place with
cold-judged ones carrying code, and that branch updates the manifest. So the gate fails here until
that commit lands. That is the gate working. Unset → exit 2; an unwritable root → exit 1.

**Owner actions (not done by this lane):** register the runner with label `near-corpora`; set
`NEAR_CORPORA_AVAILABLE=true` and `NEAR_CORPORA_DIR`, plus optionally `NEAR_CORPORA_SOURCE` or
`NEAR_CORPORA_URL`; merge the d2corpus.v2 manifest update.

## 7. Not covered / open

* **Failure kinds are classified, not threaded.** `FailureKinds.lean` re-derives the kind. It matches
  nearcore on every failed outcome compared, but it is a parallel derivation, so a future change to
  an action's conditions must be mirrored there. The comparator catches a drift.
* **Payloads of failure kinds are not compared** (account ids, amounts, nonces, panic messages).
  `NewReceiptValidationError` is compared at its own name only.
* **Attribution excludes outgoing-buffer keys** (§3) and chunk-level causes. Their final values are
  compared chunk-wide.
* **Mainnet has no per-outcome compute**: `compute_usage` is `#[borsh(skip)]` and is not stored.
* **Attribution needs per-change records.** The committed 2026-10-26 sets and the item-10 runs have
  none, so they are compared for failure kinds and compute only. Attribution is measured on
  d1run, d2corpus.v2, mainnet and the four fresh runs.
* **Mutants have no observable comparison.** They are nearcore-rejected, and their asserted outcome
  is the cold verdict.
* **D1 replay determinism.** One of two attempts diverged on chains 9 and 11 under heavy host load
  (§2). The byte-identity binding keeps this from producing a wrong record. It would matter for a
  CI job that regenerates.
* **The CI gate is not enabled.** That needs the owner actions in §6, and the d2corpus.v2 manifest
  must land first.

## Files

* `summary.json`: per population, per-field compared/mismatched, controls, identities.
* `reports/<population>.json`: the comparator reports (`ctl-*`: the breakage checker).
* `expected/mainnet.jsonl.gz`: the full mainnet records with per-change detail.
* `expected/d1run.digest.jsonl.gz`, `expected/d2corpus.digest.jsonl.gz`: a per-case digest of the
  d1run / d2corpus.v2 records. Each entry holds the binding hashes, chunk totals, outcome / receipt /
  change counts, a failure-kind histogram and the sha256 of the full record. The full records are
  1.07 GB, so they stay on the lane host (`/data/illia/nearproof-deps/w01-runs/obs/{d1,d2}`); their
  file hashes are in `generation.json`. Regenerate them with `tools/d3/observe_d12.sh`.
* `generation.json`: binaries, commands, control patch, observe summaries, file hashes.

Reproduce (d1run; likewise d2):

```
bash oracle/scripts/link-nearcore.sh
CARGO_TARGET_DIR=T cargo build --release --manifest-path oracle/v3-successor/Cargo.toml
ORACLE=T/release/near-arena-oracle-v3-successor OUT=obs PAR=4 tools/d3/observe_d12.sh d1
(cd spec/lean/v3 && lake build nearspec-v3-check-successor)
python3 tools/mainnet-replay/full_observables.py --binary spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor \
  --root $NEAR_CORPORA_DIR/d1run --cases LIST --expected obs/d1/nearcore-observables-*.jsonl --out OUT
```
