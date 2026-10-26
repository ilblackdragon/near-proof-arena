# W02 Gate-B caps: every limit on `allFeatures` is nearcore's own (2026-10-26)

Gate B forbids rejecting or excluding a valid nearcore input because of an arena- or
prover-derived limit. This lane inventories every size, count, depth, gas and fuel limit reachable
from `nearspec-v3-check-successor --tier allFeatures`, classifies each against the pinned validator
(nearcore 2.13.4, `44f7ae6c`, PV86), and removes the arena-only ones on `allFeatures` or replaces
them with nearcore's exact rule. The signed tier keeps its stated exclusions
(`checkSuccessor_signed` is still `rfl`; `allFeatures_lifts_arena_caps` states the split).

Checkers (sha256): before = `29bf5217…` (main `ad55805ea`), after = `35d88772…` (this branch),
after-without-segment-lift = `e3c9ff28…` (the same tree with `.allFeatures.segmentUnbounded := false`).

**Result.** On the full population (all six corpora, d1run, d2corpus.v2, d3c7-d3c10, and every
fixture set: 236,293 cases) the after checker moves **no verdict** against the before checker
(76,591 accept / 159,604 reject / 98 out of domain on both; no reason class changes either). That
includes the 3,138-case census (3,138 accept before and after). Lifting `c.segment` changes exactly
the 7 nearcore-valid cases with more than 32 blocks and nothing else. No corpus case reaches the
other caps. They are exercised by new pinned-nearcore fixtures (§4). All four lifted caps excluded
nearcore-valid chunks before: a 1.8 Pgas chunk, witnesses of 8.43 and 9.46 MB, a zero-fee-heavy call,
and the long segments. After the change all of them are accepted, and all blind outputs match
nearcore. One Lean bug was fixed: the transaction size gate was off by one byte for SECP256K1
transactions (§1.1).

## 1. Inventory

Class **(a)**: nearcore's rule, reproduced. Class **(b)**: arena-only cap. Class **(c)**: an
evaluator bound that never binds on a valid input (argument given). Class **(t)**: a nearcore
transport limit the validation relation cannot reproduce exactly (named exclusion, conservative).

### 1.1 Caps on the chunk-validation pipeline (`RuntimeCore.lean`, `ReshardCore.lean`, `Config.lean`)

| Lean limit | Where | nearcore 2.13.4 | Class | `allFeatures` before → after |
|---|---|---|---|---|
| `c.blocks.length ≤ 32` (`c.segment`) | `RuntimeCore.lean:174,377`, `ReshardCore.lean:232` | none: `get_state_witness_block_range` walks back to the second-last new chunk with no bound (`chain/chain/src/stateless_validation/chunk_validation.rs:143-250`) | (b) D0 AIR segment height (`spec/near-chunk-validation-v0.md:180`) | already lifted (`segmentUnbounded`); rerun in §3 |
| `|state_witness| ≤ 8 MiB` (`w.size`) | `RuntimeCore.lean:136-140,346-350`, `ReshardCore.lean:200-204` | decode limit `MAX_UNCOMPRESSED_STATE_WITNESS_SIZE` = 64 MiB (`core/primitives/src/stateless_validation/state_witness.rs:19-20`, `CompressedData::decode`, `utils/compression.rs:44-47`, `utils/io.rs:81-90`: error iff bytes read > limit) | (b) D0 witness-capacity choice (`near-chunk-validation-v0.md:189`) | **lifted** (`witnessUnbounded`); the 64 MiB rule stays exactly in the decoder (`WitnessCodec.lean:18`, reject) |
| witness ≤ `compressedSafeWitnessBytes` = 50,000,000 (`w.compressed_size`, **new**) | same lines, only when `witnessUnbounded` | `MAX_COMPRESSED_STATE_WITNESS_SIZE` = 48 MiB on the zstd-encoded witness (`partial_witness.rs:18-19`); validators drop every part above it (`chain/client/src/stateless_validation/validate.rs:82-88`) | (t) the encoded length depends on the producer's zstd encoder (level 1, 4 workers, `state_witness.rs:21-22`), not formalized; zstd expands by < n/256 + 64 KiB, so ≤ 50,000,000 B always passes (`compressedSafeWitnessBytes_ok`) | new named exclusion for (50,000,000, 64 MiB]; without it, lifting `w.size` would accept witnesses nearcore never validates |
| `1 ≤ numShards ≤ 64` (`c.layout`) | `RuntimeCore.lean:168-171,371-374`, `ReshardCore.lean:224-229` | no shard-count limit in validation; pinned mainnet dynamic resharding stops at `max_number_of_shards = 10` (`core/primitives/res/epoch_configs/mainnet/85.json:26`) | (b) D0 routing-table size (`near-chunk-validation-v0.md:175`); `≥ 1` kept | **lifted** (`layoutUnbounded`); 0 corpus cases reach it |
| `out.wasmGas ≤ gasCap`, `gasCap = some maxGasBurnt` = 1 Pgas (`e.g_alpha`) | `RuntimeCore.lean:271-272,520-521`, `ReshardCore.lean:323-324` | none per chunk. `max_gas_burnt` (1 Pgas from PV83, `runtime_configs/83.yaml:7`) bounds one call (`near-vm-runner/src/logic/gas_counter.rs:87-101`); a receipt starts while `total.compute < compute_limit` (`runtime/runtime/src/lib.rs:2385,2463,2575,2668`), so a chunk can burn up to gas limit + one call's 1 Pgas | (b) mislabelled protocol bound (the per-call limit read as per-chunk) | **removed** (`gasCap := none`); fixture `gas.above`: 1.8 Pgas, nearcore ok |
| `driver.sizeOk` (Σ base_state + 2000·removals ≤ 4,000,000) | `RuntimeCore.lean:268,517`, `ReshardCore.lean:321` | the storage-proof limits are deferral/abort semantics, not a reject (`lib.rs:2385`; `wasmtime_runner/mod.rs:345`) | (b) on the legacy driver | already `true` on every recorder driver (incl. `allFeatures`); the limits are modelled exactly (row 1.2) |
| `TxD2.sizeOk`: `body + 65 ≤ max_transaction_size` | `D2/TxD2.lean:75`, used for new transactions (`RuntimeCore.lean:189,389`, `ReshardCore.lean:243`) and `TxD2.valid` | `size_for_limits` = `wire_size` = body + borsh `Signature` from `PostQuantumSignatures` (PV85) (`core/primitives/src/transaction.rs:331-337,448-466`; `primitives-core/src/version.rs:567-575`) | (a) but **inexact**: a SECP256K1 signature is 66 B | **fixed**: `body + 1 + sig.length` (`TxD2.sizeOk_ed25519`: unchanged for ED25519, hence for the signed tier). Before, Lean accepted a SECP256K1 transaction of wire size `max + 1` that nearcore rejects (`TransactionSizeExceeded`) |
| `rsGenesisParamsOk`: `2 ≤ t ≤ 256`, `d = (t-1)/3` | `ChunkValidationV0.lean:96` | `num_total_parts` / `num_data_parts` (`chain/epoch-manager/src/adapter.rs:50-70`), Reed-Solomon over GF(2⁸) ≤ 256 shards (`core/primitives/src/reed_solomon.rs:111` `unwrap`) | (a) | unchanged (reject) |
| `c.pv86`, `c.layout` V2/V3, `c.headers`, `c.not_genesis`… | various | protocol-version / shape domain | not a size cap | unchanged |
| claim / witness-file decoding (`decodeClaimE`, `decodeWitnessFile`) | `ClaimV3.lean:166`, `WitnessV3.lean:114` | — | no length cap beyond u32 lengths of the wire format | — |

### 1.2 Protocol limits inside execution — class (a)

`tools/d3/check_gate_b_limits.py` checks 50 Lean limit constants against the pinned PV86 parameter
table (`docs/research/near-wasm-boundary-inventory.json`): **50/50 equal**. They cover the receipt
and action limits (`max_actions_per_receipt`, `max_receipt_size`, `max_arguments_length`,
`max_number_input_data_dependencies`, …), storage key/value lengths, `max_transaction_size`, both
storage-proof limits (`main_storage_proof_size_soft_limit` and `per_receipt_storage_proof_size_limit`,
4,000,000 B; byte-exact boundaries in `../storage-limit-fixtures/`), the VM host limits (registers,
logs, promises, yield payload, `max_gas_burnt`), and every Wasm preparation limit (function/type/
local/block/stack/body/instrumented-size limits; 1,030 modules golden-checked in
`../runtime-limits/`). Limits nearcore applies only when *producing* a chunk are correctly absent
from the validator relation: `combined_transactions_size_limit` (`chain/chain/src/runtime/mod.rs:936`),
`new_transactions_validation_state_size_soft_limit` (`:961`); `outgoing_receipts_{usual,big}_size_limit`
are unused at PV86 (`congestion_info.rs:103` has no caller), bandwidth scheduling replaces them
(`BandwidthScheduler.Config.pv86`).

### 1.3 Evaluator bounds — class (c), plus one fix

| Bound | Where | Why it never binds | Result on exhaustion |
|---|---|---|---|
| Wasm step budget `wasmFuel` (**changed**) | `Successor/StorageExecution.lean` `wasmFuel` | only `block`/`end`/`else` are zero-fee (`FiniteWasm.gInstr`; `prepare_v3.rs:525-538`); every other instruction costs ≥ `regular_op_cost`, so ≤ P = gas/822,756 + 2 charged instructions run; zero-fee instructions never jump back or push a frame, so ≤ F+1 of them run per activation between charged backward branches (F = `max_function_body_size` = 196,608); hence ≤ P + (2P+1)(F+1) steps | `unmodeled fuel exhausted` → `out of domain (e.wasm-α)` |
| former budget `(gas/822,756 + 2)·64 + 10⁶` | same (and still `D3/FunctionCall.lean:303` on the signed path) | **binds**: a loop over K nested empty blocks runs 2K zero-fee instructions per charged pair. Fixture `fuel.nest.large` (K = 500, 30 Ggas) and `TestGateBCaps.lean` | excluded a valid call (nearcore: `GasExceeded`) |
| `revealFuel` = 10,000 | `D2/Trie.lean:125` | trie keys ≤ 1 + 64 + 1 + 2,048 B = 4,228 nibbles; path depth ≤ 2·nibbles + 1 | unrevealed node |
| TrieStore lookup fuel `4·|key| + 4` | `Wasm/TrieStore.lean:122` | path ≤ 2·(2·|key|) + 1 nodes | `unmodeled: lookup fuel` |
| instant-receipt drain 100,000 | `StorageExecution.lean` `processWithInstant` | instant receipts are PromiseYield / lone DeleteAccount receipts (`core/primitives/src/receipt.rs:474-491`), created only by a call's promises: ≤ 1 Pgas / `action_receipt_creation` ≈ 9,300 per receipt, and processing one creates none | reject (mislabelled panic) |
| delayed / buffered queue loops | `QueueExecution.lean`, `StorageExecution.lean:595,666`, `Pipeline.lean:155` | fuel = the queue's own length (`next − first + 1`) | — |
| shuffle rejection sampling | `RuntimeCore.lean` `shuffleWithSeed` | probability < 2⁻¹⁰²⁴ | reject |

Trie keys and the delayed/buffered queues are bounded by the data itself. The shuffle bound is
probabilistic. Neither is a Gate-B cap. The fuel argument is a counting argument; it is not yet a
Lean theorem (W02's termination obligation stays open). The former budget is still in the signed
`D3/FunctionCall.lean`, which this lane leaves unchanged.

## 2. What changed (code)

* `Successor/RuntimeCore.lean`, `Successor/ReshardCore.lean`: `ExecutionDriver.witnessUnbounded`
  and `.layoutUnbounded`, next to the existing `segmentUnbounded`. Defaults are `false`, so
  `legacy_core_eq` / `legacy_genesis_eq` and `checkSuccessor_signed` stay `rfl`.
  `compressedSafeWitnessBytes` and the `w.compressed_size` guard are new.
* `Successor/Config.lean`: `ProtocolCfg.witnessUnbounded` and `.layoutUnbounded` are new.
  `.allFeatures` sets them, together with `segmentUnbounded`, and uses `gasCap := none`. Theorems:
  `allFeatures_lifts_arena_caps`, and `allFeatures_sets_globalActions` now states `gasCap = none`.
  Other successor tiers (`protoGas` … `resharding`) keep `gasCap = some maxGasBurnt` and the
  8 MiB / 64-shard / 32-block bounds. They are not the Gate-B tier.
* `D2/TxD2.lean`: `TxD2.sizeOk` uses the wire size, and `TxD2.sizeOk_ed25519` is new. This file
  is shared with the signed checker. Every signed transaction has a 64-byte signature
  (`pTxD2`), so the signed verdicts are unchanged (the 236,293-case run moves nothing).
* `Successor/StorageExecution.lean`: `wasmFuel` replaces the per-call `·64` budget on the successor
  tiers.
* `TestGateBCaps.lean` (`nearspec-v3-test-gate-b-caps`, added to `make d3-smoke`) checks the
  following. The former fuel gives `unmodeled fuel exhausted` on a 500-block nest at 30 Ggas;
  `wasmFuel` gives `abort 30000000000 30000000000 HostError(GasExceeded)`. Both budgets agree at
  1.5 Ggas. The four ED25519/SECP256K1 wire-size boundary values are checked, and so are the tier
  configurations.
* `tools/d3/replay_successor.py`: `allFeatures` widens `c.segment`, `w.size` and `c.layout`.
* `tools/d3/check_gate_b_limits.py`: the §1.2 check.
* `oracle/v3-successor`: adds `NEAR_SUCCESSOR_SCENARIO=gate-b-caps` (`src/scenarios.rs`, registered in
  `d3gen::Scenario`) and the `--long-skip START:LEN:K` option (`src/main.rs`). Without the flag, the
  rotation's `long_skip` is unchanged. Without the scenario, the generator code paths are unchanged.

## 3. Full-corpus rerun

Population: every case directory of `d1run`, `d2corpus.v2`, `d3c7`, `d3c8`, `d3c9`, `d3c10` (families
`d1`/`d2`/`d3`/`mutants`/`ood`; 235,716) plus every fixture case under
`docs/evidence/lean-chunk-completion/` (577, storage-limit cases extracted). Total: 236,293.
`--tier allFeatures`, one row per case. Per-case verdicts for all three checkers are in
`corpus-verdicts.tsv.gz`, and the totals are in `corpus-summary.json`.

| checker | accept | reject | out of domain |
|---|---|---|---|
| before (`29bf5217`, main) | 76,591 | 159,604 | 98 |
| after (`35d88772`) | 76,591 | 159,604 | 98 |
| after without the segment lift (`e3c9ff28`) | 76,584 | 159,604 | 105 |

* **before → after: 0 verdicts move** (and no out-of-domain or reject reason class changes). The
  98 exclusions are the same on both: 95 `e.wasm-α` (the thread-race exclusion of the preparation
  pipeline, all 95 nearcore-rejected), plus 3 nearcore-valid key-family fixtures (2 `w.shape`, 1
`e.mldsa_tx`: an ML-DSA key or signature, and a secp key with an ED25519 signature). Those 3 are W06's
cryptography gap, not caps. After this change, no nearcore-valid case is excluded for a size,
count, gas or fuel reason.
* **3,138-case census** (nearcore ok ∧ `expected_rel_d3 = false`, d3c7-d3c10): 3,138 accept before and
  after. Without the segment lift, 3 are out of domain.
* **With vs without the segment lift: exactly 7 cases differ**, all `accept` → `out of domain (c.segment)`,
  all `nearcore: ok`, and all with more than 32 blocks: `d1run/ood/05-h10082-s0`,
  `d2corpus.v2/ood/{05-h10102-s0, 05-h10103-s0, 13-h10102-s0}`, `d3c7/ood/05-h10102-s0`,
  `d3c8/ood/{05-h10102-s0, 05-h10103-s0}`. That is the intended set and nothing else.

## 4. Boundary fixtures (pinned nearcore, `oracle/v3-successor`)

```
NEAR_SUCCESSOR_SCENARIO=gate-b-caps $B gen --domain d3 --seed 2002 --chains 1 --blocks 45 --p-missing 0 \
  --mutate-every 0 --code-mutant-p 0 --ood-cap 100000 --out gb2002
$B gen --domain d3 --seed 3003 --chains 1 --blocks $((L+30)) --p-missing 0 --mutate-every 0 \
  --code-mutant-p 0 --ood-cap 100000 --long-skip 10:$L:0 --out seg$L        # L = 29 30 31 32 70
```

`gb2002`: 180 honest chunks; the cold validator accepted all 180. The `seg*` chains: 201 + 204 + 207 +
210 + 322 honest chunks, all accepted. `cases.tar.gz` has the 30 boundary cases and
`manifest.json` records, for each case, its steps, sizes, nearcore verdict, the three Lean verdicts,
the blind result, wall time and max RSS. All 1,324 generated cases (gb2002 + seg*) were also run with
the before/after checkers: only the 4 + 0 cases below move. A blind replay
(`tools/mainnet-replay/blind_corpus.py`, outputs zeroed, expected values from the nearcore-produced
header) gave 1,300/1,300 graded cases a full match of all 11 fields, with 24 genesis cases not graded.

| fixture | measured | nearcore | before | after | blind |
|---|---|---|---|---|---|
| `wsize.below` (`gb2002/ood/00-h10006-s3`) | witness 6,684,165 B | ok | accept | accept | match |
| `wsize.near-below` (`…/00-h10012-s3`) | 8,364,574 B (8 MiB − 24,034) | ok | accept | accept | match |
| `wsize.near-above` (`…/00-h10018-s3`) | 8,434,574 B (8 MiB + 45,966) | ok | **out of domain (w.size)** | accept | match |
| `wsize.above` (`…/00-h10024-s3`) | 9,464,574 B | ok | **out of domain (w.size)** | accept | match |
| `gas.below` (`…/00-h10006-s1`) | chunk FC gas 900 Tgas | ok | accept | accept | match |
| `gas.above` (`…/00-h10012-s1`) | 1,800 Tgas (two 900 Tgas receipts in one chunk) | ok | **out of domain (e.g_alpha)** | accept | match |
| `fuel.nest.small` (`gb2002/d3/00-h10018-s1`) | 1.5 Ggas, GasExceeded | ok | accept | accept | match |
| `fuel.nest.large` (`gb2002/d3/00-h10024-s1`) | 30 Ggas, GasExceeded | ok | **out of domain (e.wasm-α): fuel exhausted** | accept | match |
| segment 31 / 32 blocks (`seg29`, `seg30`, 2 each) | `n_blocks` 31, 32 | ok | accept | accept (no lift: accept) | match |
| segment 33 / 34 / 51 / 71 blocks (`seg31`, `seg32`, `seg70`) | `n_blocks` > 32 | ok | accept | accept (**no lift: out of domain (c.segment)**) | match |

Exact at-limit fixtures are no longer meaningful for the three removed caps, because no Lean boundary
is left at 8 MiB, at 1 Pgas or at the old fuel budget. The bounds that remain were tested as follows:

* **64 MiB decode bound and the `w.compressed_size` band.** Generating a 50-64 MiB witness takes
  about a dozen full chunks of incoming receipts and is out of reach of the generator here. It is
  tested with **constructed witnesses** (`synth`: a real claim plus a junk ChunkStateWitness of exact
  length): 8,388,608 / 8,388,609 / 50,000,000 / 50,000,001 / 67,108,864 / 67,108,865 B. Before, the
  results were reject (decode) / `w.size` / `w.size` / `w.size` / `w.size` / `w.size`. After, they are
  reject / reject / reject / `w.compressed_size` / `w.compressed_size` / `w.compressed_size`.
  `compressedSafeWitnessBytes_ok` is the arithmetic bound.
* **Transaction wire size.** A SECP256K1 transaction of exactly 1,572,864 / 1,572,865 wire bytes is not
  generatable as an honest chunk (the producer drops it), so it is tested in `TestGateBCaps.lean`.
* **`numShards > 64`.** A 65-shard chain is not runnable in the test environment, and no corpus case
  reaches it. The lift removes one comparison and nothing in the pipeline depends on the shard count.

## 5. Runtime and memory (for W02/W16)

These are wall times and max RSS of one `nearspec-v3-check-successor --tier allFeatures` process on the
shared host (load 40-260 during the runs, so times are upper bounds):

| case | witness | wall | max RSS |
|---|---|---|---|
| `wsize.above` | 9.46 MB | 133 s | 1,005 MB |
| `wsize.near-above` | 8.43 MB | 142 s | 877 MB |
| `wsize.near-below` | 8.36 MB | 89 s | 868 MB |
| `wsize.below` | 6.68 MB | 43 s | 657 MB |
| `gas.above` (1.8 Pgas, 2 × 16 `memory.fill` of 64 MiB) | 2.9 KB | 119 s | 135 MB |
| `gas.below` (0.9 Pgas) | 2.7 KB | 62 s | 134 MB |
| `fuel.nest.large` (≈1.8·10⁷ steps) | 2.7 KB | 1.8 s | 65 MB |
| segment 71 blocks | 144 KB | 5.3 s | 81 MB |
| constructed 64 MiB witness (rejected before decoding) | 64 MiB | 3-4 s | 2.23 GB |

Scaling: memory is about **106 B per witness byte**. The checker holds the claim and witness as
`List UInt8`, and an 8 MiB → 64 MiB witness costs 0.9 → 2.2 GB just to be read (≈7 GB projected for
a decoded 64 MiB witness). Time grows with the bytes of large transactions and receipts (≈14 s/MB
on the pad-argument fixtures). Function-call gas costs ≈66 s per Pgas through `memory.fill`, whose
`Exec.memFill` writes one byte per state update; instruction-heavy gas is far slower per gas. The
corpus average was about 0.25 s per case.

## 6. Open

* **Fuel sufficiency** is argued (§1.3) and tested, not proved in Lean. The signed path keeps the
  former budget.
* **`w.compressed_size`** is a conservative stand-in for nearcore's 48 MiB compressed-witness limit.
  An exact rule needs a zstd model or the encoded length as an authenticated input. Witnesses in
  (50,000,000, 64 MiB] stay excluded.
* **Contract-code responses** are bounded at 64 MiB uncompressed in nearcore
  (`MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE`, `contract_distribution.rs:372`). The Lean witness
  file carries codes with no total bound. This is a transport/cache boundary question (cold
  validation), not modelled here.
* `gasCap` and the 8 MiB / 64-shard / 32-block bounds remain on the named narrower successor tiers.
  Whether they should be lifted there too is a tier-design decision (UQ-012).
* The runtime of large witnesses (§5) is a W16 budget item: list-based bytes and per-byte memory
  fill.
