# near-arena-oracle-v3-d3 — the D3α oracle

Domain-D3α oracle for `near/pv86/chunk-validation/v0`: real chunk state witnesses with WASM
`FunctionCall`s from multi-shard nearcore `TestEnv` chains (nearcore 2.13.4,
`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, PV 86), each judged by nearcore's own stateless
validator with the contract code it needs appended to the witness, classified against `InD3α`,
plus mutants (the D2 set and code-blob mutants) with nearcore verdicts. It is the reference corpus
for the RuntimeD3 full-runtime difftest.

## Crate layout

`oracle/v3` (frozen, pinned by the signed D0 challenge) and `oracle/v3-d1` (the D1/D2 oracle) are
not modified. This crate reuses their modules unchanged through `#[path]` (`src/main.rs`):
`claim`, `d0`, `enc`, `judge`, `mutate` from `../v3/src`; `chaingen`, `chaind2`, `d1`, `d1gen`,
`d1judge`, `d2`, `d2gen` from `../v3-d1/src`. New modules:

| module | content |
|---|---|
| `src/d3contracts.rs` | the contracts (below), the code registry (hash → bytes), the D3α code scan (wasmparser 0.236.1, nearcore's version) |
| `src/d3gen.rs` | D3 genesis records and D3 traffic (random `d3rich` programs, FunctionCall / Delegate / deploy transactions) |
| `src/chaind3.rs` | the D2 chain loop (`chaind2.rs`) with the D3 genesis, D2 + D3 traffic, capture of each witness's contract accesses, cold judging |
| `src/d3judge.rs` | the reference judge: a cold nearcore validator (below) |
| `src/d3.rs` | `InD3α` classification, metadata, code mutants, case writing |
| `scripts/gen-d3-corpus.sh` | one process per chain, merge into `OUT/{d3,ood,mutants}`, `OUT/summary.json` |

The build uses the pinned nearcore through `vendor -> ../vendor` and nearcore's own `Cargo.lock`
(copied from `../v3-d1`), like the other oracle crates. It shares `../d3-ttn/target`:

```
cd oracle/v3-d3
CARGO_TARGET_DIR=$PWD/../d3-ttn/target RUSTC_WRAPPER= taskset -c 8-15,24-31 \
  /data/illia/nearproof-deps/bin/heavy cargo build --offline
../d3-ttn/target/debug/near-arena-oracle-v3-d3 contracts      # the code registry
```

Unlike `../v3-d1` this crate keeps near-store's debug assertions. `v3-d1` turns them off only for
its D1 class `dup_bad_sig_first`, which D3 chains do not inject.

## Contracts (`contracts/*.wat` → `contracts/*.wasm` with `wasm-tools parse`)

| contract | accounts | what it does |
|---|---|---|
| `d3rich` (5 603 B) | `s{k}rc` on every shard (genesis); deployed at run time | `run` / `cb` run their input as a byte-coded program (opcode table at the top of the `.wat`): storage write/read/has_key/remove (values ≤ 64 KiB), `log_utf8` / `log_utf16` (including invalid UTF-8 and UTF-16), `value_return`, `promise_create` / `then` / `and`, `promise_batch_create` / `then` with batch actions FunctionCall (also with gas weight), Transfer, CreateAccount, AddKey (full access and function call), DeployContract (`d3tiny`, embedded), DeleteKey, Stake, DeleteAccount, `promise_return`, `promise_results_count` / `promise_result` (callbacks log the statuses, can forward result 0), the getters (balances, attached deposit, storage usage, block index/timestamp, epoch height, prepaid/used gas, account ids, signer key, random seed, `chain_id`, `validator_stake` / `validator_total_stake`, input), `sha256` / `keccak256` / `keccak512` / `ripemd160`, register ops (including an invalid register), `promise_yield_create` / `promise_yield_resume`, `memory.grow`, deep recursion, burn loops (gas exhaustion), `panic`, `panic_utf8`, `abort`, `unreachable`, out-of-bounds load, divide by zero, invalid promise indices and account ids. `bad_sig` has the wrong signature and `noop` is empty. Integer-only, no curve imports. |
| `d3tiny` (345 B) | deployed at run time (transactions and `d3rich` batches) | `storage_write("t", input)`, `log_utf8("tiny")`, `value_return(input)` |
| `ttn2` (`../d3-ttn/ttn2.wasm`, unchanged) | `s{k}ctr`, `s{k}ctr2` on every shard, with `f`/`k` data as in d3-ttn; deployed at run time | storage over several contracts, promise chains |
| `d3float` | `s0fl` | f64 arithmetic: **out of D3α** (`e.float`) |
| `d3curve` | `s1cv` | `run` / `cb` call `ecrecover`: **out of D3α** (`e.ood_host`) |
| `d3hostx` (1 109 B) | `s{3 mod n}hx` | imports `ecrecover` and state-init / global-contract / gas-key host functions. `run` / `cb`: `storage_write("x", input)`, calls none of them (**in D3α**, spec §10.0a P3). `curve`: `ecrecover`; `glob`: `promise_batch_action_use_global_contract`; `stinit`: `promise_batch_action_state_init`; `gaskey`: `promise_batch_action_add_gas_key_with_full_access` (**out**, `e.ood_host`). `mlkey`: input = op ‖ borsh key, a self batch with AddKey / Stake / DeleteKey of that key; the generator always passes an ML-DSA-65 key (**out**, `e.mldsa_key`, P4) |
| `d3tiny` on `0xd3d3…d3` | the ETH-implicit account `ETH_LOCAL` (genesis) | a `Local` contract on an ETH-implicit account: calls are **out of D3α** (`e.eth_implicit_local`, P5) |
| `d3ed` | `s2ed` | imports `ed25519_verify` (see "Domain") |
| D2's `program` and small modules | `s{k}ct` and D2 deploys | reused D2 traffic |

All registry contracts are pre-compiled into every TestEnv client's compiled-contract cache before
the first block (`chaind3::setup_d3`). This avoids the TestEnv deadlock between wasmtime
compilation and chunk validation on rayon described in `../v3-d1/src/chaind2.rs`.

## Workload (`src/d3gen.rs`, `src/chaind3.rs`)

Each height mixes three kinds of traffic:

* **The D2 workload, unchanged.** This is `d2gen::World`: every non-WASM action kind, delegates,
  gas keys, stakes, bursts with forced missing chunks, and the adversarial chunk producer's
  crafted D2 classes.
* **D3 transactions, 0–4 per selected shard and height.** From the honest accounts:
  * FunctionCalls to `d3rich` with random programs. 1–8 ops, nested promise programs to depth 2,
    cross-shard calls and callbacks, `promise_and` joins, batches that create sub-accounts on any
    shard, and a final failure with probability 0.12.
  * Multi-action receipts (`[FunctionCall, Transfer?, FunctionCall]`).
  * Attached deposits (0, 1, 10²¹, 1–4·10²⁴ yocto).
  * Tight gas (0.5–8 Tgas with a burn loop).
  * `ttn2` calls.
  * Method edge cases: missing method, wrong signature, a code-less receiver.
  * Rare calls to the out-of-domain contracts.
  * `[CreateAccount, Transfer, AddKey, DeployContract(d3tiny|ttn2|d3rich), FunctionCall?]`
    bundles. The code is deployed and run in the same receipt.
  * Calls to the accounts those bundles created, which are now state code.
  * Redeploy-and-call transactions signed by those accounts.
  * `Delegate` meta transactions wrapping 1–2 FunctionCalls (+ Transfer). The sender signs with
    its genesis key `d3dl`.
* **Chain parameters, as the D2 generator.** Chain `i` has 4/5/6 shards, Reed–Solomon seat
  counts 8/100/16/3, chunk gas limits 1000/1000/1000/10/60 Tgas and epoch lengths 30/20/12, so
  segments cross epoch boundaries. Chain `i ≡ 5 (mod 8)` misses one shard's chunks for 40
  heights.

## How a stateless validator obtains contract code (nearcore 2.13.4)

1. **Code is not in the witness.** Since PV 73 the protocol excludes contract code from the
   state witness (`ProtocolFeature::_DeprecatedExcludeContractCodeFromStateWitness => 73`,
   `core/primitives-core/src/version.rs:271,528`).
   * The runtime reads code through `ContractStorage`, which is built on the trie's *underlying*
     storage: `ContractStorage::new(self.trie.storage.clone())`
     (`core/store/src/trie/update.rs:84,96`).
   * Code bytes are fetched with `storage.retrieve_raw_bytes(code_hash)`
     (`core/store/src/contract.rs:104-130`). This bypasses the trie recorder, so code bytes
     never enter `main_state_transition.base_state`.
   * Contracts deployed earlier in the same chunk come from the in-memory `ContractsTracker`
     (`contract.rs:15-79`).
2. **The producer records which contracts were called.** `action_function_call` calls
   `record_contract_call` (`runtime/runtime/src/function_call.rs:56, 355-395`). It records the
   code hash only when applying for `UpdateTrackedShard` and when the pre-state trie holds that
   hash for the account ("This avoids recording contracts that do not exist or are
   newly-deployed").
   * `ContractStorage::finalize` returns these `contract_accesses` together with the committed
     `contract_deploys`.
   * Both are stored in `StoredChunkStateTransitionDataV1`
     (`core/primitives/src/stateless_validation/stored_chunk_state_transition_data.rs:17-38`).
   * Witness creation hands them on as `ContractUpdates` with the witness
     (`chain/chain/src/stateless_validation/state_witness.rs:200-235`) to the
     `PartialWitnessActor` in a `DistributeStateWitnessRequest`
     (`chain/client/src/stateless_validation/partial_witness/partial_witness_actor.rs:95-99`).
3. **The producer distributes accesses, witness and deploys, in this order**
   (`partial_witness_actor.rs:207-280`):
   1. A `ChunkContractAccesses` message (the accessed code hashes) to the chunk validators.
   2. The witness parts.
   3. The new deploys as Reed–Solomon `PartialEncodedContractDeploys` parts
      (`:786-806`). Validators that receive the deploys decompress and *precompile* them
      (`:592-686`), so later chunks find them in the compiled-contract cache.
4. **A validator requests only the codes it has not compiled.** On `ChunkContractAccesses`
   (`:696-746`), the validator checks each hash against its compiled-contract cache
   (`contracts_cache_contains_contract`, `chain/client/src/stateless_validation/mod.rs:18-25`,
   i.e. `near_vm_runner::contract_cached`). It sends a `ContractCodeRequest` for the missing
   hashes to a random chunk producer.
   * The producer answers only hashes that are in the stored `contract_accesses` of that
     transition. It reads them with `retrieve_raw_bytes` from its storage (`:886-985`).
   * The response is decompressed and stored in the witness tracker (`:988-1001`). The set of
     received hashes must equal the requested set, otherwise it is ignored
     (`partial_witness_tracker.rs:290-326`).
   * If the request times out (`ACCESSED_CONTRACTS_REQUEST_TIMEOUT` = 2 s, `:48`) or no
     accesses message arrived, validation proceeds without codes (`try_finalize`, `:353-400`).
5. **The codes join the witness's trie values.** Before handing the witness to the chunk
   validation actor, the tracker appends the received codes to
   `main_state_transition.base_state`
   (`partial_witness_tracker.rs:693-696`: `values.extend(contracts…)`). This is exactly what
   `judge::decode_witness(bytes, codes)` does with the blobs that `enc::encode_witness(witness,
   codes)` appends to `witness.bin` (spec/claim-v3.md).
6. **Execution needs the cache or the code bytes.** Near-vm-runner first looks the code hash up
   in the compiled-contract cache, and only on a miss asks for the code
   (`runtime/near-vm-runner/src/wasmtime_runner/mod.rs:699-725`, `ContractCodeNotPresent`).
   During witness validation, a missing body for an account whose code hash is set is turned
   into `StorageError::MissingTrieValue` (`runtime/runtime/src/function_call.rs:293-305`), so
   the validator does not endorse.

So a validator's verdict depends on its compiled-contract cache. A warm validator accepts an
honest witness without any code, while a cold one needs every accessed code.

**The oracle's judge is the cold validator** (`src/d3judge.rs`). It is a `NightshadeRuntime`
over the judging client's store and epoch manager with an in-memory compiled-contract cache that
is emptied before every judgment. Every cache handle (per apply, per pipelined preparation task)
is bound to its judgment, so a straggling preparation task cannot warm the next judgment. The
judge runs the same steps as `oracle/v3/src/judge.rs`: actor checks,
`pre_validate_chunk_state_witness`, `validate_chunk_state_witness`, with panics counted as
rejects. `Rel` is therefore defined for a validator with no compiled contracts, which is
independent of node history.

### Which codes are attached (the "needed codes")

`codes` = the code bytes, in the order of their hashes, of **nearcore's own `contract_accesses`
of the main transition**. The oracle reads them from the producer's
`DistributeStateWitnessRequest::contract_updates` (`chaind3.rs`, capture loop) and takes the bytes
from the code registry. This is exactly what a cold validator requests and the producer can
serve:

* **What the set includes.** Every contract that a FunctionCall of the main transition executes,
  when its code was in the pre-state.
* **What it leaves out.** Codes deployed earlier in the same chunk: they are executed from the
  receipt's `ContractsTracker`, not from storage.
* **Implicit transitions need no code.** A missing chunk is applied with
  `is_new_chunk = false`, which returns before any receipt is processed
  (`runtime/runtime/src/lib.rs:1774-1781`).

The classifier checks this set against its own walk over the receipts (`d3::analyze_d3`). That
walk computes, for every FunctionCall that reaches its dispatch point, the receiver's code at that
moment:

* It starts from the pre-state.
* It applies deploys, account creations and deletions of earlier receipts in execution order.
* A receipt's own changes are kept only if the receipt succeeded (nearcore rolls back failed
  receipts).
* An execution is labelled `state` iff the pre-state holds that hash for the account, which is
  nearcore's `record_contract_call` rule.

`features.accesses_equal_state_executed` records whether the `state` set equals nearcore's
accesses (summary counter `check.accesses_differ_from_state_executed`).

## Domain `InD3α` (`src/d3.rs`)

`InD3α` = `InD2` with `e.wasm` lifted and `w.no_code` lifted, conjoined with:

* `c.no_resharding`: one epoch, no epoch start in the segment, no split gate
  (`DomainD3.lean` `noResharding`; requirements §1). **This is stricter than D2's
  `c.same_layout`.** Multi-epoch D2 segments are therefore *outside* D3α, so `InD2 ⊄ InD3α` on
  those cases.
* `e.float`: an executed contract has a float value type (function type, local, global,
  block/select type) or a float opcode.
* `e.ood_host` (spec §10.0a P3): a dispatched FunctionCall *calls* a Lean `curveHosts` function
  (`spec/lean/v3/NearSpecV3/Wasm/Exec.lean`: alt_bn128_*, bls12381_*, `ecrecover`,
  `p256_verify`) or a state-init / global-contract / gas-key host function (`Wasm.realOodHosts`).
  Importing one is in D3α (`features.ood_host_import`; counters `ood_host_import.{called,
  not_called, not_called_in_d3}`).
  * Decided per dispatched call by `d3contracts::ood_call(contract, method)`: the registry
    contracts call these functions unconditionally in the listed methods, and no other registry
    contract imports them.
  * Cross-check: a receipt whose gas profile shows a curve ext cost or a global-contract /
    state-init / gas-key action cost, but no call marked by the table, is also marked, and is
    counted in `check.ood_host_profile_unmarked` (must stay 0).
  * `ed25519_verify` is **not** in that list: the Lean WASM spec models it (`Host.lean`).
  * The requirements table (§1.1) places it in D3γ. The oracle only records it
    (`features.ed25519_import`, contract `d3ed`), so either reading can be applied.
* `e.mldsa_key` (P4): a dispatched FunctionCall builds a Stake / AddKey / DeleteKey action with an
  ML-DSA-65 key (d3hostx `mlkey`). The checkers report this as `w.shape`.
* `e.eth_implicit_local` (P5): a FunctionCall reaches an ETH-implicit account (`0x` + 40 hex)
  whose contract is `Local`. This is the conservative form of the legacy-wallet exclusion.
* `e.g_alpha`: the chunk's Σ `gas_burnt_for_function_call` exceeds `G_α` = 2²² · 822,756 =
  3,450,867,449,856 (`D3.gAlpha`, `spec/lean/v3/NearSpecV3/D3/FunctionCall.lean`; the Lean checker
  reports `out of domain (e.g_alpha)`).
  * The value is read from each receipt outcome's gas profile (`ExecutionMetadata` V3/V4):
    Σ `actions_profile` + Σ `wasm_ext_profile` + `wasm_gas`.
  * Why this equals nearcore's `gas_burnt_for_function_call`: nearcore adds each FunctionCall's VM
    `burnt_gas` to it and merges the VM profile into the receipt's
    (`runtime/runtime/src/function_call.rs:144-153`). No other action writes the profile. A VM
    profile sums to its burnt gas, because `wasm_gas` = burnt − action − host
    (`near-vm-runner/src/profile.rs` `compute_wasm_instruction_cost`).
  * The action part is the gas of promise actions the contract creates; it is part of the VM's
    burnt gas. A multi-action receipt's profile already sums over its FunctionCall actions.
  * `features.fc_gas_burnt_for_function_call` records the value for every case. Mutants carry
    their base's value. The counter `check.fc_profile_exceeds_gas_burnt` (a receipt whose profile
    sum exceeds its `gas_burnt`) must stay 0.
* `e.code_cache`: the verdict depends on the compiled-contract cache. This is judged per code-blob
  list, so in practice only code mutants hit it. Walk the FunctionCalls that dispatch on the
  receiver's *pre-state* code, in execution order, and take the first one whose code blob is
  neither appended nor among the witness's trie values. The condition holds when the same code
  (same hash) was deployed earlier in the chunk, in any receipt, committed or rolled back. If it
  was not deployed earlier, nearcore rejects deterministically with `MissingTrieValue`, so the
  case stays in domain. This mirrors `D3.functionCall`'s cold-cache rule (spec §10.0/§10.1).
  Honest witnesses carry every accessed code, so they are never out of D3α for this reason. A
  mutant meta records `in_d3` / `d3_violations` / `expected_rel_d3` with this condition, and the
  counters are `mutant_ood.e.code_cache.nearcore_{accept,reject}`.
* `o.unknown_receipt`, `o.code_unknown`: oracle limits. These are an executed receipt the
  oracle cannot locate and a code outside the registry.

"Executed contracts" are those of the walk above, including codes deployed in the chunk.
`features.fc_gas_burnt` records the total `gas_burnt` of the receipts that dispatched
FunctionCalls, including action fees. `G_α` uses `fc_gas_burnt_for_function_call` instead.

## Output layout (as the D2 corpus)

`OUT/d3/<chain>-h<height>-s<shard>/` holds honest D3α cases and `OUT/ood/…` holds honest cases
outside D3α (capped per violation family by `--ood-cap`). `OUT/mutants/<case>-<mutation>/` holds
the mutants. Each case directory has these files:

* **`claim.bin`.** The claim-v3 encoding.
* **`witness.bin`.** `encode_witness(borsh(ChunkStateWitness), codes)`.
* **`meta.json`.** The case's verdict, classification and features:
  * The verdict: `nearcore` (the cold verdict with `codes`), `expected_rel`,
    `nearcore_warm_no_codes` (the producer's warm-cache verdict without codes) and
    `nearcore_cold_no_codes`.
  * The classification of every rung: `in_dK` / `dK_violations` / `expected_rel_dK` for K = 0..3.
  * The codes: `contract_accesses`, `codes` (hash, name, length) and `executed_contracts`
    (hash, name, account, `state` | `deployed_in_chunk`, float, curve imports, ed25519 import).
  * The transactions: `tx_labels`, `tx_results`, `new_tx_labels`.
  * The receipts: `action_results` and `receipt_classes` (from D2's analysis).
  * `features`: the D2 features plus `n_function_calls` (dispatched), `n_function_calls_with_code`,
    `n_fc_failures`, `fc_failure_kinds`, `n_logs`, `n_promises` (receipts created by
    FunctionCall receipts), `n_callbacks` (FunctionCall receipts with input data),
    `fc_gas_burnt`, `fc_gas_burnt_for_function_call` (`e.g_alpha`), `contracts_ran`, `deployed_in_chunk`, `ran_deployed_in_chunk`,
    `code_blobs`, `code_bytes`, `ed25519_import`, `ood_host_import`, `n_ood_host_calls`,
    `ood_host_profile_unmarked`.
  * Gas price coverage: `chunk_gas_price` (B2's `next_gas_price`), `tokens_burnt_receipts`,
    `tokens_burnt_txs`, `n_outcomes_tokens_burnt_nonzero`, `receiver_reward_est` (Σ receipt gas
    price · ⌊`gas_burnt_for_function_call` · 3/10⌋) and `n_receipts_with_receiver_reward`
    (summary counters `honest_with_tokens_burnt`, `honest_with_receiver_reward`).

`OUT/summary.json` holds the totals, violation counts and the `d3` counters: coverage sums,
failure kinds, contracts run by source, mutant verdicts per family and consistency checks.

### Mutants (all verdicts from the cold nearcore validator unless marked)

* **The full set, on every `--mutate-every`-th D3 case.** It contains:
  * D0's `mutate::mutants`.
  * The single trie-node drops (`drop_each_node`, every second sampled case, capped by
    `--drop-cap`).
  * D1's mutants. The `tx_valid` ones are judged with the claim's flags.
  * D2's header mutants (`hdr2.*`) and its derived trusted-fact mutants. These are copied
    because they are private in `d2.rs`.
  * The code mutants below.
* **What the full set leaves out.** `t.chain_id` mutants are dropped when an executed contract
  imports `chain_id` (or when D2's ETH-implicit rule applies): nearcore cannot judge them
  (counter `mutants_skipped.t.chain_id`).
* **Code mutants only, on a fraction `--code-mutant-p` of the other D3 cases with codes.** The
  code mutants are:

| mutation | change |
|---|---|
| `code.drop.i` | remove needed blob i |
| `code.flip.i` | flip one bit of blob i |
| `code.truncate.0` | blob 0 cut in half |
| `code.none` | no blobs (≥ 2 needed) |
| `code.reorder` | blobs reversed |
| `code.duplicate` | blob 0 appended twice |
| `code.extra_unneeded` | an unneeded registry contract appended |
| `code.extra_garbage` | random bytes appended |

## Regenerating the corpus

```
OUT=/tmp/claude-1002/-data-illia-nearproof/29f86fd5-cfb7-44c7-996e-70d81e3d17a4/scratchpad/d3c7 \
SEED=7 CHAINS=8 BLOCKS=200 PAR=1 MUTATE_EVERY=20 CODE_MUTANT_P=0.25 OOD_CAP=25 DROP_CAP=48 \
  oracle/v3-d3/scripts/gen-d3-corpus.sh
```

That is, per chain `i`, the following command is run, followed by the merge:

```
RAYON_NUM_THREADS=256 taskset -c 8-15,24-31 /data/illia/nearproof-deps/bin/heavy \
  oracle/d3-ttn/target/debug/near-arena-oracle-v3-d3 gen --domain d3 --seed 7 --out OUT/parts/i \
  --first-chain i --chains 1 --blocks 200 --mutate-every 20 --code-mutant-p 0.25 --ood-cap 25 --drop-cap 48
```

Chains are byte-reproducible from (seed, chain index).

`MIN_GAS_PRICE=100000000` (`--min-gas-price`) sets the genesis `min_gas_price` (and
`max_gas_price` = 10²²). The default 0 keeps the TestEnv's zero gas price, under which the receiver
reward, `tx_burnt` and every outcome's `tokens_burnt` are 0. The gas-price corpus is seed 10:

```
OUT=.../d3c10 SEED=10 CHAINS=4 BLOCKS=200 PAR=1 MUTATE_EVERY=20 CODE_MUTANT_P=0.25 OOD_CAP=25 \
DROP_CAP=48 MIN_GAS_PRICE=100000000 oracle/v3-d3/scripts/gen-d3-corpus.sh
```

## Known nearcore behaviour relevant to D3

* **The validator's verdict depends on its compiled-contract cache.** Every honest witness that
  executes state code is rejected by a cold validator without codes (`MissingTrieValue`). A warm
  validator (the TestEnv clients) accepts it.
* **Finding: a missing pre-state code blob whose code was deployed earlier in the chunk gives a
  cache- and pipeline-dependent verdict (`e.code_cache`).** Take an executed pre-state contract
  whose code blob is missing from the witness, where the same code was deployed earlier in the
  same chunk (in any receipt, committed or rolled back). nearcore's verdict on such a witness
  depends on two things:
  * the compiled-contract cache: `DeployContract` precompiles into it
    (`runtime/runtime/src/actions.rs:297-341`), and a rollback of the deploying receipt does not
    evict the entry;
  * the order of the preparation pipeline: receipts that were prepared before the deploy ran were
    prepared against a cold cache.

  Both verdicts occur in the corpus. One code mutant was rejected (a pipelined call before the
  deploy) and another accepted (a postponed call after a rolled-back deploy). Such cases are
  therefore out of D3α (spec/near-chunk-validation-d3.md §10.0 decision 2, §10.1). In the seed
  7 / 8 / 9 / 10 corpora (2026-10-06 15:00 generation), nearcore accepted 61 / 75 / 18 / 15 of
  these mutants and rejected 31 / 50 / 13 / 16.
  `checkD3` reports exactly these mutants as out of domain.
* **Same-chunk deploys are not accesses.** Code deployed and executed in the same chunk is not a
  contract access and is never needed by a validator.
* **Accesses are not a minimal set.** `ContractsTracker::get` looks codes up by hash, whatever
  the account (`core/store/src/contract.rs:43-48,104-117`). So once any receipt of the chunk
  has deployed the same bytes, even on another account, a later call to a *state* contract with
  that hash is served from the tracker. nearcore still records it as an access (pre-state hash
  match), but no blob is needed. In the seed-7 corpus a few honest cases are accepted by the
  cold validator without codes (`honest_cold_no_codes_ok`). These are exactly cases where
  `d3rich` was also deployed earlier in the chunk, and their `code.drop.*` mutants are accepted.
* **Instant DeleteAccount receipts run on the current shard.** An instant `DeleteAccount`
  receipt from a meta transaction runs on the current shard (`runtime/runtime/src/lib.rs:1104`).
  This comes from the D2 traffic; D2's analysis classifies it as an `instant` receipt.
* **Extra codes are harmless.** Extra, duplicated or reordered code blobs never change the
  verdict, because the code store is a hash-addressed set of trie values. A blob whose bytes do
  not hash to a needed hash is equivalent to a missing one.
