# NEAR chunk state-transition boundary (pinned nearcore)

**Pin.** `near/nearcore` tag `2.13.4` (release 2026-09-03), commit
`44f7ae6cd7ef08bab604e20a473bf77e35d4c993` ("chore: prepare 2.13.4 mainnet release").
Shallow checkout at `/data/illia/nearproof-deps/nearcore`. Toolchain from
`rust-toolchain.toml`: Rust 1.93.0.

All `file:line` citations below are relative to that checkout and were read
directly from it. Anything not read directly from source is marked
**[unverified]**.

---

## 0. Protocol version in scope

* `STABLE_PROTOCOL_VERSION = 86`, and `PROTOCOL_VERSION` resolves to it in a
  non-nightly, non-spice build (`core/primitives-core/src/version.rs:628-647`).
  `MIN_SUPPORTED_PROTOCOL_VERSION = 83` (`version.rs:600`).
* Features gated at 85 include `AccountCostIncrease`, `ExecutionMetadataV4`,
  `GasKeys`, `DynamicResharding`, `StrictNonce`, `PostQuantumSignatures`,
  `YieldWithId`, `DelegateV2` and others. `EnforcePerReceiptStorageProofLimit`
  is gated at 86 (`version.rs:549-576`). `ProtocolFeature::enabled(pv)` is
  `pv >= feature.protocol_version()` (`version.rs:590-592`).
* **[unverified]** We have not checked whether mainnet has *voted in* PV 86 as
  of today. The binary supports up to 86. The arena should pin the slice to an
  explicit PV (we use 86) and not to "whatever mainnet runs".

---

## 1. The top-level function: `Runtime::apply`

`runtime/runtime/src/lib.rs:1717-1819`

```rust
pub fn apply(
    &self,
    trie: Trie,                                            // pre-state, rooted at prev_state_root
    validator_accounts_update: &Option<ValidatorAccountsUpdate>,
    apply_state: &ApplyState,
    incoming_receipts: &[Receipt],
    signed_txs: SignedValidPeriodTransactions,
    epoch_info_provider: &dyn EpochInfoProvider,
    state_patch: SandboxStatePatch,                        // must be empty outside sandbox (assert, :1733)
) -> Result<ApplyResult, RuntimeError>
```

The production caller is `NightshadeRuntime::process_state_update`
(`chain/chain/src/runtime/mod.rs:197-360`). It builds `ApplyState` from the
block and chunk context and the epoch manager. It builds
`ValidatorAccountsUpdate` only on the first block of an epoch
(`mod.rs:231-276`). It picks `config = runtime_config_store.get_config(current_protocol_version)`
(`mod.rs:284`) and maps `RuntimeError`s, panicking on integer overflow or
receipt-validation errors (`mod.rs:356-368`).

### 1.1 Inputs

`ApplyState` (`lib.rs:164-217`):

| field | role | trust class |
|---|---|---|
| `apply_reason` | UpdateTrackedShard / ValidateChunkStateWitness / ViewTrackedShard | context (non-semantic except metrics) |
| `block_height` | used in receipt-id and action-hash derivation (`lib.rs:220-227`, `core/primitives/src/utils.rs:278-335`) | public / block-committed |
| `prev_block_hash` | bandwidth scheduler seed (`bandwidth_scheduler/mod.rs:118-125`), stake checks | public |
| `shard_id`, `epoch_id`, `epoch_height` | shard and epoch identity | public |
| `gas_price` | block gas price (burn price) | public (block header) |
| `block_timestamp`, `random_seed` | contract-visible env | public |
| `gas_limit` | chunk gas limit; also used as the compute limit (`lib.rs:2668`) | public (chunk header `gas_limit`) |
| `current_protocol_version` | selects feature gates and `RuntimeConfig` | public (epoch) |
| `config: Arc<RuntimeConfig>` | all fees and limits (see §4) | **pinned constant** derived from PV |
| `next_wasm_config`, `cache` | compiled-contract cache warming | non-semantic (performance only) |
| `trie_access_tracker_state` | TTN accounting | affects gas only for contract storage ops |
| `is_new_chunk` | missing chunk ⇒ only the bandwidth scheduler runs (`lib.rs:1773-1779`, `missing_chunk_apply_result` `lib.rs:2937`) | public |
| `save_receipt_to_tx` | indexing only | non-semantic |
| `congestion_info: BlockCongestionInfo` | per-shard congestion of the previous chunks | public (chunk headers) |
| `bandwidth_requests: BlockBandwidthRequests` | previous-height requests | public (chunk headers) |
| `on_post_state_ready` | callback | non-semantic |

Other inputs:

* `trie`: the pre-state. Committed by `prev_state_root` (chunk header field,
  see §6). In stateless validation the trie is backed by a recorded
  `PartialState` (witness) (`core/primitives/src/stateless_validation/state_witness.rs:282-295`).
* `incoming_receipts`: receipts from other shards' previous chunks. The order
  comes from a block-hash-seeded shuffle done by the chain, outside `apply`
  (`chain/chain/src/sharding.rs:9-21`, `chain/chain/src/chain.rs:1184-1205`).
  Each is validated with `validate_receipt(.., ExistingReceipt)`. A failure
  aborts the whole apply with `RuntimeError::ReceiptValidationError`
  (`lib.rs:2570-2577`).
* `signed_txs`: the chunk's transactions plus validity-period flags (`runtime/runtime/src/types.rs`).
* `validator_accounts_update` (`lib.rs:231-242`): stake returns and rewards at
  an epoch boundary, applied first (`lib.rs:1750-1756`, `update_validator_accounts` `lib.rs:1599`).
* `epoch_info_provider`: validator stakes, shard layout, chain id. This is an
  **external-trust oracle** from the epoch manager.

### 1.2 Processing order (`lib.rs:1734-1819`)

1. Update validator accounts (only at an epoch boundary).
2. Load the delayed-receipt queue (`DelayedReceiptQueue::load`).
3. **Run the bandwidth scheduler on every chunk, including missing ones**
   (`lib.rs:1765-1771`). It writes `TrieKey::BandwidthSchedulerState` every
   time (`bandwidth_scheduler/mod.rs:127-137`), so **every applied chunk
   changes the state root even with zero txs and receipts**. The sanity hash is
   `sha256(prev_sanity_hash ‖ sha256(borsh(all_shards)))`.
4. If `!is_new_chunk`, return early.
5. Build `ReceiptSink` (congestion control and outgoing buffers), then forward
   previously buffered receipts (`lib.rs:1784-1794`).
6. `process_transactions` (`lib.rs:1882`): verify signature, nonce and balance
   (`verifier.rs:272 verify_and_charge_tx_ephemeral`), charge the signer, and
   convert each tx into a receipt (`Receipt::from_tx`, `core/primitives/src/receipt.rs:344-365`)
   with `gas_price = max(block gas_price, min_gas_purchase_price)`
   (`runtime/runtime/src/config.rs:462-464`). Local receipts (receiver on the
   same shard) are queued in `local_receipts`.
7. `process_receipts` (`lib.rs:2658-2721`): **local receipts, then delayed,
   then incoming, then promise-yield timeouts**. Each stage stops when
   `total.compute >= gas_limit` or the storage-proof soft limit is exceeded,
   and pushes the remainder to the delayed queue (`lib.rs:2380-2388`, `2563-2585`).
8. `validate_apply_state_update` (`lib.rs:2723-2869`): writes PromiseYield
   indices if they changed, finalizes congestion info, generates bandwidth
   requests, `commit(UpdatedDelayedReceipts)`, then `state_update.finalize()`.
   `finalize` turns the committed key→value map into `TrieChanges` and the new
   root (`core/store/src/trie/update.rs:242-262`).

### 1.3 Outputs: `ApplyResult` (`lib.rs:340-362`)

| field | meaning | committed where |
|---|---|---|
| `state_root` | new trie root | `ChunkExtra.state_root` → next chunk header `prev_state_root` |
| `trie_changes` | node insertions and deletions | local DB only |
| `validator_proposals` | dedup'd stake proposals | next chunk header `prev_validator_proposals` |
| `outgoing_receipts` | receipts to other shards (and to self for the next chunk) | next chunk header `prev_outgoing_receipts_root` |
| `outcomes: Vec<ExecutionOutcomeWithId>` | one per tx and per executed receipt | next chunk header `prev_outcome_root` |
| `state_changes` | per-key change log with causes | RPC/indexer only, not committed |
| `stats` (incl. `balance: BalanceStats`) | burnt amounts etc. | `prev_balance_burnt` = tx_burnt + other + slashed − subsidized (`chain/chain/src/runtime/mod.rs:387-404`) |
| `proof: Option<PartialStorage>` | recorded trie nodes (state witness) | `ChunkStateWitness.main_state_transition.base_state` |
| `congestion_info` | own shard congestion | next chunk header `congestion_info` |
| `bandwidth_requests` | requests | next chunk header `bandwidth_requests` |
| `delayed_receipts_count`, `processed_receipts`, `processed_yield_timeouts`, `contract_updates`, `receipt_to_tx`, `metrics`, `bandwidth_scheduler_state_hash` | bookkeeping, witness-building, sanity | various / not committed |

`gas_used` in the chunk extra is the sum of `outcome.gas_burnt` over all
outcomes (`chain/chain/src/runtime/mod.rs:373-376`).

---

## 2. Receipt and action execution

* `process_receipt` (`lib.rs:1303-1527`) dispatches on `VersionedReceiptEnum`:
  Data, Action, PromiseYield, PromiseResume, GlobalContractDistribution.
* `process_action_receipt` (`lib.rs:1529-1597`): if any `input_data_ids` are
  missing, postpone (`PostponedReceiptId`, `PendingDataCount`,
  `PostponedReceipt` keys). Otherwise execute.
* `apply_action_receipt` (`lib.rs:776-1156`) does the following:
  1. Collects promise results and removes `ReceivedData` (`:797-821`).
  2. `commit(ActionReceiptProcessingStarted)` (`:825`).
  3. `account = get_account(receiver)` (`:828`).
  4. Charges the base `new_action_receipt` exec fee (`:833-836`).
  5. For each action, calls `apply_action` (`lib.rs:523-773`), which charges
     `exec_fee(action)`, runs `check_account_existence` and
     `check_actor_permissions` (`actions.rs:776-899`), then the action-specific
     handler. Results merge via `ActionReceiptResult::merge` (`:439-485`).
     The first error stops the loop (`:880-884`).
  6. If ok, `check_storage_stake` (`verifier.rs:48-84`) on the receiver account.
     On ok, `set_account`. Otherwise the error is `LackBalanceForState` (`:888-910`).
  7. Gas burn price is `min(receipt.gas_price, block gas_price)` under
     `AccountCostIncrease` (PV≥85) (`:916-922`).
  8. Refunds: for non-system predecessors, `refund_unspent_gas_and_deposits`
     (`lib.rs:1166-1301`). For system (refund) receipts there is no refund and
     a failed refund's deposit is burnt (`:924-932`).
  9. `commit(ReceiptProcessing)` on success, or `rollback()` on failure. Only
     state committed *before* this receipt survives a failure (`:960-969`).
  10. `tokens_burnt = gas_burnt*burn_price − deficit + penalty + create_account_charge + action tokens_burnt`
      (`:973-984`). Before PV85 the price surplus is also added.
  11. Function-call gas reward to the receiver is `burnt_gas_reward = 3/10`
      (`parameters.yaml:6-9`) of `gas_burnt_for_function_call` (`:988-1014`).
  12. Output data receipts, then new receipt ids
      `create_receipt_id_from_receipt_id(parent, height, idx)` =
      `sha256(parent ‖ height_le64 ‖ idx_le64)` (`utils.rs:278-284, 328-335`).
      Each new receipt is forwarded or buffered via `ReceiptSink`
      (`:1078-1115`; instant receipts `:1103-1105`).
  13. The outcome status is `SuccessValue / SuccessReceiptId / Failure`
      (`:1117-1124`). Metadata is V4 under `ExecutionMetadataV4` (`:1128-1135`).
* Actions (`core/primitives/src/action/mod.rs:349-370`): CreateAccount=0,
  DeployContract=1, FunctionCall=2, Transfer=3, Stake=4, AddKey=5, DeleteKey=6,
  DeleteAccount=7, Delegate=8, DeployGlobalContract=9, UseGlobalContract=10,
  DeterministicStateInit=11, TransferToGasKey=12, WithdrawFromGasKey=13,
  DelegateV2=14. Handlers are in `runtime/runtime/src/actions.rs`,
  `access_keys.rs`, `global_contracts.rs`, `deterministic_account_id.rs`,
  `function_call.rs`.
* WASM: `action_function_call` (`runtime/runtime/src/function_call.rs`) uses
  `near-vm-runner`. The VM kind is Wasmtime since PV84
  (`core/parameters/res/runtime_configs/84.yaml:2`). Host functions are listed
  in the `imports!` macro (`runtime/near-vm-runner/src/imports.rs:96ff`, about
  90 entries; the exact count was not reconciled with the PV gates). Their
  semantics are in `runtime/near-vm-runner/src/logic/logic.rs`. The
  runtime-side `External` impl is `runtime/runtime/src/ext.rs`. WASM
  preparation and instrumentation (gas metering injection, stack limits) is in
  `runtime/near-vm-runner/src/prepare*`.

## 3. Balances, storage staking, access keys, failures

* `Account` (`core/primitives-core/src/account.rs:38-41`) is V1 or V2. The
  borsh form of V1 is the bare struct `{amount:u128, locked:u128, code_hash:[u8;32], storage_usage:u64}`
  (72 bytes, `account.rs:54-63`, serialize `:437-446`). V2 is
  `u128::MAX sentinel ‖ 0u8 ‖ AccountV2{amount, locked, storage_usage, contract: AccountContract}`
  (`:146-155`, `:406-447`). `Account::new` builds **V1** whenever the contract
  is `None` or `Local`, and V2 only for global contracts (`:163-180`).
* Storage staking: `required = storage_amount_per_byte × storage_usage`, and
  ok if `amount + locked ≥ required` or `storage_usage ≤ 770` (zero-balance
  account, NEP-448) (`verifier.rs:25, 48-90`). `storage_amount_per_byte = 1e19 yN`
  (`parameters.yaml:35`). `num_bytes_account=100`, `num_extra_bytes_record=40` (`:36-37`).
* Access keys: the `TrieKey::AccessKey` key is `0x02 ‖ account ‖ 0x02 ‖ key_handle` (`trie_key.rs:461-466`).
  Nonce and allowance are updated in tx verification (`lib.rs:312-328`). Gas
  refunds top up the allowance (`try_refund_allowance`) or the gas-key balance
  (`lib.rs:2898-2919`).
* Failure semantics: per-receipt rollback (`lib.rs:960-969`). Deposit refund
  receipt to `balance_refund_receiver` and gas refund receipt to `signer_id`
  (`lib.rs:1286-1298`). Refund receipts have predecessor `system`, gas_price 0
  (`receipt.rs:497-537`) and burn no gas (`lib.rs:972`).

## 4. Gas and fees

* `RuntimeConfig` (`core/parameters/src/config.rs:17`), `RuntimeFeesConfig`
  (`core/parameters/src/cost.rs:518`), `Fee {send_sir, send_not_sir, execution}`
  (`cost.rs:17`).
* Values come from the base file `core/parameters/res/runtime_configs/parameters.yaml`
  plus cumulative diffs `NN.yaml` for each PV, applied in order by
  `RuntimeConfigStore::new` (`core/parameters/src/config_store.rs:88-160`).
  There are 30 diff files (46…155). The snapshot is
  `core/parameters/res/runtime_configs/parameters.snap`.
* Values relevant to Transfer at PV86:
  * `action_receipt_creation` = 108_059_500_000 gas for send_sir, send_not_sir and exec (`parameters.yaml:43-47`).
  * `action_transfer` = 115_123_062_500 gas for send_sir, send_not_sir and exec (`parameters.yaml:88-92`).
  * `min_gas_purchase_price` = 0 → **1_000_000_000 yN/gas at PV85** (`85.yaml`).
  * `account_creation_charge` = 0 → 0.007 N at PV85 (`85.yaml`).
  * `gas_refund_penalty` = 0/100 and `min_gas_refund_penalty` = 0 (`parameters.yaml:14-18`), unchanged in diffs (grep shows no diff touches them).
* `exec_fee` (`runtime/runtime/src/config.rs:279-356`). For Transfer it is
  `transfer_exec_fee` (`core/parameters/src/cost.rs:722-748`), which adds
  create_account and add_full_access_key fees for implicit and deterministic
  receivers.
* `gas_penalty_for_gas_refund(g) = min(max(g·num/den, min_penalty), g)` (`cost.rs:683-693`).
  This is 0 for g = 0.

## 5. Congestion control and bandwidth scheduler

* `ReceiptSink` (`runtime/runtime/src/congestion_control.rs:162-200, 292ff`):
  outgoing receipts are forwarded if the per-shard outgoing limit and the
  granted bandwidth allow it. Otherwise they are buffered in
  `TrieKey::BufferedReceipt*` keys.
* The delayed receipt queue lives in the trie (`TrieKey::DelayedReceiptIndices`,
  `DelayedReceipt{index}`, col 7/8).
* `CongestionInfo` goes into the chunk header (validated in
  `chain/chain/src/validate.rs:170`).
* The bandwidth scheduler (`runtime/runtime/src/bandwidth_scheduler/mod.rs:44-140`)
  mutates `TrieKey::BandwidthSchedulerState` (col 15) on **every** chunk.

## 6. Trie and what the state root commits to

* **Keys.** The key is `TrieKey::append_into` (`core/primitives/src/trie_key.rs:452ff`).
  It is **not** borsh. It is `col_byte ‖ raw bytes`. Examples:
  `Account{a}` = `0x00 ‖ utf8(a)` (`:457-460`). `ContractData{a,k}` =
  `0x09 ‖ a ‖ ',' ‖ k`. `DelayedReceipt{i}` = `0x07 ‖ i_le64`. Column constants
  are at `trie_key.rs:21-79`.
* **Paths.** Keys are split into 4-bit nibbles, high nibble first
  (`core/store/src/trie/nibble_slice.rs:100-104`). Leaf and extension partial
  keys are stored hex-prefix encoded. The first byte is
  `(odd ? 0x10 + first_nibble : 0) | (leaf ? 0x20 : 0)`, followed by the
  remaining nibbles packed 2 per byte (`nibble_slice.rs:129-158`).
* **Nodes** (`core/store/src/trie/raw_node.rs:10-36`):
  `RawTrieNodeWithSize { node: RawTrieNode, memory_usage: u64 }` with
  `RawTrieNode = Leaf(Vec<u8>, ValueRef)=0 | BranchNoValue(Children)=1 | BranchWithValue(ValueRef, Children)=2 | Extension(Vec<u8>, CryptoHash)=3`.
  * `Children` borsh is a `u16` LE bitmap (bit i = child i present) followed by
    the 32-byte hashes of the present children in index order (`raw_node.rs:79-92`).
  * `ValueRef { length: u32, hash: sha256(value) }` (`core/primitives/src/state.rs:82-87`).
    Values are **never inlined** in the hashed node. They are referenced by hash.
  * **Node hash = sha256(borsh(RawTrieNodeWithSize))** (`raw_node.rs:16-19`, `CryptoHash::hash_bytes` = SHA-256, `core/primitives-core/src/hash.rs:35-37`).
  * `memory_usage` is part of the hash. With `TRIE_COSTS = {byte_of_key: 2, byte_of_value: 1, node_cost: 50}` (`core/store/src/trie/mod.rs:158`):
    * leaf: `50 + 2·|encoded_key| + (|value| + 50)`
    * branch: `50 + [|value|+50 if value] + Σ child.memory_usage`
    * extension: `50 + 2·|encoded_key| + child.memory_usage`

    (`core/store/src/trie/ops/interface.rs:78-105`, `core/store/src/trie/mem/node/mod.rs:126-170`).
  * The empty trie root is `[0;32]` (`core/store/src/trie/mod.rs:606`).
* **State root** = hash of the root node. It is a canonical function of the
  shard's full key→value map, including account, access-key, contract code,
  contract data, the delayed, buffered and yield queues, the bandwidth
  scheduler state, etc. `TrieUpdate::finalize` feeds the **last** committed
  value per key to `trie.update` (`core/store/src/trie/update.rs:242-262`),
  so intermediate writes do not matter.

## 7. Chunk header and commitments

Chunk header inner V5 (used when `DynamicResharding` is enabled, PV≥85;
`core/primitives/src/sharding.rs:318-337`; struct at
`core/primitives/src/sharding/shard_chunk_header_inner.rs:397-427`):
`prev_block_hash, prev_state_root, prev_outcome_root, encoded_merkle_root, encoded_length, height_created, shard_id, prev_gas_used, gas_limit, prev_balance_burnt, prev_outgoing_receipts_root, tx_root, prev_validator_proposals, congestion_info, bandwidth_requests, proposed_split`.

**Important:** a chunk header commits to the *pre-state* of its own
transactions (`prev_state_root`) and to the *results of the previous chunk's
application* (`prev_*`). Post-state roots are carried in `ChunkExtra` and
appear in the *next* chunk header. The check is
`validate_chunk_with_chunk_extra_and_receipts_root`
(`chain/chain/src/validate.rs:133-180`).

* `tx_root = merklize(&transactions).0` (`validate.rs:118`).
* `outcome_root`: `ApplyChunkResult::compute_outcomes_proof`
  (`chain/chain/src/types.rs:151-163`) builds `merklize(&[o.to_hashes() for o in outcomes])`.
  * `to_hashes()` = `[id, hash_borsh(PartialExecutionOutcome), sha256(log_i)…]` (`core/primitives/src/transaction.rs:746-752`).
  * `PartialExecutionOutcome = {receipt_ids, gas_burnt, tokens_burnt, executor_id, status: PartialExecutionStatus}` (`transaction.rs:573-602`).
    It excludes `compute_usage`, `metadata` and failure details: `Failure` becomes a bare tag `1`.
  * `merklize` hashes each leaf as `hash_borsh(Vec<CryptoHash>)` (u32 length
    prefix + hashes). Inner nodes are `combine_hash(a,b) = hash_borsh((a,b)) = sha256(a‖b)`.
    One item gives root = leaf hash. Empty gives `[0;32]` (`core/primitives/src/merkle.rs:42-80`).
* `prev_outgoing_receipts_root = merklize(build_receipts_hashes(outgoing_receipts))`.
  There is one leaf per shard index:
  `sha256(borsh((shard_id, Vec<&Receipt>)))` (`chain/chain/src/chain.rs:4102-4130`, `validate.rs:84-88`).
* Stateless validation: `ChunkStateWitnessV2.main_state_transition = {block_hash, base_state: PartialState, post_state_root}`
  (`core/primitives/src/stateless_validation/state_witness.rs:104-118, 282-295`).

## 8. Public / committed / witness / external-trust classification

| item | class |
|---|---|
| `prev_state_root`, `prev_outcome_root`, `prev_outgoing_receipts_root`, `tx_root`, `gas_limit`, `congestion_info`, `bandwidth_requests` | **committed** (chunk header, signed by chunk producer, included in block) |
| block `gas_price`, height, timestamp, `prev_block_hash`, random seed | **public** (block header) |
| transactions, incoming receipts | **public** (chunk body / previous chunks' outgoing receipts with Merkle proofs) |
| trie nodes on accessed paths | **witness** (`PartialState`), verified against `prev_state_root` |
| `RuntimeConfig` for PV | **pinned constant** (source + yaml) |
| protocol version, shard layout, validator set and stakes, rewards (`EpochInfoProvider`, `ValidatorAccountsUpdate`) | **external trust** (epoch manager / consensus) |
| compiled contract cache, prefetcher, metrics | **non-semantic** |

## 9. Migrations

At 2.13.4 `Runtime::apply` contains no protocol-upgrade state migrations. The
only `StateChangeCause::Migration` use is the sandbox state patch
(`lib.rs:1821-1855`). `process_state_update` computes
`is_first_block_of_version` but only logs it (`chain/chain/src/runtime/mod.rs:280-298`).
**[unverified]** No migration logic exists elsewhere in the chain crate for
PV 83→86. We only grepped `runtime/runtime/src/lib.rs` and
`chain/chain/src/runtime/mod.rs`.
