# `near/pv86/chunk-validation/v0` — domain D2: all non-WASM actions, queues, epoch boundaries

Companion to `spec/near-chunk-validation-v0.md` (the statement §1–§5, the domain ladder §6),
`spec/near-chunk-validation-d1.md` (Transfer transactions, Ed25519) and `spec/claim-v3.md`
(formats, unchanged). This document states domain D2 exactly: what a nearcore 2.13.4 chunk
validator (`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, protocol version 86) does with every
action, receipt kind and state queue that runs **without executing WASM**, the conditions
`InD2`, and how each part is formalized. Every `file:line` is relative to the pinned nearcore
checkout (`/data/illia/nearproof-deps/nearcore`). Abbreviations: `lib.rs` =
`runtime/runtime/src/lib.rs`, `actions.rs`, `access_keys.rs`, `config.rs`, `verifier.rs`,
`action_validation.rs`, `congestion_control.rs` = the files of that name in
`runtime/runtime/src/`; `rch.rs` = `core/store/src/trie/receipts_column_helper.rs`; `om.rs` =
`core/store/src/trie/outgoing_metadata.rs`; `store/utils.rs` = `core/store/src/utils/mod.rs`.
Statements not confirmed in source are marked **[unverified]**.

> **Rel_D2(c, w) := Rel(c, w) ∧ InD2(c, w)**, same `claim.bin` / `witness.bin`.
> `InD1 ⊂ InD2`: every D1 condition is either kept or weakened (§12), so a D2 prover validates
> every D1 (and D0) chunk, and `Rel_D2 ⇒ Rel`.

Contents: §1 the shape of a D2 chunk application · §2 state: trie keys and value encodings ·
§3 trie access semantics and read sets · §4 parameters and fees · §5 transactions · §6
receipt processing · §7 actions · §8 delegate actions · §9 queues (delayed, outgoing buffers,
bandwidth requests, yield timeouts) · §10 `Runtime::apply` end to end, epoch boundaries ·
§11 chain-level changes in `Rel` · §12 `InD2` · §13 the D3 interface · §14 formalization ·
§15 evidence.

## 1. Shape of a D2 chunk application

`Runtime::apply` (`lib.rs:1718-1819`), main transition (new chunk, block B2):

1. **Validator accounts update** if B2 starts an epoch (`lib.rs:1751-1757`, §10.2).
2. `DelayedReceiptQueue::load` (`lib.rs:1759-1764`): read `DelayedReceiptIndices`.
3. Bandwidth scheduler (`lib.rs:1767-1772`, D0, unchanged).
4. (new chunk only) `own_congestion_info` = the B2-slot congestion info of the shard
   (`lib.rs:1785-1786`, `ApplyState::own_congestion_info` `lib.rs:2851-2864`);
   `ReceiptSink::new` (`congestion_control.rs:86-144`): loads `BufferedReceiptIndices`
   and the receipt-group metadata of every listed shard; **forward from buffers**
   (`lib.rs:1795`, §9.2).
5. `process_transactions` (§5).
6. `process_receipts` (`lib.rs:2658-2721`): local receipts, delayed receipts, incoming
   receipts, each followed by its instant receipts; then **yield timeouts** (§9.4).
7. `validate_apply_state_update` (`lib.rs:2723-2849`): write `PromiseYieldIndices` if
   changed; congestion info = sink info + delayed-queue deltas, `allowed_shard` finalized;
   **bandwidth requests** generated from the outgoing buffers (§9.3); `finalize` the trie
   update (§3.4); dedup validator proposals.

Missing chunk (implicit transition, block M): steps 1–3 only, then `finalize`
(`lib.rs:1775-1782, 2937-2984`).

A D2 chunk is one in which no step above executes WASM: every `FunctionCall` (and every
global-contract / state-init action) that would be *dispatched* (§7.0) makes the chunk
out of domain. Everything else is formalized.

## 2. State: trie keys and value encodings

Trie keys (`core/primitives/src/trie_key.rs:452-560`; columns `trie_key.rs:24-85`). `acct` =
the account id bytes, `h` = `PublicKeyHandle` borsh = `0 ‖ 32 B` (ED25519) / `1 ‖ 64 B`
(SECP256K1) / `3 ‖ sha3-256 hash` (ML-DSA-65) (`trie_key.rs:324-335`).

| key | bytes | value (borsh, `get` = `try_from_slice`, trailing bytes ⇒ `StorageInconsistentState`, `store/utils.rs:26-39`) |
|---|---|---|
| `Account` | `0 ‖ acct` | `Account` (§2.1) |
| `ContractCode` | `1 ‖ acct` | raw code bytes |
| `AccessKey` | `2 ‖ acct ‖ 2 ‖ h` | `AccessKey` (§2.2) |
| `GasKeyNonce` | `2 ‖ acct ‖ 2 ‖ h ‖ u16le idx` | `u64` nonce |
| `ReceivedData` | `3 ‖ acct ‖ ',' ‖ data_id` | `ReceivedData { data: Option<Vec<u8>> }` |
| `PostponedReceiptId` | `4 ‖ acct ‖ ',' ‖ data_id` | `CryptoHash` (receipt id) |
| `PendingDataCount` | `5 ‖ acct ‖ ',' ‖ receipt_id` | `u32` |
| `PostponedReceipt` | `6 ‖ acct ‖ ',' ‖ receipt_id` | `Receipt` (§2.3) |
| `DelayedReceiptIndices` | `7` | `{first: u64, next_available: u64}` |
| `DelayedReceipt` | `7 ‖ u64le i` | `ReceiptOrStateStoredReceipt` (§2.4) |
| `ContractData` | `9 ‖ acct ‖ ',' ‖ key` | raw |
| `PromiseYieldIndices` | `10` | `{first: u64, next_available: u64}` |
| `PromiseYieldTimeout` | `11 ‖ u64le i` | `{account_id, data_id: hash, expires_at: u64}` (`receipt.rs:1090-1098`) |
| `PromiseYieldReceipt` | `12 ‖ acct ‖ ',' ‖ data_id` | `Receipt` |
| `BufferedReceiptIndices` | `13` | `BTreeMap<u64 shard, {first, next}>` (`receipt.rs:1136-1139`) |
| `BufferedReceipt` | `14 ‖ u16le shard ‖ u64le i` | `ReceiptOrStateStoredReceipt` |
| `BandwidthSchedulerState` | `15` | D0 |
| `BufferedReceiptGroupsQueueData` | `16 ‖ u64le shard` | `ReceiptGroupsQueueData::V0 = 0 ‖ {first, next: u64, total_size: u64, total_gas: u128, total_receipts_num: u64}` (`om.rs:200-224`) |
| `BufferedReceiptGroupsQueueItem` | `17 ‖ u64le shard ‖ u64le i` | `ReceiptGroup::V0 = 0 ‖ {size: u64, gas: u128}` (`om.rs:88-106`) |
| `PromiseYieldStatus` | `20 ‖ acct ‖ ',' ‖ data_id` | `PromiseYieldStatus` (`ResumeInitiated` …) |
| `DataIdToYieldId` / `YieldIdToDataId` | `23` / `22 ‖ acct ‖ ',' ‖ id` | hash |

Global-contract columns (18, 19) are never touched in D2.

### 2.1 `Account` (`core/primitives-core/src/account.rs:40-456`)

* **V1** (untagged): `amount u128 ‖ locked u128 ‖ code_hash [32] ‖ storage_usage u64` (72 B).
  `contract = None` iff `code_hash = 0³²`, else `Local(code_hash)` (`account.rs:107-113`).
* **V2**: `u128::MAX ‖ 0u8 ‖ amount u128 ‖ locked u128 ‖ storage_usage u64 ‖ AccountContract`,
  `AccountContract = 0 None | 1 Local(hash) | 2 Global(hash) | 3 GlobalByAccount(AccountId)`
  (`account.rs:85-91, 140-152, 410-456`). Decoding: first `u128` = sentinel ⇒ V2 (any other
  tag after the sentinel fails); otherwise V1.
* `Account::new(amount, locked, contract, usage)` builds V1 for `None`/`Local`, V2 otherwise
  (`account.rs:166-184`); `set_contract` keeps V1 for `None`/`Local` and converts V1→V2 for a
  global contract; a V2 account stays V2 forever (`account.rs:283-300`).
* **D2 handles both versions.** V2 accounts arise at PV 86 from ETH-implicit account creation
  (`EthImplicitGlobalContract`, PV 83, `core/primitives-core/src/version.rs:556`, §7.4) and
  from `UseGlobalContract` (D3). Everything D2 does with an account (`amount`, `locked`,
  `storage_usage`, `contract` for `DeleteAccount`/`DeployContract`) is defined for both, and
  writes re-encode in the account's own version.

### 2.2 `AccessKey` (`account.rs:466-620`)

`AccessKey { nonce: u64, permission }`, `permission = 0 FunctionCall(fc) | 1 FullAccess |
2 GasKeyFunctionCall(GasKeyInfo, fc) | 3 GasKeyFullAccess(GasKeyInfo)`,
`fc = { allowance: Option<u128>, receiver_id: String, method_names: Vec<String> }` (strings:
well-formed UTF-8), `GasKeyInfo = { balance: u128, num_nonces: u16 }` (18 B).
A gas key's own `nonce` field is always 0 (`access_keys.rs:205-207`); its nonces live under
`GasKeyNonce` keys `0 … num_nonces−1`.

### 2.3 `Receipt` (`core/primitives/src/receipt.rs:57-80, 565-660, 828-860`)

`Receipt = ReceiptV0 { predecessor_id, receiver_id, receipt_id: hash, receipt: ReceiptEnum }`
(untagged). `ReceiptEnum = 0 Action(ActionReceipt) | 1 Data(DataReceipt) | 2 PromiseYield(ActionReceipt)
| 3 PromiseResume(DataReceipt) | 4 GlobalContractDistribution | 5 ActionV2(ActionReceiptV2) |
6 PromiseYieldV2(ActionReceiptV2)`.
`ActionReceipt = { signer_id, signer_public_key: PublicKey, gas_price: u128,
output_data_receivers: Vec<{data_id, receiver_id}>, input_data_ids: Vec<hash>, actions: Vec<Action> }`;
`ActionReceiptV2` adds `refund_to: Option<AccountId>` after `signer_id`.
`DataReceipt = { data_id, data: Option<Vec<u8>> }`.
`balance_refund_receiver = refund_to.unwrap_or(predecessor_id)` (`receipt.rs:417-432`).
`Action` (`core/primitives/src/action/mod.rs:349-370`): tags 0 CreateAccount `{}`, 1
DeployContract `{code: Vec<u8>}`, 2 FunctionCall `{method_name: String, args: Vec<u8>, gas: u64,
deposit: u128}`, 3 Transfer `{deposit}`, 4 Stake `{stake: u128, public_key}`, 5 AddKey
`{public_key, access_key}`, 6 DeleteKey `{public_key}`, 7 DeleteAccount `{beneficiary_id}`,
8 Delegate (§8), 9 DeployGlobalContract, 10 UseGlobalContract, 11 DeterministicStateInit,
12 TransferToGasKey `{public_key, deposit}`, 13 WithdrawFromGasKey `{public_key, amount}`,
14 DelegateV2 (§8). Delegate inner actions are `NonDelegateAction` (tags 8 and 14 rejected at
decoding, `action/delegate.rs:431-441`).

### 2.4 `ReceiptOrStateStoredReceipt` (`receipt.rs:150-330`)

Stored as either a plain `Receipt` or `0xFF ‖ 0xFF ‖ ver ‖ Receipt ‖ congestion_gas u64 ‖
congestion_size u64` (`StateStoredReceipt::V0` (ver 0) / `V1` (ver 1)). The two leading bytes
discriminate (a `Receipt` starts with a borsh account-id length, whose second byte is 0).
At PV 86 every push writes **V1** (`use_state_stored_receipt` = true since PV 72,
`congestion_control.rs:846-852, 474-484`); pops accept all three forms and take gas/size from
the metadata for `StateStoredReceipt`, recompute them for a plain `Receipt`
(`congestion_control.rs:657-676, 946-955`). Only V1 entries update the receipt-group metadata
(`receipt.rs:180-200`).

## 3. Trie access semantics and read sets

The validator's trie is `Trie::from_recorded_storage(base_state, prev_state_root)` wrapped in
a recorder with the 4 MB proof-size limit (`chain/chain/src/runtime/mod.rs:1240-1258`). Every
node or value is looked up by its hash in the recorded set; a missing one is
`StorageError::MissingTrieValue` ⇒ `Err` ⇒ the witness is rejected. **The witness is
accepted only if every node/value nearcore touches on the paths below is present**; nodes
nearcore does not touch may be missing (and extra nodes may be present).

### 3.1 `TrieUpdate` (`core/store/src/trie/update.rs:28-262`)

All runtime reads and writes go through one `TrieUpdate` per apply: `committed` (per key the
list of committed values) and `prospective` (uncommitted). `get(k)`: prospective, else last
committed, else the **pre-state trie** (`update.rs:119-145`) — the trie itself is never
modified before `finalize`. `commit` moves prospective into committed; `rollback` drops
prospective (`update.rs:205-230`). Semantically: a key → `Option<value>` overlay with a
savepoint; reads of overlay keys never touch the trie.

Kinds of trie reads (each reads the nodes on the key's nibble path from the root until the
path ends or leaves the trie):

| access | nearcore | reads |
|---|---|---|
| `get` | `Trie::get` | path nodes **and the value** |
| `get_ref`, `contains_key` | `get_optimized_ref`, `contains_key` (`trie/mod.rs:1474-1550`) | path nodes only (the leaf's `ValueRef` gives length and hash); used by `has_received_data` (`store/utils.rs:91-100`), the yield-timeout check (`lib.rs:3014`), `get_code_len` (`update.rs:177-196`, `ExcludeExistingCodeFromWitnessForCodeLen` PV 83) |
| prefix iteration | `TrieUpdate::iter`/`locked_iter` (`update/iterator.rs:40-150`) over `TrieIteratorImpl::seek_prefix` + `next` (`trie/ops/iter.rs:125-250, 337-372`) | the nodes on the path to the prefix, then **every node and every value** in the subtree of keys with that prefix (the iterator returns `(key, value)` and dereferences each value, `ops/iter.rs:364-367`); ancestors of the prefix node are marked `prefix_boundary` and are not explored further. The yielded key set is merged with the overlay (overlay deletions hide trie keys, overlay insertions add keys). |
| `get_pure` (no side effects) | prefetch / contract-preparation lookahead (`lib.rs:3256-3322`, `pipelining.rs:152-240`) | errors are swallowed: these reads never affect validity |

Transactions' signer accounts / access keys / gas-key nonces are prefetched for every
non-expired transaction but an error surfaces only when used (`lib.rs:1922-1977, 2030-2076`,
D1 §3 step 5); the relation therefore reads them at the point of use. The values seen at use
are those of the overlay (the prefetch cache is updated in place by successful transactions,
`lib.rs:2246-2266`, and nothing else writes these keys before step 6).

### 3.2 Read-set summary per operation

* account / access key / gas-key nonce / received data / postponed receipt / pending count /
  yield receipt / yield status / data-id mapping / queue item / indices: `get` (path + value);
* `has_received_data` (`process_action_receipt`), `contains_key(PromiseYieldReceipt)`
  (timeouts), `get_code_len` (`DeleteAccount` of an account with a local contract):
  path only;
* `DeleteAccount`: three prefix iterations (§7.8): `compute_gas_key_balance_sum` over
  `2 ‖ acct ‖ 2` (`store/utils.rs:435-474`), then `remove_account` over `2 ‖ acct ‖ 2` and
  `9 ‖ acct ‖ ','` (`store/utils.rs:482-552`) — every node and value of those subtrees;
* outgoing-buffer forwarding iterates buffer items through `state_update.trie` directly
  (`congestion_control.rs:347-349`, `rch.rs:219-237, 330-380`): the items of the
  pre-state trie, `get` each, until the first receipt that is not forwarded (which is read too);
* `finalize` (§3.4): the nodes `generic_insert` / `generic_delete` + `squash_node` visit.

### 3.3 Proof-size limit

`check_proof_size_limit_exceed` = `upper_bound_size > 4 000 000`
(`trie/trie_recording.rs:161-163`, `main_storage_proof_size_soft_limit`,
`runtime_configs/72.yaml:1`), where `upper_bound_size` = Σ sizes of distinct recorded
nodes/values + 2000 per `TrieUpdate::remove` of a `ContractData` key
(`update.rs:160-172`, `trie_recording.rs:140-146`). It gates local/delayed/incoming receipt
processing and yield timeouts exactly like the compute limit. D2 keeps it unreachable
(`w.size`, §12): `Σ |main base_state values| + 2000 · R ≤ 4 000 000`, `R` = number of
`ContractData` removals in the main transition (recorded nodes are a subset of
`base_state`).

### 3.4 `finalize` (`update.rs:242-261`, `trie/mod.rs:1586-1700`)

The committed overlay, **in ascending byte order of the raw keys** (a `BTreeMap<Vec<u8>, …>`),
is applied one key at a time to the pre-state trie with `TrieStorageUpdate`
(`trie/trie_storage_update.rs`, the recorded-storage path; validators never use memtries):
`Some(v)` ⇒ `generic_insert`, `None` ⇒ `generic_delete` (`trie/mod.rs:1678-1700`). Keys
written and later removed in the same apply are deleted (a no-op if absent in the trie,
still reading the path).

* `generic_insert` (`trie/ops/insert_delete.rs:37-260`): as v2's `PTrie.upsert`
  (`spec/lean/NearSpec/TrieUpsert.lean`): descending into an existing child reads it
  (`ensure_updated`); splitting a leaf or an extension does **not** read the extension's child;
  `memory_usage` per node: leaf `50 + 2·|hp(key)| + (|v| + 50)`, extension `50 + 2·|hp(key)| +
  child`, branch `50 + [|v| + 50] + Σ children` (`ops/interface.rs:84-105`).
* `generic_delete` (`insert_delete.rs:262-438`): descend along the key (reading every child
  entered); if the key is absent (leaf with another key, missing branch child, branch without
  value at the end, extension not a prefix) nothing changes. If removed: the leaf becomes
  `Empty` / the branch loses its value, and on the way up every node of the path is
  **squashed** (`trie/ops/squash.rs:29-110`): a branch drops `Empty` children; 0 children and
  no value ⇒ `Empty`; 0 children with a value ⇒ leaf with empty key; **1 child and no value ⇒
  `extend_child([idx], child)`, which reads that remaining child from storage**
  (`squash.rs:84-92, 118-121`) — the sibling of a deleted subtree must be in the witness; an
  extension on the path ⇒ `extend_child(ext, child)` (child already updated). `extend_child`:
  child `Empty` ⇒ `Empty`; child leaf ⇒ leaf with merged key; child branch ⇒ extension kept;
  child extension ⇒ merged extension (`squash.rs:113-178`). Memory usage is recomputed along
  the path (`insert_delete.rs:418-436`).
* Deleting the last key yields the empty trie, root `0³²` (`trie_storage_update.rs`, `Trie::EMPTY_ROOT`).

## 4. Parameters (PV 86 = PV 85 config; no `86.yaml` exists)

From `core/parameters/res/runtime_configs/parameters.yaml` + the version diffs, cross-checked
with `core/parameters/src/snapshots/near_parameters__config_store__tests__85.json.snap`.
`(send_sir, send_not_sir, exec)` in gas; compute = gas unless stated.

| cost | send_sir | send_not_sir | exec |
|---|---|---|---|
| `new_action_receipt` | 108 059 500 000 | 108 059 500 000 | 108 059 500 000 |
| `create_account` (`85.yaml`) | 500 000 000 000 | 500 000 000 000 | 7 200 000 000 000 |
| `deploy_contract_base` | 184 765 750 000 | 184 765 750 000 | 184 765 750 000 (compute 20 000 000 000 000, `84.yaml:11-23`) |
| `deploy_contract_byte` | 6 812 999 | 47 683 715 | 64 572 944 (compute 250 000 000, `84.yaml:24-35`) |
| `function_call_base` | 200 000 000 000 | 200 000 000 000 | 780 000 000 000 |
| `function_call_byte` | 2 235 934 | 47 683 715 | 2 235 934 |
| `transfer` | 115 123 062 500 | 115 123 062 500 | 115 123 062 500 |
| `stake` | 141 715 687 500 | 141 715 687 500 | 102 217 625 000 |
| `add_full_access_key` | 101 765 125 000 | 101 765 125 000 | 101 765 125 000 |
| `add_function_call_key_base` | 102 217 625 000 | 102 217 625 000 | 102 217 625 000 |
| `add_function_call_key_byte` | 1 925 331 | 47 683 715 | 1 925 331 |
| `delete_key` | 94 946 625 000 | 94 946 625 000 | 94 946 625 000 |
| `delete_account` | 147 489 000 000 | 147 489 000 000 | 147 489 000 000 |
| `delegate` | 200 000 000 000 | 200 000 000 000 | 200 000 000 000 |
| `gas_key_transfer_base` | 115 123 062 500 | 115 123 062 500 | 235 676 644 250 |
| `gas_key_byte` | 59 357 464 | 59 357 464 | 101 435 400 |
| `gas_key_nonce_write_base` | 0 | 0 | 64 196 736 000 |

Storage: `storage_amount_per_byte = 10¹⁹`, `num_bytes_account = 100`,
`num_extra_bytes_record = 40` (`parameters.yaml:35-37`); `ZERO_BALANCE_ACCOUNT_STORAGE_LIMIT = 770`
(`verifier.rs:24`). `storage_remove_base` gas 53 473 030 500 / compute 200 000 000 000
(`61.yaml:5`), `storage_remove_key_byte` 38 220 384, `storage_remove_ret_value_byte` 11 531 556
(compute = gas). Gas economics: `burnt_gas_reward = 3/10`, `gas_refund_penalty = 0/100`,
`min_gas_refund_penalty = 0` (so the refund penalty is always 0, `core/parameters/src/cost.rs:683-693`),
`min_gas_purchase_price = 10⁹`, `account_creation_charge = 0.007 NEAR = 7·10²¹`
(`85.yaml`). Limits: `max_actions_per_receipt = 100`, `max_deploy_actions_per_receipt = 10`
(`84.yaml:10`), `max_total_prepaid_gas = 10¹⁵` (`83.yaml:9`), `max_receipt_size = 4 194 304`,
`max_transaction_size = 1 572 864` (`69.yaml`), `max_contract_size = 4 194 304`,
`max_length_method_name = 256`, `max_arguments_length = 4 194 304`,
`max_number_bytes_method_names = 2 000`, `max_number_input_data_dependencies = 128`,
`max_length_returned_data = 4 194 304` (`parameters.yaml:261-273`).
`min_allowed_top_level_account_length = 65` (`64.yaml:2`), `registrar_account_id = "registrar"`,
`account_id_validity_rules_version = 2` (`83.yaml:3`), `eth_implicit_accounts = true`
(`70.yaml:1`). Signature verification costs: ED25519 and SECP256K1 0, ML-DSA-65
100 000 000 000 (`85.yaml`).

### 4.1 Fee functions (`config.rs`, `core/parameters/src/cost.rs:722-876`)

`sir = (sender = receiver)`. Per action (send fee `send(a, sir, receiver)`, exec fee `exec(a, receiver)`):

* CreateAccount: `create_account`; DeleteAccount: `delete_account`; DeleteKey: `delete_key`;
  Stake: `stake`; Delegate/DelegateV2: `delegate`.
* DeployContract `code`: `deploy_contract_base + |code| · deploy_contract_byte` (exec compute
  uses the compute values above).
* FunctionCall: `function_call_base + (|method_name| + |args|) · function_call_byte`.
* Transfer to `r`: `transfer` + `create_account` if `r` is ETH-implicit or NEAR-deterministic,
  + `create_account + add_full_access_key` if NEAR-implicit (`cost.rs:722-777`).
* AddKey: FullAccess / GasKeyFullAccess ⇒ `add_full_access_key`; FunctionCall /
  GasKeyFunctionCall ⇒ `add_function_call_key_base + Σ(|m|+1) · add_function_call_key_byte`;
  gas keys additionally: send `gas_key_byte · 18` (`GasKeyInfo::borsh_len`), exec
  `num_nonces · gas_key_nonce_write_base + num_nonces · (|2 ‖ acct ‖ 2 ‖ h| + 2 + 8) · gas_key_byte`
  (`config.rs:201-238, 358-398`, `cost.rs:844-876`; `|h|` = `trie_id_len`: 33 / 65).
* TransferToGasKey / WithdrawFromGasKey (key `pk`): send `gas_key_transfer_base + |h| · gas_key_byte`;
  exec `gas_key_transfer_base + (|2 ‖ receiver ‖ 2 ‖ h| + 27) · gas_key_byte` (27 = borsh length
  of `AccessKey::gas_key_full_access(0)`, `cost.rs:794-825`).
* Delegate: send `delegate + total_send_fees(sir', inner actions, inner receiver)` with the
  *outer* `sir` (`config.rs:117-143`).

Aggregates: `total_send_fees`, `total_prepaid_send_fees` (only Delegate: the inner actions'
send fees with `sir' = (sender_id = inner receiver)`, `config.rs:240-277`),
`total_prepaid_exec_fees` (Delegate: inner exec fees + `delegate` exec + `new_action_receipt`
exec, `config.rs:529-556`), `total_deposit` (Transfer, FunctionCall, TransferToGasKey
deposits; Delegate: the inner deposits, `config.rs:558-586`), `total_prepaid_gas` (FunctionCall
gas, recursively through Delegate, `config.rs:588-602`). All sums checked (`IntegerOverflowError`).

`tx_cost` (`config.rs:400-479`): `burnt = new_action_receipt.send(sir) + total_send_fees +
sig_verification(signer key, delegate keys)`; `gas_remaining = prepaid_gas +
prepaid_send.gas + new_action_receipt.exec + prepaid_exec.gas`; `burnt_amount =
gas_price · burnt`; `receipt_gas_price = max(gas_price, 10⁹)`; `gas_cost = burnt_amount +
receipt_gas_price · gas_remaining`; `deposit_cost = total_deposit`; `total_cost = gas_cost +
deposit_cost`; any overflow ⇒ `CostOverflow`.

## 5. Transactions (`process_transactions`, `lib.rs:1882-2279`)

D1 §3 holds verbatim, generalized to every action list:

1. Duplicate hash skipped; expired ⇒ failed outcome.
2. `validate_transaction` (`verifier.rs:109-121`): `validate_actions` in `NewReceipt` mode
   (§6.6) on the transaction's actions with receiver = tx receiver; then
   `check_valid_for_config` (`transaction.rs:301-337`: version gates open at PV 86; size
   `|borsh(Transaction)| + |borsh(Signature)| ≤ 1 572 864`); then the signature (D1 §2).
   Failure ⇒ failed outcome.
3. `tx_cost` (§4.1); overflow ⇒ failed outcome.
4. Signer account (absent ⇒ failed), access key `(signer, pk)` (absent ⇒ failed).
5. **Regular nonce** (`TransactionNonce::Nonce`): `verify_and_charge_tx_ephemeral`
   (`verifier.rs:272-378`): gas key ⇒ failed (`InvalidNonceIndex`); nonce (monotonic/strict,
   `< height·10⁶` saturating); `amount ≥ total_cost`; FC key with allowance ⇒ `allowance ≥
   total_cost`, new allowance `= allowance − total_cost`; storage stake with
   `amount − total_cost`; FC key ⇒ `verify_function_call_permission` (`verifier.rs:167-210`):
   exactly one action, a `FunctionCall` with zero deposit, `tx.receiver = fc.receiver_id`,
   method in `method_names` (if non-empty). Success writes `amount − total_cost`, key nonce
   `= tx_nonce`, and the new allowance (`lib.rs:286-314`).
6. **Gas-key nonce** (`TransactionNonce::GasKeyNonce{nonce, idx}`, `TransactionV1`): the gas-key
   nonce row `(signer, pk, idx)` is read (absent ⇒ failed `InvalidNonceIndex`,
   `lib.rs:2078-2101`); `verify_and_charge_gas_key_tx_ephemeral` (`verifier.rs:383-538`): key
   must be a gas key (else failed); `idx < num_nonces`; nonce rule against the row;
   `gas_key.balance ≥ gas_cost` (else failed); `balance ≥ burnt_amount`; FC permission check
   (as 5); then **deposit**: `amount < deposit_cost` or storage stake with `amount −
   deposit_cost` failing ⇒ **`DepositFailed`**: the gas key is charged `burnt_amount` only,
   the account is unchanged, the nonce row is advanced, **no receipt**, outcome
   `failed_with_gas_burnt(gas_burnt, burnt_amount)` (`transaction.rs:727-744`: status
   Failure, gas and tokens counted) (`lib.rs:2128-2142`); success charges the key `gas_cost`,
   the account `deposit_cost`, advances the row.
7. Success: receipt `Receipt::from_tx` (`receipt.rs:344-365`) with **all** actions, id
   `sha256(tx_hash ‖ u64 height ‖ u64 0)`, gas price `receipt_gas_price`; local iff
   `receiver = signer`, else `forward_or_buffer_receipt` (§9.2) — buffering is **in** D2.
   Burnt overflow drops the outcome (D1). Chunk gas/compute += `gas_burnt` (compute =
   `compute_burnt` = gas for send fees). Writes (`lib.rs:2238-2266`): account, gas-key nonce
   row (gas-key path), access key (nonce / allowance / gas-key balance).

Outcome of a transaction: D1 §3 (`SuccessReceiptId(rid)` or `Failure`).

## 6. Receipt processing

### 6.1 Order and limits (`lib.rs:2357-2721`)

`compute_limit = gas_limit` of B2's slot. Local receipts (FIFO), then delayed receipts (pop
while `total.compute < limit`), then incoming receipts; before each local/incoming receipt:
`total.compute ≥ limit` (or the proof limit, §3.3) ⇒ the receipt is **pushed to the delayed
queue** instead (§9.1). Incoming receipts are first validated with `validate_receipt`
(`ExistingReceipt` mode); a failure is `RuntimeError::ReceiptValidationError`, which panics in
`apply_chunk` (`chain/chain/src/runtime/mod.rs:357-369`) ⇒ reject. Popped delayed receipts are
validated likewise, a failure is `StorageInconsistentState` ⇒ reject (`lib.rs:2504-2517`).
After each processed receipt, its **instant receipts** (new receipts with
`is_instant_receipt`: a `PromiseYield`, or an `Action` receipt whose actions are exactly
`[DeleteAccount]` and has no input data ids, `receipt.rs:474-495`) are processed immediately,
in FIFO order, regardless of limits (`lib.rs:2619-2656`). Each processed receipt with an
outcome adds `(gas_burnt, compute_usage)` to `total` (`lib.rs:2335-2345`).

### 6.2 `process_receipt` (`lib.rs:1303-1527`)

* **Data** `{data_id, data}` to `acct`: set `ReceivedData(acct, data_id) := {data}`; `get
  PostponedReceiptId(acct, data_id)`: absent ⇒ done; present `rid` ⇒ remove it, `get
  PendingDataCount(acct, rid)` (absent ⇒ `StorageInconsistentState`); count = 1 ⇒ remove the
  count, `get PostponedReceipt(acct, rid)` (absent ⇒ inconsistent), remove it, **apply it**
  (§6.4) — its outcome is this receipt's outcome; count > 1 ⇒ store `count − 1` (count 0 ⇒
  inconsistent). No outcome otherwise. Then commit.
* **Action / ActionV2**: `process_action_receipt` (§6.3).
* **PromiseYield / PromiseYieldV2**: `set PromiseYieldReceipt(acct, input_data_ids[0]) :=
  receipt` (`store/utils.rs:182-194`), commit, no outcome.
* **PromiseResume** `{data_id, data}`: if `data = None` (a timeout) and `get
  PromiseYieldStatus = ResumeInitiated` ⇒ no-op (no commit). `get PromiseYieldReceipt(acct,
  data_id)`: absent ⇒ no-op; present ⇒ remove it, remove its status, (`YieldWithId`, PV 85)
  `get DataIdToYieldId(acct, data_id)` and, if present, remove both mappings; set
  `ReceivedData(acct, data_id) := {data}`; **apply** the yield receipt (§6.4).
* **GlobalContractDistribution**: out of D2.

### 6.3 `process_action_receipt` (`lib.rs:1529-1597`)

For each `input_data_id` in order: `has_received_data` (path read only); missing ⇒ count it
and `set PostponedReceiptId(acct, id) := receipt_id`. Count 0 ⇒ apply (§6.4); else set
`PendingDataCount(acct, receipt_id) := count` and `PostponedReceipt(acct, receipt_id) :=
receipt`, commit, no outcome.

### 6.4 `apply_action_receipt` (`lib.rs:776-1164`)

1. For each input data id: `get ReceivedData` (absent ⇒ inconsistent), remove it (results are
   only consumed by FunctionCall). **Commit** (`lib.rs:827-829`).
2. `account = get Account(receiver)`; `actor = predecessor`; `result` starts with
   `gas_burnt = gas_used = new_action_receipt.exec`, `compute = its compute`.
3. For each action `i` (`lib.rs:845-888`): `apply_action` (§7); if it succeeded, every new
   receipt it produced is checked with `validate_receipt(NewReceipt)` (size ≤
   `max_receipt_size` plus §6.6), a failure turns the action result into
   `NewReceiptValidationError`; `merge` (`lib.rs:439-485`: gas/compute/logs always added;
   on success new receipts, proposals, tokens burnt appended; on failure `set_error` clears
   new receipts, proposals, tokens burnt, subsidized); stop at the first error (index `i`).
4. **Storage stake** (`lib.rs:890-913`): on success and if the account exists,
   `check_storage_stake(account, amount)` (`verifier.rs:48-86`: `amount + locked ≥
   usage · 10¹⁹` or `usage ≤ 770`; multiplication/addition overflow ⇒ inconsistent ⇒ reject):
   ok ⇒ `set Account`; lacking ⇒ `set_error(LackBalanceForState)`.
5. Prices: `purchase = receipt.gas_price`, `burn = min(purchase, block gas_price)`
   (`AccountCostIncrease`, PV 85, `lib.rs:916-928`).
6. Refunds: `predecessor = system` ⇒ no refunds; on failure the total deposit is added to
   `other_burnt_amount` (`lib.rs:931-939`). Otherwise `refund_unspent_gas_and_deposits`
   (`lib.rs:1166-1301`) with `created = account_did_not_exist ∧ account exists now ∧ success`:
   `prepaid = total_prepaid_gas + total_prepaid_send_fees.gas`; `prepaid_exec =
   total_prepaid_exec_fees.gas + new_action_receipt.exec`; `gross = prepaid + prepaid_exec −
   (failure ? gas_burnt : gas_used)`; penalty 0; `unused_refund = purchase · gross`;
   `surplus = (purchase − burn) · gas_burnt` (`deficit` is 0 since `burn ≤ purchase`);
   `burned_refund = surplus`; if `created`: `charge = min(7·10²¹ ∸ burn · create_account.exec,
   burned_refund)`, `burned_refund −= charge`; `gas_balance_refund = unused_refund +
   burned_refund`. New receipts: on failure a **balance refund** `Receipt::new_balance_refund
   (balance_refund_receiver, total_deposit)` if `> 0`; then a **gas refund**
   `Receipt::new_gas_refund(signer_id, gas_balance_refund, signer_public_key)` if `> 0`
   (`receipt.rs:497-545`: predecessor `system`, signer `system`/`signer_id`, key empty
   ED25519 / signer key, gas price 0, one Transfer).
7. Proposals moved to the chunk list (`lib.rs:958-959`); **commit on success, rollback on
   failure** (`lib.rs:961-971`) — a failed receipt's state changes (including step 4's
   account write) vanish; step 1's data removal was committed before.
8. `gas_burnt_outcome = predecessor = system ? 0 : result.gas_burnt`; `tx_burnt =
   burn · gas_burnt_outcome − deficit + refund_penalty + create_account_charge +
   result.tokens_burnt` (`lib.rs:972-989`). Receiver reward `= burn · (3/10 ·
   gas_burnt_for_function_call)` = 0 in D2 (no function call burns gas, `lib.rs:991-1022`).
   `stats.tx_burnt += tx_burnt` (checked).
9. Output data receivers (`lib.rs:1034-1073`): if the receipt has `output_data_receivers`:
   result `ReceiptIndex(k)` cannot occur in D2 (only FunctionCall returns it); otherwise for
   each receiver a **Data receipt** `{predecessor: receiver_id of this receipt, receiver:
   r.receiver_id, data_id: r.data_id, data: success ? Some([]) : None}` is appended.
10. Receipt ids (`lib.rs:1075-1120`): new receipt `k` gets `sha256(receipt_id ‖ u64 height ‖
    u64 k)` (`utils.rs:270-335`); instant receipts go to the instant queue, the others to
    `forward_or_buffer_receipt` (§9.2); `receipt_ids` lists the **Action/PromiseYield** new
    receipts only (Data receipts are omitted).
11. Status: success ⇒ `SuccessValue([])` (`ReturnData::None`), failure ⇒ `Failure`
    (`lib.rs:1122-1128`). Outcome `{id: receipt_id, receipt_ids, gas_burnt: result.gas_burnt
    (also for system receipts), tokens_burnt: tx_burnt, executor: receiver, logs: []}`;
    compute = `result.compute_usage`.

Outcome hashing: `[id, sha256(borsh(PartialExecutionOutcome))] ++ map sha256 logs`
(`transaction.rs:746-752`); `PartialExecutionStatus`: `Failure = 1`, `SuccessValue(v) = 2 ‖
bytes v`, `SuccessReceiptId = 3 ‖ hash` (`transaction.rs:597-612`). Logs are empty in D2.

### 6.5 Refund receipts (`predecessor = system`)

They are ordinary action receipts with one Transfer (§7.3): a gas refund (`signer_id =
receiver`) first tries `try_refund_gas_key_balance` (`actions.rs:103-120`: the key `(receiver,
signer_public_key)` exists and is a gas key ⇒ its balance += deposit, account **not**
credited), else credits the account and `try_refund_allowance` (`actions.rs:122-146`: an FC
key with an allowance gets `allowance ⊕ deposit` saturating, written only if it grew). A
refund to a non-existent account fails (`AccountDoesNotExist`, implicit creation needs a
non-refund), and its deposit is burnt (`other_burnt_amount`).

### 6.6 `validate_receipt` / `validate_actions` (`verifier.rs:540-644`, `action_validation.rs:40-482`)

`validate_receipt`: (`NewReceipt` only) `|borsh(receipt)| ≤ max_receipt_size`; predecessor and
receiver are valid account ids; Action/PromiseYield: `|input_data_ids| ≤
max_number_input_data_dependencies`, `refund_to` valid, `validate_actions_with_mode`;
Data/PromiseResume: `|data| ≤ max_length_returned_data`.
`validate_actions_with_mode`: `|actions| ≤ 100`; (`NewReceipt`) ≤ 10 deploy actions;
`DeleteAccount` only as last action; at most one Delegate/DelegateV2; per action:
DeployContract `|code| ≤ max_contract_size`; FunctionCall `gas > 0`, `|method| ≤
max_length_method_name`, `|args| ≤ max_arguments_length`; Stake: `is_valid_staking_key`
(ED25519, decompresses, torsion-free: `[ℓ]P = O`, `core/crypto/src/key_conversion.rs:6-23`);
AddKey: FC permission `receiver_id` a valid account id, each method `≤
max_length_method_name`, `Σ(|m|+1) ≤ max_number_bytes_method_names`; gas keys: FC allowance
must be `None`, `1 ≤ num_nonces ≤ 1024`, `balance = 0`; DeleteAccount: beneficiary valid;
Delegate: inner `|actions| ≤ 100` then `validate_actions_with_mode` on the inner actions with
receiver = inner receiver (`FixDelegatedDeterministicStateInit`, PV 85); total prepaid gas
≤ 10¹⁵.

## 7. Actions (`Runtime::apply_action`, `lib.rs:523-774`)

### 7.0 Common prologue and the dispatch point

`exec = exec_fee(action, receiver)`; `result.gas_used = result.gas_burnt = exec.gas`,
`compute = exec.compute`. `is_refund = predecessor = system`;
`implicit_eligible = |actions| = 1 ∧ ¬is_refund`.
`check_account_existence` (`actions.rs:824-914`): CreateAccount on an existing account ⇒
`AccountAlreadyExists`; on a missing implicit id ⇒ `OnlyImplicitAccountCreationAllowed`;
Transfer to a missing account ⇒ ok iff `implicit_eligible` and the id is implicit (NEAR,
ETH or deterministic) else `AccountDoesNotExist`; every other action (except
DeterministicStateInit) needs the account. `check_actor_permissions`
(`actions.rs:776-822`): DeployContract, Stake, AddKey, DeleteKey, WithdrawFromGasKey (and
global-contract actions) need `actor = receiver`; DeleteAccount also needs `locked = 0`
(`DeleteAccountStaking`). A failed check is an action error. **Dispatch point**: after both
checks pass the action body runs; for `FunctionCall`, `DeployGlobalContract`,
`UseGlobalContract`, `DeterministicStateInit` this is the D3 hook (§13), out of D2.

### 7.1 CreateAccount (`actions.rs:155-199`)

Top-level id (no `.`, not `system`): `|id| < 65` and predecessor ≠ `registrar` ⇒
`CreateAccountOnlyByRegistrar`; otherwise the id must be a direct sub-account of the
predecessor (`is_sub_account_of`) else `CreateAccountNotAllowed`. Success: `actor :=
receiver`, `account := Account::new(0, 0, None, 100)` (V1).

### 7.2 DeployContract (`actions.rs:297-341`)

`clear_account_contract_storage_usage`: subtract the current contract's storage (`Local(h)` ⇒
`get_code_len(ContractCode(acct))` — path read only, absent ⇒ 0; `Global`/`GlobalByAccount`
⇒ 32 / `|id|`; None ⇒ 0), saturating; `usage += |code|` (overflow ⇒ inconsistent);
`contract := Local(sha256(code))` (V1 stays V1, V2 stays V2); `set ContractCode(acct) :=
code`. Precompilation into the compiled-contract cache does not affect state or validity.
**No WASM is executed and the witness carries no code** (`w.no_code` holds).

### 7.3 Transfer (`lib.rs:2887-2935`, `actions.rs:148-153, 201-295`)

Existing account: gas refund (`is_refund ∧ signer = receiver`) ⇒ §6.5; otherwise `amount +=
deposit` (overflow ⇒ inconsistent ⇒ reject). Missing (implicit creation): `actor := receiver`;
* NEAR-implicit (64 hex): key `ED25519(hex⁻¹(id))` with `AccessKey{nonce: (height−1)·10⁶,
  FullAccess}` written; `account := V1(deposit, 0, None, 100 + 33 + 9 + 40 = 182)`
  (`actions.rs:213-232`);
* ETH-implicit (`0x`+40 hex), PV 86 (`EthImplicitGlobalContract`): `account :=
  V2(deposit, 0, usage 100 + 32 = 132, Global(H))`, `H = eth_wallet_global_contract_hash(chain_id)`
  (`runtime/near-wallet-contract/src/lib.rs:89-105`): `mainnet`/`mocknet` ⇒
  `1daa835c…cad7ceb5`, `testnet` ⇒ `238feac1…9b67f6c5`, any other chain id ⇒
  `sha256(wallet_contract_localnet.wasm)` = `d2884a90…c142c49e8d`. **Nothing else is
  written** (no code, no key). `chain_id` is claim fact T3;
* NEAR-deterministic (`0s`+40 hex): `account := V1(deposit, 0, None, 100)`
  (`deterministic_account_id.rs:94-109`).

### 7.4 Stake (`actions.rs:47-101`)

`inc = stake ∸ locked`; `amount < inc` ⇒ `TriesToStake`; `locked = 0 ∧ stake = 0` ⇒
`TriesToUnstake`; `stake > 0 ∧ stake < minimum_stake` ⇒ `InsufficientStake`
(`minimum_stake` = claim fact `apply_facts[·].minimum_stake`, T11); success: proposal
`ValidatorStake::V1(receiver, pk, stake)`; if `stake > locked`: `amount −= inc`, `locked :=
stake` (an unstake only proposes; the lock is returned at the epoch boundary, §10.2).

### 7.5 AddKey (`access_keys.rs:149-255`)

Key exists ⇒ `AddKeyAlreadyExists`. Regular key: written with `nonce := (height−1)·10⁶`,
`usage += |h| + |borsh(key)| + 40`. Gas key: written with nonce 0, `num_nonces` rows
`GasKeyNonce(i) := (height−1)·10⁶`, `usage += num_nonces · (|h| + 2 + 8 + 40) + |h| +
|borsh(key)| + 40` (`access_keys.rs:17-44, 194-228`). Overflow ⇒ inconsistent.

### 7.6 DeleteKey (`access_keys.rs:52-147`)

Absent ⇒ `DeleteKeyDoesNotExist`. Regular: remove, `usage ∸= |h| + |borsh(key)| + 40`. Gas
key: `balance > 10²⁴` (1 NEAR) ⇒ `GasKeyBalanceTooHigh`; else `tokens_burnt += balance`,
remove rows `0 … num_nonces−1` (blind removes), compute `+= storage_removes_compute(n, n ·
|nonce key|, 8n)` (`config.rs:56-69`), remove the key, `usage ∸=` the gas-key cost of §7.5.

### 7.7 TransferToGasKey / WithdrawFromGasKey (`access_keys.rs:257-335`)

Key absent or not a gas key ⇒ `GasKeyDoesNotExist`. To: `balance += deposit` (overflow ⇒
inconsistent), write the key (the account was charged the deposit at the tx/receipt level).
Withdraw: `balance < amount` ⇒ `InsufficientGasKeyBalance`; else `balance −= amount`, write
the key, `amount_account += amount` (overflow ⇒ inconsistent).

### 7.8 DeleteAccount (`actions.rs:343-431`, `store/utils.rs:435-552`)

1. Contract storage (`FixDeleteAccountGlobalContractStorageUsage`, PV 85): as §7.2's
   `get_contract_storage_usage`; `usage' = usage ∸ contract_storage`; `usage' > 10 000` ⇒
   `DeleteAccountWithLargeState`.
2. `compute_gas_key_balance_sum`: iterate the keys with prefix `2 ‖ acct ‖ 2` (§3.1), parse
   the handle (`0`/`1`/`3` tag + 32/64/32 B, anything else ⇒ inconsistent) and the optional
   `u16` nonce suffix (other lengths ⇒ inconsistent), skip nonce rows, `get` each key (via
   the overlay) and sum gas-key balances (overflow ⇒ inconsistent). `> 10²⁴` ⇒
   `GasKeyBalanceTooHigh`.
3. `amount > 0` ⇒ new receipt `new_balance_refund(beneficiary, amount)`.
4. `remove_account`: remove `Account`, `ContractCode`, every key and nonce row found by a
   second iteration of `2 ‖ acct ‖ 2`, and every `ContractData` key found by iterating
   `9 ‖ acct ‖ ','` (each counts 2000 in the proof upper bound, §3.3).
5. `tokens_burnt += gas-key balance sum`; nonce rows ⇒ compute `+=
   storage_removes_compute(count, Σ|raw key|, 8·count)`; `actor := predecessor`; `account :=
   None` (so step §6.4.4 writes nothing).

### 7.9 Instant `DeleteAccount` receipts

A Delegate whose inner actions are exactly `[DeleteAccount]` produces an instant receipt
(§6.1), processed right after on **this** shard whatever its receiver (§8).

## 8. Delegate / DelegateV2 (`actions.rs:487-774`, `action/delegate.rs`)

Signed message: `sha256(u32le(2³⁰ + 366) ‖ borsh(DelegateAction))` for Delegate,
`sha256(u32le(2³⁰ + 611) ‖ borsh(VersionedDelegateActionPayload::V2 = 0 ‖ DelegateActionV2))`
for DelegateV2 (`core/primitives/src/signable_message.rs:18-25, 216-228`). `DelegateAction =
{sender_id, receiver_id, actions: Vec<NonDelegateAction>, nonce: u64, max_block_height: u64,
public_key}`; V2 has `nonce: TransactionNonce`.

`apply_delegate_action`: signature invalid (`Signature::verify`, ED25519 = D1 §2) ⇒
`DelegateActionInvalidSignature`; `height > max_block_height` ⇒ `DelegateActionExpired`;
`sender_id ≠ receiver` ⇒ `DelegateActionSenderDoesNotMatchTxReceiver`; then
`validate_delegate_action_key` (`actions.rs:600-774`): key `(sender, pk)` absent ⇒
`AccessKeyNotFound`; plain nonce with a gas key ⇒ `DelegateActionRequiresNonGasKey`;
gas-key nonce: not a gas key ⇒ `DelegateActionRequiresGasKey`, `idx ≥ num_nonces` ⇒
`DelegateActionInvalidNonceIndex`, row absent ⇒ inconsistent; `nonce ≤ current` ⇒
`DelegateActionInvalidNonce`; `nonce ≥ height · 10⁶` (unchecked multiplication) ⇒
`DelegateActionNonceTooLarge`; FC key: `|actions| ≠ 1` or not a FunctionCall ⇒
`RequiresFullAccess`, deposit > 0 ⇒ `DepositWithFunctionCall` (returns,
`FixDelegateActionDepositWithFunctionCallError` PV 85), receiver / method mismatch; then
the access-key nonce (or the gas-key row) `:= nonce`. Success: new `Action` receipt
`{predecessor: sender, receiver: inner receiver, signer/key/gas price of the outer receipt,
actions: inner}`; `gas_used += required_cost(new receipt).gas + prepaid_send.gas`
(`required_cost = total_prepaid_exec_fees + total_prepaid_gas + new_action_receipt.exec`),
`gas_burnt += prepaid_send.gas`, `compute += prepaid_send.compute` (`actions.rs:519-557`).
A SECP256K1 delegate signature is out of D2 (`e.secp`); ML-DSA keys are out (`w.shape`).

## 9. Queues

### 9.1 Delayed receipts (`congestion_control.rs:796-944`, `rch.rs:83-237`)

`load` reads `DelayedReceiptIndices` (absent ⇒ `{0,0}`). **push**(receipt): `gas =
compute_receipt_congestion_gas` (Action/ActionV2: `total_prepaid_gas +
total_prepaid_exec_fees.gas + new_action_receipt.exec + total_prepaid_send_fees.gas`; every
other kind 0, `congestion_control.rs:678-741`), `size = |borsh(receipt)|`; set
`DelayedReceipt(next) := StateStoredReceipt::V1(receipt, gas, size)`, `next += 1`, write the
indices; accumulate `new_gas/new_bytes`. **pop** (`congestion_control.rs:880-917`): while the
proof limit is not exceeded and `first < next`: `get DelayedReceipt(first)` (absent ⇒
inconsistent), remove it, `first += 1`, write indices; accumulate `removed_gas/bytes` from the
metadata (or recomputed for a plain `Receipt`); return it if it routes to this shard
(receipts of other shards — resharding leftovers — are dropped). Congestion: `delayed_gas +=
new − removed`, `bytes += new − removed` at the end (`congestion_control.rs:931-943`, adds
before subtracts; underflow/overflow panics).

### 9.2 Receipt sink: limits, forwarding, buffering (`congestion_control.rs:86-500`)

Limits per shard `s` of the block's congestion map: `gas = s = own ? u64::MAX :
outgoing_gas_limit(s's congestion, missed, own)` (D0), `size = granted bandwidth (own → s)`;
a shard without an entry: `(u64::MAX, 0)`.
**try_forward**(r, gas, size, shard): `size := min(size, 4 194 304)`; forward iff `limit.gas ≥
min(gas, allowed_shard_outgoing_gas = 10¹⁵)` (`ClampOutgoingGasAdmission`, PV 85) and
`limit.size ≥ size`; then `limit.gas ∸= gas` (saturating), `limit.size −= size`.
**forward_from_buffer** (`congestion_control.rs:236-286, 338-399`): for every split-parent
shard of the layout, then every shard id of the layout in order: iterate the buffer
`BufferedReceipt(shard, first…next−1)` (reading each from the pre-state trie), `gas, size` from
the metadata (recomputed for a plain `Receipt`), `try_forward` to the receipt's current
shard; stop at the first that is not forwarded. For each forwarded: own congestion
`receipt_bytes −= size`, `buffered_gas −= gas`; then `pop_n(k)` removes the first `k` items
(blind removes, indices written if `k > 0`) and, for V1 entries, `update_on_receipt_popped`
(§9.3). **forward_or_buffer_receipt**(r): `shard` = receiver's shard, `size = |borsh r|`, `gas =
congestion gas`; `try_forward`; else **buffer**: own congestion `receipt_bytes += size`,
`buffered_gas += gas`, `update_on_receipt_pushed(shard, size, gas)`, `BufferedReceipt(shard,
next) := StateStoredReceipt::V1`, indices `next += 1` (the map entry is created if absent),
`BufferedReceiptIndices` rewritten. Note that a new receipt may be forwarded while older ones
of the same shard stay buffered (the buffer is not checked).

### 9.3 Receipt groups and bandwidth requests (`om.rs:22-340`, `congestion_control.rs:503-610`, `core/primitives/src/bandwidth_scheduler.rs:81-170`)

Metadata per shard (`BufferedReceiptGroupsQueueData`), loaded for every shard in
`BufferedReceiptIndices` (absent ⇒ none). **pushed**(size, gas): totals += (checked), `num +=
1`; `pop_back` the last group (`get` + remove, indices `next −= 1`), then either (if `size +
size_last > 100 000`, `ByteSize::kb(100)` with bytesize 1.1.0 `KB = 1000`, or gas bound
`u64::MAX` exceeded) push it back and push a new group `{size, gas}`, or push back the
enlarged group; with no group: push `{size, gas}`; every push/pop writes the queue data.
**popped**(size, gas): totals −= , `num −= 1`; `modify_first`: `get` the first group,
subtract; empty (size 0) ⇒ `pop_front` (which `get`s it again and removes it) else write it
back (and write the data). **Requests** (`generate_bandwidth_requests`, after all receipts): for
each shard id of the layout: `len = next − first` of its buffer (absent ⇒ 0); `len = 0` ⇒ no
request; metadata present with `total_receipts_num = len` ⇒ the group sizes from iterating
`BufferedReceiptGroupsQueueItem(shard, first…)` (`get` each, *from the final overlay*), else
the single size `max_receipt_size`; plus the split-parent's buffer first;
`make_from_receipt_sizes`: running total of `min(size, 4 194 304)`; skip while `≤
base_bandwidth`; set bit of the first of the 40 request values `base + (max_single_grant −
base)·(i+1)/40` that is `≥` the total; stop if none; no bit set ⇒ no request. Result
`BandwidthRequests::V1(requests)` compared with the header (`validate.rs:171-174`).

### 9.4 Yield timeouts (`lib.rs:2986-3088`)

`get PromiseYieldIndices` (absent ⇒ `{0,0}`); while `first < next`: stop if `total.compute ≥
limit` (or proof limit); `get PromiseYieldTimeout(first)` (absent ⇒ inconsistent); stop if
`expires_at > height`; if `contains_key PromiseYieldReceipt(acct, data_id)` (path only):
create `PromiseResume{data_id, data: None}` from `acct` to `acct` with id
`sha256(data_id ‖ u64 height ‖ u64 k)` (k counts created resumes) and
`forward_or_buffer_receipt` it (to this shard: forwarded with `u64::MAX` gas and the
self-grant); remove the timeout entry, `first += 1`. Indices written at the end iff changed
(`lib.rs:2745-2753`). No WASM runs here; the resume executes in a later chunk.

## 10. `Runtime::apply` end to end; epoch boundaries

### 10.1 Chunk results

`gas_used = Σ outcome.gas_burnt` (checked, panics); `balance_burnt = tx_burnt + other_burnt`
(subsidized and slashed are 0 in D2) (`chain/chain/src/runtime/mod.rs:372-406`);
`validator_proposals` = the proposals of all processed receipts, deduplicated keeping the
**last** proposal of each account, in reverse order of appearance (`lib.rs:2814-2823`);
congestion info as §9.1/§9.2 plus `allowed_shard = shard_ids[(height + shard_index) mod n]`
(`congestion_info.rs:360-384`, `lib.rs:2759-2772`); bandwidth requests §9.3; outgoing receipts =
the forwarded receipts in order. Header comparison: D0 §3.7 with these values
(`validate.rs:133-188`).

### 10.2 `ValidatorAccountsUpdate` (`lib.rs:1599-1716`, `chain/chain/src/runtime/mod.rs:229-271`)

If the applied block X starts an epoch (claim `epoch_start_after` of X's parent = 1),
`stake_info`, `validator_rewards` (claim `apply_facts[·].validator_update`, unfiltered) are
filtered to accounts on this shard; `last_proposals` = proposals of the shard's previous
chunk filtered to the shard (last wins per account): for the main transition the B2-slot
header's `prev_validator_proposals`, for an implicit transition the main transition's
`ChunkExtra.validator_proposals` (`update_shard.rs:170, 223`); `treasury` = claim treasury if
on this shard. For each `(acct, max_stake)` in `stake_info` (order irrelevant: every failure
rejects, writes are per key): account present: `locked += reward` (if any; overflow panics),
`locked < max_stake` ⇒ inconsistent, `return = locked − max(max_stake, last_proposal)`
(underflow panics), `locked −= return`, `amount += return` (overflow panics), set; absent ∧
`max_stake > 0` ⇒ inconsistent. Treasury not in `stake_info`: account must exist and have a
reward (else inconsistent), `amount += reward`. Commit. Applies to missing chunks too.

### 10.3 Missing chunk

Validator update (if epoch start), delayed indices load, scheduler, finalize; congestion
info and bandwidth requests unchanged (`lib.rs:2937-2984`).

## 11. Chain-level changes in `Rel` (D2 vs D1)

* **Several epochs** (`c.single_epoch` lifted): the `epochs` table has one entry per
  distinct epoch id among `c.epoch_id` and the segment's headers (ascending, no extras); every
  entry has PV 86 and the **same shard-layout bytes** as `c.epoch_id`'s (else out of domain,
  resharding). `epoch_start_after[i]` must match the headers (`spec/claim-v3.md` §2.2):
  `epoch(after blocks[i]) = blocks[i].next_epoch_id` if 1, `= blocks[i].epoch_id` if 0.
* `apply_facts[k].validator_update` is `Some` iff the k-th applied block starts an epoch;
  `split_gate` must be `None` (`c.no_split_gate`, D∞).
* The witness decoder accepts every D2 receipt, transaction and action shape (§12 `w.shape`).

## 12. `InD2`

D2 keeps these D0/D1 conditions unchanged: `c.pv86` (for every epoch), `c.layout`,
`c.headers`, `c.not_genesis`, `c.segment`, `c.no_split_gate` (split gate only),
`w.no_code`, `e.scheduler_state`. It **lifts** `c.single_epoch`, `c.own_congestion_zero`,
`r.shape`, `r.success`, `r.refunds`, `w.proof_shape`, `w.tx_shape` (replaced by `w.shape`),
`t.signer_v1`, `e.compute`, `e.queues_empty`, `e.forwarded`, `e.distinct_ids`. New/changed:

| id | condition | reason |
|---|---|---|
| `c.same_layout` | all epochs of the claim have byte-identical `shard_layout`; no non-empty outgoing buffer to a shard id outside the layout | resharding (D∞) |
| `w.size` | `|state_witness| ≤ 8 MiB`; `Σ|main base_state values| + 2000·R ≤ 4 000 000` (`R` = `ContractData` removals in the main transition) | the storage-proof limit (§3.3) never triggers |
| `w.shape` | no action `DeployGlobalContract`/`UseGlobalContract`/`DeterministicStateInit`, no `GlobalContractDistribution` receipt, no ML-DSA-65 public key (receipt signer keys, AddKey/DeleteKey/Stake/gas-key actions, delegate keys) in any decoded transaction or receipt (witness lists and every receipt read from state); transactions (both lists) carry ED25519 keys and signatures | global contracts and SHA3-256 key handles / ML-DSA and secp256k1 *transaction* signature verification are not formalized |
| `e.wasm` | no FunctionCall action reaches the dispatch point (§7.0) — e.g. an incoming, local, delayed, postponed or yielded receipt with a FunctionCall whose receiver exists and earlier actions succeeded | WASM execution (D3) |
| `e.secp` | no SECP256K1 Delegate signature is verified | ECDSA recovery not formalized |
| `e.storage_proof` | (implied by `w.size`) the proof limit is never reached | |

**Inside D2** (formalized, not excluded): every transaction shape with ED25519 signatures
(any action list, V0/V1, monotonic/strict nonces, gas-key nonces with `DepositFailed`,
function-call keys with allowances, FunctionCall transactions whose receipt is forwarded or
delayed), every non-WASM action with all its failure modes, multi-action receipts, ActionV2
receipts with `refund_to`, refunds to accounts / gas keys / allowances, deposit burns of failed
refunds, data receipts and postponed receipts, PromiseYield storage and PromiseResume no-ops,
yield timeouts, delayed receipts (push and pop, both encodings), outgoing buffers with
receipt groups and bandwidth requests, instant DeleteAccount receipts, AccountV2,
ETH-/NEAR-implicit and deterministic account creation, validator proposals and
`ValidatorAccountsUpdate` at epoch boundaries (main and implicit transitions), segments
spanning several epochs with one layout, and the full trie semantics (insert, delete,
squash, prefix iteration) with nearcore's read set.

## 13. The D3 interface

The Lean D2 runtime is parameterized by `ActionHooks` (`NearSpecV3/D2/Actions.lean`):

```
structure ActCtx where env : Env; r : Rcpt; a : ActionR; idx : Nat; nActs : Nat
structure ActSt  where o : Ovl; account : Option Acct; actor : Bytes
structure AR     where gasBurnt gasUsed compute : Nat; ok : Bool; newReceipts : List Rcpt;
                       proposals : List Proposal; tokensBurnt : Nat
structure ActionHooks where
  functionCall : ActCtx → ActSt → AR → Base → Except String (ActSt × AR)
```

`functionCall` is called at the dispatch point (§7.0) with the receipt context, the overlay,
the receiver account, the actor and the result so far (exec fee charged); its result is merged
exactly like every other action (`D2/Receipts.lean` `actionLoop`). D2 instantiates it with
`out of domain (e.wasm)` (`d2Hooks`). D3 supplies WASM execution; the D2 code already carries
the generic parts it needs: input-data reads (§6.4.1), `ReceiptIndex` handling of output data
receivers (§6.4.9, unreachable in D2), the receiver reward (§6.4.8, 0 in D2). D3 also extends
`D2.Base` with the global-contract / state-init actions (decoded as `out of domain (w.shape)`
today), adds `GlobalContractDistribution` receipts to `D2.RBody` and lifts `w.no_code`. The
receipt-kind processors (`processReceipt`: Data / Action / PromiseYield / PromiseResume), the
queues (`D2/Queues.lean`), transactions (`D2/TxD2.lean`), the validator update and the chain-level
checks are total in D2 and are reused unchanged.

## 14. Formalization (`spec/lean/v3`, Lake package `NearSpecV3`)

| module | content |
|---|---|
| `D2/Types` | Account V1/V2, AccessKey, actions, receipts, StateStoredReceipt: decoders and encoders |
| `D2/Params` | §4 |
| `D2/Trie` | full reveal of the recorded store, `PTrie.delete` with squash (§3.4), path-only refs, prefix iteration with nearcore's read set |
| `D2/State` | the `TrieUpdate` overlay (§3.1), `finalize` |
| `D2/Fees`, `D2/Validate` | §4.1, §6.6 |
| `D2/Actions` | §7, §8, `ActionHooks` |
| `D2/Receipts` | §6 |
| `D2/Queues` | §9 |
| `D2/Validators` | §10.2 |
| `D2/TxD2` | §5 |
| `D2/RuntimeD2` | §1, §10 |
| `ChunkValidationD2` | `checkD2`, `RelD2` (§11) |
| `ChallengeD2` | `ArenaCore.ChallengeSpec` with `Rel = RelD2` |

Executable: `nearspec-v3-check-d2 [--d1|--d0] CASE…`.

## 15. Evidence

* **Public D1 / D0 fixtures** (`oracle/fixtures/v3/public-d1`, 529 cases; `oracle/fixtures/v3/public`,
  201 cases): `nearspec-v3-check-d2` gives the same verdict as `nearspec-v3-check-d1` /
  `-check-d0` on every case the lower rung decides (accept/reject), so `InD1 ⊂ InD2` and
  `InD0 ⊂ InD2` hold on them; of the lower rung's out-of-domain cases 98 become in-domain for
  D2 (43 + 55, all accepted, nearcore accepted every one), 8 are rejected (nearcore rejected
  every one) and 8 stay out of domain (`c.not_genesis`).
* **Trie finalize** (`nearspec-v3-test-trie-d2`, vectors from `spec/tools/trie_vectors_d2.py`,
  an independent canonical-trie builder with nearcore's node encoding and memory usage): random
  maps with shared prefixes, branch values and empty values, random insert / overwrite /
  delete sets (incl. deleting every key): 4 900 cases, 0 mismatches of the post-state root.
  This tests `PTrie.del` + squash + memory usage, not the read set (which needs nearcore's
  verdicts on dropped nodes: the D2 difftest's single-node-drop mutants).
* D2 corpora from the D2 oracle (`expected_rel_d2`): see the lane's final report.

