# `near/pv86/chunk-validation/v0` — domain D3: the runtime around a `FunctionCall` (RuntimeD3)

Companion to `spec/near-chunk-validation-d2.md` (D2: every non-WASM action, queues, epochs; its §13
"The D3 interface"), the D3 WASM spec (`spec/lean/v3/NearSpecV3/Wasm/*`, prose:
`docs/research/near-wasm-prose-spec.md`, boundary: `docs/research/near-wasm-boundary.md`) and the
contract-storage accounting note `docs/research/d3-trie-accounting.md`. This document is the
transcription of **everything nearcore 2.13.4 (`44f7ae6`, PV 86) does around a `FunctionCall`
action** that `RuntimeD3` must model *outside* the WASM machine: dispatch, contract lookup, the
`VMContext`, how a `VMOutcome` becomes an `ActionResult`, the receipts built from the VM's
`ReceiptManager`, what changes in `apply_action_receipt`, which outcome bytes are hashed, and the
exact (additive) extensions of the D2 Lean interface.

Every `file:line` is relative to the pinned nearcore checkout `/data/illia/nearproof-deps/nearcore`
unless it starts with `spec/` or `docs/` (this repository). Abbreviations:

| short | file |
|---|---|
| `lib.rs`, `actions.rs`, `ext.rs`, `fc.rs`, `rm.rs`, `pipelining.rs`, `contract_code.rs` | `runtime/runtime/src/{lib,actions,ext,function_call,receipt_manager,pipelining,contract_code}.rs` |
| `W:logic.rs`, `W:mod.rs` | `runtime/near-vm-runner/src/wasmtime_runner/{logic,mod}.rs` (the live VM at PV 86) |
| `L:logic.rs`, `L:context.rs` | `runtime/near-vm-runner/src/logic/{logic,context}.rs` |
| `utils.rs`, `tx.rs`, `receipt.rs` | `core/primitives/src/{utils,transaction,receipt}.rs` |
| `contract.rs`, `update.rs`, `store/utils.rs` | `core/store/src/contract.rs`, `core/store/src/trie/update.rs`, `core/store/src/utils/mod.rs` |
| `pwt.rs` | `chain/client/src/stateless_validation/partial_witness/partial_witness_tracker.rs` |
| `rt/mod.rs` | `chain/chain/src/runtime/mod.rs` |
| `D2/…`, `Wasm/…` | `spec/lean/v3/NearSpecV3/D2/…`, `spec/lean/v3/NearSpecV3/Wasm/…` |

Statements not confirmed in source are marked **[unverified]**; modelling decisions this document
proposes (not facts about nearcore) are marked **[decision]**.

Contents: §1 the `FunctionCall` arm, end to end · §2 contract code: lookup, witness, cache · §3
`VMContext` · §4 from `VMOutcome` to `ActionResult` · §5 receipts from the `ReceiptManager` · §6
what changes in `apply_action_receipt` · §7 exactly which outcome bytes are hashed · §8 the D2
interface extensions · §9 the mock action log vs nearcore receipts · §10 new domain conditions and
hazards · §11 corrections to D2 §13.

---

## 1. The `FunctionCall` arm, end to end

Order of effects for one `FunctionCall` action `fc = {method_name, args, gas, deposit}` at action
index `i` of an action receipt `r` (receiver `acct`), inside `apply_action_receipt`'s action loop
(`lib.rs:848-888`):

1. **Action hash** `ah = create_action_hash_from_receipt_id(r.receipt_id, block_height, i)`
   (`lib.rs:849-853`) `= sha256(r.receipt_id ‖ u64le(block_height) ‖ u64le(2⁶⁴−1−i))`
   (`utils.rs:287-297, 327-334`). Computed for every action, used only by FunctionCall (and
   state init).
2. **Prologue** (`lib.rs:540-567`, D2 §7.0): `result.gas_burnt = result.gas_used = exec_fee(fc)`
   (`function_call_base.exec + function_call_byte.exec · (|method|+|args|)`), `compute` likewise;
   `check_account_existence` — FunctionCall needs the account (`AccountDoesNotExist`);
   `check_actor_permissions` — no restriction for FunctionCall. A failing check returns an
   action error; nothing below runs, `gas_burnt_for_function_call = 0`.
3. **Dispatch** (`lib.rs:631-668`): `account = account.expect(EXPECT_ACCOUNT_EXISTS)`;
   `contract_id = RuntimeContractIdentifier::resolve(acct, account.contract, state_update,
   wasm_config, chain_id, AccessOptions::DEFAULT)?` (`contract_code.rs:39-83`, §2.1; a
   `StorageError` rejects); `contract = preparation_pipeline.get_contract(r, contract_id, i, None)`
   (`pipelining.rs:323-374`: preparation = code lookup + compile + load + method resolution, §2,
   `docs/research/near-wasm-boundary.md` §2); `is_last_action = (i + 1 = |actions|)`.
4. **`action_function_call`** (`fc.rs:31-233`):
   1. `account.amount + fc.deposit` overflows u128 ⇒ `StorageInconsistentState` ⇒ **reject**
      (`fc.rs:49-54`). (So `ExecutionResultState::new`'s `expect` cannot fire, `L:logic.rs:66-70`.)
   2. `record_contract_call` (`fc.rs:56, 355-393`): a no-op unless `apply_reason =
      UpdateTrackedShard` (`fc.rs:362-364`); at `ValidateChunkStateWitness` it does nothing (it is
      how the *producer* learns which code hashes to announce, §2.2).
   3. Fresh `ReceiptManager::default()` and `RuntimeExt::new(state_update, receipt_manager, acct,
      account.clone(), ah, epoch_id, block_height, …, storage_proof_size_before_receipt)`
      (`fc.rs:61-75`; `ext.rs:89-119`, `data_count = 0` at `ext.rs:109`).
   4. `outcome = execute_function_call(…)?` (`fc.rs:76-89`, `fc.rs:236-348`): builds the
      `VMContext` (§3), runs the VM (`fc.rs:284`), classifies runner errors (§4.1), and — only for
      an outcome the VM produced, aborted or not — distributes unused gas to weighted function
      calls (`fc.rs:341-345`, §5.5).
   5. Result handling (§4.2): an aborted outcome sets `result.result = Err(FunctionCallError)`
      (`fc.rs:100-142`); then always: `gas_burnt += burnt`, `gas_burnt_for_function_call +=
      burnt`, `gas_used += used`, `compute += compute`, `logs += logs`, profile merged
      (`fc.rs:143-153`); only on success: yield timeouts enqueued, receipts built, account
      `amount`/`storage_usage` written back, `subsidized_amount` added, `result.result =
      Ok(return_data)`, receipts appended (`fc.rs:154-230`).
5. Back in the loop (`lib.rs:870-887`): on success each new receipt is checked with
   `validate_receipt(NewReceipt)` (failure ⇒ `NewReceiptValidationError`), then `merge`
   (`lib.rs:439-480`, §6.1); the first error stops the loop.

**Deposit.** `VMContext.account_balance` is the account's amount *before* the deposit
(`fc.rs:272`, `L:context.rs:42-44`); the VM starts with `current_account_balance =
account_balance + attached_deposit` (`L:logic.rs:66-70`; Lean `Wasm/Exec.lean:468`), deducts
promise deposits from it (`L:logic.rs:89-93`, except the `one_yocto_on_promise` subsidy,
`W:logic.rs:3069-3080, 3898-3909`), and on **success** the account's amount becomes
`outcome.balance` (`fc.rs:224`) — i.e. the deposit is credited exactly when the call succeeds. On
**failure** the account is not touched by the call (`fc.rs:224-225` are inside `if
execution_succeeded`), the receipt fails, and the deposit goes back in the balance-refund receipt
(`lib.rs:1185, 1284-1289`, D2 §6.4.6) to `balance_refund_receiver` (= `refund_to` or
predecessor).

---

## 2. Contract code: lookup, witness, cache

### 2.1 Identifier resolution (`contract_code.rs:39-95`)

| `account.contract` | identifier | code hash | reads |
|---|---|---|---|
| `None` | `None` | `CryptoHash::default()` (`contract_code.rs:90`) | none |
| `Local(h)`, account id not ETH-implicit | `AccountLocal{h, acct}` | `h` | none |
| `Local(h)`, ETH-implicit, `h` a legacy wallet hash | (`eth_implicit_global_contract`) `Global{eth_wallet_global_contract_hash(chain_id)}` (`contract_code.rs:56-76`) | wallet hash | none |
| `Global(h)` | `Global{h, CodeHash(h)}` | `h` (`contract_code.rs:104-106`) | none |
| `GlobalByAccount(id)` | `Global{…, AccountId(id)}` | value hash of `TrieKey::GlobalContractCode{AccountId(id)}` (`get_ref`, MemOrFlatOrTrie); absent ⇒ `StorageInconsistentState` ⇒ reject (`contract_code.rs:107-116`) | path to that key |

Global identifiers stay out of domain in the first D3 rung unless `w.shape` is lifted (D2 §12);
the `Local` row is the D3 core.

### 2.2 Where the code bytes come from

`RuntimeContractExt::get_code` = `ContractStorage::get(code_hash)` for `AccountLocal`/`Global`,
`None` for `None` (`ext.rs:635-644`). `ContractStorage::get` (`contract.rs:104-131`) returns, in
order:

1. a contract deployed **during this chunk**: the `ContractsTracker`'s uncommitted deploys (current
   receipt) or committed deploys (earlier receipts of the chunk), keyed by code hash
   (`contract.rs:42-48`). `DeployContract` records its code there (`actions.rs:336-339`,
   `update.rs:298-300`); `TrieUpdate::commit` moves uncommitted → committed (`update.rs:222`,
   `contract.rs:63-69`), `rollback` clears the uncommitted ones (`update.rs:227`,
   `contract.rs:58-61`). Committed deploys are never removed by later deploys.
2. otherwise `storage.retrieve_raw_bytes(code_hash)` on the trie **storage** underlying the
   `TrieUpdate` (`contract.rs:119`, `update.rs:80-85`: `ContractStorage::new(trie.storage)`). For a
   stateless validator that is `TrieMemoryPartialStorage` over
   `main_state_transition.base_state` (`chain/chain/src/stateless_validation/chunk_validation.rs:433-434, 708`), a map *value-hash →
   bytes* (`core/store/src/trie/trie_storage.rs:325-337`). The read goes to the storage, **not
   through the trie recorder**, so it is not recorded and does not count towards the storage-proof
   size.
3. otherwise `None` (`contract.rs:120-128`).

**How a validator obtains the code.** The chunk producer announces the code hashes the chunk
accessed (`ChunkContractAccesses`, from `record_contract_call`, `fc.rs:355-393`: only contracts
present in the *pre-state trie* with that hash — newly deployed ones are excluded). A validator
requests only the hashes **not in its compiled-contract cache**
(`chain/client/src/stateless_validation/partial_witness/partial_witness_actor.rs:709-721`, `chain/client/src/stateless_validation/mod.rs:17-24`), and
when the codes arrive (or the 2 s request timeout passes, `pwt.rs:45-48, 335-366`) the received
blobs are **appended to `main_state_transition.base_state` as `TrieValues`**
(`pwt.rs:693-696`). The arena judge does exactly this with `witness.bin`'s `contract_code` list
(`oracle/v3/src/judge.rs:19-28`: `values.extend(codes)`; format `spec/claim-v3.md` §3).

**The compiled-contract cache short-circuits code lookup.** Preparation first looks up the
compiled module by `get_contract_cache_key(code_hash, config, vm_hash)`; only on a cache miss is
`get_code()` called, and `None` there is `VMRunnerError::ContractCodeNotPresent`
(`W:mod.rs:699-721`). The validator always has a cache (`cache: Some(compiled_contract_cache)`,
`rt/mod.rs:335`). Then (`fc.rs:293-310`):

* `ContractCodeNotPresent` ∧ `apply_reason = ValidateChunkStateWitness` ∧ `account.contract ≠
  None` ⇒ `StorageError::MissingTrieValue(TrieMemoryPartialStorage, code_hash)` ⇒ **reject**;
* `ContractCodeNotPresent` otherwise (in particular `account.contract = None`) ⇒
  `VMOutcome::nop_outcome(CompilationError::CodeDoesNotExist{acct})`: an action failure with
  **0 VM gas** (the exec fee of §1.2 stays burnt).

So a validator whose cache holds the module (or a cached compile error) accepts a witness that
lacks the code; a cold-cache validator rejects it. The verdict on such a witness is **node-local**.

**[decision] `Rel_D3` uses cold-cache semantics:** for a `FunctionCall` dispatched on an account
with `contract = Local(h)` (or a global identifier), the code is the unique available blob with
`sha256 = h` from (a) the chunk's deploy tracker (committed ∪ current receipt's uncommitted) or (b)
`w.main.values ++ codes`; if none is available, `Rel_D3` **rejects** (nearcore's
`MissingTrieValue`). On any witness that carries the code, cold and warm validators agree (the
cache key fixes the compiled module and the compile result), so this choice only decides the
node-local case. The oracle judge must therefore run with an empty compiled-contract cache on the
code-omission mutants.

**Consequences for the Lean witness pipeline.**
* `w.no_code` (D2 `ChunkValidationD2.lean:103`) is lifted; the merged value set `w.main.values ++
  codes` is what nearcore uses for **every** read, not only code lookup: `revealTrie` must be
  built from the merged list, since an appended blob can also serve a trie value read with the
  same hash (e.g. a `ContractCode` value) **[decision: follow nearcore exactly]**.
* `w.size` (D2 §12): code fetches are not recorded (above), so the D2 bound stays sound if it sums
  the merged list (conservative); summing only the original `base_state` values is tighter but
  needs the argument that no trie read records an appended blob **[decision]**.

---

## 3. `VMContext` (`fc.rs:252-281`, struct `L:context.rs:11-65`)

| field | value | source | Lean `CallCtx` (`Wasm/Machine.lean:230-252`) |
|---|---|---|---|
| `current_account_id` | `acct` | `fc.rs:261` | `currentAccount` |
| `signer_account_id` | `action_receipt.signer_id` | `fc.rs:262` | `signer` |
| `signer_account_pk` | `borsh(action_receipt.signer_public_key)` (`0 ‖ 32 B` for ED25519) | `fc.rs:263-264` | `signerPk` (must be the borsh bytes) |
| `predecessor_account_id` | `r.predecessor_id` | `fc.rs:81, 265` | `predecessor` |
| `refund_to_account_id` | `action_receipt.refund_to` (V2 only) else predecessor | `fc.rs:266` | `refundTo` |
| `input` | `fc.args` | `fc.rs:267` | `input` |
| `promise_results` | one per `input_data_id`, in order: `ReceivedData{Some(v)}` ⇒ `Successful(v)`, `{None}` ⇒ `Failed`; identical for every action of the receipt; `NotReady` never occurs | `lib.rs:796-821` | `promiseResults` (`.ok v` / `.failed`) |
| `block_height` | `apply_state.block_height` = height of the block holding the chunk (B2) | `fc.rs:269` | `blockHeight` |
| `block_timestamp` | `B2.header.raw_timestamp()` = `inner_lite.timestamp` | `fc.rs:270`, `chain/chain/src/types.rs:387`, `core/primitives/src/block_header.rs:1380-1390` | `blockTimestamp` |
| `epoch_height` | `get_epoch_height_from_prev_block(B2.prev_hash)` = claim `epochs[B2.epoch_id].epoch_height` (T7) | `fc.rs:271`, `rt/mod.rs:275` | `epochHeight` |
| `account_balance` | `account.amount` at dispatch (after earlier actions of the receipt), **without** the deposit | `fc.rs:272` | `accountBalance` |
| `account_locked_balance` | `account.locked` | `fc.rs:273` | `accountLocked` |
| `storage_usage` | `account.storage_usage` at dispatch | `fc.rs:274` | `storageUsage` |
| `account_contract` | `account.contract` (for `current_contract_code`, `W:logic.rs:4366-4398`) | `fc.rs:275` | **missing** (Host hard-codes `0`, `Wasm/Host.lean:548-549`) |
| `attached_deposit` | `fc.deposit` | `fc.rs:276` | `attachedDeposit` |
| `prepaid_gas` | `fc.gas` (also the gas counter's prepaid, `pipelining.rs:353, 390`) | `fc.rs:277` | `prepaidGas` |
| `random_seed` | `sha256(ah ‖ B2.header.random_value)` (`inner_rest.random_value`) | `fc.rs:258-259`, `utils.rs:309-319`, `chain/chain/src/types.rs:389` | `randomSeed` |
| `view_config` | `None` | `fc.rs:88, 279` | — |
| `output_data_receivers` | `is_last_action` ? the receipt's `output_data_receivers.map(receiver_id)` : `[]` | `fc.rs:253-257` | `receivers` |

`External` facts (not in `VMContext`): `validator_stake(acct)` = stake of `acct` among the
validators of `epoch_id` = epoch of B2 (`ext.rs:326-330`, `chain/epoch-manager/src/lib.rs:88-96`;
claim `epochs[·].validators`, T8), `validator_total_stake` = their sum (`chain/epoch-manager/src/lib.rs:98-104`, `unwrap`
on overflow ⇒ panic ⇒ reject), `chain_id` (claim T3, `ext.rs:338-340`); storage ops through the
`TrieUpdate` with node accounting (`docs/research/d3-trie-accounting.md`); the yield / data-id
functions of §5.

B2's header is already decoded in Lean: `BlockHdr.timestamp`, `.randomValue`, `.epochId`
(`spec/lean/v3/NearSpecV3/Wire.lean:265-276`); D2 builds `ApplyCtx` from it in `blockCtx`
(`ChunkValidationV0.lean:91-94`) and does not keep these three.

---

## 4. From `VMOutcome` to `ActionResult`

### 4.1 Runner errors (`fc.rs:292-339`) — the action-failure / reject boundary

| `near_vm_runner::run` result | effect |
|---|---|
| `Ok(outcome)`, `aborted = None` | success |
| `Ok(outcome)`, `aborted = Some(e)` (preparation/compile/link/method-resolve/trap/host error) | action failure; the outcome carries the gas burnt so far and the logs so far (`VMOutcome::abort` = `compute_outcome` + error, `L:logic.rs:4498-4502`), or zero gas for the no-op cases (`abort_but_nop_outcome_in_old_protocol`, `fix_contract_loading_cost = false`, `L:logic.rs:4531-4539`; boundary B11) |
| `ContractCodeNotPresent` | §2.2 (reject, or 0-gas `CodeDoesNotExist`) |
| `ExternalError(StorageError)` (e.g. `MissingTrieValue` during a storage op) | `RuntimeError::StorageError` ⇒ **reject** (`fc.rs:311-318`) |
| `ExternalError(ValidatorError)` | `RuntimeError::ValidatorError` ⇒ reject |
| `InconsistentStateError::IntegerOverflow` | `StorageInconsistentState` ⇒ reject (`fc.rs:319-321`) |
| `CacheError` | `StorageInconsistentState` ⇒ reject (`fc.rs:322-327`) |
| `LoadingError(msg)` | 0-gas `LoadingError` failure (`fc.rs:328-330`) — hazard H9, assumed absent |
| `WasmUnknownError` | 0-gas failure (`fc.rs:331-337`) — H9, assumed absent |

`HostError::RecordedStorageExceeded` (per-receipt storage-proof limit,
`runtime/near-vm-runner/src/logic/recorded_storage_counter.rs:16-31`) is an ordinary host error
(action failure); D2's `w.size` bound keeps it unreachable (§10).

### 4.2 Result handling (`fc.rs:100-230`)

Always (success or abort):
* `result.gas_burnt += outcome.burnt_gas`; `result.gas_burnt_for_function_call +=
  outcome.burnt_gas`; `result.gas_used += outcome.used_gas` (incl. distributed gas, §5.5);
  `result.compute_usage += outcome.compute_usage`; `result.logs.extend(outcome.logs)`;
  `result.profile.merge(outcome.profile)` (`fc.rs:143-153`; overflow ⇒ `IntegerOverflowError` ⇒
  reject). `compute_usage` = `profile.total_compute_usage(ext_costs, send_action_compute_usage)`
  (`L:logic.rs:131-141`; Lean `Gas.computeUsage`, `Wasm/Machine.lean:138-146`).
* Aborted ⇒ `result.result = Err(ActionError{FunctionCallError(convert(e))})` (`fc.rs:137-141`).
  The error value never reaches a hash (§7).

Only on success (`fc.rs:154-230`), in this order:
1. `promise_yield_indices = get(PromiseYieldIndices)` — **an unconditional trie read on every
   successful function call** (`fc.rs:156-157`, `store/utils.rs:150-154`); missing nodes ⇒ reject.
2. Action receipts in `ReceiptManager.action_receipts` order (§5.4); for each one with
   `is_promise_yield`: `enqueue_promise_yield_timeout(acct, input_data_ids[0], block_height + 200)`
   (`fc.rs:164-173`; `yield_timeout_length_in_blocks: 200`,
   `core/parameters/res/runtime_configs/parameters.yaml:275`): `set PromiseYieldTimeout{next} :=
   borsh{acct, data_id, expires_at}`, `next += 1` (`expect` ⇒ panic on overflow,
   `store/utils.rs:164-180`).
3. Data / PromiseResume receipts appended after all action receipts (`fc.rs:202-217`).
4. `PromiseYieldIndices` written iff changed (`fc.rs:220-222`).
5. `account.amount := outcome.balance`, `account.storage_usage := outcome.storage_usage`
   (`fc.rs:224-225`).
6. `result.subsidized_amount += outcome.subsidized_amount` (`fc.rs:226-227`).
7. `result.result = Ok(outcome.return_data)`; `result.new_receipts.extend(…)` (`fc.rs:228-229`).

All trie writes made during the call (contract storage, yield status, yield-id mappings, the
timeout entries) are in the `TrieUpdate`'s prospective changes: committed with the receipt or
rolled back with it (`lib.rs:961-970`). The trie-node accounting cache (`AccountingState`) is
chunk-scoped and survives rollback (`ext.rs:647-679`; created once per chunk, `docs/research/d3-trie-accounting.md` §2; `Wasm/ChunkStorage.lean:6-10`).

---

## 5. Receipts from the `ReceiptManager`

### 5.1 Data structures (`rm.rs:29-66`)

`ActionReceiptMetadata{receiver_id, refund_to: Option, output_data_receivers: Vec<DataReceiver>,
input_data_ids: Vec<hash>, actions: Vec<Action>, is_promise_yield}`;
`DataReceiptMetadata{data_id, data: Option<bytes>, is_promise_resume}`;
`ReceiptManager{action_receipts, data_receipts, gas_weights: Vec<((receipt_index, action_index),
weight)>, promise_yield_receipt_index}`. A **receipt index** is an index into `action_receipts`;
a **promise index** (returned to the guest) indexes the VM's `promises: Vec<Promise>`, `Promise =
Receipt(receipt_index) | NotReceipt(Vec<receipt_index>)` (`L:logic.rs:197-200`).

### 5.2 Ids

| id | formula | cite |
|---|---|---|
| action hash `ah` (per action of `r`) | `sha256(r.receipt_id ‖ u64le(h) ‖ u64le(2⁶⁴−1−i))` | `utils.rs:287-297, 327-334` |
| random seed | `sha256(ah ‖ random_value(B2))` | `utils.rs:309-319` |
| data id (k-th call of `generate_data_id` in this function call, `k = 0,1,…`) | `sha256(ah ‖ u64le(h) ‖ u64le(k))` (`create_receipt_id_from_action_hash`) | `ext.rs:303-311`, `utils.rs:299-307` |
| new receipt id (j-th entry of the receipt's final `new_receipts`) | `sha256(r.receipt_id ‖ u64le(h) ‖ u64le(j))` | `lib.rs:1081`, `lib.rs:220-226`, `utils.rs:278-285` |
| `SuccessReceiptId` | same formula with `j` = the global `ReceiptIndex` | `lib.rs:1123-1125` |

`h` = B2's height throughout. The data-id counter is **shared** by `promise_then` /
`promise_batch_then` joins and yield creation, in call order.

### 5.3 Host functions → `ReceiptManager` (`ext.rs:342-605`, `rm.rs:87-702`)

| host function(s) | External effect |
|---|---|
| `promise_create`, `promise_batch_create` | `create_action_receipt([], recv)`: push `{recv, refund_to: None, outputs: [], inputs: [], actions: [], yield: false}` (`ext.rs:342-351`, `rm.rs:111-137`) |
| `promise_then`, `promise_batch_then` (deps = receipt indices of the promise; a `NotReceipt` contributes all its indices) | one fresh data id `d_j` per dep, in dep order (`ext.rs:347-349`); for each `(d_j, dep_j)`: `action_receipts[dep_j].output_data_receivers.push({d_j, recv})`; push the new receipt with `input_data_ids = [d_j]` (`rm.rs:117-136`) |
| `promise_and` | no External call: VM-side `NotReceipt(deps)` (`W:logic.rs:2152-2220`) |
| `promise_batch_action_*` | `append_action(receipt_index, Action)` (`rm.rs:87-98`); FunctionCall: `method_name` must be UTF-8 else `HostError::InvalidMethodName` (`rm.rs:381-382`), `weight > 0` ⇒ `gas_weights.push(((ri, ai), w))` (`rm.rs:389-394`); AddKey-with-FC: every method name UTF-8 else `InvalidMethodName` (`rm.rs:594-600`) |
| `promise_set_refund_to` | `action_receipts[ri].refund_to = Some(acct)` (`rm.rs:697-702`) |
| `promise_return` | VM-side `return_data = ReceiptIndex(receipt_index)` (`W:logic.rs:4134-4152`) |
| `value_return` | VM-side `return_data = Value(bytes)`; charges data-receipt bytes per `output_data_receivers` (`W:logic.rs:4170-4226`) |
| `promise_yield_create` | `d = generate_data_id()`; push `{recv: acct, inputs: [d], yield: true}`; **trie write** `PromiseYieldStatus(acct, d) := Yielded (0)` (`ext.rs:353-369`, `rm.rs:148-165`); then the FC action is appended with deposit 0 (`W:logic.rs:3720-3800`); `d` is written to a **guest register** |
| `promise_yield_create_with_id` | **trie read** `contains YieldIdToDataId(acct, yid)` (`ext.rs:378-382`) — present ⇒ returns `None` (guest sees `u64::MAX`), nothing else; else as above plus **trie writes** `YieldIdToDataId(acct,yid) := d`, `DataIdToYieldId(acct,d) := yid` (`ext.rs:384-397`, `store/utils.rs:263-279`) |
| `promise_yield_resume(d, payload)` | **trie reads** `contains PromiseYieldReceipt(acct, d)`, `contains PromiseYieldStatus(acct, d)` (`ext.rs:407-412`, `store/utils.rs:212-240`); either present ⇒ `data_receipts.push({d, Some(payload), resume: true})` and **trie write** `PromiseYieldStatus := ResumeInitiated (1)`, guest gets 1; else nothing, guest gets 0 (`ext.rs:402-426`) |
| `promise_yield_resume_with_yield_id` | **trie read** `YieldIdToDataId(acct, yid)`; absent ⇒ 0; else as `promise_yield_resume` (`ext.rs:428-440`) |

Within one call, a yield created earlier is found by the resume check through its status write
(the `TrieUpdate` sees its own prospective writes).

### 5.4 From metadata to `Receipt` (`fc.rs:159-217`, success only)

For each `ActionReceiptMetadata` in index order:
`Receipt::V0{predecessor_id: acct, receiver_id: m.receiver_id, receipt_id: default,
receipt: (m.is_promise_yield ? PromiseYieldV2 : ActionV2)(ActionReceiptV2{signer_id:
r.signer_id, signer_public_key: r.signer_public_key, refund_to: m.refund_to, gas_price:
r.gas_price (purchase price), output_data_receivers: m.output_data_receivers, input_data_ids:
m.input_data_ids, actions: m.actions (FunctionCall gas after distribution)})}` (`fc.rs:175-197`).
Always the V2 enums (ReceiptEnum tags 6 / 5, `D2/Types.lean:416-418, 446-447`).
Then for each `DataReceiptMetadata`: `Receipt::V0{predecessor_id: acct, receiver_id: acct,
receipt: (resume ? PromiseResume : Data){data_id, data}}` (`fc.rs:202-217`).

### 5.5 Gas weights (`fc.rs:341-345`, `rm.rs:654-695`)

After the run, for any VM-produced outcome (also an aborted one; not for the early-return no-op
outcomes of §4.1): `unused = fc.gas ⊖ outcome.used_gas` (saturating); `W = Σ weights` (u128);
if `W = 0 ∨ unused = 0` nothing; else for each `(idx, w)` in `gas_weights` order:
`a = ⌊unused · w / W⌋` (u128, cast u64), `action.gas += a` (checked ⇒ `IntegerOverflowError` ⇒
reject), and the **last** entry additionally gets `unused − Σa`; `outcome.used_gas += unused`.
The distributed gas is visible in the new FunctionCall actions (their borsh, hence receipt bytes,
outgoing-receipts root, congestion gas) and in `gas_used` (refunds).

### 5.6 Order of all new receipts of an action receipt

`apply_action_receipt` builds `result.new_receipts` as (`lib.rs:439-480, 1166-1301, 1034-1073`):
1. per action `i` in order, on success: that action's receipts — for a FunctionCall: its action
   receipts (manager order), then its Data/PromiseResume receipts (§5.4); for a Delegate: the inner
   receipt;
2. refunds (non-system predecessor): balance refund (failure, deposit > 0), then gas refund (> 0)
   (`lib.rs:1284-1298`);
3. output data receipts (§6.5), unless the result is `ReceiptIndex`.

Ids are assigned by position in this list (§5.2); instant receipts (PromiseYield; `[DeleteAccount]`
without inputs, `receipt.rs:474-492`) go to the instant queue, the rest to
`forward_or_buffer_receipt`; `receipt_ids` of the outcome lists only the Action / PromiseYield
receipts (Data and PromiseResume omitted) (`lib.rs:1076-1120`). D2's `emitReceipts`
(`D2/Receipts.lean:94-102`) is exactly this and is reused unchanged: `receiptIdFrom parent h k`
(`spec/lean/NearSpec/Primitives.lean:120-121`), instant/forward by `isInstant`, ids of `isAction`
receipts only.

PromiseResume receipts are *not* instant: they leave through the receipt sink (to the own shard),
and come back as incoming receipts of a later chunk (D2 §6.2 handles them).

---

## 6. What changes in `apply_action_receipt` (`lib.rs:776-1156`)

### 6.1 `merge` (`lib.rs:439-493`) with function calls

`assert gas_burnt_for_function_call ≤ gas_burnt ≤ gas_used` (panic ⇒ reject); always add
`gas_burnt`, `gas_burnt_for_function_call` (checked), `gas_used`, `compute`, and **append logs**;
on `Ok(ret)`: if `ret = ReceiptIndex(k)` then `k += |self.new_receipts|` (local → global index,
`lib.rs:461-464`); `self.result = Ok(ret)` — the receipt's result is the **last** action's
return data, so e.g. `[FunctionCall, Transfer]` ends with `ReturnData::None`; append receipts and
proposals; `tokens_burnt += …`, `subsidized_amount += …` (checked). On `Err`: `set_error` clears
receipts, proposals, `tokens_burnt`, `subsidized_amount`; **keeps** gas, `gas_burnt_for_function_call`,
compute, logs (`lib.rs:487-493`).

### 6.2 Storage stake, refunds, commit/rollback

Unchanged from D2 §6.4 steps 4–7: the storage-stake check uses the account as written back by the
call (`fc.rs:224-225` → `lib.rs:891-913`); refunds use `gas_used` on success, `gas_burnt` on
failure (`lib.rs:1186-1198`), `total_prepaid_gas` includes `fc.gas` (D2 `refunds`,
`D2/Receipts.lean:60-90`, already general).

### 6.3 Tokens burnt and the receiver reward (`lib.rs:972-1026`)

`tx_burnt = burn · gas_burnt_outcome − deficit + penalty + create_account_charge + tokens_burnt`
(as D2); **`outcome.tokens_burnt := tx_burnt` here** (`lib.rs:987`). Then:

```
receiver_gas_reward = ⌊gas_burnt_for_function_call · 3 / 10⌋        (lib.rs:990-995; burnt_gas_reward 3/10, core/parameters/res/runtime_configs/parameters.yaml:6-9; unwrap ⇒ panic)
receiver_reward     = burn · receiver_gas_reward                     (AccountCostIncrease, lib.rs:998-1006; checked ⇒ reject)
if receiver_reward > 0:                                              (lib.rs:1008-1021)
    a = get Account(acct)   — from the TrieUpdate *after* commit/rollback
    if a exists: tx_burnt −= receiver_reward; a.amount += receiver_reward (checked ⇒ reject);
                 set Account(acct) := a; commit
stats.tx_burnt += tx_burnt;  stats.subsidized += result.subsidized_amount   (lib.rs:1023-1026)
```

So the reward is paid **also when the receipt failed** (gas and `gas_burnt_for_function_call` survive
`set_error`), it is not paid if the receiver account no longer exists (e.g. a later
`DeleteAccount` in the same receipt), and the **outcome's `tokens_burnt` includes the reward**
while the chunk's `tx_burnt` excludes it.

### 6.4 Chunk-level burnt balance (`rt/mod.rs:386-403`)

`balance_burnt = (tx_burnt + other_burnt + slashed_burnt) − subsidized` (overflow or negative ⇒
`Error::Other` ⇒ reject). D2 computes `tx_burnt + other_burnt` (`D2/RuntimeD2.lean:213`);
`subsidized > 0` is new in D3 (the `one_yocto_on_promise` exemption, `core/parameters/res/runtime_configs/85.yaml:1`).

### 6.5 Output data receivers (`lib.rs:1034-1073`)

If the receipt has `output_data_receivers`:
* `result = Ok(ReceiptIndex(k))`: `new_receipts[k]` (must exist, `expect` ⇒ panic ⇒ reject; must be
  an action/yield receipt, else `unreachable!`) gets `output_data_receivers.extend(parent's
  receivers)` — the data obligation is **forwarded** to the returned promise. This happens after
  `validate_receipt(NewReceipt)` (`lib.rs:870-881`) and is not re-validated. No Data receipts.
* otherwise, one `Data` receipt per receiver `{predecessor: acct, receiver: d.receiver_id,
  data_id: d.data_id, data}` with `data = Some(v)` for `Ok(Value(v))`, `Some([])` for
  `Ok(None)`, `None` for `Err` (`lib.rs:1054-1071`).

### 6.6 Status, outcome, compute (`lib.rs:1122-1155`)

| final `result.result` | `ExecutionStatus` |
|---|---|
| `Ok(ReceiptIndex(k))` | `SuccessReceiptId(sha256(r.receipt_id ‖ u64le(h) ‖ u64le(k)))` |
| `Ok(Value(v))` | `SuccessValue(v)` |
| `Ok(None)` | `SuccessValue([])` |
| `Err(e)` | `Failure(ActionError(e))` |

`ExecutionOutcome{status, logs: result.logs (all actions, incl. a failing one), receipt_ids,
gas_burnt: result.gas_burnt, compute_usage: Some(result.compute_usage), tokens_burnt (§6.3),
executor_id: acct, metadata: V4{profile, contracts}}`. The chunk's `gas_used` sums outcome
`gas_burnt` and the receipt-limit loop sums `compute_usage` (D2 §6.1) — both now include WASM.

---

## 7. Exactly which outcome bytes are hashed

The outcome root is `merklize(outcomes.map(o ⇒ o.to_hashes()))` (`chain/chain/src/types.rs:151-159`;
`merklize` hashes each item with `hash_borsh`, `core/primitives/src/merkle.rs:47-52`), and
`to_hashes() = [id, hash_borsh(PartialExecutionOutcome(o)), sha256(log₁.as_bytes()), …,
sha256(logₙ.as_bytes())]` (`tx.rs:746-752`). Hence the leaf of an outcome with `n` logs is

```
sha256( u32le(2+n) ‖ id ‖ sha256(P) ‖ sha256(log₁) ‖ … ‖ sha256(logₙ) )
P = u32le(|receipt_ids|) ‖ receipt_ids ‖ u64le(gas_burnt) ‖ u128le(tokens_burnt)
    ‖ borsh_string(executor_id) ‖ status
status = 0x01                                    Failure
       | 0x02 ‖ u32le(|v|) ‖ v                   SuccessValue(v)
       | 0x03 ‖ receipt_id (32 B)                SuccessReceiptId
```

(`PartialExecutionOutcome` `tx.rs:571-591`; `PartialExecutionStatus` with explicit discriminants
`tx.rs:593-613`, `Failure(_) ⇒ Failure` drops the payload at `tx.rs:608`.)

**For a failure exactly one byte, `0x01`, enters the hash.** No error kind, no `ActionError.index`,
no `FunctionCallError` variant, no message — in particular **not** the `String` of
`HostError::GuestPanic{panic_msg}`, `ExecutionError`, `LinkError{msg}`, `CompilationError`,
`MethodResolveError`, `WasmTrap` kind, `GasExceeded` vs `GasLimitExceeded` — is hashed; nor are
`compute_usage` (`#[borsh(skip)]`, `tx.rs:637-638`) or `metadata` (profile, contracts). The error
is otherwise unobservable: data receipts carry `None` (§6.5), state is rolled back, refunds depend
only on the failure bit. Error *kinds* matter to `Rel` only through (a) the gas burnt and logs the
abort leaves, and (b) the action-failure vs reject boundary of §4.1. `Rel_D3` may therefore
quotient errors to the failure bit (boundary B10/H6); the difftests still compare exact kinds.

**Logs are hashed byte-exactly**, in emission order, across all actions of the receipt, also on
failure: this includes the `"ABORT: {msg}, filename: \"{f}\" line: {l} col: {c}"` log of the
AssemblyScript `abort` host function (`W:logic.rs:4316-4344`), which is pushed before its
`GuestPanic` error. **Return values are hashed** (`SuccessValue(v)`) only when the FunctionCall is
the receipt's last action (§6.1).

---

## 8. D2 interface extensions (all additive; D2 behaviour unchanged at the defaults)

Lean note: anonymous constructors `⟨…⟩` ignore default values, so the four sites that build these
structures positionally must be updated mechanically (or switched to named fields):
`D2/Actions.lean:399`, `D2/Receipts.lean:118, 164-165`, `RuntimeD1.lean:77, 132, 195`,
`D2/RuntimeD2.lean:21, 63`.

| # | extension | default (= D2) | nearcore line it serves |
|---|---|---|---|
| E1 | `ApplyCtx` (or `Env`) `+ blockTimestamp : Nat`, `+ randomValue : Bytes`, `+ epochHeight : Nat`, `+ validators : List (Bytes × Nat)`; filled in `checkD3` from B2's `BlockHdr.timestamp/.randomValue/.epochId` and the claim's `epochs` | unused by D2 | `fc.rs:258-271`, `ext.rs:326-340`, `rt/mod.rs:275, 321-331` |
| E2 | `Env + codeOf : Bytes → Option Bytes` (value-hash → blob over `w.main.values ++ codes`) and `revealTrie` over the merged list | `fun _ => none`; `codes = []` (D2 requires `w.no_code`) | `pwt.rs:693-696`, `contract.rs:119`, `core/store/src/trie/trie_storage.rs:325-337` |
| E3 | `ActCtx + inputs : List (Option Bytes)` (the received data of `input_data_ids`, in order) — `applyActionReceipt` step 1 already decodes them and discards (`D2/Receipts.lean:109-114`) | `[]` | `lib.rs:796-821` |
| E4 | `ActSt + deploys : List Bytes` (codes deployed in the current receipt, uncommitted) and `RS + deployed : List Bytes` (committed); `actDeploy` appends; `applyActionReceipt` merges on commit, drops on rollback | `[]`; D2 never reads them | `actions.rs:336-339`, `update.rs:222, 227`, `contract.rs:42-69` |
| E5 | `ActSt + ttn : TTN.Acct` and `RS + ttn` — the chunk-scoped trie accounting cache, threaded through every call and **kept on rollback** | `{}`; D2 never reads it | `ext.rs:647-679`, `fc.rs:73`, `Wasm/ChunkStorage.lean:42-77` |
| E6 | `AR + gasFC : Nat` (`gas_burnt_for_function_call`): summed in `actionLoop` always (checked), kept by `AR.fail` | `0` | `lib.rs:448-451, 487-493`, `fc.rs:144-145` |
| E7 | `AR + logs : List Bytes`: appended in `actionLoop` always, kept by `AR.fail` | `[]` | `lib.rs:458`, `fc.rs:152` |
| E8 | `AR + ret : Ret` with `inductive Ret | none | value (v : Bytes) | receiptIdx (k : Nat)`; in `actionLoop` on success `res.ret := shift ar.ret |res.newReceipts|` (only `receiptIdx` shifts); every non-FC action returns `.none` | `.none` | `lib.rs:459-466`, `fc.rs:228` |
| E9 | `AR + subsidized : Nat`: added on success (checked), cleared by `AR.fail`; `RS + subsidized`; `MainOutD2.balanceBurnt := tx + other − subsidized` (negative ⇒ `invalid`) | `0` | `lib.rs:472-475, 492, 1025-1026`, `rt/mod.rs:386-403` |
| E10 | receiver reward in `applyActionReceipt` after `commit/rollback`: `rew = burn · (gasFC·3/10)`; if `rew > 0 ∧ getAcct recv = some a`: `txBurnt −= rew`, `a.amount += rew` (≥ 2¹²⁸ ⇒ invalid), set, commit; outcome `tokensBurnt` unchanged (pre-subtraction) | `gasFC = 0 ⇒ rew = 0` ⇒ D2 path | `lib.rs:987-1024` |
| E11 | output data in `applyActionReceipt`: `res.ok ∧ ret = receiptIdx k ∧ outputs ≠ []` ⇒ `newReceipts[k].outputs ++= a.outputs` (index missing / non-action ⇒ `panicked`), no data receipts; else `data := if ok then (match ret with .value v => some v | _ => some []) else none` | `ret = .none` ⇒ `some []`, as D2 | `lib.rs:1034-1073` |
| E12 | `OStatus + valueBytes (v : Bytes)` (encode `[2] ++ u32 |v| ++ v`) — or generalize `.value` to carry `v`, with D2 passing `[]`; status from `ret`: `.receiptIdx k ⇒ .receipt (receiptIdFrom r.rid h k)` | `.value` = `SuccessValue([])` | `lib.rs:1122-1129`, `tx.rs:597-612` |
| E13 | `OutD1 + logs : List Bytes`; `leaf = sha256 (u32 (2+n) ++ id ++ sha256 partial ++ concat (logs.map sha256))` | `[]` ⇒ the D1 leaf (`RuntimeD1.lean:72`) | `tx.rs:746-752` |
| E14 | `ActionHooks.functionCall` keeps its type; D3's implementation needs only E1–E5 through `ActCtx`/`ActSt` (contract, balance, usage, locked from `st.account`; height from `env.ctx`; action hash from `(c.r.rid, h, c.idx)`; `is_last_action = c.idx + 1 = c.nActs`; outputs from `c.a.outputs`) and returns E6–E9 in `AR`, the new receipts (V2 action/yield receipts then data/resume receipts, §5.4) in `AR.newReceipts`, and the updated account (`amount`, `usage`) in `st.account` on success | `d2Hooks` = `out of domain (e.wasm)` | `fc.rs:31-233` |
| E15 | new `Base` constructors / hooks for `DeployGlobalContract`, `UseGlobalContract`, `DeterministicStateInit` and `RBody` `GlobalContractDistribution` (lifting `w.shape`) | decoded as `out of domain (w.shape)` | D2 §13; `lib.rs:595-630` |

Not needed: `emitReceipts`, `refunds`, `validReceipt`, `processReceipt` (Data / PromiseYield /
PromiseResume), the queues, transactions and the validator update are reused unchanged
(D2 §13). Two D2 invariants that D3 receipts exercise for the first time and that the D2 code
already handles generally: `validate_receipt(NewReceipt)` on VM-created receipts (FunctionCall
`gas > 0` *after* distribution, `refund_to` validity, Data `|data| ≤ max_length_returned_data`,
`max_receipt_size`; D2 §6.6), and ActionV2 / PromiseYieldV2 / PromiseResume encodings
(`D2/Types.lean:415-449`).

---

## 9. The mock action log (`Wasm/Machine.lean`, `Wasm/Host.lean`) vs nearcore receipts

The D3α host functions run against the mock `External` of `runtime/near-vm-runner/src/logic/mocks/mock_external.rs` (`mock_external.rs` below):
`St.actions : Array MAct` (`Machine.lean:260-270, 296`), `St.dataCount`, `St.promises :
Array PromiseV` (`Machine.lean:254-258, 293`), `St.ret : Option (ByteArray ⊕ Nat)`
(`Machine.lean:285`). In the mock **a receipt index is an action-log index**
(`mock_external.rs:236-254`, `Host.lean:268-273`).

### 9.1 What the mock already carries

| `MAct.text` (Host.lean) | carries | nearcore counterpart |
|---|---|---|
| `CR(d₁,…)>acct` + `receiver` (`Host.lean:736-797`) | receiver; dependency receipts (as action-log indices) | `create_action_receipt(deps, acct)` |
| `YC:<did>>acct:<yid or ->` + `yieldCreate = (did, yid?)` (`Host.lean:469-497, 904-925`) | yield receipt, its data id, the user yield id | `create_promise_yield_receipt[_with_id]` |
| `FC@r:<method hex>:<args hex>:<deposit>:<gas>:<weight>` (`Host.lean:416-431`) | every FunctionCall field incl. the weight | `append_action_function_call_weight` |
| `CA@r`, `DC@r:<code>`, `TR@r:<amt>`, `ST@r:<amt>:<pk>`, `AF@r:<pk>:<nonce>`, `AC@r:<pk>:<nonce>:<allowance or ->:<recv>:<names>`, `DK@r:<pk>`, `DA@r:<beneficiary>` (`Host.lean:806-885`) | complete action data (pk as raw borsh bytes; allowance 0 rendered `-` = `None`) | `append_action_*` |
| `RT@r:acct` (`Host.lean:798-805`) | `refund_to` | `set_refund_to` |
| `YR:<did>:<payload>` (`Host.lean:926-940, 1000-1016`) | a resume (data id, payload) | `create_promise_resume_receipt` |
| `St.ret = inl v` / `inr r` | `ReturnData::Value(v)` / `ReceiptIndex` (as action-log index) | `return_data` |
| `St.balance`, `St.storageUsage`, `St.logs`, `St.gas` (burnt, used, compute) | `outcome.balance`, `.storage_usage`, `.logs`, `.burnt_gas`, `.used_gas`, `.compute_usage` | `VMOutcome` (`L:logic.rs:4479-4493`) |

### 9.2 What is missing or differs (RuntimeD3 must supply it)

Guest-visible (must be fixed *inside* the VM run, not post hoc):
1. **Data ids.** Mock `dataId n = sha256(u64le n)` (`Host.lean:408`, `mock_external.rs:205-211`);
   nearcore `sha256(ah ‖ u64le h ‖ u64le n)` (§5.2). The yield data id is written to a guest
   register (`Host.lean:924`). Needs `ah` and `h` in `CallCtx`.
2. **The data-id counter.** The mock increments it only for yields; nearcore also for each
   dependency of `promise_then` / `promise_batch_then` (`ext.rs:347-349`). Interleaving changes
   every later yield's data id.
3. **Yield/resume state.** `promise_yield_resume` returns 1 iff the data id is a yield in *state*
   (`PromiseYieldReceipt` or `PromiseYieldStatus` present, incl. this call's own status writes);
   the mock looks only at its action log and always logs a `YR` entry
   (`Host.lean:936-940`). `promise_yield_create_with_id`'s duplicate check reads
   `YieldIdToDataId` from state (also earlier receipts and chunks); the mock checks the log.
   `promise_yield_resume_with_yield_id` resolves the yield id from state.
4. **`current_contract_code`** returns the account's contract (`W:logic.rs:4366-4398`), the mock
   `0` (`Host.lean:548-549`).
5. **`InvalidMethodName`**: non-UTF-8 method names in FunctionCall / AddKey-with-FC actions fail in
   the real `ReceiptManager` (`rm.rs:381-382, 596-600`); the mock accepts them.
6. **Deterministic state init**: `promise_batch_action_state_init*` returns the *action index within
   the receipt* (`rm.rs:293-308`), the mock returns the action-log index (`Host.lean:458-466`); and
   `set_state_init_data_entry` indexes the receipt's actions (`rm.rs:322-347`). (Global-contract
   family; out of the first D3 rung.)

Not guest-visible (post-processing from a structured log suffices):
7. **Receipt indices.** Convert action-log indices to manager indices: the manager index of a
   `CR`/`YC` entry is the number of `CR`/`YC` entries before it; `PromiseV` deps, `FC@r`/`…@r`
   targets and `St.ret = inr r` must be mapped. (`sir` checks use receivers only, unaffected.)
8. **Output data receivers / input data ids** of `then`-joins: not recorded; derived from `CR(deps)`
   in log order with the data ids of item 1–2 (§5.3).
9. **Gas distribution** (§5.5) is runtime-level (`fc.rs:341-345`): the harness outcome
   (`Wasm/Exec.lean:482-501`) excludes it; FunctionCall `gas` fields and `used_gas` change.
10. **`subsidized_amount`**: the mock skips the deduction for the 1-yocto case
    (`Host.lean:428-429, 495-496`) but does not count it; `St` needs a `subsidized` field (§6.4).
11. **`OTHER` entries** (gas-key actions, global-contract deploy/use, state init) carry no data
    (`Host.lean:440-466, 954-998, 1022-1039`): structured fields are needed for their actions.
12. **Trie writes of the External** (yield status, yield-id mappings) and the success-only
    timeout-queue writes (`fc.rs:156-222`) must go to the D2 overlay, as must contract storage:
    today `TTN.RealStore` keeps its own overlay map (`Wasm/ChunkStorage.lean:45, 61`); RuntimeD3
    must read and write through `D2.Ovl` (prospective/committed, receipt-level commit/rollback).
13. **Representation.** `MAct.text` is a rendering; RuntimeD3 needs a structured log
    (receiver, refund_to, actions as `D2.Act` with exact borsh `raw`, inputs/outputs) or a
    `ReceiptManager` model in `St`. The receipt fields not in the log at all are filled by §5.4
    (predecessor, signer, signer key, gas price).

---

## 10. New domain conditions and hazards (`InD3` deltas)

* `e.wasm` is lifted for `FunctionCall` on accounts with `contract ∈ {None, Local}`; global
  identifiers (and ETH-implicit legacy wallet resolution, §2.1) stay out (`w.shape`) until E15.
* `w.no_code` lifted (§2.2); missing code for an account with a contract ⇒ reject (cold cache).
* WASM-level conditions of the D3 spec (curve host functions out, `unmodeled` = out of domain,
  H1–H14 of `docs/research/near-wasm-boundary.md` §8; H9 `LoadingError`/`WasmUnknownError`, H2/H10
  resource `LinkError`s assumed absent).
* `w.size` (D2 §12) keeps the per-receipt `RecordedStorageExceeded` unreachable: the recorded-size
  delta of a receipt is at most the chunk's recorded size, which `w.size` bounds by 4 000 000
  **[unverified that `recorded_storage_size_upper_bound` ≤ Σ values + 2000·R in the presence of
  contract-storage removals; D2's argument covers it for D2 operations]**.
* The `PromiseYieldIndices` read of every successful call (§4.2.1) and the yield trie reads
  (§5.3) enter the read set; the D2 single-node-drop mutants are the evidence pattern.

### 10.0 Decisions (lead, 2026-10-06)

1. **`Rel_D3` is the cold-cache, cache-independent statement.** The code of every executed
   pre-state contract must come from the witness. A nearcore validator with a warm
   compiled-contract cache may accept witnesses that `Rel_D3` rejects, for example a witness
   carrying no code blobs at all; the corpus judge observed this on every honest witness tried. A
   proof cannot depend on what a particular validator has cached, so `Rel_D3` is the conservative
   statement.
2. **Cache-dependent code verdicts are a decidable D3α domain condition (`e.code_cache`).**

   - **Condition.** A case is out of D3α when both hold:
     - an executed pre-state contract's code blob is absent from the witness;
     - the same code was deployed earlier in the chunk, whether committed or rolled back.

   - **nearcore finding.** For such witnesses, the verdict depends on the validator's
     compiled-contract cache, since `DeployContract` precompiles and a rollback does not evict.
     It also depends on the order in which the preparation pipeline prepared the receipts:
     receipts submitted before the deploy ran were prepared cold. The corpus shows both verdicts.
3. **`G_α`** (`D3.gAlpha` = 2²² · 822,756 ≈ 3.45 Tgas) bounds the chunk's Σ
   `gas_burnt_for_function_call`; above it, the case is `out of domain (e.g_alpha)`.

### 10.0a Precise statements (findings P1–P5 of the independent Python checker, `oracle/tools/README-d3.md`)

* **P1, pre-state contract.** At a `FunctionCall`, the receiver's contract is a *pre-state
  contract* iff its current `Local` code hash equals its `Local` code hash in the chunk's pre-state
  trie, i.e. unchanged since the chunk started.
  - The preparation pipeline reuses a preparation whose `expected_hash` still matches
    (`pipelining.rs:152-300, 351`).
  - `e.code_cache` applies to pre-state contracts only, whether the earlier deploy of the same code
    was committed or rolled back, and to any account.
  - A contract whose hash changed in this chunk is served by the deploy tracker
    (`core/store/src/contract.rs:104-130`).
* **P2, when G_α is evaluated.** After the whole main transition has been applied, including
  `finalize`. It is checked together with `w.size`, before the post-state-root and header
  comparisons.
  - A storage error anywhere in the main transition rejects, even past the crossing.
  - Deciding the condition requires executing the whole chunk.
* **P3, excluded host functions.** The state-init, global-contract and gas-key families and the
  curve functions are out of domain when **called** (`Wasm.realOodHosts`; curve functions are not
  modelled). Importing them is not out of domain. Floats are decided at preparation.
* **P4, ML-DSA keys created by a contract.** `Stake`, `AddKey` and `DeleteKey` actions with an
  ML-DSA-65 key make the case out of domain (`w.shape`) when the new receipt's actions are decoded.
  `PostQuantumSignatures` is enabled at PV 85, so the VM accepts these keys.
* **P5, ETH-implicit accounts.** A `FunctionCall` on an ETH-implicit account with a `Local`
  contract is out of domain. This conservatively covers the legacy-wallet resolution of
  `contract_code.rs:56-76`; the wallet hashes are not enumerated.

### 10.1 As implemented (`NearSpecV3/D3/FunctionCall.lean`, RuntimeD3 rung 1)

* **In domain:** FunctionCall on `None` / `Local` contracts. This covers:
  - every non-curve host function except the state-init, global-contract and gas-key families
    (`oodHosts`; they are D2 `w.shape` families);
  - yields with nearcore's real External: state reads/writes through the overlay, data ids
    `sha256(ah ‖ h ‖ n)` with the then-join counter, and timeouts enqueued on success.
* **Code-cache dependence → out of domain (finding of the D3 corpus code mutants).** The blob of
  the account's *pre-state* contract may be missing from the witness while the same code was
  deployed earlier in the chunk. That deploy may have been committed or rolled back
  (`ActCtx.attempted`, `RS.attempted`). nearcore's verdict then depends on two things:
  - the compiled-contract cache, which `DeployContract` precompiles into and a rollback does not
    undo;
  - the preparation pipeline (receipts submitted before the deploy ran were prepared against a
    cold cache).

  Observed on the corpus: one honest-derived mutant was rejected (pipelined call before the deploy)
  and one accepted (postponed call after a rolled-back deploy). `checkD3` classifies all such cases
  `out of domain (e.wasm-α)`. A missing pre-state blob without such a deploy is nearcore's
  `MissingTrieValue` (reject). A contract set by a deploy in this chunk is served by the deploy
  tracker.
* **Trie-node accounting:** a per-call cache. The chunk-scoped cache (E5) changes only the
  gas-profile split, because `wasm_touching_trie_node = wasm_read_cached_trie_node` in gas and
  compute at PV86.

## 11. Corrections to D2 §13

D2 §13 says the D2 code "already carries the generic parts [D3] needs: input-data reads
(§6.4.1), `ReceiptIndex` handling of output data receivers (§6.4.9, unreachable in D2), the
receiver reward (§6.4.8, 0 in D2)". The **prose** (§6.4) states them, but the **Lean** does not:
`applyActionReceipt` discards the received data (`D2/Receipts.lean:112-113`), always emits data
receipts with `some []`/`none` (`D2/Receipts.lean:157-158`), and has no reward step
(`D2/Receipts.lean:150`, comment only); `OutD1` has no logs and `OStatus.value` no payload
(`RuntimeD1.lean:52-72`). These are E3, E8–E13 above.

## 12. Evidence: three-way full-runtime difftest (nearcore / Lean `checkD3` / Python `spec_check_v3_d3.py`)

The four oracle corpora come from `oracle/v3-d3`, `scripts/gen-d3-corpus.sh`. Each chain has 200 blocks
and 4–6 shards, with D2 and D3 traffic mixed. The D3 traffic includes:
* `d3rich`, `ttn2`, `d3tiny` and `d3hostx`;
* promise DAGs, callbacks, yields, deploy-and-call and Delegate-wrapped calls, under tight gas;
* the P3–P5 probes.

nearcore's verdict is the cold-cache validator's (§10.0). Lean is `nearspec-v3-check-d3`; Python is
`oracle/tools/spec_check_v3_d3.py`, written independently from the nearcore source, the prose and the
clean-room VM. The driver is `oracle/v3-d3/tools/difftest_d3.py --python`.

| corpus | chains | cases | Lean vs nearcore | Python vs nearcore | Lean vs Python (verdicts incl. out of domain) |
|---|---|---|---|---|---|
| seed 7 | 8 | 33,248 | 0 | 0 | 0 |
| seed 8 | 12 | 49,490 | 0 | 0 | 0 |
| seed 9 | 4 | 15,995 | 0 | 0 | 0 |
| seed 10, `min_gas_price` = 10⁸ | 4 | 16,551 | 0 | 0 | 0 |
| **total** | | **115,284** | **0** | **0** | **0** |

Over the 115,284 cases, both checkers agree with each other on every case:

| | count |
|---|---|
| both accept | 41,131 |
| both reject | 71,605 |
| both out of domain | 2,548 |

The out-of-domain verdicts of both checkers coincide with the oracle classifier's marks on
`e.code_cache` and `e.g_alpha`. No checker accepts a case the oracle puts above G_α.

The seed-10 corpus (nonzero gas price) exercises the receiver reward, `tx_burnt` and the outcome
`tokens_burnt`:
* receiver reward > 0 in 1,826 in-domain cases;
* receipt `tokens_burnt` > 0 in 2,510.

The P3–P5 probes give, for example, the following cases in the seed-7 corpus:

| probe | case | verdict |
|---|---|---|
| imports a curve / state-init function but does not call it | `d3/00-h10027-s2` | in domain, accepted |
| calls `ecrecover` | `ood/00-h10006-s2` | out of domain |
| calls `promise_batch_action_state_init` | `ood/00-h10035-s2` | out of domain |
| ML-DSA AddKey | `ood/00-h10007-s2` | out of domain (`w.shape`) |
| ETH-implicit receiver with a Local contract | `ood/00-h10010-s3` | out of domain |

**The first run had 7 Lean-only disagreements**, fixed in `Wasm/Host.lean` and `D3/FunctionCall.lean`:
* **Missing method-name check.** A `promise_yield_create` with a non-UTF-8 method name is
  nearcore's `InvalidMethodName` (`receipt_manager.rs:381-382`), but the yield paths lacked the
  real-External check.
* **Wrong verdict for unmodeled shapes.** An action-log shape the spec does not model was
  reported as a reject. Every `unmodeled` hook path is now out of domain.

**D1/D2 regressions after the additive D2/D1 edits:**
* The full D2 corpus (67,384 cases, three-way) is identical to `spec/difftest-report-v3-d2.json` in
  `cases`, `summary`, `stats`, `disagreements`, the subset checks and the families.
* The full D1 corpus (53,048 cases, three-way, `--lean-d0`) is identical to
  `spec/difftest-report-v3-d1.json` in every field except timings and path strings.
