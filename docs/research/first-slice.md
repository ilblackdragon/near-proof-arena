# First challenge slice: local Transfer action receipts → shard trie root

**Pin.** nearcore tag `2.13.4`, commit `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`.
Protocol version **86** (`STABLE_PROTOCOL_VERSION`, `core/primitives-core/src/version.rs:628`).
Mainnet runtime parameters come from `RuntimeConfigStore::new(None).get_config(86)`.
For the wider boundary see `nearcore-boundary.md` in this directory.

**Proposed name:** `near/pv86/receipt-transfer-batch/v0`. The statement is a
*subset* of NEAR's chunk transition. It is not "NEAR state transition".

**Status of verification.** All encodings, constants and example hashes below
come from two sources:

1. The real `node_runtime::Runtime::apply` (pinned crates), run in-process on
   an in-memory trie (§7).
2. An independent ~150-line Python re-implementation written only from this
   spec (`/data/illia/nearproof-deps/oracle-probe/spec_check.py`).

The two agree byte for byte on the pre-root, the post-root and the outcome
roots of both scenarios.

---

## 1. Statement

Public inputs:

* `pre_root : [u8;32]`. State root of the shard before the batch.
* `block_height : u64`, `block_gas_price : u128`. Block context, from `ApplyState`.
* `receipts : [Receipt]`. An ordered list, borsh-encoded exactly as in nearcore (§3.3).
* Pinned constants for PV86 (§2).

Witness:

* A `PartialState`: the set of `RawTrieNodeWithSize` serializations on the
  root→leaf paths of every touched `TrieKey::Account{receiver}`, plus the
  72-byte account values. This is exactly what nearcore's recorder captures
  (§6, example has 8 items).

Public outputs (claims):

* `post_root : [u8;32]`. Root of the trie after applying all receipts in order.
* `outcomes : [ExecutionOutcomeWithId]` (or just their `to_hashes()`), and
  `outcome_root = merklize([o.to_hashes() for o in outcomes])`.
* `refund_receipts : [Receipt]` (the outgoing gas-refund receipts, only when
  `block_gas_price < receipt.gas_price`).
* `tokens_burnt_total : u128` (the `stats.balance.tx_burnt_amount` contribution).

Relation: `(pre_root, receipts, ctx) ↦ (post_root, outcomes, refund_receipts)`
equals what `Runtime::apply` computes for the receipt-processing part of the
chunk, under the domain restrictions in §4.

### 1.1 How `post_root` relates to the real chunk post-state root (honesty note)

`Runtime::apply` **always** also writes `TrieKey::BandwidthSchedulerState`
(key byte `0x0f`), even for an empty chunk (`runtime/runtime/src/lib.rs:1765-1771`,
`runtime/runtime/src/bandwidth_scheduler/mod.rs:127-137`). So the root that
nearcore commits (`ChunkExtra.state_root`, and the next chunk's
`prev_state_root`) is **not** our `post_root`. The probe checked this
decomposition. It prints `DECOMPOSITION OK` in both scenarios:

```
full_apply_root = root( pre_kv  ⊕  {Account(receiver_i) ↦ new_value_i}  ⊕  {0x0f ↦ bw_state'} )
slice post_root = root( pre_kv  ⊕  {Account(receiver_i) ↦ new_value_i} )
```

The two key sets are disjoint, and the trie root is a canonical function of
the final key→value map (`core/store/src/trie/update.rs:242-262`), so the
slice is a faithful *projection*. It is not a root that ever appears on
chain. Adding the single-shard bandwidth-scheduler write is the natural v1
extension (§8).

## 2. Pinned constants (PV86, mainnet parameters)

| constant | value | source |
|---|---|---|
| `new_action_receipt` exec gas (= compute) | 108_059_500_000 | `core/parameters/res/runtime_configs/parameters.yaml:43-47` |
| `transfer` exec gas (= compute), named receiver | 115_123_062_500 | `parameters.yaml:88-92`, `core/parameters/src/cost.rs:722-748` |
| **G** = gas burnt per Transfer receipt | **223_182_562_500** | sum of the two above (oracle confirms) |
| `storage_amount_per_byte` | 10^19 yN | `parameters.yaml:35` |
| zero-balance-account storage limit | 770 bytes | `runtime/runtime/src/verifier.rs:25` |
| `min_gas_purchase_price` | 10^9 yN/gas (since PV85) | `core/parameters/res/runtime_configs/85.yaml` |
| `gas_refund_penalty`, `min_gas_refund_penalty` | 0/100, 0 | `parameters.yaml:14-18` |
| `burnt_gas_reward` | 3/10 (irrelevant: no function call) | `parameters.yaml:6-9` |
| trie costs `node_cost, byte_of_key, byte_of_value` | 50, 2, 1 | `core/store/src/trie/mod.rs:158` |
| hash | SHA-256 | `core/primitives-core/src/hash.rs:35-50` |

## 3. Byte-level encodings

### 3.1 Trie key for an account

`TrieKey::Account{account_id}` → `0x00 ‖ utf8(account_id)`. There is no
length prefix and no borsh (`core/primitives/src/trie_key.rs:21-24, 457-460`).
Example: `alice.near` → `00616c6963652e6e656172`.

### 3.2 Account value (AccountV1, the only variant in the slice domain)

`Account::new(.., AccountContract::None|Local, ..)` produces `Account::V1`
(`core/primitives-core/src/account.rs:163-180`). V1 borsh serializes as the
bare struct, with **no enum tag** (`account.rs:437-446`):

```
amount        u128 LE  (16)
locked        u128 LE  (16)
code_hash     [u8;32]  (32)   -- all zeros = no contract
storage_usage u64 LE   (8)
                      = 72 bytes
```

V2 (global contracts) is `u128::MAX ‖ 0x00 ‖ borsh(AccountV2)` (`account.rs:406-447`).
V2 is **excluded**. Deserialization tells the two apart by the first u128
(`account.rs:410-433`).

Example (bob.near, 50 NEAR, storage_usage 182):
`000000726906646ee95b2900000000 00 | 00×16 | 00×32 | b600000000000000`.

`storage_usage = 182` matches one account plus one full-access ed25519 key:
`100 + (33 + 9 + 40)`. The probe uses it, but any value satisfying §4 works.

### 3.3 Receipt (input)

`Receipt` borsh is the bare `ReceiptV0`, untagged (`core/primitives/src/receipt.rs:221-233`):

```
predecessor_id   string (u32 LE len ‖ bytes)
receiver_id      string
receipt_id       [u8;32]
receipt          ReceiptEnum: tag u8 = 0 (Action)  (receipt.rs:567-575)
  signer_id            string
  signer_public_key    PublicKey: u8 key type (0=ED25519) ‖ 32 bytes
  gas_price            u128 LE
  output_data_receivers Vec (u32 len = 0)
  input_data_ids        Vec (u32 len = 0)
  actions               Vec (u32 len = 1) ‖ Action tag u8 = 3 (Transfer)  (action/mod.rs:349-370) ‖ deposit u128 LE
```

Example r1 (alice → bob, 3 NEAR, gas_price 1e9):
```
0a000000 616c6963652e6e656172            predecessor "alice.near"
08000000 626f622e6e656172                receiver "bob.near"
82f3e9c6…79e57828                        receipt_id (= sha256("r1") in the probe)
00                                       ReceiptEnum::Action
0a000000 616c6963652e6e656172            signer_id
00 4da7e0f4…16a61dc1                     ed25519 pk
00ca9a3b000000000000000000000000         gas_price = 1_000_000_000
00000000 00000000                        no output receivers, no input data
01000000 03 000000e3c8666c53467b0200000000 00   [Transfer{deposit = 3·10^24}]
```

Transactions produce exactly this `V0 + ReceiptEnum::Action` shape
(`Receipt::from_tx`, `receipt.rs:344-365`). The `ActionV2` variant (tag 5) is
excluded.

### 3.4 Trie nodes and root

The rules below are from `core/store/src/trie/raw_node.rs`,
`core/store/src/trie/nibble_slice.rs` and `core/store/src/trie/ops/interface.rs`:

* Key → nibbles, high nibble first.
* Node = `borsh(RawTrieNodeWithSize{node, memory_usage: u64})` and
  `hash = sha256(node bytes)` (`raw_node.rs:10-19`):
  * `Leaf = 0x00 ‖ u32 len ‖ hp(key_rest, leaf=true) ‖ ValueRef`
  * `BranchNoValue = 0x01 ‖ u16 bitmap ‖ child hashes (ascending index)`
  * `BranchWithValue = 0x02 ‖ ValueRef ‖ u16 bitmap ‖ child hashes`
  * `Extension = 0x03 ‖ u32 len ‖ hp(segment, leaf=false) ‖ child hash`
  * `ValueRef = u32 LE len ‖ sha256(value)` (`core/primitives/src/state.rs:82-87`). Values are never inlined.
* Hex-prefix `hp(nibs, leaf)`: first byte is `(odd ? 0x10|nibs[0] : 0x00) | (leaf ? 0x20 : 0)`,
  followed by the remaining nibbles packed two per byte (`nibble_slice.rs:129-158`).
* `memory_usage`:
  * leaf: `50 + 2·|hp| + (|value| + 50)`
  * extension: `50 + 2·|hp| + child`
  * branch: `50 + [value? |value|+50] + Σ children`
* Empty trie root = 32 zero bytes. Otherwise root = hash of the root node.
* The structure is the canonical compressed Patricia trie of the key set. The
  Python re-implementation builds it recursively: one item gives a leaf; a
  common prefix gives an extension; otherwise a branch.

**Key simplification for the slice:** a Transfer never inserts or deletes
keys, and the Account value length stays 72 bytes. So the trie *shape* and
every `memory_usage` are unchanged. Only node hashes along the touched paths
change. A Lean model needs "update value at an existing leaf and rehash the
path", not general insert/delete.

### 3.5 Outcome and outcome hashing

`ExecutionOutcomeWithId::to_hashes() = [id, sha256(borsh(PartialExecutionOutcome)), sha256(log_i)…]`
(`core/primitives/src/transaction.rs:746-752`), with
`PartialExecutionOutcome = {receipt_ids: Vec<[u8;32]>, gas_burnt: u64, tokens_burnt: u128, executor_id: string, status}`
(`transaction.rs:573-602`). Status here is `SuccessValue(vec![])`, encoded as
`0x02 ‖ 00000000`. `compute_usage` and `metadata` (ExecutionMetadata V4 with
a profile and `contracts: [None]`) are **not** hashed.

`outcome_root = merklize(list of to_hashes())` (`chain/chain/src/types.rs:151-163`):

* Each leaf is `sha256(u32 count ‖ hashes…)`.
* Inner nodes are `sha256(left ‖ right)`.
* An odd last node is promoted unchanged.
* One leaf gives root = leaf. Empty gives zeros.

(`core/primitives/src/merkle.rs:42-110`)

## 4. Domain restrictions (what makes this an honest subset)

For every receipt `r` in the list:

1. `r = Receipt::V0{ receipt: ReceiptEnum::Action(ActionReceipt{..}) }` with
   `actions = [Transfer{deposit}]` (exactly one action),
   `input_data_ids = []` and `output_data_receivers = []`.
2. `r.predecessor_id ≠ "system"`. Refund receipts take a different path:
   no gas burnt, allowance and gas-key refund (`lib.rs:924-932, 972, 2898-2919`).
3. `r.receiver_id` is a valid AccountId of type **NamedAccount**: not 64-hex
   (NEAR-implicit), not `0x`+40 hex (ETH-implicit) and not `0s`+40 hex
   (deterministic). Otherwise the exec fee changes (`cost.rs:722-748`; rules in
   near-account-id 2.0.0 `validation.rs:96-120`).
4. `Account(r.receiver_id)` **exists** at the time `r` is processed and is
   encoded as AccountV1 (72 bytes). If it is missing, the transfer fails with
   `AccountDoesNotExist` and a deposit refund is issued
   (`runtime/runtime/src/actions.rs:856-863, 880-899`).
5. `amount + deposit < 2^128`. Overflow is a `StorageInconsistentState` error
   that aborts the whole `apply` (`actions.rs:148-153`).
6. Storage stake holds after the credit:
   `amount' + locked ≥ 10^19 · storage_usage` **or** `storage_usage ≤ 770`
   (`verifier.rs:48-90`). Otherwise the result is `LackBalanceForState`
   failure, rollback and refund (`lib.rs:886-910`). Pre-states that already
   satisfy this keep satisfying it after a credit.
7. The receipt passes `validate_receipt(.., ExistingReceipt)` (`verifier.rs:540ff`).
   Otherwise the chunk is invalid.
8. Receipt ids are pairwise distinct.

For the batch and context:

9. Total compute `N·G` stays below the chunk `gas_limit`, and the storage-proof
   soft limit (4_000_000 bytes since PV72) is not hit. Otherwise later receipts
   are pushed to the delayed queue (`lib.rs:2563-2585`). (For example
   gas_limit = 1000 Tgas allows N ≤ 4480.)
10. No delayed, buffered or yielded receipts are pending, and there are no
    transactions or validator updates. Those run before or around incoming
    receipts and touch other keys (`lib.rs:1750-1803, 2658-2700`).
11. `current_protocol_version = 86`.

Scenario tiers:

* **Tier A** (`block_gas_price ≥ r.gas_price` for all r): no outgoing receipts.
  `outcome.receipt_ids = []` and `tokens_burnt = G · r.gas_price`. The burn
  price is `min(purchase, block)` (`lib.rs:913-922`).
* **Tier B** (`block_gas_price < r.gas_price`, the common mainnet case after
  PV85, because receipts buy gas at ≥ 1e9; whether mainnet block gas price is
  currently below 1e9 is **[unverified]**): one gas-refund receipt per input
  receipt, and `tokens_burnt = G · block_gas_price`.

## 5. Exact semantics (per receipt, in list order)

Let `a = Account(r.receiver_id)` read from the current state,
`p_r = r.gas_price`, `p_b = block_gas_price`, and `p = min(p_r, p_b)`.

The state change, from `apply_action_receipt` (`lib.rs:776-1156`) →
`apply_action` (`lib.rs:523-773`) → `action_transfer_or_implicit_account_creation`
(`lib.rs:2887-2935`) → `action_transfer` (`actions.rs:148-153`):

```
a.amount := a.amount + deposit          -- locked, code_hash, storage_usage unchanged
state[0x00‖receiver] := borsh(a)       -- set_account after the storage-stake check (lib.rs:887-893)
```

The sender's (predecessor's) account is **not touched**. The deposit and the
gas were already debited at tx→receipt conversion, which is outside the slice.

Gas and refund (`lib.rs:830-836, 912-1014`, `refund_unspent_gas_and_deposits`
`lib.rs:1166-1301`):

* `gas_used = gas_burnt = G`, `prepaid = G` (for Transfer `total_prepaid_gas`
  and `total_prepaid_send_fees` are 0), so `gross_gas_refund = 0` and
  `penalty = 0` (`cost.rs:683-693`).
* `price_surplus = (p_r − p)·G`, which is non-zero only in Tier B.
  `price_deficit = 0` always, because `p ≤ p_r`.
* Tier B emits `Receipt::new_gas_refund(signer_id, (p_r − p_b)·G, signer_public_key)`
  (`receipt.rs:519-537`). It has predecessor `"system"`, gas_price 0 and
  actions `[Transfer]`. Its id is `sha256(r.receipt_id ‖ block_height_le64 ‖ 0_le64)`
  (`lib.rs:1081`, `core/primitives/src/utils.rs:278-284, 328-335`). It goes to
  `outgoing_receipts`, even for the same shard.

The outcome is
`{id: r.receipt_id, logs: [], receipt_ids: [refund_id?], gas_burnt: G, compute_usage: Some(G), tokens_burnt: G·p, executor_id: r.receiver_id, status: SuccessValue([]), metadata: V4{…, contracts:[None]}}`
(`lib.rs:1117-1155`). The stats change is `tx_burnt_amount += G·p`.

## 6. Worked example (real values from the oracle; reproduced in Python)

Pre-state KV (6 entries: 3 accounts plus 3 full-access keys, so the trie has
real branching):

```
00 alice.near  -> 100 NEAR, locked 0, code 0, su 182
00 bob.near    ->  50 NEAR
00 carol.near  ->   7 NEAR
02 <acct> 02 00 <ed25519 pk> -> 000000000000000001 (AccessKey{nonce 0, FullAccess})   ×3
```

`PRE_ROOT = 6c4793e8635848320ad809bbb6734cbf54530d3766fa954ea919413eabbf6fcb`

Receipts:

* r1 = alice→bob 3 NEAR, id `82f3e9c6…79e57828`
* r2 = bob→carol 1.5 NEAR, id `db77fd01…57fd17e4`

Both have `p_r = 1e9` and block height 10.

`SLICE POST_ROOT = 28ff3f4acacc0ce6cab564899e1736e885eed9739caabf6b77268455867f39c3`.
alice is unchanged, bob = 53 NEAR, carol = 8.5 NEAR.

`FULL Runtime::apply root = 1420be412762e74b9ffa60aead6a770a6a220dab5415ad6243551a930198953d`
(adds key `0f` = bandwidth scheduler state).

| | Tier A (p_b = 1e9) | Tier B (p_b = 1e8) |
|---|---|---|
| per-receipt `tokens_burnt` | 223_182_562_500_000_000_000 | 22_318_256_250_000_000_000 |
| refund receipts | none | 2 × Transfer 200_864_306_250_000_000_000 to signer |
| outcome leaf hash r1 / r2 | `a6e6dc57…1fbb64fe` / `84064c3a…4066fa13` | `38cc3bc0…e932704d` / `d4c05099…928841b9` |
| `outcome_root` | `92f0cd9e2326f2495ff07a56620770dcdc46b9aaf1eb2f00ce6ce786b8d0a127` | `f904e4c1c8a0fd160b4bba9b700cc175837ccfa3167a3f731e3976c203b8ca02` |
| `post_root` | same `28ff3f4a…` | same `28ff3f4a…` |

Slice witness: 8 trie values, as recorded by nearcore's `TrieRecorder`, with
the pre-state annotated. A trie rebuilt from the witness alone,
`Trie::from_recorded_storage`, reproduces `post_root`.

```
6c4793e8… (root)  03 01000000 10 | 1f217e85… | b905000000000000            Extension hp=[0] (odd, nibble 0), mem 1465
1f217e85…         01 0500 | 3e52ba52… 437eb6c0… | 8505000000000000          Branch children {0 (accounts), 2 (access keys)}
3e52ba52…         03 01000000 16 | f55c3380… | a202000000000000            Extension nibble 6 (all account ids start 0x6…)
f55c3380…         01 0e00 | 3a8fde97…(a) 34b183a7…(b) 6b88e442…(c) | 6e02…  Branch children {1,2,3}
34b183a7… (bob)   00 08000000 20 6f622e6e656172 | 48000000 87f4649d… | bc00000000000000   Leaf, mem 50+2·8+122 = 188
6b88e442… (carol) 00 0a000000 20 61726f6c2e6e656172 | 48000000 2b4bdbcd… | c000000000000000
+ the two 72-byte account values (bob, carol)
```

## 7. Executable oracle: feasible, done

* Project: `/data/illia/nearproof-deps/oracle-probe`.
  * `Cargo.toml` has path dependencies into the pinned checkout: `node-runtime`,
    `near-store`, `near-primitives[test_utils]`, `near-primitives-core`,
    `near-parameters`, `near-crypto`, `near-vm-runner`. It has its own empty
    `[workspace]`, the nearcore `[patch.crates-io]` protobuf entries, and
    nearcore's `Cargo.lock` and `rust-toolchain.toml` copied in.
  * After resolution all 520 third-party and nearcore package versions are **identical** to
    nearcore's lock.
* Code: `src/main.rs` (≈260 lines). It does the following:
  * Builds a `TestTriesBuilder` in-memory `ShardTries` with
    `ShardLayout::single_shard` and fills it via `set_account`/`set_access_key`.
  * Uses the real `RuntimeConfigStore::new(None).get_config(86)`.
  * Builds a full `ApplyState`.
  * Calls **`Runtime::apply`** with a recording trie,
    `MockEpochInfoProvider` and empty txs.
  * Prints roots, outcomes (borsh plus `to_hashes`), `outcome_root`, the
    state changes, the witness nodes, and the full KV dumps.
  * Re-derives the slice root, checks it from the witness alone, and asserts
    the bandwidth-state decomposition.
* Build: `cargo build` (dev profile, opt-level 1) took **2m43s wall** on 32
  cores. The target dir was cold; the cargo registry and the protobuf git
  dependency were warm or fetched in that run. `target/` is 7.3 GB.
  Incremental rebuild is about 3 s. A run is about 4 ms, with `apply` under 1 ms.
* Independent check: `python3 spec_check.py run.log` re-implements the trie,
  the Account encoding, the transfer semantics, outcome hashing and merklize
  from this document. It asserts equality for pre_root, post_root and both
  outcome roots, and prints `ALL CHECKS PASSED`.
* How to run:
  `cd /data/illia/nearproof-deps/oracle-probe && cargo run -q > run.log && python3 spec_check.py run.log`.
* Caveats:
  * `MockEpochInfoProvider` reports chain_id `localnet` and no validators.
    This is irrelevant to Transfer but matters for later slices.
  * The probe uses the disk-trie path (`ShardTries`, no memtrie and no flat
    storage). Production validators use memtries. The roots are identical by
    construction, but we did not run the memtrie path. **[not exercised]**
* Generalizing it into a challenge generator means parameterizing accounts,
  receipts and gas prices (for example from a JSON spec). The oracle can be
  the *full* `Runtime::apply`, reporting both `full_apply_root` and the slice
  projection.

## 8. Explicit exclusions (v0)

Not modeled, and the challenge must not claim them:

* Transactions: signature verification (ed25519, secp256k1, ML-DSA), nonce and
  access-key checks, `verify_and_charge_tx_ephemeral`, tx→receipt conversion
  and the debit of the sender, send fees, `tx_root`.
* Every action other than Transfer, and multi-action receipts. This includes
  function calls and WASM/near-vm-runner, host functions, and gas metering
  inside contracts.
* Implicit and deterministic account creation via Transfer, ETH-implicit
  receivers, `account_creation_charge`.
* Failure paths: nonexistent receiver, storage-stake failure, overflow,
  rollback, deposit refunds.
* Refund receipts as *inputs* (predecessor `system`), gas-key and allowance refunds.
* Data receipts, postponed receipts, promise yield and resume, global contract
  distribution, instant receipts.
* Delayed receipt queue, compute and gas limit overflow into the queue,
  storage-proof size limits, congestion control (buffering, `CongestionInfo`),
  **bandwidth scheduler state write** (§1.1), bandwidth requests.
* Cross-shard routing, shard layout and resharding, `outgoing_receipts_root`.
  Refunds are produced as outputs, but their per-shard merklization is not part of v0.
* Validator account updates, rewards, stake proposals, epoch logic.
* AccountV2 (global contracts), `ReceiptEnum::ActionV2` / `refund_to`.
* Chunk header assembly, `ChunkExtra`, `prev_balance_burnt` aggregation
  (other_burnt, slashed, subsidized), and `gas_used`.
* Protocol versions other than 86 and testnet parameters.

## 9. Suggested next slices (in order of formalization cost)

1. **v1:** add the single-shard `BandwidthSchedulerState` write, so the
   committed root equals the real `Runtime::apply` root for a receipts-only
   chunk. This needs the borsh layout of `BandwidthSchedulerStateV1` and the
   scheduler's allowance arithmetic for one link. **[not yet derived]** The
   observed value bytes are in `run.log` (`0f` → `0001000000…1a`).
2. Failure path: nonexistent receiver or storage-stake failure, giving rollback
   plus a deposit-refund receipt.
3. Refund receipts as inputs (predecessor `system`). These touch `AccessKey`
   (allowance), which requires trie insert/delete-free updates to a second key
   type.
4. Implicit account creation via Transfer. This brings trie inserts,
   `storage_usage` computation and `account_creation_charge`.
5. Tx→receipt conversion (signature as an external-trust predicate first).
