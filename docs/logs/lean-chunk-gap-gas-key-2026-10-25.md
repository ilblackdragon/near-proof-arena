# Gas-key promise hosts: reachability, semantics and the additive gate extension

Lane: **gas-key** (`e.wasm-α: unmodeled host function promise_batch_action_add_gas_key_with_full_access`, 73 cases).
Branch `work/gap-gas-key` (worktree `/data/illia/nearproof-wt/gap-gas-key`), base `c96375ae9`.
Pinned validator: nearcore 2.13.4, commit `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, PV 86,
source at `/data/illia/nearproof-deps/nearcore`.
Corpora: `/data/illia/nearproof-deps/corpora/d3c7`–`d3c10`, gap set 3,138 cases
(`meta.json: nearcore == "ok" ∧ expected_rel_d3 == false`, `/tmp/opencode/ood-valid2.txt`).

Every number below was recomputed in this session from the built binaries on the actual
`claim.bin`/`witness.bin` of each case. Nothing is extrapolated.

---

## 1. Reachability and exact semantics in the pinned validator

All three hosts are reachable at PV86 and are gated by protocol feature `GasKeys`
(`core/primitives-core/src/version.rs:343`, enabled for PV 86 in the `enabled()` match at
`version.rs:562`). The imports are declared unconditionally in
`runtime/near-vm-runner/src/imports.rs`; the feature only governs *action validity*, not import
linking. `mock_external.rs:520-522` reports `post_quantum_keys_enabled() = true` under the mock,
and `runtime/runtime/src/ext.rs:620-622` reports
`ProtocolFeature::PostQuantumSignatures.enabled(protocol_version)` for the trie-backed runtime.

### 1.1 `promise_batch_action_transfer_to_gas_key` (`logic/logic.rs:2990-3037`)

Order: `pay_base(base)`; `is_view()` → `ProhibitedInView`; `get_public_key(ptr,len)` (memory/register
read + borsh decode, **error deferred**); `pk_len = decode().as_ref().map_or(0, |pk| pk.len())`;
`get_u128(amount_ptr)`; `promise_idx_to_receipt_idx_with_sir`; `get_receipt_receiver`;
`gas_key_transfer_send_fee(sir, pk_len)` and `gas_key_transfer_exec_fee(receiver_id.len(), pk_len)`;
two `pay_action_accumulated` calls (`gas_key_transfer_base`, then `gas_key_byte`);
`deduct_balance(amount)`; `append_action_transfer_to_gas_key(receipt_idx, public_key_res?, amount)`.
The decode error surfaces only at the final `public_key_res?`, i.e. **after** the balance deduction.

### 1.2 `promise_batch_action_add_gas_key_with_full_access` (`logic/logic.rs:3056-3090`)

Order: `pay_base(base)`; view check; `get_public_key`; `pk_len`; **`num_nonces = u16::try_from(...)`
→ `IntegerOverflow` when the argument exceeds 65535**; `promise_idx_to_receipt_idx_with_sir`;
`pay_action_base(ActionCosts::add_full_access_key, sir)`; `get_receipt_receiver`;
`gas_key_add_key_send_fee(sir)`; `gas_key_add_key_exec_fee(receiver_id.len(), pk_len, num_nonces)`;
`pay_gas_key_add_key_fees`; `append_action_add_gas_key_with_full_access(receipt_idx,
public_key_res?, num_nonces)`.

### 1.3 `promise_batch_action_add_gas_key_with_function_call` (`logic/logic.rs:3115-3152`)

Order: `pay_base(base)`; view check; `get_public_key`; `pk_len`; `u16::try_from(num_nonces)`;
`get_u128(allowance_ptr)` then `allowance = if > 0 { Some } else { None }`;
`read_and_parse_account_id(receiver_id_ptr, receiver_id_len)`;
`get_memory_or_register(method_names_ptr, method_names_len)`; `split_method_names`;
`promise_idx_to_receipt_idx_with_sir`;
`num_bytes = null_terminated_method_names_len(&method_names)` (= Σ len+1);
`pay_action_base(add_function_call_key_base, sir)`;
`pay_action_per_byte(add_function_call_key_byte, num_bytes, sir)`;
`get_receipt_receiver`; send/exec gas-key fees; `pay_gas_key_add_key_fees`; append.

### 1.4 Fee structure (`core/parameters/src/cost.rs:786-880`, `logic/gas_counter.rs:356-372`)

* `GasKeyTransferFee.base = fee(gas_key_transfer_base)`, `.per_byte = fee(gas_key_byte) * public_key_len`
  for **send**, and `* (access_key_key_len(account_id_len, public_key_len) + min_gas_key_borsh_len())`
  for **exec** (`cost.rs:794-825`).
* `GasKeyAddFee.base = fee(gas_key_nonce_write_base).exec_fee() * num_nonces`;
  `.per_byte = fee(gas_key_byte).exec_fee() * (access_key_key_len + size_of::<NonceIndex>() + NONCE_VALUE_LEN) * num_nonces`
  (`cost.rs:857-880`); send part = `fee(gas_key_byte).send_fee(sir) * GasKeyInfo::borsh_len()` (`cost.rs:844-852`).
* `pay_gas_key_add_key_fees` pays `(burn = ZERO, use = exec_fee.base.gas)` under
  `gas_key_nonce_write_base`, then `(burn = send_fee, use = send_fee.gas + exec_fee.per_byte.gas)`
  under `gas_key_byte`.
* Constants: `access_key_key_len = COLUMN_PREFIX_LEN(1) + account_id_len + ACCESS_KEY_SEPARATOR_LEN(1)
  + public_key_len` (`trie_key.rs:13-15`); `GasKeyInfo::borsh_len() = 16 + 2 = 18`
  (`account.rs:556-558`); `AccessKey::min_gas_key_borsh_len() = 8 + 1 + 16 + 2 = 27`
  (`account.rs:485-486`); `NONCE_VALUE_LEN = size_of::<Nonce>() = 8` (`account.rs:481`);
  `size_of::<NonceIndex>() = 2`.

### 1.5 Appended action bytes

* `Action::TransferToGasKey` = discriminant **12** (`action/mod.rs:366`), body
  `TransferToGasKeyAction { public_key, deposit }` (`action/mod.rs:304-309`) →
  `[12] ‖ pk.borsh ‖ u128 deposit`.
* `Action::AddKey` = discriminant **5** (`action/mod.rs:362` region), body
  `AddKeyAction { public_key, access_key }` (`action/mod.rs:37-42`) →
  `[5] ‖ pk.borsh ‖ access_key.borsh`.
  * full access: `AccessKey::gas_key_full_access(n)` = `nonce 0 ‖ permission` where permission is
    `GasKeyFullAccess(GasKeyInfo { balance: 0, num_nonces: n })` → `[3] ‖ u128 0 ‖ u16 n`
    (`account.rs:493-500`, `575-586`).
  * function call: `GasKeyFunctionCall(GasKeyInfo { balance: 0, num_nonces: n }, FunctionCallPermission)`
    → `[2] ‖ u128 0 ‖ u16 n ‖ [0] ‖ borshString receiver ‖ u32 nMethods ‖ …`
    (`account.rs:502-513`); the host normalises `allowance == 0` to `None` before appending
    (`logic.rs:3137-3138`).

### 1.6 Receipt-level validation the appended actions must pass

`validate_receipt(…, ValidateReceiptMode::NewReceipt)` runs on every emitted receipt
(`runtime/runtime/src/lib.rs:871-883`); for an `AddKey` action with a gas-key permission
`validate_add_key_action` (`action_validation.rs:301-336`) requires:
`GasKeys` feature enabled; `function_call_permission().allowance.is_none()`; `1 ≤ num_nonces ≤
MAX_NONCES_FOR_GAS_KEY = 1024` (`account.rs:589`); `balance == ZERO`. `TransferToGasKey` only
requires the `GasKeys` feature (`action_validation.rs:390-396`).

### 1.7 Comparison with the Lean arms (`NearSpecV3/Wasm/Host.lean`)

| item | nearcore | Lean arm | match |
|---|---|---|---|
| base charge first | `pay_base(base)` | `payBaseH C.base` | ✓ |
| pk read + deferred decode error | `get_public_key`, `public_key_res?` at the end | `memOrRegH` then `pkValid` last | ✓ |
| `pk_len` on decode failure | `map_or(0, …)` | `gasKeyPkLen pk = if pkValid pk then pk.size else 0` | ✓ |
| nonce bound | `u16::try_from` → `≥ 65536` is `IntegerOverflow` | `if a[3] ≥ 65536 then hErr "IntegerOverflow"` | ✓ |
| send base | `fee(gas_key_transfer_base).send_fee(sir)` | `F.gasKeyTransfer.send sir` | ✓ |
| send per byte | `fee(gas_key_byte).send_fee(sir) * pk_len` | `F.gasKeyByte.send sir * pl` | ✓ |
| exec per byte | `fee(gas_key_byte).exec_fee() * (access_key_key_len + 27)` | `F.gasKeyByte.exec * (accessKeyKeyLen recvLen pl + 27)` | ✓ |
| add-key exec base | `fee(gas_key_nonce_write_base).exec_fee() * n` | `F.gasKeyNonceWrite.exec * n` | ✓ |
| add-key exec per byte | `fee(gas_key_byte).exec_fee() * (access_key_key_len + 2 + 8) * n` | `F.gasKeyByte.exec * (accessKeyKeyLen recvLen pl + 2 + 8) * n` | ✓ |
| add-key send | `fee(gas_key_byte).send_fee(sir) * 18` | `F.gasKeyByte.send sir * 18` | ✓ |
| account-id length | `AccountId::len()` (bytes) | `(receiptReceiver …).utf8ByteSize` | ✓ (IDs are validated ASCII) |
| balance deduction before pk error | `deduct_balance` then `public_key_res?` | `deductBalanceH` then `pkValid` | ✓ |
| method-name bytes | `null_terminated_method_names_len` = Σ len+1 | `names.foldl (… + n.size + 1) 0` | ✓ |

**Discrepancies found (none semantic):**

1. **Overflow checks.** nearcore wraps the fee products in `checked_mul`/`checked_add` and returns
   `IntegerOverflow`; `payGasKeyAddH` and `payActionBaseH` do not. `payActionPerByteH` does.
   This is the pre-existing style for every action fee in the spec (the signed arms have the same
   gap), so the extension does not widen it. Recorded as an open exclusion-class note, not a
   correctness claim: on the 73 cases no product approaches `2^64`.
2. **Deferred decode error vs. fee order for `transfer_to_gas_key`.** nearcore computes
   `pk_len` from the *decoded* key, so a malformed key yields `pk_len = 0` and the send per-byte
   fee is zero; Lean's `gasKeyPkLen` reproduces this. ✓ Verified by reading, not tested on a
   malformed-key case — none of the 73 has one.

No other mismatch was found. The arms charge, order errors and encode exactly as the pinned source.

### 1.8 The gap was a gate, not a semantics gap

`Wasm/Exec.lean:71-76` (`realOodHosts`) lists all ten hosts as out-of-domain under the trie-backed
`External`; `Wasm/Exec.lean:82-87` (`globalPromiseHosts`) lifted only seven of them under
`globalActions`. The three gas-key arms were therefore unreachable in every successor tier even
though they exist in the signed table and their semantics match. That is exactly the "host imports
alone do not establish executed coverage" case the plan describes: the arms were dead code behind a
gate.

---

## 2. The additive change

Three edits, all additive. No `St` or `NearCfg` field is added; the existing successor flag
`globalActions` (default `false`) carries the extension.

### 2.1 `NearSpecV3/Wasm/Exec.lean`

* `globalPromiseHosts` gains the three gas-key names (7 → 10 entries). `globalPromiseHosts` is the
  *successor* gate list; it already sat only inside `!(s.globalActions && …)`.
* New `gasKeyPromiseHosts` names the gas-key subset so the extension can be stated exactly.
* New predicate `hostExcluded` is definitionally `callHost`'s guard, with five theorems:
  `hostExcluded_def` (`rfl`), `hostExcluded_signed` (at `globalActions = false` the guard is the
  signed guard), `hostExcluded_signed_of_any_list` (the signed guard is the *original* gate for
  **any** list — the extension cannot move it), `globalPromiseHosts_subset_realOodHosts` (every
  lifted name is in `realOodHosts`, so lifting only ever removes exclusions),
  `gasKeyPromiseHosts_subset_global`, and `hostExcluded_lifted` (with `globalActions` set and a
  trie-backed store, a lifted name's guard is `false`).

### 2.2 `NearSpecV3/Wasm/Host.lean`

The three arms now emit canonical raw action bytes gated on `(← get).globalActions`, mirroring the
existing `deployGlobalH`/`useGlobalH`/`stateInitH` pattern. Without raw bytes the `"OTHER"`
placeholder would reach `D3.manager` and be reported as an unmodelled log entry, so this is
required for the lift to do anything.

* `gasKeyTransferRaw pk amount` = `[12] ‖ pk ‖ u128 amount`
* `gasKeyFullAccessRaw pk n` = `[5] ‖ pk ‖ u64 0 ‖ [3] ‖ u128 0 ‖ u16 n`
* `gasKeyFunctionCallRaw pk n allowance recv names` = `[5] ‖ pk ‖ u64 0 ‖ [2] ‖ u128 0 ‖ u16 n ‖
  allowTag ‖ borsh receiver ‖ u32 count ‖ …` with `allowTag = [0]` when `allowance = 0`.
* The function-call arm now binds `allowance` and `recv` (previously discarded) to build those bytes.
  No charge order changed: both reads happen exactly where they did.

### 2.3 `NearSpecV3/Successor/PromiseActionsTests.lean`

The old assertion "gas-key host remains excluded even when globals enabled" is replaced (it asserted
the bug). New assertions: all three hosts are lifted with `globalActions := true`, all three stay
excluded at `globalActions := false`, `hostExcluded` equals the signed guard on a signed state, and
the three encoders round-trip through `pActGlobal` with no leftover bytes. Two negative controls
prove the round-trip tests are non-vacuous: `num_nonces` 0 and 1025 must fail `validBase`, and a
deliberately corrupted balance field makes the test fail (verified by temporarily editing the
encoder and rebuilding).

---

## 3. Signed path proofs remain `rfl`

Re-verified after the change, in a fresh file importing `NearSpecV3.Successor.Config`:

```lean
example (c w : Bytes) : checkSuccessor signedCfg c w = D3.checkD3 c w := rfl
example (c w : Bytes) : RelSuccessor signedCfg c w ↔ D3.RelD3 c w := Iff.rfl
example (c w : Bytes) : D3.RelD3 c w = (D3.checkD3 c w = .ok ()) := rfl
example (c w : Bytes) : RelD2 c w = (acceptsD2 c w = true) := rfl
example (c w : Bytes) : Tier.checker .signed c w = D3.checkD3 c w := rfl
```

All five elaborate. `checkSuccessor_signed`, `relSuccessor_signed_iff`, `acceptsSuccessor_signed`,
`tier_signed_eq_checkD3` and `signed_tier_checker_eq` are unchanged declarations and still build.

**Why the change cannot move them.** `checkD2Core`, `checkD3`, `RelD2`, `RelD3` are definitions; the
`signedCfg` path sets `globalActions := false`, so the guard `!(false && l.contains name)` reduces to
`true` for every list `l`. `hostExcluded_signed_of_any_list` states exactly this for an arbitrary
`l`, so extending `globalPromiseHosts` cannot change the signed term. The signed tier's binary
behaviour confirms it: **0 diffs on all 3,138 cases** (section 4).

---

## 4. Regression results

Both binaries are the same build of `nearspec-v3-check-successor`; "before" is the base commit's
binary, "after" is the changed one. Case lists and per-case JSONL are in `/tmp/opencode/`
(`gaskey-before-*.jsonl`, `gaskey-new-*.jsonl`, `gaskey-base-*.jsonl`).

### 4.1 The 73 gas-key cases

| tier | before | after | note |
|---|---|---|---|
| signed | 73 `out_of_domain` | 73 `out_of_domain` | unchanged by construction |
| globalActions | 73 `out_of_domain` | 69 `accept`, 4 `out_of_domain` | the 4 also need `curveHosts` |
| curveHosts | 73 `out_of_domain` | 73 `out_of_domain` | `curveHosts` omits `globalActions` |
| **allFeatures** | **73 `out_of_domain`** | **73 `accept`** | the lane's target |

The four cases that `globalActions` alone cannot decide are
`d3c7/ood/00-h10006-s2`, `d3c7/ood/02-h10031-s2`, `d3c8/ood/11-h10016-s2`,
`d3c8/ood/11-h10111-s2`. All four additionally call `ecrecover`, which needs the `curveHosts`
selector as well; `allFeatures` sets both. They are not gas-key failures — the gas-key host already
runs and the exclusion moved on to the next host — so they are reported as a cross-lane dependency,
not a regression.

### 4.2 The full 3,138-case set, `allFeatures`

| verdict, reason | before | after |
|---|---|---|
| `accept` | 2,581 | 2,654 |
| `out_of_domain` ML-DSA-65 public key | 266 | 266 |
| `out_of_domain` pre-state compiled-contract cache | 86 | 86 |
| `out_of_domain` non-ED25519 transaction key | 80 | 80 |
| **`out_of_domain` gas-key host** | **73** | **0** |
| `out_of_domain` SECP256K1 delegate | 41 | 41 |
| `reject` MissingTrieValue (contract code) | 8 | 8 |
| `out_of_domain` `c.segment` | 3 | 3 |
| total | 3,138 | 3,138 |

Exact per-case comparison: **3,065 cases keep their identical verdict *and* reason string; 73 change
(`out_of_domain` → `accept`); 0 change in the other direction.** No case moved to `reject`, and no
case's exclusion reason text changed except the 73 that now accept.

### 4.3 Other tiers, all 3,138 cases

| tier | before | after | diffs |
|---|---|---|---|
| signed | 700 accept / 2,438 ood | 700 accept / 2,438 ood | **0** |
| curveHosts | 2,354 / 8 / 776 | 2,354 / 8 / 776 | **0** |
| resharding | 2,354 / 8 / 776 | 2,354 / 8 / 776 | **0** |
| globalActions | 2,339 accept / 8 reject / 791 ood | 2,408 / 8 / 722 | **70** |

The `globalActions` row moves 70 cases to accept — 69 gas-key-only plus the 1 whose next blocker
changed from the gas-key host to `ecrecover` (reason text changed, still excluded). The signed,
`curveHosts` and `resharding` tiers are byte-identical because none of them sets `globalActions`.

### 4.4 Independent sample outside the lane

To check the 3,065 unchanged cases a second way, a 400-case random sample was drawn from the 3,065
non-gas-key cases (`random.seed(20261025`, `/tmp/opencode/spot400.txt`) and run through both binaries
at `allFeatures`. **0 diffs.** This sample is not the same run as 4.2: it re-measures a subset
independently and confirms the "0 changes" claim was not an artefact of the earlier comparison code.

### 4.5 Axiom audit

`#print axioms` on the six new theorems (`Config.lean:428-433`) reports exactly
`[propext, Classical.choice, Quot.sound]` — the allowed set — for every one. The pre-existing three
check points are unchanged. `grep -rn sorry` over `Exec.lean` and `Host.lean`: no matches. No
`native_decide`, no `@[implemented_by]`, no new `axiom` declaration.

---

## 5. What the change does *not* claim

* It does not claim the ten-host gate is complete. `realOodHosts` still lists all ten as
  out-of-domain for the signed statement; only the successor flag lifts them.
* It does not claim gas accounting is proven equal. The arm-level match in section 1.7 is a reading
  of the source, and the empirical evidence is the 73 `accept` verdicts, which bind Lean's computed
  outcome/gas/receipts roots to the validator-attested header. Both together are the evidence; neither
  alone is.
* It does not change `checkD3`, `RelD3`, `checkD2Core` or `RelD2`, and does not widen any signed
  relation. The signed tier's 0 diffs is the mechanical check.
* The 4 cross-lane cases remain excluded under `globalActions`; the gas-key lane is not the whole
  reason those 73 were excluded, only the first blocker for 4 of them.

## 6. Files changed

| file | change |
|---|---|
| `spec/lean/v3/NearSpecV3/Wasm/Exec.lean` | `globalPromiseHosts` 7 → 10; `gasKeyPromiseHosts`; `hostExcluded` + 5 theorems |
| `spec/lean/v3/NearSpecV3/Wasm/Host.lean` | 3 raw-action encoders; 3 arms emit `rawAction` under `globalActions`; function-call arm binds `allowance`/`recv` |
| `spec/lean/v3/NearSpecV3/Successor/Config.lean` | 6 `#print axioms` check points |
| `spec/lean/v3/NearSpecV3/Successor/PromiseActionsTests.lean` | replaced the exclusion assertion with lift/no-lift/guard/round-trip assertions |
| `docs/evidence/lean-chunk-gap-census-2026-10-25.md` | row 73 marked closed; totals updated |
