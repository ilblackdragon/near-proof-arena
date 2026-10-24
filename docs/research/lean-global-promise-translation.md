# Global and state-init promise action translation

`NearCfg.globalActions` defaults to false. Enabling it carries the flag into `St`, lifts all ten
translated entries of `realOodHosts` — the seven global/state-init hosts and the three gas-key hosts —
and emits canonical raw action payloads. Signed configurations and mock harness defaults retain their
previous host behavior, including the mock's global log-index return value for state initialization.
`globalPromiseHosts` is the lifted set; `realOodHosts` still lists all ten, so a call remains out of
domain while the flag is false.

Gas-key payloads (`Wasm/Host.lean`):
- `promise_batch_action_transfer_to_gas_key` → tag 12 ‖ `PublicKey` ‖ `u128` deposit
  (`TransferToGasKeyAction`, `core/primitives/src/action/mod.rs:296-320`).
- `promise_batch_action_add_gas_key_with_full_access` → tag 5 ‖ `PublicKey` ‖ `AccessKey{nonce = 0,
  GasKeyFullAccess{balance = 0, num_nonces}}` (`AccessKey::gas_key_full_access`,
  `core/primitives-core/src/account.rs:493-514, 575-586`).
- `promise_batch_action_add_gas_key_with_function_call` → the same `AddKey` shape with
  `GasKeyFunctionCall{balance = 0, num_nonces}` and a `FunctionCallPermission`. nearcore maps a zero
  allowance argument to `None` before appending (`runtime/near-vm-runner/src/logic/logic.rs:3145`), so
  a zero allowance encodes option tag 0, not `1 ‖ 0`.

Both gas-key variants are ordinary D2 actions, so `finishActsGlobal` types them through the existing
tag-12 and tag-5 decoder arms; there is no gas-key-specific decoder. The encoders mirror
`D2.Perm.encode`/`AK.encode` byte for byte but are written against the raw `PublicKeyBuffer` that the
host already validated, because `Wasm/Host.lean` must not import the D2 layer.

`MAct.rawAction` contains a receipt log index and Borsh action bytes. `stateInitData` retains the
identifier, deposit and actual key/value pairs, so later `set_state_init_data_entry` calls can update
the payload. Hash/account deployment modes are kept distinct. Identifiers are read once through the
existing memory/register and account-validation paths, preserving their charge order.

Real state-init indices are **per-receipt action ordinals**, including ordinary actions and excluding
refund-routing metadata. Interleaved receipts have independent ordinals. Set-data looks up that
ordinal within the named receipt, validates it refers to a state-init action, and stores both key and
value. Serialization sorts by byte-lexicographic key order. Duplicate insertion replaces the value
before returning DataEntryAlreadyExists, matching the pinned BTreeMap operation; failed calls still
roll back their effects in the action-receipt pipeline. Error receipt indices use the manager's receipt
ordinal rather than the mock log index.

`Successor.managerGlobal` reuses existing dependency/data-id/refund/gas-weight logic. For its internal
manager pass only, raw entries occupy CreateAccount staging slots with unchanged log indices. The
adapter resolves the target receipt, calculates the per-receipt action position, verifies the slot is
the expected unweighted `[0]` staging payload, and replaces it with the canonical raw bytes before
returning. No staging action reaches execution. `finishActsGlobal` decodes the resulting payloads
through `GlobalCodecs.pActGlobal`, requiring complete consumption. The original D3 manager/decoder
remain available for configurations with the flag disabled.

Pinned sources:
- `near-vm-runner/src/logic/logic.rs:2491–2518`: deploy-global mode, memory and fee order.
- `logic.rs:2695–2772`: state-init deposit/index and set-data gas order.
- `runtime/runtime/src/receipt_manager.rs:292–347`: per-receipt append index and actual BTreeMap data.

Validation: build `NearSpecV3.Successor.PromiseActionsTests`. Native directed tests cover mixed
ordinary/global actions on two interleaved receipts, refund metadata, each global mode, identifier
encoding, per-receipt indices, data values and sorted keys, duplicates, wrong action indices, old
mock defaults and disabled real host dispatch. Gas-key coverage is separate and additive:
`tools/d3/global-promise-fixtures/gas-keys.wasm` calls all three gas-key hosts and the suite asserts
the emitted bytes decode to the exact typed actions (`toGasKey` with its deposit, `gasFull 0 4`, and
`gasFc 0 2` with `allowance = none` and methods `f`, `g`, `m`); encoder-level tests assert
byte-identity with `Perm.encode`/`AK.encode` and the zero-allowance option tag. The compiled WAT fixture
executes all seven hosts and asserts both state-init indices equal one. Its alice/bob receiver names
are intentionally not derived state-init IDs; this is a VM/serialization fixture and a whole-chunk
receipt-validation failure control, not a claim of successful deterministic-account initialization.
Independent positive whole chunks need the corresponding derived `0s` receiver IDs.

Root integration must select `managerGlobal` and `finishActsGlobal` together with the enabled flag.
This module does not implement gas-key promise translation or close all W07 validation obligations.
