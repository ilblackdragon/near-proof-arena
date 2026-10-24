# Global and state-init promise action translation

`NearCfg.globalActions` defaults to false. Enabling it carries the flag into `St`, lifts exactly the
seven global/state-init entries of `realOodHosts`, and emits canonical raw action payloads. The three
gas-key entries remain excluded. Signed configurations and mock harness defaults retain their previous
host behavior, including the mock's global log-index return value for state initialization.

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
mock defaults, disabled real host dispatch and residual gas-key exclusion. The compiled WAT fixture
executes all seven hosts and asserts both state-init indices equal one. Its alice/bob receiver names
are intentionally not derived state-init IDs; this is a VM/serialization fixture and a whole-chunk
receipt-validation failure control, not a claim of successful deterministic-account initialization.
Independent positive whole chunks need the corresponding derived `0s` receiver IDs.

Root integration must select `managerGlobal` and `finishActsGlobal` together with the enabled flag.
This module does not implement gas-key promise translation or close all W07 validation obligations.
