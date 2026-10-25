# L4 — gas-key promise host translation (W07 item)

**Claim record**

| field | value |
|---|---|
| Package | W07 "Complete gas-key translation" (the gas-key sub-item only) |
| Owner | L4 |
| Worktree / branch | `/data/illia/nearproof-wt/lean-chunk-L4`, `lane/lean-chunk-L4` |
| Base tip | `5bf2ee8f4` (main, "integrate W05 curve hosts into runCall") |
| Tip | `1d68231a1` |
| Owned inventory rows | `L0-host-promise_batch_action_add_gas_key_with_full_access`, `L0-host-promise_batch_action_add_gas_key_with_function_call`, `L0-host-promise_batch_action_transfer_to_gas_key`, and action rows `L0-action-12`/`L0-action-13` as the encodings those hosts emit |
| Shared interfaces touched | `Wasm.Host.hostCall` arms (three), `Wasm.realOodHosts`/`Wasm.globalPromiseHosts` membership, `NearSpecV3.Successor.PromiseActionsTests` |
| Deliverable | Canonical borsh bytes for the three gas-key promise actions, lifted out of the successor OOD gate, with encoder and whole-chunk tests |

## What was actually broken

The three gas-key promise hosts already had dispatch arms and already charged gas in nearcore's
order, and the inventory called them `implemented` on that basis. But each appended its action as
`{ text := "OTHER" }` with **no** `rawAction`, and all three sat in `realOodHosts` unconditionally.
So with `globalActions := true` the successor action-log translator had nothing to decode: the
action reached the log as an untyped `OTHER` entry. The action-log *translation* obligation in W07
was therefore unimplemented even though the row said `implemented` — the row means "Lean has a
dispatch arm for this name", not "this behaviour was tested against nearcore" (the generator's own
docstring). This change closes the translation gap, not a dispatch gap. Row statuses are unchanged.

## Implementation

`spec/lean/v3/NearSpecV3/Wasm/Host.lean`:

- `toGasKeyRaw pk deposit` = `tag 12 ‖ PublicKey ‖ u128 deposit` (`TransferToGasKeyAction`,
  `core/primitives/src/action/mod.rs:296-320`).
- `addGasKeyRaw pk perm` = `tag 5 ‖ PublicKey ‖ AccessKey`, with `AccessKey.nonce = 0` for a freshly
  appended key (`AccessKey::gas_key_full_access`/`gas_key_function_call`,
  `core/primitives-core/src/account.rs:493-514`).
- `gasKeyFullPerm numNonces` = permission tag 3 ‖ `GasKeyInfo{balance = 0, num_nonces}`
  (`account.rs:546-549, 575-586`).
- `gasKeyFcPerm numNonces allowance receiver methods` = permission tag 2 ‖ `GasKeyInfo{balance = 0}`
  ‖ `FunctionCallPermission` (`account.rs:582, 608-640`).

The layouts are written against the raw `PublicKeyBuffer` that the host has already validated with
`pkValid`, because `Wasm/Host.lean` cannot import the D2 layer without a cycle (`D2/Types.lean` →
`D2/GlobalTypes.lean` → `Wasm/Crypto.lean`, while `Wasm/Host.lean` also imports `Wasm/Crypto.lean`).
They mirror `D2.Perm.encode`/`AK.encode` byte for byte; byte-identity is asserted in the tests rather
than maintained by sharing the code.

One semantic detail mattered: nearcore maps a **zero** `allowance` argument to `None` before
appending (`runtime/near-vm-runner/src/logic/logic.rs:3145`). An earlier draft encoded a zero
allowance as `Some 0` (`1 ‖ u128 0`), which decodes to a different permission. The tests now assert
the option tag directly: `none` → `0`, `some 99` → `1`.

`spec/lean/v3/NearSpecV3/Wasm/Exec.lean`: `globalPromiseHosts` now lists all ten translated entries,
so `callHost` stops classifying the three gas-key names as out of domain when `globalActions` is on.
`realOodHosts` still lists all ten, so a call remains out of domain when the flag is off. This is an
opt-in successor behaviour; the signed D3α statement (`spec/near-chunk-validation-d3.md` §10.0 P3)
is unchanged and still correct for signed configurations.

## Verification (run in this worktree, not copied)

- `lake build NearSpecV3.Successor.PromiseActionsTests` — green, 70 jobs. Test line:
  `Global promise tests passed: modes, identifiers, per-receipt indices, values, sorting, errors, gas-key actions and old-path guards`.
- Full default `lake build` in `spec/lean/v3` — **245 jobs green** on the rebased base `5bf2ee8f4`.
- Encoder byte-identity and round-trip: `toGasKeyRaw`/`addGasKeyRaw` outputs compared to
  `Perm.encode`/`AK.encode` for the same logical action, and each decoded back through
  `GlobalCodecs.pActGlobal` to the exact `toGasKey`/`addKey` value.
- Allowance option tags: `none` → `[0]`, `some 99` → `[1]` at the permission's allowance offset.
- Whole-chunk fixture `tools/d3/global-promise-fixtures/gas-keys.wasm` (713 B, from the checked-in
  `.wat`) calls all three hosts on two receipts. The suite decodes the emitted actions to
  `.transfer 16`, `.toGasKey` with deposit 16 and the 32-byte key, `.addKey` with `.gasFull 0 4`, and
  `.gasFc 0 2` with `allowance = none` and methods `f`, `g`, `m`.
- Coverage inventory regenerated (`docs/research/lean-chunk-coverage.json`) and
  `lean_chunk_coverage.py --check` reports "matches pinned sources"; only the two edited source
  hashes moved.
- The prior exclusion assertion was replaced: "gas-key host lifted once globals are enabled" plus a
  "still excluded when the flag is off" control, so the gate is tested in both directions.
- No `sorry` was introduced in the edited files.

## Premises and limits

- **Not yet replayed against pinned nearcore.** The new fixture is a VM/action-log and serialization
  control. It proves the emitted bytes decode to the intended typed actions; it does **not** prove a
  whole chunk carrying these actions is accepted by nearcore. That needs an oracle-generated chunk
  window for this fixture (the existing `all-hosts-valid-receivers` window does not cover gas keys).
  The inventory's acceptance test for these rows therefore stays unmet.
- The gas-key **execution** semantics on the target side — funding, nonce indices, withdraw/transfer
  out, key deletion with balance — are separate from this translation work. Nothing here claims them.
- `promise_yield_resume*`'s result-tag mismatch noted in the earlier handover is unrelated and still
  open.

## Rebase onto main and a base regression this lane had to repair

Rebased onto `main` at `4d82b3374` (main had moved 8 commits since this lane's base `5bf2ee8f4`;
zero file overlap, so the rebase was textually clean). Three findings:

1. **A base regression, not a lane one.** W11 (`4d264c005`) added `splitMap`/`lastSplit`/`ancestorMap`
   to `Layout` and did not update `TestGlobalActions.lean` and `TestStorageResolution.lean`, which
   build a `Layout` with the anonymous constructor `⟨boundaries, shardIds, idToIndex⟩`. An anonymous
   constructor does not fill structure defaults, so both files stopped compiling
   (`Layout.mk has 6 explicit field, but only 3 were provided`). W11's "full build green (250 jobs)"
   missed it because neither file is in v3's `defaultTargets`. On main, `make d3-drivers` and
   `make d3-smoke` both exited 2. Fixed in `cf3aedd3d` with named fields (values unchanged, layouts
   stay empty-split); verified `make d3-drivers` and `make d3-smoke` both exit 0 afterwards. This is
   a repair of main's state, unrelated to the gas-key change.
2. **The coverage inventory needed regeneration for W11, not for this lane.** Rebasing moved
   `Layout.lean`'s hash. Regeneration changes exactly one field, `source_sha256.Layout.lean`; all 222
   rows are byte-identical and no row status changes (`529c858a9`).
3. **The gas-key work itself needed no change.** Its three commits are textually untouched by the
   rebase, and its source hashes were already recorded.

Full verification on the rebased tip (`cf3aedd3d`), each run in this worktree:

| gate | result |
|---|---|
| `lake build` in `spec/lean/v3` | **246 jobs green** |
| `lake build NearSpecV3.Successor.PromiseActionsTests` | green; "gas-key actions" line |
| `make pin-check` | exit 0 |
| `lean_chunk_coverage.py --check` | exit 0, "matches pinned sources" |
| `make d3-drivers` | exit 0, 9 binaries |
| `make d3-smoke` | exit 0 end to end (was exit 2 on main) |
| `nearspec-v3-test-global-actions` | exit 0, passed |
| `nearspec-v3-test-storage-resolution` | exit 0, passed |
| `smoke_successor.py` | exit 0, 49 configuration comparisons + policy check |
| `check_runtime_golden.py` | exit 0, 1030 allocation + 6 phase cases |
| `check_float_golden.py` | exit 0, 2050 operator cases + 32 bundles |

The claims in the sections above are unchanged by the rebase. The two limits still stand: the
gas-key fixture has no pinned-nearcore whole-chunk replay, and gas-key execution semantics are out
of scope here.
