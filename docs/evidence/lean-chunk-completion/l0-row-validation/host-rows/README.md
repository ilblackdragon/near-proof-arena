# L0 row validation: the 16 remaining host rows (`host-rows` scenario, 2026-10-31)

This package covers the host rows that the first pass of [l0-row-validation](../README.md) left
`implemented`:

- **7 hosts that no case called:** `current_contract_code`, `refund_to_account_id`,
  `promise_set_refund_to`, `storage_iter_{prefix,range,next}` and `gas`.
- **9 hosts with no nearcore-rejected exercising chunk:**
  - `promise_batch_action_add_gas_key_with_{full_access,function_call}` and
    `promise_batch_action_transfer_to_gas_key`;
  - `promise_batch_action_deploy_global_contract{,_by_account_id}` and
    `promise_batch_action_use_global_contract_by_account_id`;
  - `promise_batch_action_state_init{,_by_account_id}` and `set_state_init_data_entry`.

Target: nearcore 2.13.4 (`44f7ae6c`), PV86. Checkers: the Gate-B freeze checker
(`9b583e3a…`, default path, unchanged) and the control build `16238557…` (unchanged from the
first pass). Generator: `oracle/v3-successor`, with the new opt-in scenario `host-rows`
(`src/xfam.rs` `host_rows`, contract `contracts/hostrows.wat`). Binary sha256 `f35cc41f…`.

**Result.**
- 15 of the 16 rows are promoted to `validated`.
- `current_contract_code` stays `implemented` because of a **Lean completeness bug** (§3):
  - Lean rejects 205 nearcore-accepted cases, 16 of them honest chunks;
  - Lean accepts no nearcore-rejected case (0 soundness disagreements).

## 1. Scenario

The chain is quiet: no baseline traffic and no crafted injections. It runs 46 steps on 9 dedicated
genesis accounts. [`steps.md`](steps.md) lists every step with nearcore's receipt kinds.

Contracts:
- **`hostrows`** (`oracle/v3-successor/contracts/hostrows.wat`), new. It calls each of the 7
  uncalled hosts:
  - `ccc` stores and returns `current_contract_code`'s result byte and register;
  - `rta` returns `refund_to_account_id`;
  - `psr` calls `promise_set_refund_to` on a transfer batch, a function-call batch, an invalid
    promise index or a joint promise;
  - `itp`/`itr`/`itn` write, then call a `storage_iter_*` host;
  - `gas` calls the `env.gas` import (i32 parameter) with `k` from its input.
- **`kgashost`**: the keys-scenario gas-key contract, unchanged.
- **`hrall`**: `tools/d3/global-promise-fixtures/all-hosts-valid-receivers.wat`, unchanged, the
  contract of the global-promise fixtures.

nearcore's outcomes (identical for all 4 seeds):

| host | what nearcore did |
|---|---|
| `current_contract_code` | returned 1 on local code (also right after an in-receipt deploy), 2 on a `UseGlobalContract(CodeHash)` account, and 3 on a `UseGlobalContract(AccountId)` account, directly and across shards |
| `refund_to_account_id` | value: self, cross-shard, on a global-contract account, and in a callee whose receipt carries a refund-to account |
| `promise_set_refund_to` | success for a transfer and for a callee. Failures: `InvalidPromiseIndex`, `CannotSetRefundToOnJointPromise`, `InvalidAccountId` ("A!"). On a transfer to an absent account, the deposit refund goes to the refund-to account; when that account is absent too, the refund fails as well |
| `storage_iter_{prefix,range,next}` | `HostError(Deprecated)` trap: the receipt fails and its write rolls back. The chunk is accepted. A cross-shard variant behaves the same, and a write-only control succeeds |
| `gas(k)` | `k` = 0, 1,000, 23·10⁶ and 300,000 succeed. 24.4·10⁶ at 20 Tgas fails with `GasExceeded`. u32::MAX at 300 Tgas fails with `GasLimitExceeded`. 10⁶ at 300 Tgas succeeds |
| gas-key hosts | `addfull`, `fund`, `addfund` and `fundto` succeed; `addfull` across shards succeeds. Failures: `addfc` (`NewReceiptValidationError`, since a function-call gas key cannot have an allowance), a missing gas key, and a malformed key (`InvalidPublicKey`) |
| global/state-init hosts | `run` at 300 Tgas emits both batches, whose receipts then fail at the transfer to the not-yet-existing deterministic accounts (as in the global-promise fixtures). At 20 Tgas, `run` fails with `GasExceeded`. A cross-shard call behaves the same |

Every chunk with scenario activity gets the full mutant set (`xfam::force_full_mutants`).

## 2. Populations and verdicts

Runs: seeds 811–814 on chain shapes 0/1/2/4 (4/5/6/5 shards, gas limits 1000/1000/1000/60
Tgas), 40 blocks, `--p-missing 0.05`. Every case is judged by cold pinned nearcore. The
collector (`tools/d3/collect_xfam.py`, new `HostRows` check) reports 0 problems on all 4 runs:
every step executed, and every defining outcome in the table above holds.

Default-checker replay (`replay_successor.py`, `allFeatures`). The trace build gives identical
verdicts and reasons: 11,437/11,437.

| seed | honest (all accepted by nearcore) | mutants | nearcore accept → Lean accept / reject | nearcore reject → Lean reject / accept |
|---|---|---|---|---|
| 811 | 155 | 2,634 | 686 / **51** | 2,052 / 0 |
| 812 | 187 | 2,594 | 705 / **51** | 2,025 / 0 |
| 813 | 229 | 2,701 | 772 / **52** | 2,106 / 0 |
| 814 | 192 | 2,745 | 748 / **51** | 2,138 / 0 |
| total | 763 | 10,674 | 2,911 / **205** | 8,321 / 0 |

No Lean accept of a nearcore reject. All 205 disagreements are Lean rejects (`invalid: main
transition post state root`) of nearcore-accepted cases: 16 honest chunks plus mutants of them
that nearcore still accepts. `current_contract_code` fires in every one (`summary.json`).

## 3. Bug: `current_contract_code` on a global-contract account (completeness)

nearcore (`runtime/near-vm-runner/src/logic/logic.rs:4000-4030`) returns the following, by the
account's `AccountContract`:

| `AccountContract` | return value | register |
|---|---|---|
| `None` | 0 | — |
| `Local(h)` | 1 | `h` |
| `Global(h)` | 2 | `h` |
| `GlobalByAccount(a)` | 3 | the bytes of `a` |

Lean (`spec/lean/v3/NearSpecV3/Wasm/Host.lean:726-730`) returns 1 with the code hash for any
`some h`. The successor context always sets `accountContract := some (toBA hh)`, with `hh` the
resolved code hash (`Successor/StorageExecution.lean:202`, and likewise in the other tier files).

The per-step check confirms the cause:

| `ccc` step | nearcore result | Lean verdict on the chunk (4 seeds) |
|---|---|---|
| `ccc.local`, `ccc.local.cross-shard`, `deploy+ccc` | 1 | accept (12/12) |
| `ccc.global-hash`, `use-global-hash+ccc` | 2 | reject (8/8) |
| `ccc.global-account`, `ccc.global-account.cross-shard` | 3 | reject (8/8) |

A contract that stores or returns the value therefore gets a different post-state or outcome root
in Lean, and Lean rejects a valid chunk. The bug is not a soundness bug, and nothing on the default
path was changed here.

The fix belongs in the Lean model:
- carry the account's `AccountContract` kind (and, for `GlobalByAccount`, the account id) into
  `CallCtx`;
- return 2 or 3 accordingly.

After the fix, re-run this population. The 16 honest disagreeing chunks are in `cases.tar.gz`
(role `disagreement:honest`).

Rows that fire in the same chunks (`promise_set_refund_to` 48 and
`promise_batch_action_add_gas_key_with_full_access` 39) are attributed to `current_contract_code`.
Every one of those cases also runs it (`l0_exercise.py evidence --disagreement-cause`). Disagreeing
cases are never counted as exercising evidence (`l0_exercise.py map`).

## 4. Per-row evidence

The first-pass exercise map (`runs/map2.json`) is merged per row with this population's map. Each
control is `NEARSPEC_ABLATE=host:<name>`: the arm burns 1 extra gas. It is replayed on 12
nearcore-accepted and 4 nearcore-rejected exercising cases. Every unablated replay passes 16/16.

| row | nearcore-accepted | nearcore-rejected | disagreements (caused) | control flips | status |
|---|---|---|---|---|---|
| `current_contract_code` | 164 | 542 | 205 (205) | 12/16 | **implemented** (§3) |
| `refund_to_account_id` | 220 | 318 | 0 | 12/16 | validated |
| `promise_set_refund_to` | 364 | 592 | 48 (0) | 12/16 | validated |
| `storage_iter_prefix` | 104 | 144 | 0 | 12/16 | validated |
| `storage_iter_range` | 56 | 72 | 0 | 12/16 | validated |
| `storage_iter_next` | 48 | 72 | 0 | 12/16 | validated |
| `gas` | 298 | 446 | 0 | 10/16 | validated |
| `promise_batch_action_add_gas_key_with_full_access` | 252 | 307 | 39 (0) | 12/16 | validated |
| `promise_batch_action_add_gas_key_with_function_call` | 49 | 75 | 0 | 12/16 | validated |
| `promise_batch_action_transfer_to_gas_key` | 172 | 231 | 0 | 12/16 | validated |
| `promise_batch_action_deploy_global_contract` | 106 | 152 | 0 | 12/16 | validated |
| `promise_batch_action_deploy_global_contract_by_account_id` | 106 | 152 | 0 | 12/16 | validated |
| `promise_batch_action_use_global_contract_by_account_id` | 106 | 152 | 0 | 12/16 | validated |
| `promise_batch_action_state_init` | 233 | 221 | 0 | 12/16 | validated |
| `promise_batch_action_state_init_by_account_id` | 106 | 152 | 0 | 12/16 | validated |
| `set_state_init_data_entry` | 106 | 152 | 0 | 12/16 | validated |

The `gas` control flips 10 of 16 cases, not 12. The extra unit of gas is lost in the
over-the-limit cases, which fail with the same error either way.

The account with no code (where `current_contract_code` returns 0) cannot be exercised by a
function call: such a call fails with `CodeDoesNotExist` before any host runs. The 0 arm is
unreachable from a chunk.

## 5. Files

- `summary.json`: per-seed chain parameters and verdict partitions.
- `steps.md`: steps and nearcore's receipt kinds.
- `manifests/hr81?.json.gz`: collector manifests (per step: receipts, statuses, gas, cases).
- `replay/default-results.jsonl.gz`: the default checker's rows (11,437 cases). Its sha256 is in
  `rows.json` `default_replay.host_rows`.
- `replay/trace.jsonl.gz`: the control-build trace.
- `replay/map-hr.json.gz`: this population's exercise map.
- `replay/ablate-hr.json`: the 16 controls.
- `row-extra.json`: the evidence paths and the bug text merged into `rows.json`.
- `cases.tar.gz` + `cases-index.json`: 150 cases, namely every host-rows case used by a control
  plus the 16 honest disagreeing chunks. Replayed from the extracted files with the default
  checker: 134 agree (102 accept, 32 reject), and the 16 honest chunks disagree as in §3.

## Reproduce

```
bash oracle/scripts/link-nearcore.sh && cargo build --release --manifest-path oracle/v3-successor/Cargo.toml
for x in "811 0" "812 1" "813 2" "814 4"; do set -- $x
  NEAR_SUCCESSOR_SCENARIO=host-rows $ORACLE gen --domain d3 --seed $1 --first-chain $2 --chains 1 \
    --blocks 40 --p-missing 0.05 --mutate-every 0 --code-mutant-p 0 --ood-cap 100000 --drop-cap 12 --out run$1
  python3 tools/d3/collect_xfam.py --source run$1 --out coll$1; done
python3 tools/d3/replay_successor.py --binary $FREEZE --tier allFeatures --cases-file all.txt --out default --jobs 4
python3 tools/d3/l0_exercise.py trace --binary $CTL --cases-file all.txt --out trace.jsonl --jobs 4
python3 tools/d3/l0_exercise.py identity --trace trace.jsonl --reference default/results.jsonl
python3 tools/d3/l0_exercise.py map --trace trace.jsonl --out map-hr.json
# map3.json = runs/map2.json with the 16 host rows replaced by the per-row union with map-hr.json
python3 tools/d3/l0_exercise.py ablate --binary $CTL --map map3.json --out ablate-hr.json --workdir abl --jobs 8 --targets host:…
python3 tools/d3/l0_exercise.py evidence --map map3.json guard-map-repo.json \
  --ablate ablate.json guard-ablate-repo.json ablate-hr.json --out rows.json \
  --disagreement-cause host:current_contract_code --extra host-rows/row-extra.json
```

Working files: `/data/illia/nearproof-deps/l0-validate/hr/` on the lane host.
