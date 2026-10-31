# L0 row validation, third pass (2026-10-31): stopped on a soundness finding

This pass covers the 19 rows that were still `implemented`, all except `L0-host-current_contract_code`, which is handled separately.
The work **stopped before any row was promoted**: the reachability analysis of `L0-D3-013` found a
Lean/nearcore divergence that permits a Lean accept of a nearcore reject (section 1). No status in
`rows.json` or `docs/research/lean-chunk-coverage.json` has been changed. The evidence below was
gathered first; it is recorded so the promotions can be applied unchanged once the bug is fixed and
re-checked.

## 1. Soundness bug: `promise_batch_action_add_gas_key_with_function_call` skips the UTF-8 check

- **nearcore 2.13.4** (`runtime/near-vm-runner/src/logic/logic.rs:3115-3170`): the host pays the base
  and the action fees, then calls `ext.append_action_add_gas_key_with_function_call`. That call goes to
  `runtime/runtime/src/receipt_manager.rs:478-508`, which converts each method name with
  `String::from_utf8`. A non-UTF-8 name fails the call with `HostError::InvalidMethodName`, and the
  contract stops there.
  - `split_method_names` (`logic/utils.rs:11-20`) checks only for empty names.
- **Lean** (`spec/lean/v3/NearSpecV3/Wasm/Host.lean:1187-1207`) has no such check, so the arm
  succeeds and the contract keeps running.
  - The plain add-key arm has the check (`Host.lean:1052-1053`, citing `receipt_manager.rs:594-600`).
    The gas-key arm does not.
  - The arm is live on `allFeatures`: `globalActions` is set and the host is in `globalPromiseHosts`.
- **Consequences**:
  - If the contract returns normally, `managerGlobal` + `finishActsGlobal` fail to decode the raw
    AddKey (`decode: invalid UTF-8 (method_name)`). The error is rethrown unclassified
    (`Successor/PromiseActions.lean:41`), so Lean **rejects a chunk that nearcore accepts**, where the
    receipt simply fails. That is a completeness bug.
  - If the contract keeps executing after the host call and then fails (for example `log_utf8`, then
    `unreachable`), no receipt is built, so the decoder never runs. Lean's outcome then differs from
    nearcore's: the error, the gas burnt, the logs, the refund and the balance. A chunk whose committed
    post-state follows Lean's semantics is then accepted by Lean and rejected by nearcore. **That is a
    soundness bug.**
  - It is not yet shown on a whole chunk. An evaluation of the Lean arm alone (real store,
    `globalActions := true`, method name `[0xFF]`) returns `ok`: scratch
    `/data/illia/nearproof-deps/l0-validate/b4/scratch/gaskey_utf8.lean`.
- **Fix**: after `if !pkValid pk then hErr "InvalidPublicKey"`, add the same check as `Host.lean:1052`:
  `if (← get).real.isSome && names.any (fun n => (String.fromUTF8? n).isNone) then hErr "InvalidMethodName"`.
  Mirror it in the Logged copy. Then add a whole-chunk fixture, judged cold by nearcore, that calls
  the host with a non-UTF-8 name: one variant returns, one continues and traps. Also add a breakage
  control.

## 2. Evidence gathered (not yet applied)

All of it is under `/data/illia/nearproof-deps/l0-validate/b4/` on the lane host. The runs are judged
by cold pinned nearcore 2.13.4. The default checker is the Gate-B freeze binary (`9b583e3a…`) and
the control build is ctl-v3 (`689dbfb4…`).

| population | cases | default replay | ctl-v3 trace identity |
|---|---|---|---|
| `run-float`: the versioned generator (pre-existing binary, `oracle.sha256`), `NEAR_SUCCESSOR_CONTRACT=float-17-success.wasm` (`gen_float_chunk_contracts.py --dynamic`, sha `8ec6af0b…`), seed 17, 1 chain, 12 blocks, `--mutate-every 1 --code-mutant-p 1` | 2,557 | pass, 0 disagreements | 2,557 / 2,557 |
| `run2-w005`, `run2-w006`: this commit's generator (`oracle-l0`, sha `6dcb3c3e…`), `NEAR_L0_ROW_MUTANTS=1`, the injected contract `w005.wat` (memory import, `PrepareError(Memory)`) / `w006.wat` (49,999 locals, `WasmtimeCompileError … function[3]`), seeds 17/18, 16 blocks, `--p-missing 0.3`, every case mutated | 5,491 | pass, 0 disagreements | 5,491 / 5,491 |

Maps exclude `t.tx_valid` flips and derived trusted-fact mutants (`l0_exercise.py map
--exclude-sources`). Results per row:

| row | exercising cases (nearcore accept / reject) | control (flipped / replayed) | would become |
|---|---|---|---|
| L0-instr-float, L0-W-012 | 52 / 201 (`w.drop_node.main.*`, `hdr.*`, `w.main_post_root`, …) | `instr:float` 12/16 | validated |
| L0-W-005 | 46 / 103 | `wasm:prep` 12/16 | validated |
| L0-W-006 | 74 / 159 | `wasm:compile` 12/16 | validated |
| L0-D2-020 | 68 `l0.w.new_tx.oversize_rehashed` (nearcore: `TransactionSizeExceeded` in `pre_validate`), each rejected first by the guard; boundary: 68 `maxsize_rehashed` accepted by both | `guard:` 12/12 → accept | validated |
| L0-D2-023 | 121 `l0.c.prev_block_extra_slot` / `drop_slot` (nearcore: prev block not found) | `guard:` 1/12 → accept | validated |
| L0-D2-025 | 68 `l0.c.prev_block_hi_above` (nearcore: prev block not found) | `guard:` 3/12 → accept | validated |
| L0-D2-012, L0-same-layout, L0-D2-019, L0-split-gate, L0-guard-noResharding | — | — | impossible-at-boundary (`third-pass-statuses.json`; Lean `genesis_segment_same_layout`, `genesis_segment_no_split_gate`) |

The `D2-023` and `D2-025` ablations accept a chunk that nearcore rejects. So these guards are
load-bearing: removing either one is itself a Lean-accepts/nearcore-rejects defect.

Source arguments for the remaining exclusion rows. Scratch lemmas are in
`/data/illia/nearproof-deps/l0-validate/b4/scratch/`: `w011.lean`, `w013.lean`, `w013b.lean` and
`w014.lean`. Each is type-checked against tree-g with axioms ⊆ {propext, Classical.choice,
Quot.sound}. None is in `defaultTargets` yet.

- **L0-D3-003**: no `unmodeled` throw in `functionCallRecordedF` reaches the catch, apart from the
  `L0-D3-013` decode path.
- **L0-D3-013**: the re-encoding exclusion itself is unreachable. The rethrown decode error is
  reachable: that is the bug in section 1.
- **L0-D3-014**: unreachable. `promise_return` stores only `.receipt` indices of CR/YC log entries,
  and `D3.manager` maps every one of them.
- **L0-W-011**: bad frame and pc out of range are unreachable on certified code (`run_inv`,
  `frame_ok`). The short-gas-table and float load/store arms are excluded by `Prepare.lean:483-495`
  and `Decode.lean:261-264`.
- **L0-W-013**: unreachable (`popArgs_ok`, `realHasH_some`, `realGetH_some`).
- **L0-W-014**: unreachable on nearcore tries, given that every extension on the lookup path is
  non-empty (assumption from `insert_delete.rs` / `squash.rs`). `ChunkStorage.lean:77` is in an
  unimported harness. The bound in `fuel-termination` and `gate-b-caps` should state that premise.

## 3. Exact next steps

1. Fix the section 1 bug in Lean, rebuild the default checker and ctl, and add its whole-chunk fixture
   and control. Re-run the `host-rows` and corpus replays for the gas-key host.
2. Re-run `replay.sh` / `ablate.sh` / `ablate2.sh` (in `b4/`) on the new binaries.
3. Copy the scratch lemmas into `L0GuardSubsumption.lean` and add the D3/W status entries to
   `third-pass-statuses.json`.
4. Run `l0_exercise.py evidence --only …` (`--map map-float-x.json map-r2-x.json --ablate
   ablate-float.json ablate-r2.json ablate-r2g.json`), then `statuses --spec third-pass-statuses.json`.
   Remove the superseded entries from `second-pass-statuses.json`.
5. Run `lean_chunk_coverage.py --output` and `--check`, update the summary doc, and run the full
   `lake build`.
