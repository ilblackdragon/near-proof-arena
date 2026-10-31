# L0 row validation, third pass (2026-10-31)

This pass covers the 18 rows still `implemented` after the second pass. The 19th, `L0-host-current_contract_code`,
was handled separately (`../host-rows/ccc-fix`). All 18 are now settled: 7 `validated` and 11
`impossible-at-boundary`. The coverage inventory has 0 `implemented` rows (178 validated, 47
impossible-at-boundary).

On the way, the pass found and fixed a **soundness bug** in the gas-key function-call host (§1).

Binaries:
- Default checker before the fix: main with the `current_contract_code` fix, sha256 `ee00c918…`.
- Default checker after the fix: this branch, sha256
  `0b0f01ec382faf1efb70839954c130677d171198331f44c15d043f38e6fe8833`.
- Control build: ctl-v3, sha256 `689dbfb4…`.
- Generator: this branch's `oracle/v3-successor`, sha256 `cba1abb1…`. Every new option is opt-in.

Working files are under `/data/illia/nearproof-deps/l0-validate/b4/` on the lane host. The scripts
are copied to [`scripts/`](scripts/), the contracts to [`contracts/`](contracts/), and example cases
(index in `cases/index.json`) to [`cases/`](cases/).

## 1. Soundness bug: `promise_batch_action_add_gas_key_with_function_call` skipped the UTF-8 check (fixed)

- **nearcore** (`runtime/near-vm-runner/src/logic/logic.rs:3115-3170`): the host first pays its fees
  and validates the key. It then calls `ReceiptManager::append_action_add_gas_key_with_function_call`
  (`runtime/runtime/src/receipt_manager.rs:478-508`), which converts each method name with
  `String::from_utf8`. A name that is not UTF-8 fails the call with `HostError::InvalidMethodName`,
  and the contract stops.
- **Lean before the fix** (`Wasm/Host.lean`, the gas-key function-call arm): no check, so the
  contract kept running. The plain add-key arm already had the check (`receipt_manager.rs:594-600`).
- **Fix**: the same check, in the same place nearcore makes it, after `pkValid`:
  `if (← get).real.isSome && names.any (fun n => (String.fromUTF8? n).isNone) then hErr "InvalidMethodName"`.
  - The Logged layer has no separate copy of this arm: `Logged.W.hostCallL` falls through to
    `hostCall`.
  - The proofs over the arm build unchanged: `FuelHost.HOR_hc_67`, `HostCommArms.CR_hc_67`,
    `HostQArms` and `WasmCRHostCall`.
  - The full default `lake build` passes, with axioms ⊆ {propext, Classical.choice, Quot.sound}.

**Fixture family** (`scripts/gen-gk.sh`, `scripts/pipeline.sh`). The contract
(`contracts/gkcont.wat` / `gkret.wat`) replaces the `d3float` account's code
(`NEAR_SUCCESSOR_CONTRACT`). It creates a promise and adds a function-call gas key with method name
`0xFF`. There are two variants:
- `gkret` returns normally after the call;
- `gkcont` logs and then traps (`unreachable`).

Each variant runs on 4 seeds (31–34) with `NEAR_L0_ROW_MUTANTS=1`. Every case gets the full mutant
set, including the `e.ood_host` chunks. nearcore fails every target call with `InvalidMethodName`
and emits no log.

To show a Lean accept of a nearcore reject at chunk level:
1. Run the pre-fix checker in `--blind` mode on the 24 honest `gkcont` chunks. Its outputs (outcome
   root, gas, …) differ from nearcore's.
2. Re-run the same chains deterministically (the honest cases are byte-identical) with
   `NEAR_L0_HDR_OVERRIDES` (`oracle/v3-successor/src/l0mut.rs`). This adds the mutant
   `l0.hdr.lean_outputs`: the endorsed header in claim and witness carries Lean's outputs.
3. Cold nearcore judges all 24 of these mutants (23 `InvalidOutcomesProof`, 1 post-state root) and
   rejects them.

18,122 cases in total:

| checker | tier | Lean accept / nearcore reject | Lean reject / nearcore accept | other moves |
|---|---|---|---|---|
| before (`ee00c918`) | allFeatures | **23** (the `l0.hdr.lean_outputs` mutants) | 732 (`decode: invalid UTF-8 (method_name)` 373, `InvalidOutcomesProof` 359) | — |
| after (`0b0f01ec`) | allFeatures | 0 | 0 | 919 reject → reject with a new reason |
| before / after | signed | 0 / 0 | 0 / 0 | none. `signed` excludes the gas-key host (`out of domain (e.wasm-α)`), so it is **not affected** |

**Before/after on the other populations** (`before-after/ba-*.json`, `tools/d3/l0_before_after.py`).
On every one, 0 cases move and 0 are Lean accepts of a nearcore reject after the fix:

| population | cases | allFeatures | signed |
|---|---|---|---|
| census | 3,138 | 0 moved | 0 moved |
| committed fixtures (freeze list) | 1,364 | 0 moved | 0 moved |
| host-rows (seeds 811–814) | 11,437 | 0 moved | 0 moved |
| 1-in-8 corpus sample (seed 20261031) | 29,465 | 0 moved | 0 moved |

The pre-fix checker is the breakage control: it disagrees on the 755 gas-key cases.

## 2. Rows validated (7)

Populations, all judged by cold pinned nearcore:
- `run-float`: float contract `float-17-success` (`gen_float_chunk_contracts.py --dynamic`, sha
  `8ec6af0b…`), seed 17, 12 blocks, every case mutated. 2,557 cases.
- `run2-w005` / `run2-w006`: injected contracts `w005` (an `env.memory` import, so
  `PrepareError(Memory)`) and `w006` (49,999 locals: NEAR preparation passes, Wasmtime compilation
  fails, and nearcore reports `WasmtimeCompileError … function[3]`, as Lean predicts). Seeds 17/18,
  `--p-missing 0.3`, every case mutated, plus the `NEAR_L0_ROW_MUTANTS` witness+claim mutants.
  5,491 cases.

Checks on these populations:
- Default replay: 0 disagreements.
- The ctl-v3 trace is identical to the default checker on all 8,048 cases.
- The new checker (`0b0f01ec`) is identical as well.
- The maps leave out `t.tx_valid` flips and derived trusted-fact mutants
  (`l0_exercise.py map --exclude-sources`).

| row | exercising (nearcore accept / reject) | control (flipped / replayed) |
|---|---|---|
| L0-instr-float, L0-W-012 | 52 / 201 | `instr:float` 12/16 |
| L0-W-005 | 46 / 103 | `wasm:prep` 12/16 |
| L0-W-006 | 74 / 159 | `wasm:compile` 12/16 |
| L0-D2-020 | 68 `l0.w.new_tx.oversize_rehashed` (`TransactionSizeExceeded`), each rejected first by the guard. Boundary: the 68 `maxsize_rehashed` mutants are accepted by both | `guard:` 12/12 → accept |
| L0-D2-023 | 121 `l0.c.prev_block_extra_slot` / `drop_slot` | `guard:` 1/12 → accept |
| L0-D2-025 | 68 `l0.c.prev_block_hi_above` | `guard:` 3/12 → accept |

The D2-023/025 mutants fabricate the prev block: they re-hash it and name it from the chunk header,
in both claim and witness. nearcore does not have that block, so it rejects. With either guard
removed, Lean accepts some of these chunks, so both guards are load-bearing.

## 3. Rows `impossible-at-boundary` (11)

The reasons are in [`../third-pass-statuses.json`](../third-pass-statuses.json). The lemmas are in
`spec/lean/v3/NearSpecV3/L0GuardSubsumption.lean`.

**`L0-D2-012`, `L0-same-layout`, `L0-D2-019`, `L0-split-gate`, `L0-guard-noResharding`.** On
allFeatures these guards run only for segments that reach genesis. Such a segment covers every
epoch from genesis onward, and these guards run after `c.pv86`, so all those epochs are PV86.
- For a genesis protocol version other than 29, nearcore requires a static genesis config
  (`genesis.rs:64-69`).
- So `config(86)` is static. Every epoch keeps the genesis layout, and no block carries a split gate:
  nearcore computes one only under a dynamic config (`runtime/mod.rs:282-298, 597`).
- Lean lemmas: `genesis_segment_same_layout` and `genesis_segment_no_split_gate` (no axioms), over
  `Successor.LayoutReach.Chain`.
- On mainnet (genesis PV 29), `c.pv86` fails first.

**`L0-W-011`.**
- `run_inv`, `frame_ok`, `buildLblLive_live`: on fuel-certified code, a frame never names a missing
  function or a pc outside its code.
- `step_lookups`: with prepare's gas-table size check, every step finds its instruction and its gas.
- Float load/store is decoded only from load/store opcodes (`Decode.lean:261-264`).
- The remaining invariant arms (labels, function/type indices) are argued from Validate's typing.

**`L0-W-013`.**
- `popArgs_ok`: the arity throw is dead.
- `realHasH_some`, `realGetH_some`: every store accessor is dominated by a `real.isSome` test on an
  unchanged state.

**`L0-W-014`.**
- `lookup_errors`: the lookup fuel `4|key|+4` exceeds the path length when every extension key is
  non-empty.
- Assumption, recorded and argued from `insert_delete.rs` / `squash.rs`: nearcore never builds an
  empty extension.
- `ChunkStorage.lean:77` is in a harness that allFeatures does not import.

**`L0-D3-003`, `L0-D3-013`, `L0-D3-014`.** These are source arguments. No `unmodeled` throw in
`functionCallRecordedF` reaches the catch.
- The re-encoding exclusion is dead, because every emitted action encoding is read back exactly.
- `promise_return` indices are always mapped by the manager.
- The only reachable branch found, the decode error of a non-UTF-8 gas-key method name, was the §1
  bug and is fixed.

## Reproduce

Generators, replays and controls: `scripts/gen-float-w00x.sh`, `scripts/gen2.sh`,
`scripts/replay.sh`, `scripts/ablate.sh` and `scripts/ablate2.sh`. Gas-key family:
`scripts/pipeline.sh`. Before/after: `scripts/run.sh`, then `scripts/ba.sh`. Promotion:

```
python3 tools/d3/l0_exercise.py evidence --map map-float-x.json map-r2-x.json \
  --ablate ablate-float.json ablate-r2.json ablate-r2g.json --out rows.json --extra extra3.json \
  --only L0-instr-float L0-W-012 L0-W-005 L0-W-006 L0-D2-020 L0-D2-023 L0-D2-025
python3 tools/d3/l0_exercise.py statuses --spec third-pass-statuses.json --out rows.json
python3 tools/d3/lean_chunk_coverage.py --repo . --nearcore … --output docs/research/lean-chunk-coverage.json
```
