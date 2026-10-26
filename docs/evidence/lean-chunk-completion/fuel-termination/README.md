# Evaluator fuel and termination on the `allFeatures` path (W02)

Gate B requires that no valid supported execution is rejected as fuel exhaustion. This directory
lists every fuel parameter on the successor (`allFeatures`) path, says where each value comes from
and what exhaustion does, and records the one defect found and fixed. Each sufficiency argument
is labelled as proved in Lean, structural, or an open obligation.

Target: nearcore 2.13.4 (`44f7ae6c`), PV86. Checker before: `29bf5217…` (main `ad55805ea`). Checker
after: `8b4dd7c9…` (this change). Generator: `oracle/v3-successor` `7e0137aa…`, with the new
`fuel-stress` scenario.

## 1. Finding: the Wasm step budget was too small for valid contracts

Up to this change, `Successor/StorageExecution.lean` (like the signed `D3/FunctionCall.lean`) ran
`Wasm.run` with fuel `(gas / regular_op_cost + 2) · 64 + 10⁶`. That allows 64 interpreter steps per
`regular_op_cost` of prepaid gas. Finite-wasm charges **nothing** for `block`, `else` and `end`.
`loop` is also zero at its own point, because its header charge sits after it
(`FiniteWasm.gInstr`). The interpreter still spends one step on each of them. A loop body of `k`
empty `block`s and a `br` costs about two `regular_op_cost` per iteration and takes `2k + 2` steps.
PV86 allows `k ≤ max_blocks_per_function = 5,000`. Such a contract therefore exhausts the legacy
budget after spending roughly 128/k of its attached gas: about 1.3 % at k = 4,999.

Reproduced on pinned-nearcore whole chunks (§4). Before the fix, all three block-loop chunks were
`out_of_domain (e.wasm-α): unmodeled unmodeled fuel exhausted`. nearcore validates each of them,
with a `FunctionCall` that fails with "Exceeded the prepaid gas". After the fix all three accept,
and their outputs match nearcore blind.

**Fix (successor only).** `Wasm/Fuel.lean` defines
`wasmFuel cfg gas = (gas / regular_op_cost + 2) · (2 · max_blocks_per_function + 2) + 10⁶`: 10,002
steps per costly step at PV86. `StorageExecution.functionCall` now uses it. The signed
`D3.functionCall` is unchanged. There, the same input is an out-of-domain verdict, never a wrong
accept or reject.

**The change cannot move any verdict that the legacy budget decided** (proved; no axioms beyond the
three allowed). From `Wasm/Fuel.lean`:

* `run_fuel_le`: if `run n s ≠ fuel exhausted` and `n ≤ m`, then `run m s = run n s`.
* `callEntry_fuel_le`, `runCall_fuel_le` and `runCallWithLimits_fuel_le`: the same, up to the
  call's `Run` result. The start function and the method each get the full budget.
* `legacyFuel_le_wasmFuel`, `successorFuel_moves_only_exhausted`: under the PV86 parameters,
  every call result is either unchanged or was `unmodeled fuel exhausted` under the legacy budget.

So the only verdicts that can move are former `fuel exhausted` out-of-domain verdicts. The census
(§5) confirms that on the 3,138 cases.

## 2. Why `wasmFuel` suffices, and what is still open

Let `P(s)` be the sum over call frames of the free instructions (`block`/`loop`/`else`/`end`) at or
after the frame's `pc`. Let `F` be the largest per-function free count, `Tc` the number of costly
instructions executed and `T` the total number of steps.

| obligation | statement | status |
|---|---|---|
| O-W1a | `block`, `loop` and `end` steps advance the top `pc` by one in the same function, or pop the frame. This includes the case where a charge point sits at that `pc` (charging changes only gas). | **proved**: `exec_block_frames`, `exec_loop_frames`, `exec_end_frames`, `doReturn_frames`, `charge_cont_frames`, `step_free_progress` |
| O-W1b | `else` jumps forward. This needs the label invariant that `matchBlocks`/`endOf` establish: a non-loop label's target is past the current `pc`. | open; 0 violations measured |
| O-W2 | A costly step raises `P` by at most `F`. A call pushes one frame and a backward `br` resets one `pc`. Everything else moves forward or pops, and host calls leave the frames alone. | open (needs every `exec` arm and every host arm); 0 violations measured |
| O-W3 | `F ≤ 2·max_blocks_per_function + 1`. This follows from `prepare`'s `TooManyBlocksPerFunction` check and validated nesting (`#end = #block + #loop + #if + 1`, `#else ≤ #if`). | open; max measured `F` = 10,001 = the bound |
| O-W4 | The finite-wasm prepaid invariant `Tc · regular_op_cost ≤ Σ charged ≤ prepaid`. Every costly fee is `≥ regular_op_cost`, and a group's fee is charged before the group runs. Branch targets start groups, because `.post` points are never merged into an earlier point. | open (needs `optimize`/`gasTable` correctness); 0 violations measured |

O-W1 and O-W2 give `T − Tc ≤ P₀ + F·Tc`, so `T ≤ (F + 1)(Tc + 1)`. O-W3 and O-W4 then give
`T ≤ wasmFuel`. The bound is nearly tight: `blocks4999` measured `T / Tc` = 9,999 against the allowed
10,002.

**Measured** with `nearspec-v3-fuel-probe` (`oracle/wasm-d3/lean/FuelProbe.lean`). The probe mirrors
`runCall` with the mock `External`, recomputes `P` before and after every step, and checks each
inequality on every run (`replay/probe-random-opcodes.jsonl.gz`, `replay/probe3.jsonl`):

| population | runs executed | free steps not lowering `P` (O-W1) | costly rise > `F` (O-W2) | `F` > 10,001 (O-W3) | `Tc·regular > charged` (O-W4) | `T > wasmFuel` | `T > legacy` |
|---|---|---|---|---|---|---|---|
| 2,000 random contracts (`gen_d3a.py`, seed 7) and 9,175 opcode/limit cases (`opcases.py`) | 10,603 of 11,175 (the others stop in preparation, link or loading) | 0 | 0 | 0 | 0 | 0 | 0 |
| fuel-stress methods (12) | 12 | 0 | 0 | 0 | 0 | 0 | 2 (`blocks4999` at 0.3 Tgas, `blocks200` at 1 Tgas) |

Largest observed values: `T` = 364,627,574 (random set), stack depth 4,096 (`recurse`: 262,144 / 64),
`T/Tc` = 10,001 (an opcode limit case at `max_blocks_per_function`).

## 3. Inventory: every fuel on the `allFeatures` path

The import closure of `MainSuccessor` is 120 modules. `Logged/WasmStepE.lean` is **not** in it, and
it is not in any `defaultTargets` closure. It is imported only by `Logged/WasmRun` → `Logged/D3L`
(the logged D3 mirror) and by `oracle/wasm-d3/lean/LoggedHarness`. Its proofs cannot affect the
successor checker. No module in the closure uses `partial def`. The `termination_by` uses are
`Wasm/InstrSize.lean` and `Logged/LazyTrie.lean`, and both are proved.

| # | site | fuel and its source | on exhaustion | why it suffices |
|---|---|---|---|---|
| 1 | `Wasm.run` via `StorageExecution.functionCall` | `wasmFuel cfg gas`, from the action's prepaid gas (≤ 300 Tgas); start and method each get it | `unmodeled fuel exhausted` → **out of domain** `e.wasm-α` | §2 (O-W1b…O-W4 open); before W02 this was **insufficient** (§1) |
| 2 | `Wasm.run` via signed `D3.functionCall` (legacy-driver tiers, not `allFeatures`) | legacy `(g/r+2)·64+10⁶` | out of domain | **insufficient** for block-heavy loops; kept so the signed statement does not change |
| 3 | per-step work in `exec`: `memory.fill`/`copy`/`init`, `table.fill`/`init`, `memory.grow` | `for` over `n`, after the bounds check and after the linear fee `n·unit` is charged | n/a (structural) | `n ≤ 128 MiB` (2,048 pages) or `≤` table size, and the fee is paid first |
| 4 | host functions (`Host.lean`, `CryptoHost.lean`) | `for` loops over lengths that `readMemH`/`payPerH` charged and bounds-checked first; utf-8/16 scans bounded by `max_log_len + 1`; `promise_and` by the bytes read | n/a | bounded by memory (≤ 128 MiB) and gas |
| 5 | `Crypto.ripemd160` padding `while` (`Loop.forIn`) | none | n/a | ≤ 63 iterations (`p.size` grows by 1 until `≡ 56 mod 64`) |
| 6 | `instantiate` data/elem init, decoding | `for` over segments/vectors | trap / decode error | each element consumes ≥ 1 input byte; the code is ≤ 4 MiB |
| 7 | curve `powAux`/`smulAux` (alt_bn128, BLS12-381, P-256, secp256k1, Ed25519) | fuel = exponent bit width (256…3,200); a too-large exponent would compute silently wrong (`b^(e mod 2^f)`) | **wrong value** | **proved** for every constant exponent (`altbn_*_fuel`, `bls_*_fuel`, `p256_fuel`, `secp_fuel`, `ed25519_fuel`); variable scalars are 32-byte inputs or reduced mod an order `< 2^256` |
| 8 | `Float.bitLenF`/`F64.bitLenF` (4,096), `isqrtGo` (64), `ChaCha20.bitLen` (64) | constants | wrong value | operands `< 2^2200`, `< 2^128`, `< 2^32` (module docs) |
| 9 | `D2.revealAll`, `LazyTrie.lz` | `revealFuel` = 10,000 levels | node left unrevealed → read reports **missing** (reject) | trie depth ≤ 1 + key nibbles; the longest PV86 key (contract data: 1 + 64 + 1 + 2,048 B) is 4,228 nibbles; nodes are bound to the chain's state root |
| 10 | `TrieStore.lookupFrom` | `4·|key| + 4` nodes | `unmodeled: lookup fuel` → out of domain | path ≤ `2·|key| + 1` nodes (every branch or extension consumes ≥ 1 nibble) |
| 11 | `processWithInstant.drain` | 100,000 instant receipts per receipt | `invalid: nearcore panics (instant receipt fuel)` → **reject** | instant receipts are `PromiseYield` and single-`DeleteAccount` receipts (`receipt.rs:474-486`), each created by a host call costing ≥ ~10¹¹ gas from ≤ 300 Tgas; processing one creates no further instant receipt. So ≤ ~3,000 ≪ 100,000. Argument, not mechanized |
| 12 | `processDelayedLoop` | `next − first + 1` | **silent stop** | every iteration pops one element or returns; nothing pushes the delayed queue in this phase. Argument, not mechanized |
| 13 | `delayPopLWith`, `fwdLoopLWith`, `yieldLoop`, `Pipeline.peekDelayed`, `groupSizesL` | the index range (`next − first (+1)`) | returns the accumulator | structural: the index increments every iteration, and the fuel-0 branch coincides with the loop's own exit |
| 14 | receipt-proof shuffle `genIndex` (`RuntimeCore`, `ReshardCore`) | 64 rejection draws per index | `invalid: shuffle fuel exhausted (probability < 2^-1024)` → **reject** | **probabilistic only**. With `rand 0.8.5`'s u32 zone `(n << lz(n)) − 1` a draw is rejected with probability up to ½ (n = 2^k + 1), so the bound per index is `2^-64`, not the `2^-1024` that the message and `ChaCha20.lean`'s doc claim. Open (O-S1) |
| 15 | bandwidth-scheduler shuffle and `processLoop` | 64 draws; `1 + Σ|increases|` | `invalid: bandwidth scheduler aborted` → **reject** | `processLoop`: one bucket per increase (module doc). Shuffle: as #14 (O-S1) |
| 16 | `ReedSolomon` `chunks_exact` and `Wire`/borsh counts | the length or count | decode error | structural |

**Not on the path:** `TrieBuild.trieFuel` (D0), `ArenaCore` interpreter fuel (challenge layer),
`MainRuntime` and the `oracle/wasm-d3` drivers (legacy budget, test harnesses only).

## 4. Pinned-nearcore stress fixtures (`fuel-stress`)

`NEAR_SUCCESSOR_SCENARIO=fuel-stress gen --domain d3 --seed 2026 --chains 1 --blocks 45 --p-missing 0
--mutate-every 0 --code-mutant-p 0 --ood-cap 100000`: 4 shards, 180 honest chunks, all accepted by
the cold validator. `fuelc.wat` is the contract. `tools/d3/collect_fuel_stress.py` gives
`manifest-f2026.json` (0 problems; each status is nearcore's). `cases.tar.gz` holds the 14 cases
that apply the 16 calls (`cases-index.json` lists the sha256s).

| step | nearcore | Lean before | Lean after | after: wall / max RSS |
|---|---|---|---|---|
| `nops` 300 Tgas, cheapest instruction (~328 M steps) | out of gas, 300.9 Tgas burnt | accept | accept | 38 s / 66 MiB |
| `spin` 300 Tgas (bare `br`) | out of gas | accept | accept | 58 s / 65 MiB |
| `blocks200` 5 Tgas | out of gas | **out of domain (fuel exhausted)** | accept | 99 s / 66 MiB |
| `blocks200` 1 Tgas | out of gas | **out of domain (fuel exhausted)** | accept | 30 s / 65 MiB |
| `blocks4999` 0.3 Tgas (1.7 G steps) | out of gas | **out of domain (fuel exhausted)** | accept | 141 s / 65 MiB |
| `recurse` / `recurse_big` (stack limit: depth 4,096 / 33) | `MemoryAccessViolation` | accept | accept | 0.3 s |
| `memmax`: 2,048 pages, 128 MiB fill, 64 MiB copy | out of gas | accept | accept | 10 s / 393 MiB |
| `memfill_loop`: 64 MiB fills | out of gas | accept | accept | 23 s / 132 MiB |
| `sha_loop` / `host_loop` (`used_gas`, 3.4 M calls) | out of gas | accept | accept | 4 s / 2 s |
| `grow_loop` (`memory.grow 0`, 40 M steps) / `count` (10⁷ iterations, succeeds) | out of gas / value | accept | accept | 11 s / 17 s |
| three `nops` 300 Tgas in one chunk (900 Tgas) | 3 × out of gas | accept | accept | 75 s / 66 MiB |

Blind replay (`blind_corpus.py`, every produced value removed): **14/14 match**, pass
(`replay/blind-report.json`). All 180 honest chunks of the run accept with the new checker
(`replay/fs-all-after.jsonl`, maximum 211 s and 394 MiB). The timings come from a heavily loaded
32-core host (load average around 250) and are upper bounds.

**Runtime scaling (for W16).** Fuel is not the binding limit after this change. Evaluation time is.
The checker runs at about 8–9 M interpreter steps per second. The worst steps-per-gas contract,
`blocks4999`, needs about 5.7·10⁹ steps per Tgas, so a 300 Tgas receipt takes about
1.7·10¹² steps (~55 h). A 1 Pgas chunk of such receipts takes about 5.7·10¹² steps (~7.7 days). The
same gas in the cheapest *costly* instruction takes about 0.33·10⁹ steps (~40 s). A
prover-independent budget must either accept this 10⁴ spread or have the interpreter skip
zero-fee control instructions in bulk, for example by precomputing `block`/`end` runs.

## 5. Corpus verdict movement

The population is the 3,138-case gap census: `nearcore == "ok" ∧ expected_rel_d3 == false` over
d3c7–d3c10. It was run under `allFeatures` with both checkers (`tools/d3/replay_successor.py`):

| checker | accept | reject | out of domain | `fuel` reasons |
|---|---|---|---|---|
| before `29bf5217…` | 3,138 | 0 | 0 | 0 |
| after `8b4dd7c9…` | 3,138 | 0 | 0 | 0 |

Per case, the two runs are set-identical and differ on **0 / 3,138** verdicts and reasons.
`make d3-smoke` also passes on the new tree.

By `successorFuel_moves_only_exhausted`, a census case could move only if it was
`fuel exhausted` before. None was.

## 6. Open items

* O-W1b, O-W2, O-W3 and O-W4 (§2) are what remains between the measured bound and a theorem
  `run (wasmFuel cfg gas) s ≠ fuel exhausted`. O-W4 is the largest: correctness of finite-wasm's
  `optimize`.
* O-S1: the two shuffles (#14, #15) reject a valid chunk with probability `≤ 2^-64` per index, and
  their documented `2^-1024` is wrong. Fix: draw up to 1,024 times and report exhaustion as out of
  domain. Monotonicity in the draw count is the same argument as `run_fuel_le`. This was not done
  here. The receipt shuffle sits in the shared validation shell, where the legacy driver is
  proved definitionally equal to the signed checkers.
* #11 and #12 are argued, not mechanized.
* The signed `D3.functionCall` keeps the insufficient legacy budget (out of domain on the §1
  inputs).
* Evaluation time at protocol scale (§4).

## Reproduce

```
cd spec/lean/v3 && lake build nearspec-v3-check-successor
cd oracle/wasm-d3/lean && lake build nearspec-v3-fuel-probe
# probe input lines: `<label> <prepaid_gas> <wasm_file> [method]`
nearspec-v3-fuel-probe --check-potential [--legacy-check] < LIST
python3 tools/d3/collect_fuel_stress.py --source RUN --out manifest.json
python3 tools/mainnet-replay/blind_corpus.py --binary CHECKER --cases LIST --out OUT --tier allFeatures
```
