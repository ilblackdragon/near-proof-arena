# Fix: `current_contract_code` on global-contract accounts (completeness, 2026-10-31)

The [host-rows population](../README.md) showed that Lean rejected 205 nearcore-accepted cases:
on an account that uses a global contract, Lean's `current_contract_code` returned 1, where
nearcore returns 2 or 3. This package fixes that on the successor path. The coordinator
pre-approved it as a completeness fix toward nearcore.

The coordinator also asked to keep the signed tier unchanged, or show it cannot move.

## 1. Change

nearcore builds `VMContext.account_contract` from the receiver's current `account.contract()`
(`runtime/runtime/src/function_call.rs:275`). `current_contract_code`
(`runtime/near-vm-runner/src/logic/logic.rs:4000-4030`) then returns:

| account contract | return value | register |
|---|---|---|
| none | 0 | — |
| local, hash `h` | 1 | `h` |
| global by hash, hash `h` | 2 | `h` |
| global by account id `a` | 3 | the bytes of `a` |

Lean, `spec/lean/v3/NearSpecV3/`:

- `Wasm/Machine.lean`: `CallCtx` gains `accountContractTag : Nat := 1`, the return value when
  `accountContract = some _`.
- `Wasm/Host.lean` (`current_contract_code`): `some h` now writes `h` to the register and
  returns `ctx.accountContractTag`. Before, it always returned 1. `none` still returns 0.
- `Successor/StorageExecution.lean`:
  - new `ctxContract : D2.Contract → Option ByteArray × Nat`, with exactly the table above;
  - the successor `functionCallRecordedF` sets `accountContract`/`accountContractTag` from
    `acct.contract`, the receiver's current account in the receipt. Before, it set
    `some (resolved code hash)`.
- The proof-side copies of the same engine get the same two lines, so the existing equality and
  refinement proofs still go through unchanged:
  - `Successor/StorageExecutionOrig.lean` (`TierFlagsEq`);
  - `Successor/TierWhole.lean`;
  - `Successor/TierO4NS.lean` and `Successor/TierO4NSSim.lean`.

A side effect, also toward nearcore: for a pre-PV83 legacy ETH-wallet magic hash, the register now
gets the account's own hash, not the redirected wallet hash, because nearcore reads
`account.contract()` before any redirect. No fixture holds such an account (row `L0-D3-006`).

**Signed tier: it cannot move.**
- The signed engines are untouched: `D3/FunctionCall.lean`, `Logged/D3L.lean` and the
  `TierFloats` D3-hook copy still build `accountContract := some hash` and never set the new
  field. So their `accountContractTag` is the default 1, and the arm computes exactly
  `regSetH a[0] h; pushRet 1`, as before.
- Independently, the signed statement excludes global contracts (D3α), so 2 and 3 could not arise
  there anyway.
- Measured: the signed replays of the census and the committed fixtures are identical, case by
  case, in verdict and reason (§3).

**Build.** The full default build (`lake build`, all `defaultTargets`, 424 jobs) passes, as does
`nearspec-v3-check-successor`. There is no `sorry`. Every `depends on axioms` line lists a subset
of `propext`, `Classical.choice`, `Quot.sound`.

Binaries (sha256):

| | sha256 |
|---|---|
| new checker `nearspec-v3-check-successor` | `ee00c9183a1650c6fcb210796e98788310ef61ae1870a720d30d2b0440c57a29` |
| new control build (`tools/d3/l0_ctl_patch.py` over the same tree) | `055cc374b213a5c6874d881a398d0a04c95114bed85ce2abed868932633b4c20` |
| before / breakage control: Gate-B freeze checker | `9b583e3a42e6bb50edf5ec8557fea7e30b9f0a01d72724f688aac15929b233f8` |

## 2. The host-rows population, before / after (`allFeatures`)

11,437 cases, 4 seeds (811–814), every one judged by cold pinned nearcore 2.13.4:

| Lean verdict vs nearcore | before (freeze checker) | after (new checker) |
|---|---|---|
| accept / accept | 2,911 | 3,116 |
| reject / reject | 8,321 | 8,321 |
| **reject / accept** | **205** | **0** |
| accept / reject | 0 | 0 |

- All 205 cases moved from reject to accept: 16 honest chunks and 189 mutants that nearcore
  accepts. The replay passes.
- 261 nearcore-rejected mutants keep the reject verdict but change reason. These are mutants of
  the same chunks: before, they failed at the post-state root; now they fail at the check the
  mutation targets.
- The control build with the trace on gives verdicts and reasons identical to the new checker on
  11,437/11,437.
- The 150 committed host-rows cases (`../cases.tar.gz`), replayed from the extracted files: 150/150
  agree, against 134 before.

**Breakage control: the current (freeze) checker.** On the same population it disagrees with
nearcore on exactly the 205 cases above, so the comparison detects removal of the fix. In
particular, every chunk where nearcore's `ccc` returned 2 or 3 is rejected (16/16).

## 3. Census, fixtures and corpus sample, before / after

Before: the Gate-B freeze replays (`gateb-freeze-2368b8713`), same case lists. After: the new
checker. "Moved" counts cases whose (verdict, reason) changed.

| population | tier | before | after | moved |
|---|---|---|---|---|
| 3,138 gap census | `allFeatures` | 3,138 accept | 3,138 accept | 0 |
| 3,138 gap census | `signed` | 735 accept / 2,403 out of domain | same | 0 |
| 1,364 committed fixtures (`fixtures-final.txt`) | `allFeatures` | 819 accept / 527 reject / 18 out of domain, all agreeing | same | 0 |
| 1,364 committed fixtures | `signed` | 434 accept / 421 reject / 509 out of domain | same | 0 |
| corpus 1-in-8 sample (29,465 of 235,716: every 8th line of `corpus-cases.txt`) | `allFeatures` | 9,602 accept / 19,853 reject / 10 out of domain (named exclusions), all verdicts agreeing | same | 0 |

No population has a Lean accept of a nearcore reject, before or after.

## 4. Row evidence

The new control build reruns the trace, map and per-row ablation of the 16 host rows on the
host-rows population. The first-pass populations never call `current_contract_code`, so their
traces are unaffected.

| row | nearcore-accepted | nearcore-rejected | disagreements | control flips |
|---|---|---|---|---|
| `current_contract_code` | 369 | 542 | 0 | 12/16 |
| `promise_set_refund_to` | 412 | 592 | 0 | 12/16 |
| `promise_batch_action_add_gas_key_with_full_access` | 291 | 307 | 0 | 12/16 |
| the other 13 host-rows rows | unchanged | unchanged | 0 | unchanged (10–12/16) |

`current_contract_code` is now `validated`.

## Files

- `before-after.json`: per-population before/after verdict counts and moved cases
  (`tools/d3/l0_before_after.py` output).
- `after-host-rows-results.jsonl.gz`: the new checker's rows on the host-rows population.
- `trace-new.jsonl.gz`, `map-hr2.json.gz`: the new control build's trace and exercise map.
- `ablate-hr2.json`: the 16 controls with the new control build.
