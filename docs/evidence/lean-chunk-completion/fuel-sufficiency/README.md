# Fuel sufficiency theorem (W02, workplan item 3, 2026-10-30)

Lean: `spec/lean/v3/NearSpecV3/Wasm/FuelSufficiency.lean`. It is a default build target
(`lakefile.toml` `defaultTargets`), so CI compiles it. There is no `sorry`. The axiom audit
(`axioms.txt`, printed by every build of the module) lists only `propext`, `Classical.choice` and
`Quot.sound`. **No definition was changed**: the checker, `wasmFuel`, `run` and `runCallWithLimits`
are untouched. No verdict can move, so no fixture family or before/after verdict table is needed
(rules: those are required for *semantic* changes). Tier scope: the theorem is about the
successor budget `wasmFuel`, which is what `--tier allFeatures` uses (`Successor/StorageExecution.lean`,
`fuel := wasmFuel cfg gas` with `prepaidGas := gas`). The signed `D3.functionCall` keeps
`legacyFuel` and is **not** covered; its worst-case-loop exclusion is workplan item 6b.

## What is proved

Potential: `Φ(s) = K·⌊g/r⌋ + Σ_frames (K·rest(pc) + free(pc))`, with `K = freeStepFactor cfg =
2·max_blocks_per_function + 2` and `r = regular_op_cost`. `free(pc)` is O-W1/O-W3's count of
zero-fee control instructions after `pc`. `rest(pc)` is O-W4's prepaid credit: the costly
instructions the current finite-wasm group still runs without a further charge.

| theorem | statement |
|---|---|
| `step_dec` | `Certified cfg p cd → HostsOK → 0 < r → Inv cd s → step cfg p s = .cont s' → Inv cd s' ∧ s'.gas.prepaid = s.gas.prepaid ∧ Φ s' + 1 ≤ Φ s` |
| `run_stable` | under the same hypotheses, `Φ s < n → n ≤ m → run cfg p m s = run cfg p n s` |
| `run_from_step` | `Φ s < n → ∃ t, run cfg p n s = step cfg p t ∧ ∀ u, step cfg p t ≠ .cont u`: the result is a real step's terminal result, never the step budget |
| `callEntry_stable` / `callEntry_run_from_step` | the same for a wasm entry (`start` or method) whose state has `prepaid ≤ gas`, at fuel `wasmFuel cfg gas`; the entry potential is `≤ K·⌊prepaid/r⌋ + F < wasmFuel` |
| `runCallWithLimits_stable`, **`wasmFuel_sufficient`** | for every `cfg` with `0 < r`, `HostsOK`, and `CodeCertified cfg code blockLevel`: `∀ m ≥ wasmFuel cfg ctx.prepaidGas, runCallWithLimits cfg code method ctx m … = runCallWithLimits cfg code method ctx (wasmFuel cfg ctx.prepaidGas) …` |

So, given the two named hypotheses, the step budget never decides an outcome of the successor's call:
no execution can become `unmodeled fuel exhausted` because of it. This covers both entries
(`start` and the method), including the prepaid-gas bookkeeping between them (`instantiate_gas`,
`callEntry_prepaid`, `step_fin_prepaid`).

## Obligations

| obligation | status |
|---|---|
| O-W1a (free steps advance or pop) | proved before; now also part of `exec_dec` |
| **O-W1b** (`else` jumps forward) | **proved** relative to the certificate: `exec_dec` (`else_` arm) uses `moveOK`'s `pc < target` and the label correspondence `FrameInv` (runtime labels = the certificate's static label stack, an invariant of every step) |
| **O-W2** (a costly step raises `free` by ≤ F; frames only change by call/return) | **proved for every `exec` arm** (`exec_data` for the 35 data instructions, `exec_dec` for the 12 control/call arms, `enter_spec`, `doBr_spec`, `doReturn_spec`). For **host functions** it is the hypothesis `HostsOK` (a host keeps `frames` and `prepaid` and does not raise `remaining`): **open** (one case per host arm, 89 + 14 arms; the `Logged/WasmCR` `cr` tactic shows the shape such a proof takes) |
| **O-W3** (`free ≤ 2·max_blocks_per_function + 1`) | checked per function by `certOK` (`free.all (≤ 2B+1)`), so used as a certificate fact, not derived from `prepare`'s block count |
| **O-W4** (charges happen before execution) | **runtime half proved**: at a live charge point the charge pays `r` per costly instruction of the group (`fee.c ≥ r·grp`), and jump targets, call returns and function entries need no credit (`rest = 0`). `div_pay` and `step_dec` turn that into the `Φ` decrease. **Static half open**: that `gasTable` (finite-wasm `optimize`) and `matchBlocks` output always pass `certOK` for code `prepare` accepts (`CodeCertified`) is not proved in general. It is decidable per contract and measured below |

`HostsOK` and `CodeCertified` are explicit hypotheses of `wasmFuel_sufficient`, not axioms.

## The certificate (`certOK`, built by `buildCert`)

For each function: `free` and `rest` (backward passes), the static label stack per `pc` (the forward
pass of `matchBlocks`' open stack, targets from `endOf`), and liveness (finite-wasm's `poly`
flag). `certOK` checks them with local, linear-time conditions. The builder is untrusted
code: only `certOK` is used by the proofs. Dead code (after `br`/`return`/`unreachable`) is
exempt from the fee and move checks. This is needed: finite-wasm does emit charge points there
(for example an adjusted loop header in dead code) whose fee does not cover the dead group.

## Measurement of `CodeCertified` (`nearspec-v3-fuel-cert`, `oracle/wasm-d3/lean/FuelCert.lean`)

Binary sha256 `941878300f9c7224…`. The configuration is the successor's (`floatPv86` with curve hosts and global actions). Populations:
every distinct module in every `witness.bin` under `/data/illia/nearproof-deps/corpora` and in the
evidence tarballs (`tools/d3/extract_witness_wasm.py`: 236,871 witnesses → 4,744 distinct blobs,
of which 2,532 prepare. This includes `fuelc.wat`'s `blocks4999`, which is at the `max_blocks_per_function`
bound). Also `gen_d3a.py` random typed contracts, 2,000 each for seeds 7, 11, 13 and 17, and the
9,175 `opcases.py` operator and limit cases.

| population | prepared modules | functions | modules failing `certOK` | breakage control: modules failing |
|---|---|---|---|---|
| corpus + evidence witnesses | 2,532 | 35,923 | **0** | 2,511 |
| gen_d3a seed 7 | 2,000 | 5,037 | **0** | 2,000 |
| gen_d3a seed 11 | 2,000 | 4,980 | **0** | 2,000 |
| gen_d3a seed 13 | 2,000 | 5,065 | **0** | 2,000 |
| gen_d3a seed 17 | 2,000 | 4,986 | **0** | 2,000 |
| opcases | 9,142 | 20,153 | **0** | 9,124 |
| **total** | **19,674** | **76,144** | **0** | 19,635 |

Deliberate-breakage control (`--break`): every charge point is under-charged by one
`regular_op_cost`. The check then rejects 19,635 of 19,674 modules, every one at a `fee < r·grp`
position. The modules that still pass have no charge point whose fee is exactly `r·grp`, for example
only loop headers, which carry an extra `r`. Per-module rows: `cert-census.jsonl.gz` and
`break-control.jsonl.gz`. Totals: `census-summary.txt`.

No counterexample to O-W1b…O-W4 was found, so `wasmFuel` is unchanged.

## Open, with reasons

1. **`HostsOK`** (O-W2, host arms). It needs a per-arm proof over `Host.lean`, `CryptoHost.lean`
   and `TrieAccounting`. That is a relational `EStateM` tactic of the `Logged/WasmCR` kind and was not
   built in this lane.
2. **`CodeCertified` for all prepared code** (O-W4 static half, O-W3 from `prepare`). It needs
   `prepare = .ok p` ⇒ `validateBody` succeeded for every body (through `earlyPass`'s monad), plus
   correctness of `matchBlocks`, finite-wasm's frame/`poly` tracking, `gAdjust`, and both `optimize`
   passes. It is measured: 76,144 functions, 0 failures.
3. The theorem is stated at `runCallWithLimits`. `StorageExecution.functionCall` passes exactly
   `wasmFuel cfg gas` with `prepaidGas := gas` (`StorageExecution.lean:138-140`). That link is by
   inspection, not a Lean lemma over the monadic chunk pipeline.

## Reproduce

```
cd spec/lean/v3 && lake build NearSpecV3.Wasm.FuelSufficiency     # prints the axiom audit
cd oracle/wasm-d3/lean && lake build nearspec-v3-fuel-cert
python3 tools/d3/extract_witness_wasm.py OUT /data/illia/nearproof-deps/corpora docs/evidence/lean-chunk-completion
ls OUT/*.wasm | nearspec-v3-fuel-cert [--break]
```
