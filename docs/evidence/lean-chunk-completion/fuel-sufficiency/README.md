# Fuel sufficiency theorem (W02, workplan item 3, 2026-10-30, general proof 2026-10-31)

## Status after round 3 (2026-10-31): general proof, guard retired

`wasmFuel` is proved sufficient for **every** contract, without the `CodeCertified` hypothesis, and
the `w.fuel_certificate` guard is gone from the checker. Axioms everywhere: `propext`,
`Classical.choice`, `Quot.sound` (`axioms.txt`). No `sorry`. Every module below is a default build
target (`lakefile.toml`); the full default `lake build` is green (437 jobs).

**Final theorem** (`Successor/FuelFinal.lean`):

```lean
theorem functionCall_fuel_sufficient (fl : Flags) (cfg : NearCfg) (hr : 0 < cfg.regularOpCost)
    (hl : cfg.regularOpCost ≤ cfg.linearOpBaseCost) (F : NearCfg → Nat → Nat)
    (hF : ∀ g, wasmFuel cfg g ≤ F cfg g) :
    functionCallRecordedF fl F cfg = functionCallRecorded fl cfg
```

`functionCall_fuel_sufficient_pv86` discharges `hr`/`hl` at PV86 (822,756 ≤ 26,328,192). The new
hypothesis `hl` is the only assumption beyond round 2's.

**General VM theorem** (`Wasm/FuelGeneral.lean`, namespace `Wasm.FuelGen`):

```lean
theorem wasmFuel_sufficient {cfg : NearCfg} (hr : 0 < cfg.regularOpCost)
    (hl : cfg.regularOpCost ≤ cfg.linearOpBaseCost) (code : ByteArray) (method : String)
    (ctx : CallCtx) (k : Nat) (full : Bool) (real : Option TTN.RealStore) :
    runCallWithLimits cfg code method ctx (wasmFuel cfg ctx.prepaidGas + k) true full real =
      runCallWithLimits cfg code method ctx (wasmFuel cfg ctx.prepaidGas) true full real
```

It rests on `prepare_fnOK` (every function `prepare` outputs satisfies `FnOK`: the nesting `NestOK`
at `openAt`, finite-wasm's table charging every group before it runs `WC`, and at most
`2·max_blocks_per_function + 1` free instructions), built from `FuelNest` (`validateBody_wellNested`,
`prepare_funcs`, `nestOK_of_wellNested`, `freeCount_le_of_wellNested`) and `FuelGas*` (`wc_gasTable`,
the O-W4 static half), and on main's `hostsOK` for the host arms.

**Guard deadness** (`Wasm/FuelCertOK.lean`, `Successor/FuelFinal.lean`):

```lean
theorem certOK_of_static (cfg : NearCfg) (pf : PFunc) (hw : WellNested pf.code)
    (hn : NestOK pf (openAt pf.code)) (hwc : WC cfg pf (openAt pf.code))
    (hfree : freeCount pf.code ≤ 2 * cfg.maxBlocksPerFunction + 1) :
    certOK cfg pf (buildCert cfg pf) = true                      -- FnOK → certOK
theorem fuelCertified_true {cfg : NearCfg} (hr : 0 < cfg.regularOpCost)
    (hl : cfg.regularOpCost ≤ cfg.linearOpBaseCost) (code : ByteArray) :
    fuelCertified cfg code = true
theorem vmCallGuarded_eq (cfg : NearCfg) (hr : 0 < cfg.regularOpCost)
    (hl : cfg.regularOpCost ≤ cfg.linearOpBaseCost) (fuelOf : NearCfg → Nat → Nat) :
    vmCallGuarded fuelOf cfg = vmCall fuelOf cfg
```

`vmCallGuarded` is the round-2 `vmCall` verbatim (certificate first, `w.fuel_certificate` on
failure). `certOK_of_static` matches the certificate with the static facts: `free` is the suffix
count of free instructions, `rest` is `req`, the label stack is `labelsOf (openAt ·)`, and liveness is
sound (a live position is `Live`) and closed under the successors `moveOK` checks.

### Provenance and integration

The proof is branch `worktree-agent-a16ff044a4ee5abb2` (`a250d3b58`…`a5a4263fa`, with the
`aa6deac1` FuelNest and `a413fb1c` `wc_gasTable` branches), brought onto main under these names:

| branch module | on main | change |
|---|---|---|
| `FuelDefs`, `FuelNest`, `FuelGas`, `FuelGasFin/Inv/Opt/Scan/Sem` | same names | `FuelDefs` imports `FuelCert` and `FuelHostDefs` and drops its duplicate `fallsThrough` and its `HostOK` |
| `FuelSuff`, `FuelCall` | same names, namespace `Wasm.FuelGen` | their names clashed with main's `FuelSufficiency` (`Inv`, `run_stable`, `runCallWithLimits_stable`, …); they take main's `HostsOK` |
| `FuelSufficiency` | `Wasm/FuelGeneral.lean`, namespace `Wasm.FuelGen` | uses main's `hostsOK` |
| `FuelHost`, `FuelHostBase` | **dropped** | duplicate of main's `FuelHost`/`hostsOK` |

Reusing main's `hostsOK`: the branch's `HostOK` asked a host arm not to lower `gas.used`; main's
`HostsOK` (`HostMono`) asks it not to raise `gas.remaining`. `FuelSuff.callHost_cont` uses only the
latter (the omega step now reads `remaining`), so the weaker, already proved statement suffices.
`HostMono`, `HostsOK` and the four `Keeps` facts `FuelHost` needs moved to a new
`Wasm/FuelHostDefs.lean`, so `FuelHost` no longer imports the certificate proof. `FuelNest`'s
`gen_forIn h => x hx` helper syntax replaced `gen_forIn h as x hx`, which had made `as` a token and
broke `a :: as` patterns in `L0GuardSubsumption`.

### Builder change (`Wasm/FuelCert.lean`)

`certOK` (the check) is unchanged; the builder `buildCert` is not trusted and was rewritten:

* liveness is now **reachability**: the least set containing the entry and closed under the
  successors `moveOK` checks (`succsAt`), computed by forward passes until stable (at most
  `code.size + 1` passes, `liveIter_fix`). Round 2 used finite-wasm's unreachability flag
  (`GF.poly`). That flag marks live code that no execution reaches (for example the code after
  `block … unreachable … end` when no branch targets the block), so `certOK` then also checked
  finite-wasm's fees there. `WC` only speaks about `Live` positions, so that stronger check is not
  derivable from `FnOK`; it is true on every measured module (round-2 census) but not proved.
* labels are recorded at every position `0 … n` (round 2: `0 … n-1`); `free`/`rest` are the same
  values as tail-recursive `fillBack` passes.

So `fuelCertified_true` and `vmCallGuarded_eq` are about the current builder. The **removed** guard
in the round-2 checker used the old builder; that it never fired is the measurement below (the
round-2 census over every distinct corpus module plus the replay), not a theorem.

### Relation change: guard removed

`vmCall` (`Successor/StorageExecution.lean`) is now `.ok (runCallWithLimits …)`; the
`w.fuel_certificate` out-of-domain reason no longer exists (`escG2` stays in the O4 escape set,
unproduced). Tier proofs `TierO2.vmF_curve`, `TierO3Call.vmF_global`/`vmCall_lowQ`,
`TierWholeWalk.recRefine_floats` and `TierO4NSSim.tail_rel` lost their certificate case. The L0
control patch (`tools/d3/l0_ctl_patch.py`) no longer instruments `vmCall` (`wasm:fuelcert` retired).

Before/after. Before = main `e575746aa` checker `nearspec-v3-check-successor` (the control, with the
guard), sha256 `0b0f01ec382faf1efb70839954c130677d171198331f44c15d043f38e6fe8833`. After = this
branch, sha256 `461a7cd9718a7af496586ef8f491f2af0baef0e74c4998f7bcd74f8c0f1cef55`. Input: a seeded
(`random.Random(20261031)`, `r3-mksample.py`) 1-in-8 sample of every corpus population (all 224
warm originals) plus the 338 evidence-fixture cases of round 2: 30,028 cases (`r3-sample-cases.txt.gz`),
tier `allFeatures`.

| population | cases | accept (before → after) | reject | out of domain | `w.fuel_certificate` before | moved |
|---|---|---|---|---|---|---|
| d1run | 6,631 | 1,828 → 1,828 | 4,803 → 4,803 | 0 → 0 | 0 | 0 |
| d2corpus.v2 | 8,423 | 2,382 → 2,382 | 6,041 → 6,041 | 0 → 0 | 0 | 0 |
| d2corpus.v2-warm-originals | 224 | 0 → 0 | 224 → 224 | 0 → 0 | 0 | 0 |
| d3c10 | 2,069 | 790 → 790 | 1,279 → 1,279 | 0 → 0 | 0 | 0 |
| d3c7 | 4,156 | 1,597 → 1,597 | 2,558 → 2,558 | 1 → 1 | 0 | 0 |
| d3c8 | 6,187 | 2,327 → 2,327 | 3,853 → 3,853 | 7 → 7 | 0 | 0 |
| d3c9 | 2,000 | 761 → 761 | 1,238 → 1,238 | 1 → 1 | 0 | 0 |
| evidence fixtures | 338 | 164 → 164 | 174 → 174 | 0 → 0 | 0 | 0 |
| **total** | **30,028** | | | | **0** | **0** |

Verdicts and reasons are identical row for row (`r3-before-after.txt`, `r3-rows-before.jsonl.gz`,
`r3-rows-after.jsonl.gz`, `compare-r3.py`). With the round-2 census (every distinct module of all
236,871 corpus witnesses passes the old certificate, below), no corpus case can move.

Coverage: `L0-AF-fuel-certificate` is `impossible-at-boundary` with `fuelCertified_true` and
`vmCallGuarded_eq` as evidence (`tools/d3/lean_chunk_coverage.py`; `--check` passes). `L0-W-011`
cites `buildCert_live` (formerly `buildLblLive_live`).

Not re-run: the `nearspec-v3-fuel-cert` census tool (`oracle/wasm-d3/lean/FuelCert.lean`) uses
`buildCert`, so a rebuild of it now checks the reachability certificate; the census tables below are
the round-2 measurement with the old builder.

## Reproduce (round 3)

```
cd spec/lean/v3 && lake build NearSpecV3.Successor.FuelFinal   # FuelGeneral, FuelCertOK; prints the axioms
python3 docs/evidence/lean-chunk-completion/fuel-sufficiency/r3-mksample.py cases.txt
python3 docs/evidence/lean-chunk-completion/fuel-sufficiency/runck.py BEFORE cases.txt before.jsonl allFeatures 8
python3 docs/evidence/lean-chunk-completion/fuel-sufficiency/runck.py AFTER cases.txt after.jsonl allFeatures 8
python3 docs/evidence/lean-chunk-completion/fuel-sufficiency/compare-r3.py before.jsonl after.jsonl
```

(`r3-mksample.py` reads the fixture case list from round 2's `guard-sample-cases.txt`; those
directories are the extracted evidence tarballs.)

---

Rounds 1 and 2 follow unchanged as the record. Where they say `vmCall` runs `fuelCertified`, or
that `CodeCertified` is open, round 3 supersedes them.

## Round 1–2 preamble (2026-10-30)

Lean: `spec/lean/v3/NearSpecV3/Wasm/FuelSufficiency.lean`. It is a default build target
(`lakefile.toml` `defaultTargets`), so CI compiles it. There is no `sorry`. The axiom audit
(`axioms.txt`, printed by every build of the module) lists only `propext`, `Classical.choice` and
`Quot.sound`. **No definition was changed**: the checker, `wasmFuel`, `run` and `runCallWithLimits`
are untouched. No verdict can move, so no fixture family or before/after verdict table is needed
(rules: those are required for *semantic* changes). Tier scope: the theorem is about the
successor budget `wasmFuel`, which is what `--tier allFeatures` uses (`Successor/StorageExecution.lean`,
`fuel := wasmFuel cfg gas` with `prepaidGas := gas`). The signed `D3.functionCall` keeps
`legacyFuel` and is **not** covered; its worst-case-loop exclusion is workplan item 6b.

## Status after round 2 (2026-10-30): item 3 closed (superseded by round 3)

**Final theorem** (`NearSpecV3.Successor.StorageExecution.functionCall_fuel_sufficient`,
`spec/lean/v3/NearSpecV3/Successor/FuelFinal.lean`, a default build target):

```lean
theorem functionCall_fuel_sufficient (cfg : NearCfg) (hr : 0 < cfg.regularOpCost)
    (F : NearCfg → Nat → Nat) (hF : ∀ g, wasmFuel cfg g ≤ F cfg g) :
    functionCallRecordedF F cfg = functionCallRecorded cfg
```

The successor's `FunctionCall` hook is `functionCallRecorded = functionCallRecordedF wasmFuel`
(`functionCallRecorded_fuel`, `rfl`). It computes, on every input, exactly what it computes under
any larger step budget `F`. The budget therefore never decides an `allFeatures` verdict. The only
hypothesis beyond the hook's inputs is `0 < regular_op_cost`, which `functionCall_fuel_sufficient_pv86`
discharges for every configuration with the PV86 cost of 822,756. Axioms: `propext`,
`Classical.choice`, `Quot.sound` (`axioms.txt`). There is no `sorry`.

How the three round-1 hypotheses were discharged:

1. **`HostsOK`: proved** (`Wasm/FuelHost.lean`, `hostsOK`, about 1,035 lines). There is one
   generated theorem per arm: 75 `hostCall` arms and 14 `cryptoHostCall` arms. The relation
   `HOR r x` is a port of `Logged/WasmCR`'s `cr` approach: a successful run from any state that is
   `HostMono` from `r` ends `HostMono` from `r`. That also covers hosts that write back an earlier
   state. Gas operations use `GOK` (no-error `burn`/`deduct`/`payPer`/`payAction`/`TTN.commit` keep
   `prepaid` and do not lower `used`). Storage operations use `TOK` (`storageWrite`/`Remove`/`Read`/`HasKey`).
   No arm was found non-monotone. The generator is `gen_fuel_host.py`, with `host-arms.txt` and
   `crypto-arms.txt`.
2. **`CodeCertified`: made a checked condition.** This changes the relation; the evidence is below.
   The successor's VM call is now `vmCall` (`Successor/StorageExecution.lean`). It runs
   `fuelCertified cfg code` (`Wasm/FuelCert.lean`: `prepare`, then `prepCertOK`) and reports
   `out of domain (e.wasm-α): w.fuel_certificate …` if any prepared function fails the certificate.
   Otherwise it runs `runCallWithLimits` as before. `fuelCertified_codeCertified` turns the check into
   the hypothesis. The signed tier (`D3/FunctionCall.lean`) is untouched.
3. **The `wasmFuel`/`prepaidGas` link: proved by construction.** `vmCall` passes
   `fuelOf cfg ctx.prepaidGas`, the hook builds `ctx` with `prepaidGas := gas`, and the theorem is
   stated about the hook itself (`functionCallRecordedF F` vs `functionCallRecorded`), so there is no
   inspection step left. The refactor (`functionCallRecordedF`, `vmCall`) is otherwise
   definitional.

### Why `CodeCertified` was not proved in general

A general proof needs four layers, each of them a long proof about monadic code:

- (a) `prepare cfg code b = .ok p` implies `validateBody` succeeded for each body. That has to be
  traced through `earlyPass`'s `StateT PS (ReaderT ByteArray (StateT Nat (Except PE)))` section
  loop, `boundedP` sub-parsers and the code-section `for`.
- (b) Validation implies balanced nesting, with `matchBlocks`' `endOf`/`elseOf` matching the
  validator's control frames and the final `end` last. No such lemma exists for `checkInstr`'s
  control stack.
- (c) For finite-wasm's `gasTable` (a `StateM GS` fold over the code): which raw points sit at which
  offset; `gAdjust` rewriting earlier points by index, in particular the loop `pre`/`post` marks;
  the frame `poly` flag; then two `optimizeWith` folds whose merge conditions decide group
  boundaries; then the `set!` table.
- (d) The correspondence of (c)'s frame stack and dead-code flag with the certificate's label
  stack and liveness.

None of (a)–(d) has supporting lemmas in the tree. Each round trip of a lemma about these folds
costs minutes of elaboration on the shared host. I judged it out of reach within this lane, and the
coordinator's alternative (a checked guard) applies. The general proof remains a possible
strengthening: it would make the guard provably dead code.

### Guard evidence (relation change)

Checkers built from this branch: before = `HEAD` `StorageExecution.lean` (sha256 `f40158a4bb72…`),
after = with `vmCall` (sha256 `12f2fbbdca3c…`). The input set (`guard-sample-cases.txt`) is a seeded
sample (`random.Random(20261030)`) of 2,000 cases from each of `d1run`, `d2corpus.v2`, `d3c7`,
`d3c8`, `d3c9` and `d3c10`, all 224 `d2corpus.v2-warm-originals` cases, and all 338 case
directories in the evidence fixture tarballs: 12,562 cases in total. Tier: `allFeatures`.

| population | cases | accept (before → after) | reject | out of domain | moved |
|---|---|---|---|---|---|
| d1run | 2,000 | 541 → 541 | 1,459 → 1,459 | 0 → 0 | 0 |
| d2corpus.v2 | 2,000 | 523 → 523 | 1,477 → 1,477 | 0 → 0 | 0 |
| d2corpus.v2-warm-originals | 224 | 0 → 0 | 224 → 224 | 0 → 0 | 0 |
| d3c7 | 2,000 | 781 → 781 | 1,218 → 1,218 | 1 → 1 | 0 |
| d3c8 | 2,000 | 746 → 746 | 1,250 → 1,250 | 4 → 4 | 0 |
| d3c9 | 2,000 | 763 → 763 | 1,236 → 1,236 | 1 → 1 | 0 |
| d3c10 | 2,000 | 735 → 735 | 1,259 → 1,259 | 6 → 6 | 0 |
| evidence fixtures | 338 | 164 → 164 | 174 → 174 | 0 → 0 | 0 |
| **total** | **12,562** | | | | **0** |

Verdicts and reasons are identical row for row (`guard-before-after.txt`, `rows-before.jsonl.gz`,
`rows-after.jsonl.gz`). The guard can only fire on a contract whose prepared functions fail
`certOK`. The full-corpus census in §Measurement below covers every distinct module in every
corpus witness (236,871 witnesses) and found none. So the unsampled corpus cases cannot move
either, by the same function (the `fuelCertified` configuration differs from the census's only in
the float and host flags, and those do not affect a prepared module's gas table).

**Deliberate-breakage control** (`checker-broken`, sha256 `b6796a5e6b08…`): `fuelCertified`
checks a copy of the prepared module with every charge under-charged by one `regular_op_cost`.
The control ran on 1,200 cases (300 each from `d3c7`, `d3c8`, `d3c9`, `d3c10`;
`rows-broken.jsonl.gz`):

| after verdict | broken verdict | reason `w.fuel_certificate` | cases |
|---|---|---|---|
| accept | out of domain | yes | 348 |
| reject | out of domain | yes | 239 |
| accept | accept | no | 89 (no failing call executed) |
| reject | reject | no | 522 (rejected before any call ran) |
| out of domain | out of domain | no | 2 |

So the guard fires on 587 of 1,200 cases and only ever moves a verdict to out of domain, never to
accept. (A reject → out-of-domain move under the control is expected: the case is rejected
later than the call.) No new chunk family is needed. The guard has no positive fixtures in the
sense of contracts that fail the certificate, because none exist in any population; the census
and the control are the evidence that it is live. Performance cost: one extra `prepare` per
`FunctionCall` action.

## Round 1 (conditional theorem)

### What is proved

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

## Open after round 1 (all three closed in round 2, see the top of this file)

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
