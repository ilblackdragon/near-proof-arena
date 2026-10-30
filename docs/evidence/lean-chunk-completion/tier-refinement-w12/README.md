# W12 tier refinement, obligations O1–O7 (workplan item 5, 2026-10-30)

Lean: `spec/lean/v3/NearSpecV3/Successor/{TierFloats,TierHooks,TierRefine}.lean`. `TierRefine` is a
default `lake build` target (`lakefile.toml`) and imports the other two. No `sorry`. The axiom
audit (`#print axioms` from the build log) is in `axioms.txt`: only `propext`, `Classical.choice`,
`Quot.sound`. Build log excerpt: `build.log`.

**No definition was changed and no verdict can move** (first session; the second session's flag
refactor of `StorageExecution` is proved equal to the old engine and measured, §6). The new files add theorems and two
helper definitions, `Wasm.earlyPassWith` and `D3.functionCallWith`. Each is a verbatim copy of an
existing body with its configuration-dependent calls taken as parameters. `earlyPass_eq_with` and
`functionCall_eq_with` prove they equal the originals by `rfl`, so a drift breaks the build. The
checker binaries, `checkD3`/`RelD3` and every tier's checker are the same terms as before. For that
reason there are no new fixtures and no before/after verdict table. The rules ask for those only
for semantic changes, and this work makes none. `make pin-check` is unaffected (no oracle or signed
source touched).

## 1. Relation

`Refines x y` (`TierProofs.lean`, unchanged) means `x = y`, or `x` is an exclusion
(`out of domain …`). Where the lower checker accepts or rejects (error string included), the higher
one returns exactly the same result. `Tier.verdict_of_refines` is the verdict-level reading.

## 2. Status of O1–O7

| id | obligation | status | theorems |
|---|---|---|---|
| O1 | floats | **proved at every configuration** (2026-10-30: the whole-state engine too, §5) | `Lift.floats` (`TierWholeWalk.lean`), `Lift.floats_legacy`, `relSuccessor_floats_mono`, `relSuccessor_protoGas_floatsProtoGas`, `relSuccessor_genesis_genesisFloatsProtoGas` |
| O2 | curve hosts | **proved at every whole-state configuration** (2026-10-30, third session, §7) | `Lift.curveHosts`, `relSuccessor_storageResolution_curveHosts`, `relSuccessor_globalActions_curve` (`TierO2.lean`) |
| O3 | global actions | **proved on claims whose shard layouts are well formed** (2026-10-30, seventh session, §15; the §9 hypothesis `LayoutsWF`, shown to hold on real chunks): on every whole-state configuration with global actions off, switching them on refines the checker (`Lift.globalActions_wf`); `.storageResolution ⊑ .globalActions`, `.resharding ⊑ .allFeatures`, and `.curveHosts ⊑ .allFeatures` at verdict level under the layout hypothesis only. Earlier steps (§7, §9, §11, §14): interpreter two-run host call, `LowQ`, call level, decoder agreement, pipe relation, queue operations, `MRQ`, non-distribution invariant, recorded call and dispatch, engine walk. Open: the unconditional `Lift` (the layout fact comes from claim admission, not from the checker). With O2: `relSuccessor_globalActions_allFeatures` (no premise), `relSuccessor_storageResolution_allFeatures_wf` | `Lift.globalActions_wf`, `relSuccessor_storageResolution_globalActions_wf`, `lift_resharding_globalActions_wf`, `relSuccessor_resharding_allFeatures_wf`, `relSuccessor_curveHosts_allFeatures_wf`, `checkD2CoreWithObs_o3`, `checkD2CoreGWith_o3`, `checkReshardCoreObs_o3`, `drvRel_of_lower` (`TierO3Lift.lean`); `run_global`, `run_global_nd`, `applyNewChunkD2_rr`, `processDelayedLoop_rr`, `yieldLoop_rr` (`TierO3Run.lean`); `layoutsWF_06_h10006_s0`, `layoutsWF_seed37_00_h10085_s7` (`TierO3Real.lean`); `callHost_RR_global` (`HostCommStep.lean`); `globalHyp` (`HostQStep.lean`); `TierO3*.lean`; routing: `recorderDriver_receiptShard_globals`, `recorderDriver_outgoingRoot_globals` (`TierMono.lean`) |
| O4 | storage resolution | **proved under two per-witness premises** (2026-10-30, sixth O4 session, §16): `.runtimeLimits ⊑ .storageResolution` on `O4Witness` files whenever the storage-resolution result equals the `NS` reference shell's (G1 soft limit, G6 VM recorder state) and is not a named escape (G2, G3, G3b, G4, G7). G4 and G5 are settled, `FCSim` is walked, and the premises are non-vacuous (`o4_premises_nonvacuous`) and measured (§16.3). §16.1 found a **completeness bug** in `.signed` and the legacy-engine tiers: they reject nearcore-valid chunks whose ContractData removals cross the soft limit. It is not fixed, because the fix changes the signed statement (proposal in §16.1). Earlier steps: §10, §12, §13 | `relSuccessor_runtimeLimits_storageResolution`, `verdict_runtimeLimits_storageResolution`, `o4_premises_nonvacuous`, `engineAgreeX`, `fwdSimX`, `simx_applyNewChunkD2` (`TierO4NSMain.lean`); `fcSimNS`, `actSimNS`, `code_rel`, `tail_rel`, `resolve_local_nonEth`, `simx_processWithInstant` (`TierO4NSSim.lean`); `checkD2CoreGWith_legacy_ns`, `runtimeLimits_ns_of`, `engineAgreeX_of_simX` (`TierO4X.lean`); `checkNS`, `StorageExecutionNS` (`TierO4NS.lean`); earlier: `relSuccessor_runtimeLimits_storageResolution_of` (`TierO4.lean`), `TierO4Engine.lean`, `TierO4Receipt.lean` |
| O5 | loading limits | **discharged for the named tiers**: every tier sets the flag, so no named pair differs in it | `Tier.cfg_loadingLimits`, `runtimeLimits_cfg_eq`, `relSuccessor_runtimeLimits_mono`, `relSuccessor_signed_runtimeLimits` |
| O6 | resharding, non-genesis | **proved at verdict level** (2026-10-30, §8): on every whole-state configuration with the genesis main transition and the Gate-B bounds in force, switching resharding on preserves every accept and every reject (`VRefines`; the reject reason may differ) | `checkSuccessor_resharding_vmono`, `relSuccessor_resharding_vmono` (`.curveHosts ⊑ .resharding`), `resharding_vlift_curveHosts`, `resharding_vlift_globalActionsCurve` (`TierO6.lean`) |
| O7 | complete-code witness | **proved at chunk level** (2026-10-30, §6): on every whole-state configuration the complete-code flag moves no verdict, in either direction | `Lift.completeCode`, `relSuccessor_completeCodeGlobal_globalActions`, `relSuccessor_globalActions_completeCodeGlobal` (`TierO7.lean`) |

### O1, the proof chain

1. **Preparation** (`TierFloats.lean`). `PRef x y` is the preparation-monad (`PM`) form of
   `Refines`: on every input, `x` returns `.error (.ood _)` or the same result as `y`. Its bind,
   `forIn` (list, array, `[a:b]`) and `if` congruences give `pref_lockstep`, the PM analogue of
   `refines_lockstep`.
   * `sectionBody_floats`: for every section id, `sectionBody cfg ⊑ sectionBody {cfg with floats := true}`.
     The three guards `floatGuardImport/Global/Body` are `false` under floats
     (`floatGuard*_on`); the left either throws `.ood` there or continues identically.
   * `earlyPass_floats`: through `earlyPassWith` (section parser as a parameter). The section
     result `match` is handled by generalising both runs and relating them with `sectionBody_floats`.
   * **`prepare_floats`**: `prepare cfg code bl = prepare {cfg with floats := true} code bl ∨
     ∃ w, prepare cfg code bl = .outOfDomain w`, for every `cfg`, code blob and block level.
2. **Execution never reads the flag**: `exec_floats`, `step_floats`, `instantiate_floats` (`rfl`),
   `run_floats` (induction on fuel), `callEntry_floats`, `runCall_floats` and
   `runCallWithLimits_floats` (equal once preparation is equal).
3. **Hook**: `D3.functionCall cfg` reads `cfg` only through `contractOOD cfg code` and
   `runCallWithLimits cfg code …`, on the same blob. `functionCallWith_mono`: if two instantiations
   agree on every blob, or the first one excludes it (`CallRel`), the hook refines.
   `callRel_floats` discharges `CallRel` from `prepare_floats`. `functionCallD3_mono` passes the
   `unmodeled` wrapper, and `d3Hooks_floats` gives `HooksRefine (d3Hooks cfg) (d3Hooks {cfg with floats := true})`.
4. **Pipeline** (`TierHooks.lean`): `checkD2Core_hooks_mono` and `checkD2CoreG_hooks_mono`. For
   any hooks, `HooksRefine h h'` makes the legacy checker refine. The lockstep walk goes through
   `applyAction`, `actionLoop`, `applyActionReceipt`, `processReceipt`, `processWithTotals`,
   `processWithInstant` (and its `drain`), `processLocals`, `processDelayed`, `processIncoming`,
   `applyNewChunkD2` and `checkD2CoreObs`. The pipeline only binds the hook's result and never
   catches it.
5. **Configuration and tier** (`TierRefine.lean`): `Lift.floats_legacy` (with
   `checkSuccessor_legacy_eq`, the root on a legacy-engine configuration, and
   `ProtocolCfg.wasm_floats`). Named pairs: `.signed ⊑ .floats`, `.protoGas ⊑ .floatsProtoGas`,
   `.genesis ⊑ .genesisFloatsProtoGas`. Compositions: `.signed ⊑ .genesisFloatsProtoGas`,
   `.floats ⊑ .genesisFloatsProtoGas`, `.signed ⊑ .runtimeLimits`.

(Superseded 2026-10-30, §5: `Lift.floats` covers the whole-state engine.) What O1 did not cover: floats on the whole-state (recorder) engine. No named pair needs it,
because every whole-state tier already sets `floats`. The general `Lift cfg {cfg with floats := true}`
on a whole-state configuration needs the same walk through `StorageExecution`, whose monad threads
a `Recording` state.

### Why O2, O3, O4, O6 and O7 stay open

* **O2 (curve hosts)**: the selector lives in the interpreter state (`St.curveHosts`), not in
  `NearCfg`. The two runs' states differ in that field at every step, so the proof needs a
  commutation lemma `exec cfg p {s with curveHosts := b} … = (exec cfg p s …).withCurveHosts b` for
  every instruction arm and every host function in `Wasm/Host.lean` and `Wasm/CryptoHost.lean`.
  It also needs a `StorageExecution` walk, because every curve-host tier is whole-state. Neither
  exists yet.
* **O3 (global actions)**: it changes the witness codecs, routing, `Recording.globalActions` (read
  through `get` at 10 sites in `StorageExecution`) and the host action encodings in `Host.lean`.
  This needs a simulation with a state relation, not the equal-state lockstep used here.
* **O4 (storage resolution)**: an engine change (`applyNewChunkD2` → `StorageExecution.run`). It
  needs an agreement theorem between two runtimes, not a refinement walk.
* **O6 (resharding, non-genesis)**: `checkReshardCoreObs` restructures the shell (per-block layouts,
  `walkSegment`, split-gate recomputation). Only `VRefines` can hold (Finding 2 of
  `tier-proofs/`). This is a dedicated correspondence proof. A source read found no disagreement:
  with no split gate, both sides require the header's `proposed_split` to be none.
* **O7**: see §4.

## 3. Proof engineering notes

* `refines_lockstep`'s `exact Refines.refl _` at default transparency can unfold whole pipelines
  when two subterms differ. The `hooks_lockstep` closers (`hk_close`) are `with_reducible`. A
  default-transparency `exact Refines.refl _` runs only on the goals left at the end of a walk.
* `split` on a goal whose two sides have *different* discriminants splits them separately. For
  the hook, the abstraction `functionCallWith` (rather than a direct walk of `D3.functionCall`)
  keeps the two calls apart and lets `CallRel.none` rewrite the right side from the left side's
  `none` branch.

## 4. O7: what `completeCodeGlobal` would need

`.completeCodeGlobal` is `.globalActions` with `CodeWitnessPolicy.complete`. The policy is read once
per call, in `resolveCodeBytes`. Disagreements (census `tier-proofs/ccg.json`):

| CCG | GA | nearcore | n | cause |
|---|---|---|---|---|
| reject (`w.code_complete`) | accept | ok | 178 + 8 | code served by an in-chunk or rolled-back deploy (compiled cache) |
| reject (`w.code_complete`) | reject, other reason | err/ok | 704 + 224 | same verdict, different reason string |
| reject (`w.code_complete`) | out of domain | err | 4 + 95 | the 95 pipeline races |

So `CCG ⊑ GA` fails: CCG rejects 186 chunks that nearcore and GA accept. `GA ⊑ CCG` fails for the
same chunks. On those, nearcore agrees with GA. The CCG rejections are its documented cache-free
design ("reject incomplete code witnesses"), not a soundness problem.

Finding (resolve level, `complete_accepts_untimely` / `coldPartial_untimely_ood`): `.complete`
*accepts* code that only a committed in-chunk deploy serves, even when the call's preparation was
pipelined before that deploy (`timely = false`). On that step the cold validator is a thread race,
and `.coldPartial` reports it out of domain. Under the rule "nearcore nondeterminism is out of
domain, never an accept", that step is wrong. No corpus or fixture case reaches it: the census has
no CCG-accept / GA-out-of-domain row.

A fix that would make `CCG ⊑ GA` hold (`Refines`, exact strings) changes `resolveCompleteCode` as
follows:

* an incomplete or unauthenticated witness becomes `out of domain (w.code_complete): …`;
* a committed hit honours `timely`;
* code only in `attempted` becomes out of domain;
* code found nowhere gives `invalid: MissingTrieValue (contract code)`.

With those changes, `resolveCodeBytes .complete` refines `.coldPartial` pointwise. This was not
done here, for two reasons:

1. It is a semantic change: CCG would stop deciding about 1,000 corpus cases. The rules then
   require fixtures, a breakage control and a verdict table.
2. The chunk-level step needs a `StorageExecution` simulation whose two runs carry `Recording`
   states that differ in `codePolicy` (the same machinery as O3).

Whether CCG should keep its cache-free reject semantics or become an exclusion is a decision about
the statement's meaning. It is not a pre-approved soundness fix, so it is left to the owner.

## 5. Update 2026-10-30

### Race arm of completeCodeGlobal: fixed (then superseded by W08)

The §4 finding was adopted as a soundness fix (pre-approved): `resolveCompleteCode` sent the
untimely committed-deploy arm to the cold policy's race exclusion. Only that arm changed. W08 has
since merged a complete-code policy that *is* the cold policy (`complete_eq_cold`, race exclusion
`e.code_prep_race`). On merging, main's version was taken, and the W12 resolve lemmas were restated
against it: main's `complete_untimely_ood` / `coldPartial_untimely_ood` plus W12's `complete_untimely_ood_general`, `complete_ok_coldPartial` and `raceExclusion_isExclusion`. Evidence,
fixtures (4 seeds, 3,853 cases, 23,118 replays), the breakage control and the before/after tables
are in `docs/evidence/lean-chunk-completion/pipeline-race-fixtures/`. The `complete_accepts_untimely`
lemma of §4 described the pre-fix behaviour and has been replaced by `complete_untimely_ood`.

### Refinement machinery for the whole-state engine (`TierWhole.lean`, `TierWholeWalk.lean`)

* **`MRef x y`** is `Refines` in `StorageExecution`'s monad
  `StateT Recording (ReaderT Env (Except String))`: from every state and environment, `x` reports an
  exclusion or returns exactly `y`'s value and final state. It comes with bind, throw, `tryCatch`,
  `if`, `foldlM`/`forIn`/`mapM` congruences.
* **`functionCallRecordedWith`** is an `rfl` copy of `functionCallRecorded` with `contractOOD`,
  `wasmFuel` and `runCallWithLimits` abstracted. `functionCallRecordedWith_mono` relates two
  instantiations under `CallRel`.
* **The walk:** `applyAction_rec_mono` … `applyNewChunkD2_rec_mono` lead to `run_rec_mono`, which
  says the recorder engine refines when its recorded call does (`RecRefine`).
* **Shells:** `checkD2CoreWithObs_apply_mono`, `checkD2CoreGWith_apply_mono` and
  `checkReshardCoreObs_apply_mono` refine whenever the driver's `apply` does.
* **`Lift.floats`:** switching floats on refines at every configuration.

Proof-engineering note: the `repeat`-based lockstep walk stops silently when it hits Lean's
recursion depth on long bodies (`repeat` is `first | (tac; repeat tac) | skip`). A second
`all_goals rec_lockstep` pass resumes it.

### What is still open, and why

O2, O3, O4, O6 and O7 at chunk level are **not** proved. The equal-state machinery above covers
configuration changes that only alter the Wasm configuration's reads in `NearCfg`. The remaining
obligations need more:

* **O2 (curve hosts) and O3 (global actions)** both change a flag held in the interpreter state
  (`St.curveHosts`, `St.globalActions`). The two runs' states differ in that field at every step.
  This needs a commutation lemma `f {s with flag := b} = (f s).withFlag b` for every instruction arm
  of `Wasm.exec` and every host function in `Wasm/Host.lean` and `Wasm/CryptoHost.lean`, about 300
  definitions in the `EStateM String St` monad. O3 additionally needs:
  * `managerGlobal` versus `manager` on action logs without global actions;
  * agreement of the global codecs with the D2 codecs on every input the D2 codecs decode;
  * the queue policies;
  * a state-relating walk for `Recording.globalActions`, which `get` reads at 10 sites.
* **O4 (storage resolution)** needs an agreement theorem between two engines (`applyNewChunkD2` and
  `StorageExecution.run`).
* **O6 (resharding, non-genesis)** needs a verdict-level correspondence proof between two
  differently structured shells. (Done 2026-10-30, §8.)
* **O7 at chunk level** needs:
  * W08's code-resolution policy, which W08 owns;
  * an accept-preservation walk with states that differ in `Recording.codePolicy`. Its resolve-level
    step is proved: `complete_ok_coldPartial` (every `.complete` accept is a `.coldPartial` accept
    of the same bytes) and `complete_untimely_ood` (both policies exclude the race arm).

## 6. Update 2026-10-30 (second session): flags as parameters, O7 at chunk level

### The flag refactor (approved by the integrator)

`Successor/StorageExecution.lean` (not a signed file) no longer keeps `globalActions` and
`codePolicy` in its `Recording` state. They are a parameter, `StorageExecution.Flags`, threaded
through the engine (`functionCallRecorded fl cfg …`, `applyAction fl cfg …`, …,
`applyNewChunkD2 fl …`). Functions that only read `globalActions` take it as a `Bool`
(`forwardOrBufferR ga …`, `decodeStoredRcptR ga …`, `pipeDecode ga`, …). `run` keeps its signature
and builds the flags from its two arguments.

**Equality with the pre-refactor engine (proved).** `StorageExecutionOrig.lean` is the pre-refactor
engine, verbatim except that its state type is `RecordingO` (the new `Recording` plus the two
flags) and the pure helpers are shared. `TierFlagsEq.lean` proves
`run_eq_orig : StorageExecution.run … = Orig.run …` for every input. The walk relates the two
engines by `Sim fl xO xN` (from the old state `s.withF fl`, the old computation returns the new
one's result, with the flags added back to the final state). The flags are never written, so every
function of the engine closes (`Sim.functionCallRecordedF` … `Sim.applyNewChunkD2`). One engineering
point: each `match` of the frozen copy elaborates to its own auxiliary constant. The tactic
`orig_matchers` replaces each by the refactored side's auxiliary of the same type, after checking
the two constants are definitionally equal (the kernel rechecks the change), so `split` cases both
sides together. A second one: `applyActionReceipt`'s mutable variables elaborate to about ten nested join
points (`have __do_jp := fun … => …`); zeta-reducing them duplicates the continuation into every
branch, and the walk did not finish in 25 minutes. `sim_let` relates the two join points once
(`∀ xs, Sim fl (jO xs) (jN xs)`) and walks the body with them abstract (`sim_walk_jp`); that proof
checks in about 10 minutes, the whole module in about 15.

**Verdicts (binary changed, so measured too).** Checker before (merge commit `eb057760e`) and after
(this commit), `tools/d3/replay_successor.py`, per case verdict *and* reason:

| population | tier | cases | identical | changed |
|---|---|---|---|---|
| 577 fixtures (`combined/fixtures.txt`) | signed | 577 | 577 | 0 |
| 577 fixtures | allFeatures | 577 | 577 | 0 |
| 577 fixtures | globalActions | 577 | 577 | 0 |
| 577 fixtures | completeCodeGlobal | 577 | 577 | 0 |
| 3,138 gap census | allFeatures | 3,138 | 3,138 | 0 |
| 3,138 gap census | signed | 3,138 | 3,138 | 0 |

Verdict counts (after): fixtures signed 143 accept / 166 reject / 268 out of domain; allFeatures
402 / 175 / 0; globalActions and completeCodeGlobal 279 / 141 / 157 each; census allFeatures
3,138 accept; census signed 735 accept / 2,403 out of domain. Checker SHA-256: before
`197e28fe…`, after `54b8a117…` (before any later commit of this lane; the Lean-only proof modules do
not enter the binary). Per-case results: `flags-replay/`. No verdict and no reason
moved, so no fixture family, breakage control or before/after table beyond this one is needed: the
refactor is not a semantic change (`run_eq_orig`).

### O7 at chunk level (proved)

With the policy a parameter, the existing recorder-engine walk (`run_rec_mono`, `TierWholeWalk.lean`)
applies. It was generalised: `RecRefine P ga p cfg p' cfg'` relates the recorded calls of two runs
that share `globalActions` and may differ in the Wasm configuration and the code policy, on calls
whose environment satisfies `P`; every walk lemma carries `P env`. O1 (`Lift.floats`) is the instance
`P := True`, `p = p'`.

* `resOf_policy_eq`, `functionCallRecorded_policy_eq`: on a content-addressed store
  (`StoreAuth e := e.store.Auth`) the two policies resolve every call the same way
  (`complete_eq_cold`), so the recorded calls are equal.
* `run_policy_mono`: the engine at one policy refines the engine at the other, on such stores.
* `checkD2CoreWithObsA_apply_mono`, `checkD2CoreGWithA_apply_mono`, `checkReshardCoreObsA_apply_mono`:
  the shells refine under `ApplyRefineA` (refinement of `apply` on authenticated stores only). Every
  shell builds its main-transition store as `mkHStore merged`, authenticated by `mkHStore_auth`
  (`TierStoreAuth.lean`).
* **`Lift.completeCode`**: on every configuration with storage resolution, global actions or
  resharding set, `Lift {cfg with completeCodeWitness := b} {cfg with completeCodeWitness := b'}`
  for all `b b'`.
* Named tiers: `.completeCodeGlobal ⊑ .globalActions` and `.globalActions ⊑ .completeCodeGlobal`
  (`relSuccessor_completeCodeGlobal_globalActions`, `relSuccessor_globalActions_completeCodeGlobal`).
  The two tiers decide every input the same way up to exclusion reasons. The fixture replay agrees:
  identical verdicts and reasons on all 577 fixtures.

### Still open

* **O3 (global actions).** The recorder-state part is now a parameter (`ga`), but a refinement
  `ga = false ⊑ ga = true` still needs, beyond the engine walk: (1) the global codecs
  (`pRcptGlobal`, `pTxD2Global`, `decodeStoredRcptGlobal`) return the D2 codecs' value, or the D2
  codec's *same error string*, on every input the D2 codecs do not exclude (the global decoders
  accept action tags 9–11 and ML-DSA keys where the D2 decoders fail, so the statement needed is
  "the D2 decode fails with an exclusion there"; whether every such D2 failure is reported as an
  exclusion has not been checked); (2) `managerGlobal`/`finishActsGlobal` agree with
  `manager`/`finishActs` on VM action logs without global actions; (3) the queue policy
  `globalQueuePolicy` agrees with the D2 queue functions on non-distribution receipts;
  (4) the interpreter's `St.globalActions` flag (`Host.lean`: promise-action encodings, the
  `hostExcluded` guard) commutes, which is the per-arm commutation generator (`HostComm.lean`'s
  `CR` framework, not yet generated over `hostCall.eq_N` / `cryptoHostCall.eq_N`).
* **O2 (curve hosts).** The same per-arm generator over `St.curveHosts` plus the
  `successorDispatch_extends` host-table step. The `CR` lemmas exist for four gas helpers only.
* **O4 (storage resolution)**: engine agreement `applyNewChunkD2` vs `StorageExecution.run`.
  (2026-10-30, third session: shell and tier level proved given the engine agreement; see §10.)
* **O6 (resharding, non-genesis)**: verdict-level correspondence `checkD2CoreWith` vs
  `checkReshardCore`. (Done 2026-10-30, §7.)

### Next steps (handover, 2026-10-30; resume on branch `worktree-agent-a5081ae59762de001`)

(Superseded by §7: O2 is proved and the O3 steps are restated there.)

Pre-check done for O3 (1), by reading the source (no proof yet): the D2 decoders exclude rather than
reject on what the global decoders newly accept. `D2.pBase` throws `oodDeployGlobal` /
`oodUseGlobal` / `oodStateInit` (all `out of domain (w.shape): …`) on action tags 9, 10, 11, and
`D2.pPk` throws `oodMlDsaKey` on key tag 2, before reading anything else. `decodeStateWitnessD2` /
`decodeStateWitnessWith` do not re-wrap these errors. **No reject found.** Still to check:
`oodMlDsaSig` sites, the delegate path (tags 8/14 and `pDelegateBody` vs `pDelegateBodyGlobal`),
`pTxD2` vs `pTxD2Global`, and `decodeStoredRcpt` vs `decodeStoredRcptGlobal`.

In order, committing after each:

1. **CR generator** (`HostComm.lean`). Copy FuelHost's generation pattern: one theorem per
   `hostCall.eq_N` / `cryptoHostCall.eq_N` arm and per `exec` arm, closed by the `cr` tactic, for
   `φ := setCH b` and `φ := setGA b` (add `setGA`). The flag reads (`Host.lean` 571/577/592/615/1167/
   1179/1199 for `globalActions`; the curve-host dispatch for `curveHosts`) are not commutations.
   They need the *two-run* form `CR φ x y` with `x ≠ y`, plus a separate lemma per site saying the
   `false` run excludes or agrees. Add `HostComm` to `defaultTargets`.
2. **O3 composition.** Prove the decoder lemmas above, then `managerGlobal`/`finishActsGlobal` =
   `manager`/`finishActs` on logs without global actions, and `globalQueuePolicy` = D2 queue
   functions on non-distribution receipts. Then write a walk with `ga` differing: extend
   `RecRefine` with `ga ga'`. The `pipeDecode` divergence matters: the pipeline state `pipe`
   depends on the decoder, so equal-state `MRef` needs decoder agreement on *every* stored receipt
   the run reads, or a state relation on `pipe`. Then do the driver fields
   (`decodeWitness`/`receiptShard`/`validateRouting`/`outgoingRoot`; routing is already in
   `TierMono`).
3. **O2**: `St.curveHosts` through `runCall` (from step 1) plus `successorDispatch_extends`, then
   `RecRefine` with the two Wasm configurations and `Lift` via `run_rec_mono`.
4. **O4**: agreement of `applyNewChunkD2` (legacy) and `StorageExecution.run` on the legacy domain.
5. **O6**: `VRefines (checkD2CoreWith recorderDriver …) (checkReshardCore reshardingDriver …)` on
   non-genesis segments.

Tooling lessons for these walks (`TierFlagsEq.lean`): use only `with_reducible` closers; use
`orig_matchers` when the two sides come from different elaborations; use `sim_let`/`sim_walk_jp`
for `do` join points.

## 7. Update 2026-10-30 (third session): O2 proved, O3 components

No definition was changed; every new module is a proof module (default `lake build` target). Full
default build: 399 jobs, ok. `make pin-check` ok. No `sorry`. Axiom audit of every new theorem:
`axioms-o2-o3.txt` (only `propext`, `Classical.choice`, `Quot.sound`; 29 `#print axioms`). The
"Next steps" of §6 are superseded by this section.

### The commutation generator (`HostComm.lean`, `HostCommArms.lean`, `HostCommStep.lean`)

* `setF oc og` overwrites `St.curveHosts` (when `oc = some c`) and `St.globalActions` (when
  `og = some g`). `CR φ x y` is the two-run commutation; the framework and helper lemmas follow
  `Logged/WasmCR*.lean` (store map `E σ`) with the flag map in its place.
* `HostCommArms.lean` is generated (`gen/gen_hostcomm_arms.py`, arm list read from `FuelHost.lean`):
  one theorem per `hostCall.eq_N` (75) and `cryptoHostCall.eq_N` (14) arm. The ten
  `globalPromiseHosts` arms (they contain the seven `globalActions` reads, `Host.lean` 571, 577, 592,
  615, 1167, 1179, 1199) commute with every map that leaves the flag alone (`setF oc none`); every other
  arm with every `setF oc og`. Summaries: `CR_hostCall`, `CR_hostCall_none`, `CR_cryptoHostCall`,
  `CR_dispatchArm`, `CR_dispatchArm_none`. The module checks in about 35 s.
* `HostCommStep.lean`: every machine helper and non-call instruction commutes (`F_*`, `sf`). Host
  calls are two-run steps, `RR X φ lower upper`: the upper result is the lower one mapped by `φ`, or
  the lower one stopped with a message in `X`:
  * `callHost_RR_curve`: selector on; `X = XC`, the 14 curve names with a successor arm
    (`host function NAME not modelled in D3α`);
  * `callHost_RR_global`: `globalActions` on, from a trie-backed lower state with the flag off; `X = XG`,
    the ten lifted names (`out-of-domain host function NAME called`).
  `RR_exec`, `RR_step`, `RR_run`, `ER_callEntry` lift these to a run, from a `CallHyp` whose predicate
  `Q` must survive the lower run (`True` for O2).

### O2 (`TierO2.lean`): proved

1. `instantiate_curve`: instantiation commutes with the selector (`instLoops`, an `rfl` copy of its two
   segment loops; `forIn_fst`).
2. `runCall_curve`, `runCallWithLimits_curve`: on a trie-backed call (`real = some _`, which is what
   `vmCall` passes) the upper call is the lower call with the selector set in its final state, or the
   lower call is `.line "unmodeled host function NAME not modelled in D3α"` for a curve name. (`runCallT`
   is an `rfl` copy of `runCall` with the post-instantiation tail named `runTail`.)
3. `lineOutcome_XC`: each of those 14 lines is an exclusion of the recorded call. `String.splitOn` is
   well-founded recursion and does not reduce by `decide`; `split_eval` unfolds it with its equation
   lemma on the closed strings.
4. `functionCallRecordedWith_vmF`, `recRefine_curve`: the recorded call refines (it reads the final
   state only through projections, so the flag is invisible); `RecRefine P ga p w p {w with curveHosts := true}`.
5. **`Lift.curveHosts`**: for every configuration with storage resolution, global actions, complete
   code or resharding set, `Lift cfg {cfg with curveHosts := true}` (through `run_rec_mono` and the
   `*_apply_mono` shells). Named: `.storageResolution ⊑ .curveHosts`
   (`relSuccessor_storageResolution_curveHosts`, the only named pair differing in the selector alone)
   and `relSuccessor_globalActions_curve`.

Not covered: the selector on a legacy-engine configuration (no named tier has it; it would need the
same step for `D3.functionCall` and the legacy hook walk).

### O3: decoder check (finished) and components (`TierO3.lean`)

Decoder source check, completed. Where the global decoders accept and the D2 decoders do not, the D2
failure is an exclusion (`w.shape`), never a reject:

| site | D2 | global | lemma |
|---|---|---|---|
| key tag 2 (stake, add/delete key, gas keys, delegate key, receipt signer key) | `oodMlDsaKey` | accepts | `pPk_mlDsa_ood`; tags > 2 rejected identically by `pPublicKey` (`pPublicKey_tag_le`) |
| signature tag 2 (`pSig`: delegate) | same truncation error, else `oodMlDsaSig` | accepts | `pSig_mlDsa` |
| action tags 9, 10, 11 | `oodDeployGlobal` / `oodUseGlobal` / `oodStateInit` | accepts | `pBase_global_ood` |
| receipt tag 4 | `oodGcd` | accepts | `pRcpt_distribution_ood` |
| transaction key/signature not ED25519 (`pTxD2`) | `out of domain (w.shape): non-ED25519 …` | accepts | source reading |
| delegate tags 8/14 nested in a delegate | `decode: DelegateAction mustn't contain a nested one` | the same string | source reading |
| `decodeStoredRcpt` vs `decodeStoredRcptGlobal` | maps every non-shape error to `inconsistent what` | the same mapping | source reading |

Where D2 decodes, the global decoders return the same value: `pPkGlobal_of_pPk`,
`pBaseGlobal_of_pBase`, `pActGlobal_of_pBaseAct` (base actions; `baseRaw` is the identity off
state-init, `baseRaw_of_pBase`). **One gap is not proved:** on a delegate action `pActGlobal`
re-serializes the payload and raw bytes from the decoded fields (`borshBytes`, `u32` count, raw inner
actions, `nonceBytes`, `u64`, `PublicKey.encode`) and `pTxD2Global` re-serializes the body
(`rawPrefix ++ u32 count ++ raws ++ strict`), where D2 keeps the consumed bytes. Every field is
fixed-width or length-prefixed borsh, so the two agree; the proof needs a round-trip lemma
(`consumed bs rest = encode x` for `pAccountId`, `pVec`, `pTxNonce`, `pU64`, `pPublicKey`, `pBaseAct`).
No disagreement with nearcore is expected or was found: the difference is in our re-encoding only.

Other components proved:

* `finishActsGlobal_of_finishActs`: where `finishActs` yields actions, `finishActsGlobal` yields the same.
  Where `finishActs` fails it throws an exclusion or an `unmodeled: …` error, which `applyAction`'s
  catch turns into an exclusion.
* `managerGlobal_eq_manager`: equal on a log without raw actions (`NoRaw`).
* `globalTarget_of_not_distribution`: on a non-distribution receipt whose D2 shard is in the layout,
  the global queue target is the D2 shard. (If `shardOf` falls outside `shardIds`, which a malformed
  layout permits since `shardOf` defaults to 0, the global target excludes or rejects where D2 does
  not; whether the claim decoder rules such layouts out has not been checked.)

### O3: what remains, in order (next steps)

1. **Lower-run invariant.** `callHost_RR_global` needs, at every host call of the lower run,
   `globalActions = false` and `real.isSome`; `managerGlobal_eq_manager` needs `NoRaw` of the final log.
   All three hold (only `realOpH`/`realSetH`/`realPutH`/`removeRecord` write `real`, always as `some`;
   only the ten lifted arms write `rawAction`, and only when the flag is set), but need a
   preservation walk over every arm. Pattern: `FuelHost`'s `HOR` (a predicate preserved by every arm,
   errors included because the recorded call reads the log of an aborted call too), generated over the
   same equation lemmas. Then instantiate `CallHyp XG none (some true) Q` with
   `Q s := s.globalActions = false ∧ s.real.isSome ∧ NoRaw s.actions`.
2. **`lineOutcome_XG`**: the ten lifted-name lines, as `lineOutcome_XC` (`split_eval`).
3. **`runCall`/`vmCall` for `globalActions`**: as `runCall_curve`, but `instantiate` sets the flag from
   `cfg.globalActions` and `runCall` does not override it (`instantiate_curve`'s proof works for
   `setF none (some g)` unchanged: `instLoops_F` is generic).
4. **Recorded call with `ga` differing**: `functionCallRecordedWith_vmF` with `ga` false on the left
   and true on the right; the `manager`/`finishActs` steps by `managerGlobal_eq_manager` (from `NoRaw`)
   and `finishActsGlobal_of_finishActs`.
5. **Engine walk with `ga` differing** (`RecRefine` with `ga ga'`): the `ga` reads of
   `StorageExecution` (`applyGlobal`, `forwardOrBufferR`, `delayPopR`, `decodeStoredRcptR`,
   `pipeDecode`, …). Needs the decoder round-trip of the gap above for stored receipts with delegate
   actions, and `globalTarget_of_not_distribution` with the layout condition discharged.
6. **Driver fields** (`decodeWitness`, `validateRouting`; `receiptShard`/`outgoingRoot` are in
   `TierMono`), then `Lift` for `.storageResolution ⊑ .globalActions`.

### O3: layout well-formedness (checked 2026-10-30, after the coordinator's follow-up)

The claim decoder does **not** rule out a receipt whose D2 shard is outside the layout.
`decodeLayout` (`Layout.lean:58-84`) reads `boundary_accounts` and `shard_ids` as two independent
vectors, and the shells check only `1 ≤ numShards` (and `≤ 64` unless `layoutUnbounded`,
`RuntimeCore.lean:230, 439`). With `shard_ids.length ≠ boundary_accounts.length + 1`,
`Layout.shardOf` falls back to `getD … 0`, and shard `0` need not be in `shard_ids`. There the D2
queue routes to shard 0 while `globalTarget` throws (`out of domain (c.layout)` on a V2 layout,
`invalid: ShardingError …` on a V3 one). So `.storageResolution ⊑ .globalActions` is false as stated
on such claims, in the reject direction for V3.

Not a real chunk: nearcore builds every `ShardLayout` through its constructors, which keep
`shard_ids.len() == boundary_accounts.len() + 1` (`core/primitives/src/shard_layout/v2.rs`, `v3.rs`,
pinned 2.13.4). An ill-formed layout is unreachable from an honest epoch config, so nearcore has no
verdict for it, rather than a reject. To check before acting on it: whether the claim's layout bytes are
authenticated against the epoch config. If they are, the case is unreachable for every valid claim.

Two ways to handle it in the statement. I have done neither, because each needs a decision:
* **Exclusion (semantic change):** add `check (L.shardIds.length == L.boundaries.length + 1)
  "out of domain (c.layout): …"` to the shells' layout check. Verdicts can move only on ill-formed
  layouts. The rules then require fixtures, a breakage control and a before/after table. This keeps
  the signed statement's meaning only if the signed checker is left unchanged (put the check on the
  successor shells only).
* **Hypothesis:** state O3's `Lift` for claims whose layouts are well formed. This needs no
  definition change, but the refinement is then conditional.

## 8. Update 2026-10-30 (third session): O6 proved at verdict level

Lean: `spec/lean/v3/NearSpecV3/Successor/TierO6.lean` (a default target). No `sorry`. Axioms of every
theorem below: `propext`, `Classical.choice`, `Quot.sound` (`o6-replay/axioms.txt`). No definition
changed, so no checker verdict can move; the module adds theorems and proof-only helpers
(`VR`, `newIn`, `expectedWalk`, `dedupStep`, `fsMap`, …). Default `lake build` (395 jobs) ok,
`make pin-check` ok.

### The statement

`checkSuccessor_resharding_vmono cfg … : VLift cfg { cfg with resharding := true }` for every
configuration with `resharding = false`, `genesisMainTransition = true`, `storageResolution = true`
and the Gate-B bounds in force (`segmentUnbounded = witnessUnbounded = layoutUnbounded = false`).
Every named pair that differs in resharding is such a configuration:

| theorem | pair |
|---|---|
| `relSuccessor_resharding_vmono`, `resharding_vlift_curveHosts` | `.curveHosts ⊑ .resharding` (all inputs) |
| `resharding_vlift_globalActionsCurve` | `{globalActions with curveHosts} ⊑ {… with resharding}`, the `hR` premise of `relSuccessor_globalActions_allFeatures_of` |
| `relSuccessor_curveHosts_allFeatures_of_GA` | `.curveHosts ⊑ .allFeatures`, now premised on O3 only |
| `relSuccessor_globalActions_allFeatures_of_C` | `.globalActions ⊑ .allFeatures`, now premised on O2 only |

`VRefines` is the strongest form that holds: the resharding shell checks a malformed layout in
another order, so a reject can carry another reason (Finding 2 of `tier-proofs/`, reproduced below).

### The proof

1. **Segments with a genesis block**: both tiers run `checkD2CoreGWith`; the existing
   `checkD2CoreGWith_resharding_mono` gives `Refines`.
2. **Segments without one**: the non-resharding tier runs `checkD2CoreGWith`, which there *is*
   `checkD2CoreWith`, error string included (`checkD2CoreGWith_eq_of_segment`, an `Overlap` walk
   whose genesis alternative is discharged by the segment's decoded blocks).
3. **The correspondence** `checkD2CoreWithObs_vr_reshard`: a verdict-level simulation `VR` (left
   accepts ⇒ right accepts; left rejects ⇒ right rejects; left excludes ⇒ no constraint).
   * The plain shell's two exclusions (`c.same_layout`, `c.no_split_gate`) are left-only steps: past
     them every epoch has the witness epoch's layout and no fact carries a split gate.
   * The per-epoch layout loop of `ReshardCore` then checks the one layout once per epoch
     (`forIn_const_ok`); every referenced epoch is in the table (`layoutBytes_of_table`, through
     `mem_dedupSorted`).
   * **The walk** (`walk_one_layout`): with one layout and no genesis block, `walkSegment` is the
     two-phase scan `scan_phase0`/`scan_phase1` (before the first new chunk, after it, stop at the
     second). It returns `expectedWalk b t` exactly when the plain shell's two `findIdx?` scans find
     `b` and `t` with every slot count right (`d2_of_found`, `found_of_d2`), and otherwise rejects,
     never excludes (`y_walk_err`). The shard never changes, no resharding transition is pushed, and
     the implicit transitions are `old i` for `i < b`, oldest first.
   * The source-receipt loops agree element-wise (`forIn_forall2`, `forall2_sources`); the
     implicit-transition loops agree with the resharding loop carrying the congestion and the
     remaining facts (`forIn_implicit`); the recomputed `proposed_split` is `none` without a gate
     (`expectedProposedSplit_none`), so `H.proposedSplit == none` is the plain shell's `isNone`;
     the outgoing-receipt reassignment is the identity (one layout).
4. **Configuration level**: `checkSuccessor` dispatches on `segmentHasGenesis`, and the two halves
   compose to `VRefines`.

### Data first (before the proof)

Checker `nearspec-v3-check-successor` sha256 `54b8a117…` (the binary of `flags-replay/`; this lane
does not change it). Per case: the `curveHosts` verdict against the `resharding` verdict. A
*violation* is a `curveHosts` accept or reject that `resharding` does not reproduce.

| population | cases | curveHosts → resharding | violations | reject reason differs |
|---|---|---|---|---|
| both resharding fixture sets (`resharding-fixtures/`, `resharding-fixtures-2/`) | 60 | accept→accept 3, reject→reject 2, out of domain→accept 28, out of domain→reject 25, out of domain→out of domain 2 | 0 | 1 (`seed23-02-h10062-s5-c.child_layout_is_parent`: `slot count` vs `shard not in layout`, Finding 2) |
| gap census (`flags-replay/`) | 3,138 | accept→accept 2,488, out of domain→out of domain 650 | 0 | 0 |
| `l6-uq010` honest and `ood/` cases (gen-v1, gen2) | 9,300 | accept→accept 9,300 | 0 | 0 |
| `l6-uq010` mutants, every tenth | 4,492 | accept→accept 982, reject→reject 3,510 | 0 | 0 |

The raw split runs of `resharding-fixtures-2` (`c31b` … `t3`) are no longer on disk; their committed
cases are in the fixture row. Item 6's `l6-uq010` chains have no resharding, so they test the
one-layout correspondence on ordinary segments.
No refinement violation exists on any real chunk, so nothing was exhibited against nearcore and no
fix was needed. Per-case results: `o6-replay/`.

### What is not covered

* Configurations with a Gate-B lift set (`segmentUnbounded`, `witnessUnbounded`, `layoutUnbounded`):
  no named pair differs in resharding there (`.allFeatures` sets resharding and the lifts at once,
  and its comparisons go through `Lift.gateB` after the resharding step). The walk in
  `checkD2CoreWithObs_vr_reshard` fixes the three flags; the same steps would go through with them
  as variables (the guards are exclusions on both sides), but that was not needed.
* The signed hand-over (`withReshardHandover`, `D3/Signed.lean`) calls `ReshardCore` on legacy
  errors; it is not a resharding-flag pair and is unchanged (`make pin-check` ok).
* Still open in W12: O2, O3, O4 (§6).

## 9. Update 2026-10-30 (fourth session): O3 steps 1–3, the layout decision, and what remains

No definition was changed; every new module is a proof module and a default `lake build` target.
No `sorry`. Axioms: only `propext`, `Classical.choice`, `Quot.sound` (`axioms-o3.txt`, 17 `#print axioms`). Full default build: 404 jobs, ok. `make pin-check` ok.

### Layout well-formedness: the hypothesis route (integrator decision)

O3's refinement is to be stated for claims whose layouts are well formed:
`shard_ids.length = boundary_accounts.length + 1` for every layout in the claim. Justification:
nearcore's `ShardLayout` V2/V3 constructors assert exactly this invariant
(`core/primitives/src/shard_layout/v2.rs:63,207`, `v3.rs:100,211` at the pin
`/data/illia/nearproof-deps/nearcore`), so an honest epoch config never carries another layout. The
layout is a trusted claim fact, and under admission contract A1 (UQ-013) an admitted claim's trusted
section is rebuilt byte-identically from the verifier's own chain state, so a malformed layout cannot
occur in an admitted claim. No checker definition changes. (Not yet used in a proof: the `Lift`
statement is step 6 below.)

### Step 1 (proved): the lower run's invariant

`LowQ s`: `s.globalActions = false`, `s.real.isSome`, and no raw action in `s.actions`.

* `HostQ.lean` (generated, `gen/gen_hostq.py`): the `setF` commutation proofs of `HostCommStep.lean`
  with the map `setX x` (action log, store, flag taken from `x`). Every non-call instruction commutes
  with it (`X_exec`); read at `x := s` this says those instructions keep the three fields.
* `HostQArms.lean` (generated, `gen/gen_hostq_arms.py`): `FuelHost.lean`'s `HOR` walk with `LowQ`,
  errors included (`HQ x`: from a `LowQ` state, the final state of `x`, value or error, is `LowQ`),
  over the 65 `hostCall` arms outside `globalPromiseHosts` and the 14 curve arms. The ten lifted arms
  are not needed: on a trie-backed state with the flag off `callHost` excludes every `realOodHosts`
  name before dispatch. Summaries `HQ_hostCall`, `HQ_cryptoHostCall`, `HQ_dispatchArm`.
* `HostQStep.lean`: `QRes_callHost`, `QRes_exec`, `QRes_step`, `QRes_run`, `LowQ_callEntry`, and O3's
  per-call hypothesis `globalHyp : CallHyp XG none (some true) LowQ`.

### Step 2 (proved): the call level

`TierO3Call.lean`: `instantiate_ga` (instantiation commutes with the flag; `instLoops_F` is generic),
`instantiate_eq_instX` (the instantiated state carries the configuration's flag and an empty log),
`runCall_globalG` / `runCallWithLimits_globalG` (on a trie-backed call with the flag off, the upper
call is the lower one with the flag set in its final state, or the lower call stopped at one of the
ten lifted names; and the lower call's final state is `LowQ`), `lineOutcome_XG` (the ten lines are
exclusions), `vmF_global` (`VmF XG (setF none (some true))` for the recorded call's `vm`) and
`vmCall_lowQ` (so `managerGlobal_eq_manager` applies to the lower log).

### Step 3 (proved): borsh round trip

`TierO3Codec.lean`: `Enc p enc` (a parser's input is its value's encoding followed by the rest) for
the borsh primitives, keys, nonces, signatures, `pVec`, `pOption`, the delegate body, `D2.pBaseAct`
and `D2.pAct`; `Suf` (some prefix) for `pPerm`, `pAK`, `pBase`; `consumed_append`
(`consumed (a ++ b) b = a`). **`pActGlobal_of_pAct`**: where `D2.pAct` decodes, base or delegate,
`pActGlobal` decodes the same action and rest (the rebuilt payload and raw bytes are the consumed
ones). **`pTxD2Global_of_pTxD2`**: the same for transactions, v0 and v1, body and raw included.
Engineering note: `do` blocks whose bound computation is an `if` elaborate with the continuation
copied into every branch, so `split`/`simp` on a whole transaction parser exhaust their step limits;
the walk instead fixes each branch with `if_pos`/`if_neg` on hypothesis and goal together and
rewrites each bind by `bind_of_ok`.

### What remains, in order (next steps)

4. **Stored-receipt decoder agreement.** `decodeStoredRcpt b w = .ok r → decodeStoredRcptGlobal b w = .ok r`,
   and every D2 error is either an exclusion or the same `inconsistent w` the global one returns.
   Needs `pRcptGlobal_of_pRcpt` (`pActionR` vs `pActionRGlobal`: `pVec pAct` by `pVec_congr` and
   `pActGlobal_of_pAct`, keys by `pPkGlobal_of_pPk`), then `decodeStoredGlobal` vs `decodeStored`
   (`StateStoredReceipt` wrapper) and the witness decoders (`decodeStateWitnessWith` over
   `pRcptGlobal`/`pTxD2Global`, the `decodeWitness` driver field).
5. **Engine walk with `ga` differing.** Two facts found while setting it up change its shape:
   * *The pipeline state diverges.* `Pipeline.handle` and `peekDelayed` decode stored receipts with the
     active codec and set `uncertain := true` on an error. Where the D2 codec excludes (an ML-DSA key
     or a global action in a postponed, yield or delayed receipt) the lower run's pipe becomes
     `uncertain` while the upper run's does not, and the two pipes then evolve differently. Equal-state
     `MRef` cannot hold. The relation needed is `R rL rU := rL = {rU with pipe := rL.pipe} ∧
     (rL.pipe = rU.pipe ∨ rL.pipe.uncertain = true)`: nothing resets `uncertain`, and the engine reads
     the pipe only through `deterministic` (false once uncertain, so the lower resolution gives the
     same code, `missingCode`, or `raceExclusion`, an exclusion) and `next` (which only steers pipe
     updates). This is a refinement in the right direction (the lower run excludes more), not a
     nearcore disagreement. `get` returns the whole state, so the walk needs a `get`-bind lemma that
     substitutes `rU = {rL with pipe := q}` and rewrites field reads.
   * *`finishActs` errors are `unmodeled: …`, not exclusions.* The recorded-call lemma is a
     refinement up to exclusion-or-`unmodeled` errors; `applyAction`'s `try … catch` turns the latter
     into exclusions (`unmodeledHandler_ex`), so the walk must enter the recorded call through that
     catch, not through `RecRefine`.
   Remaining `ga` reads: `applyGlobal` (lower throws `w.shape`), `processReceipt` distribution (lower
   throws `oodGcd`), `forwardOrBufferR`/`yieldLoop`/`emitReceipts` (receipts the lower run forwards are
   never distribution receipts: `rcptIsDistribution` invariant of action outputs needed),
   `delayPopR`/`forwardFromBufferR`/`decodeStoredRcptR` (step 4 plus `globalTarget_of_not_distribution`
   with the layout hypothesis), `pipeDecode`/`scheduleDelayed` (the pipe relation).
6. **Driver fields and `Lift`.** `decodeWitness` (step 4), `validateRouting` and `receiptShard` /
   `outgoingRoot` on non-distribution receipts (`TierMono`), then
   `Lift`-under-hypothesis for `.storageResolution ⊑ .globalActions` and
   `Lift (Tier.cfg .resharding) {… with globalActions := true}` (the hypothesis of
   `relSuccessor_resharding_allFeatures_of`), with `LayoutsWF c` (every layout of the decoded claim
   has `shardIds.length = boundaries.length + 1`) as hypothesis; the shells must carry it to the
   engine's `env.ctx.layout` (as O7 carried store authentication, `ApplyRefineA`).

No refinement was found false on a real chunk; no nearcore replay was needed.

## 10. Update 2026-10-30 (third session): O4, storage resolution

Lean: `spec/lean/v3/NearSpecV3/Successor/TierO4.lean` (default target). Fix:
`Successor/Config.lean` (`withStorageExclusion`). Replay evidence: `o4-replay/`. Axioms of the new
theorems: `o4-replay/axioms.txt` (only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`).

### The statement

`.runtimeLimits` and `.storageResolution` differ only in `storageResolution`, which switches the
shell's driver from `legacyDriver` to `recorderDriver cfg`. The driver change touches four places:

| phase | legacy driver | recorder driver |
|---|---|---|
| decode | `decodeWitnessFile` | `decodeWitnessFileV` (also the `near-arena-cwitness-v3` format) |
| decode | — | `w.code_response_size` exclusion (code > 64 MiB) |
| apply transactions and receipts | `applyNewChunkD2 (d3Hooks cfg)` | `StorageExecution.run cfg … false .coldPartial` |
| outputs | `w.size` exclusion `base + 2000 · removals ≤ 4,000,000`, after the main transition | none |

* `O4Witness w`: the witness file is in the original format (`isCWitnessFile w = false`; the legacy
  driver rejects a compressed-format file with `decode: wrong witness format`, the recorder decodes
  it) and its codes fit one `ContractCodeResponse` (the recorder excludes the others first; the
  legacy driver excludes them only after the main transition, so an earlier legacy reject would not
  be preserved). Both are conditions on the witness file alone.
* `EngineRef base x y`: a legacy main-transition reject on a witness within the legacy storage
  bound (`base ≤ 4,000,000`) is a recorder reject with the same string; a legacy output inside the
  legacy size bound is the recorder's output.
* `EngineAgree cfg`: `EngineRef` on every main-transition input the shells build (store
  `mkHStore merged`, trie the revealed pre-state).

### Proved

| theorem | statement |
|---|---|
| `checkD2CoreWithObs_legacy_recorder`, `checkD2CoreGWith_legacy_recorder` | shell level: `EngineAgree cfg → O4Witness w → legacyMergedBytes w ≤ 4,000,000 → Refines (legacy shell) (recorder shell)`; the decode, code-response and size phases are walked (`o4_lockstep`, `Refines.engine_bind`) |
| `checkD2CoreG_ok_bound` | the legacy genesis-capable shell accepts only when `legacyMergedBytes w ≤ 4,000,000` (`NoAcc` walk) |
| **`relSuccessor_runtimeLimits_storageResolution_of`** | `EngineAgree → O4Witness w → Refines (Tier.checker .runtimeLimits c w) (Tier.checker .storageResolution c w)`; no size premise (above the bound the left is an exclusion) |
| `verdict_runtimeLimits_storageResolution_of` | the verdict-level reading |
| `applyNewChunkD2_eq_logged`, `engineAgree_of_logged` | engine phase E0: the legacy engine on the shell's inputs is its logged mirror `applyNewChunkD2L (d3HooksL cfg)` (`R_applyNewChunkD2`, `HooksR_d3`, `HInv_mkHStore`), so `EngineAgree` reduces to `EngineAgreeL` (stated against the mirror) |
| `logged_run` | engine phase E1: `StorageExecution.logged x` returns `LM.ev e.store e.preRoot x` and only updates the recorder |
| `SimE`, `SimE.bind`, `SimE.pure`, `SimE.logged`, `SimE.modify`, `SimE.ite`, `SimE.foldlM`, `engineAgreeL_of_simE` | the engine simulation (mirror `LM α` vs recorder `M β`, value map `φ`, recorder invariant `P`), its rules, and the bridge: a simulation of the whole main transition gives `EngineAgreeL` |

### Counterexample on real chunks, and the fix (legacy side)

Checked against data before proving (`o4-replay/`): `.runtimeLimits ⊑ .storageResolution` held on the
577 fixtures and the 3,138 census (0 violations), but **failed on 26 of the 88 committed
`storage-limit-fixtures` cases**, all nearcore `ok` (pinned cold validator, `meta.json`):
`.runtimeLimits` (and every narrower legacy tier) rejected with `invalid: MissingTrieValue …` or
`invalid: StorageInconsistentState(MissingTrieValue)`; `.storageResolution` accepted. Cause: the
legacy pipeline runs the receipts that nearcore postpones at `main_storage_proof_size_soft_limit`,
and their values are legitimately absent from the witness. The signed statement already decides
those errors with the recorder engine (UQ-010 hand-over, `D3/Signed.lean`, same condition); the
narrower legacy tiers did not, although `Config.lean` documented that they "keep the exclusions".

Fix (pre-approved: the signed statement of record is unchanged, `checkSuccessor_signed` is still
`rfl`, `make pin-check` ok): `checkSuccessor`'s two non-hand-over legacy branches wrap the legacy
result in `withStorageExclusion`, which reports a legacy **reject** on a witness with
`legacyMergedBytes w > 4,000,000` as `out of domain (w.size): storage-proof upper bound may exceed
main_storage_proof_size_soft_limit` (the legacy shell's own `w.size` message). Accepts and
exclusions are unchanged (`withStorageExclusion_cases`); above the bound the legacy shell never
accepts (`checkD2CoreG_ok_bound`). Affected tiers: `.floats`, `.protoGas`, `.floatsProtoGas`,
`.genesis`, `.genesisFloatsProtoGas`, `.runtimeLimits`. Follow-on edits (no other semantics): the
named pairs stated on `D3.checkD3Core` are restated on `checkSuccessor signedCfg`
(= `withStorageExclusion (checkD3Core c w) w`, `checkSuccessor_signedCore`); `Refines.storage`
(congruence) closes the legacy leaves of `checkSuccessor_gas_mono`, `checkSuccessor_genesis_mono`,
`Lift.floats_legacy` and `Lift.floats`; `FloatOverlap.checkD3F_refines_checkD3` is proved from the
hook refinement directly. Cost: legacy rejects of structurally broken mutants above the bound become
exclusions too (24 of the 88 committed cases); `.storageResolution` and the signed statement still
reject them.

### Before/after (checker `54b8a117…` → `2347323d…`, per case verdict and reason)

`o4-replay/summary.json`, per-case rows `o4-replay/*.results.jsonl.gz`. "Before" is the fix
reverted, so it is also the breakage control: it reproduces every violation below.

| population | tier | cases | identical | changed | verdicts after (accept / reject / ood) |
|---|---|---|---|---|---|
| 577 fixtures | signed, floats, protoGas, floatsProtoGas, genesis, genesisFloatsProtoGas, runtimeLimits, storageResolution | 577 each | 577 each | 0 | e.g. runtimeLimits 153 / 141 / 283; signed 143 / 166 / 268 |
| 88 committed storage-limit fixtures | signed | 88 | 88 | 0 | 56 / 24 / 8 |
| 88 committed storage-limit fixtures | storageResolution | 88 | 88 | 0 | 64 / 24 / 0 |
| 88 committed storage-limit fixtures | floats, protoGas, floatsProtoGas, genesis, genesisFloatsProtoGas, runtimeLimits | 88 each | 38 each | 50 reject → ood (26 nearcore-valid, 24 mutants) | runtimeLimits 20 / 0 / 68 |
| 2,700 honest storage-limit chunks (s99, s101; all nearcore `ok`) | runtimeLimits | 2,700 | 2,656 | 44 reject → ood | 2,570 / 0 / 130 |
| 3,138 gap census | signed | 3,138 | 3,138 | 0 | 735 / 0 / 2,403 |
| 3,138 gap census | runtimeLimits | 3,138 | 3,138 | 0 | 1,858 / 0 / 1,280 |

The O4 pair after the fix (`runtimeLimits` decides ⇒ `storageResolution` gives the same verdict and
reason): fixtures 0 violations of 577; committed storage-limit fixtures 0 of 88 (before: 26);
census 0 of 3,138. The family is the existing two-seed storage-limit family, not a new family;
no other population moved.

### What is open, and why

`EngineAgree` (the recorder engine refines the legacy engine on the legacy domain) is not proved.
After E0/E1 the remaining obligation is a simulation between `Logged.applyNewChunkD2L (d3HooksL cfg)`
(`LM`, stateless) and `StorageExecution.applyNewChunkD2 {}` (`StateT Recording …`), phase by phase:
validator update, delayed indices, scheduler and buffer metadata (all `logged` of the same mirrors,
`logged_run`); `forwardFromBufferR` (V2: `forwardFromBufferL`; V3: `forwardFromBufferV3L`);
transactions (`processTxR` = `logged processTxD2L` plus observation); local, delayed and incoming
receipts (soft-limit checks, pipeline bookkeeping, `applyAction`: `ordinaryAction` =
`logged (applyActionL d2HooksL)` on non-call actions, `functionCallRecorded` vs `functionCallL` on
calls); yield timeouts; outputs. The state relation leaves the recorder state free except
`recorder.size ≤ base + 2000 · cdRemovals(current overlay)` (to show `softExceeded` stays false);
`cdRemovals` is monotone (`Ovl.remove` increments it, commit and rollback keep it).

**As stated over every store, `EngineAgree` is false.** These shapes make the recorder exclude or
diverge where the legacy engine decides. None occurs in the corpora, the 577 fixtures, the 3,138
census or the storage-limit family. Each needs a premise, or a recorder-side fix; a recorder fix
changes the engine the signed hand-over runs, so it is not pre-approved.

| id | shape | legacy | recorder | real chunk? |
|---|---|---|---|---|
| G1 | ContractData removals alone push the recorded size past 4,000,000 before a legacy reject (`merged ≤ 4,000,000 < merged + 2000 · removals`), soft or per-receipt limit | decides (reject) | defers receipts / `RecordedStorageExceeded` | not seen; plausible on a large-deletion chunk |
| G2 | a called contract fails the fuel certificate (`vmCall`) | runs it under `wasmFuel` | `out of domain (w.fuel_certificate)` | none measured (`fuel-sufficiency/`) |
| G3 | the preparation pipeline is `uncertain` (a lookahead receipt calls a global-contract account, or a stored receipt or account does not decode) and a later call is served by a committed in-chunk deploy | serves it (`codeAvailable`) | `e.code_prep_race` (`Pipe.deterministic` is false whenever `uncertain`) | not seen; constructible (the uncertain receipt delayed by the gas limit, or failing before its call). Nearcore is deterministic there, so the recorder is over-conservative |
| G4 | V3 layout, every forwarded buffer empty and `bufferedGas ≠ 0` | continues | `invalid: buffered receipts gas left …` | inconsistent pre-state only |
| G5 | a non-ETH-implicit account whose local contract hash is a legacy magic hash | `MissingTrieValue` reject | redirects to the global wallet contract | unreachable (no deploy produces the magic hash) |

The provable statement is `EngineAgree` restricted to inputs without G1–G5 (premises on the store
or the recorder run), plus proofs that reachable states exclude G4 and G5. G3 is the shape most
likely to move a verdict on a real chain. Its fix would make `uncertain` per task key, so an unknown
receipt does not taint unrelated calls. That changes the recorder engine the signed hand-over runs,
so the owner has to decide it.

### Next steps

1. `SimE` and its bind, pure, `logged`, `modify`, `ite` and `foldlM` rules exist. Add `forIn`/`match`
   congruences and a lockstep tactic in the style of `TierFlagsEq` (`with_reducible` closers,
   `sim_let`/`sim_walk_jp` for `applyActionReceipt`'s join points). The value map `φ` puts the
   revealed pre-state trie into the mirror's overlays (the mirror starts from `Ovl.ofTrie dummyT`, the
   recorder from `Ovl.ofTrie t`), as `Logged.R` does with `.wt (preT s root)`; each logged mirror
   then needs its trie-independence lemma (`f (o.wt t) = (f o).map (·.wt t)`, the `Logged.Lockstep`
   `*_congr`/`foldl_*_wt` family). The soft-limit
   argument needs the current overlay's `cdRemovals`, which lives in the values, not in `Recording`:
   either make `P` a relation on (state, value) pairs, or take G1 as a premise (`softExceeded`
   never true on the run).
2. Phases 1–5 of `applyNewChunkD2` (all `logged`; `forwardFromBufferR` on V2 layouts is
   `forwardFromBufferL`; on V3 layouts relate `forwardFromBufferV3L` or use the legacy
   `c.same_layout` exclusion).
3. `functionCallRecorded` vs `functionCallL` under the G2, G3 and G5 premises: `resolveCode` on
   `.local` hashes, and `resolveColdCode` vs `codeAvailable` plus the legacy pre-state probe (whose
   deploy-served branch is an exclusion).
4. The recorder-size invariant through the VM's `RealStore` recording (G1), or keep G1 as a premise.
5. Compose into `EngineAgreeL` under the premises; `relSuccessor_runtimeLimits_storageResolution_of`
   then holds under them.

## 11. Update 2026-10-30 (fifth session): O3 step 4, step 5 foundations, the non-distribution invariant

No definition was changed; every new module is a proof module and a default `lake build` target
(`TierO3Dec`, `TierO3Pipe`, `TierO3Queue`, `TierO3Engine`). No `sorry`. Axioms: only `propext`,
`Classical.choice`, `Quot.sound` (`axioms-o3-step45.txt`). §9's "What remains" is superseded by
the list at the end of this section.

### Step 4 (proved): the D2 decoders refine the global ones (`TierO3Dec.lean`)

`XR X x y`: `x = y`, or `x` fails with an error in `X`. `X = Shape` (`isShapeOOD`, the six `w.shape`
constants) for receipts, `X = Excl` (`isExclusion`) for transactions and the witness, because the
non-ED25519 transaction exclusions are not `isShapeOOD`. The ok direction is the round trip of
§9 step 3; the error direction is a walk (`ErrX`) that ignores the values the two parsers build.

* `pPk_ref`, `pBase_ref`, `pBaseAct_ref`, `pSig_ref`, `pDelegateBody_ref`, `pAct_ref`,
  `pActionR_ref`, `pRcpt_ref`, `decodeRcpt_ref`, `decodeStored_ref` (`XR Shape`).
* **`decodeStoredRcpt_ref`**: where `decodeStoredRcpt` decodes, `decodeStoredRcptGlobal` decodes the
  same receipt; where it fails, it fails with a `w.shape` exclusion or with the same
  `inconsistent what`.
* `pTxD2_ref` (`XR Excl`), **`decodeWitness_ref`**: `decodeStateWitnessD2` against
  `decodeStateWitnessWith pRcptGlobal pTxD2Global` (`recorderDriver`'s `decodeWitness` with globals).
* `pRcpt_not_distribution`, `decodeStored_not_distribution`, `decodeStoredRcpt_not_distribution`:
  the D2 decoders never produce a distribution receipt.

### Step 5a (proved): the pipe relation, in one place (`TierO3Pipe.lean`)

`PipeRel pL pU := pL = pU ∨ pL.uncertain = true`. `PipeRel.det`: where the lower pipe calls a
deploy-served code deterministic, so does the upper one (so the lower resolution is the upper's, or
`raceExclusion`). `PipeFn f g` (related pipes to related pipes) for every pipe update of
`StorageExecution`: `pipeFn_startReceipt`, `pipeFn_recordDeploys`, `pipeFn_next`, `pipeFn_startList`,
`pipeFn_stepList`, `pipeFn_sched` (the update of `scheduleDelayed`, as `schedFn`), from `*_unc`
(nothing resets `uncertain`) and `handle_rel`, `schedule_rel`, `peekDelayed_rel` (with `DecLe`
decoders: `decLe_storedRcpt`, `decLe_stored`). When O4's G3 makes `uncertain` per prepared call,
only this file changes: the rest of the proof uses `PipeRel.det` and `PipeFn` only.

### Step 5b (proved): the queue operations (`TierO3Queue.lean`)

* `Layout.WF l := l.shardIds.length = l.boundaries.length + 1` (the §9 hypothesis);
  `Layout.shardOf_mem`, `globalTarget_wf`.
* `SRel`/`LR`: refinement of read-logging store programs (identical, or the lower one stops with an
  exclusion, node by node; `SRel.runR`). `SRelQ`/`LRQ` add a fact on common results.
* The D2 queue functions are the `QueuePolicy` functions at `d2Policy` (`delayPopL_eq`,
  `fwdLoopL_eq`, `forwardFromBufferToShardL_eq`, `forwardFromBufferL_eq`); two policies related by
  `PolRel` refine (`delayPopWith_rel`, `readBufferedWith_rel`, `fwdLoopWith_rel`, …), and
  `polRel_global` relates `d2Policy` to `globalQueuePolicy` on a well-formed layout.
* Results: `forwardOrBuffer_eq` (equal on a non-distribution receipt), `delayPop_rel`,
  `forwardFromBuffer_rel`, `forwardFromBufferV3_rel`.

### Step 5c (proved): the engine relation (`TierO3Engine.lean`)

`RecRel rL rU := rL = { rU with pipe := rL.pipe } ∧ PipeRel rL.pipe rU.pipe`. `MRQ E Q x y`: from
`RecRel` states and an `E` environment, the lower program excludes, or both fail with the same
error, or both return the same value satisfying `Q` in `RecRel` states. Rules: `weaken`, `pure`,
`throw_same`, `throw_ex`, `throw_bind`, `liftE`, `bind` (passes `Q` to the continuation), `ite`,
`foldlM`, `mapM`, `get_bind`, `modify` with `rr_update`, `modifyPipe` (from `PipeFn`), `logged`
(from `LR`, via `logged_run_rr`).

### Finding: the engine walk needs a non-distribution invariant on values, not only at `emitReceipts`

Two places need "the lower run never carries a distribution receipt":
`emitReceipts`/`forwardOrBufferR` (lower `shardOf`, upper `globalTarget`) and the shells'
`outgoingRoot` on `out.outgoing` (`recorderDriver_outgoingRoot_globals`). The second is a fact about
the *final* `RS.outgoing`, so it is an invariant of every `RS` the lower run threads, not only of the
receipts it emits. It holds (distribution receipts are built only in `GlobalExecution`, which the lower
run never reaches, and the D2 decoders never produce one), but it has to be carried through the walk:
that is why `MRQ` has the value predicate `Q`. Sources of `RS.outgoing` entries: `forwardOrBufferL`
(emitted receipts, yield-timeout data receipts, transaction receipts in `processTxD2L`, which the
upper run also routes by `shardOf`), and `fwdLoopL` (D2-decoded). No refinement was found false on a
real chunk; no nearcore replay was needed.

### What remains, in order (next steps)

1. **Unary store-program facts** (`LRQ`/`SRelQ` with `Q := ND rs.outgoing`, `ND l := ∀ r ∈ l,
   rcptIsDistribution r = false`): `forwardOrBufferL` (given `ND` of the receipt), `fwdLoopL`,
   `forwardFromBuffer*`, `delayPopL`, `delayPushL`, `processTxD2L`, `applyActionL d2HooksL` (its
   `newReceipts`, for `ordinaryAction`), and `refunds` (`Except`). The `SRelQ` rules in
   `TierO3Queue.lean` already carry a result fact; add `SRelQ.refl_of` (a unary invariant gives
   `SRelQ` of a program with itself).
2. **The recorded call** (`functionCallRecordedWith false … vm` against `… true … vm'`), as an
   `MRQ` up to exclusion-or-`unmodeled` errors, entered through `applyAction`'s `try … catch`
   (`unmodeledHandler_ex`): `get_bind` then `subst` of `rL := { rU with pipe := q }` (projections
   off the pipe reduce by `dsimp`), `PipeRel.det` for `timely` (with `resolveCodeBytes … false`
   refining `… true`: same bytes, `missingCode`, or `raceExclusion`), `vmF_global` and
   `vmCall_lowQ` (`managerGlobal_eq_manager`), `finishActsGlobal_of_finishActs`; `Q`: `ND` of the
   new receipts (they are built as `.action`/`.data`).
3. **The walk**, function by function as in `TierWholeWalk.lean`, with `MRQ` and `Q := ND` on every
   `RS`: `applyGlobal` (lower `w.shape`), `processReceipt`'s distribution arm (lower `oodGcd`),
   `decodeStoredRcptR` (`decodeStoredRcpt_ref`), `forwardOrBufferR` (`forwardOrBuffer_eq` + `ND`),
   `delayPopR`/`forwardFromBufferR` (step 5b), `pipeDecode`/`scheduleDelayed`/`processLocals`/
   `processIncoming`/`processDelayedLoop` (`modifyPipe` + `pipeFn_*`; `processDelayedLoop` reads
   `pipe.next`, where both branches only update the pipe, so `PipeRel` is kept when the lower pipe
   is uncertain). Engine statement: `Refines (run w … false p) (run {w with globalActions := true} … true p)`
   on environments with `env.ctx.layout.WF`, with `ND` of the output's `outgoing`.
4. **Driver fields and `Lift`** (§9 step 6, unchanged): `decodeWitness` by `decodeWitness_ref`;
   `validateRouting`/`receiptShard` on witness receipts (D2-decoded, so non-distribution); `outgoingRoot`
   by the engine's `ND` output; the shells as O7 threads `StoreAuth` (`ApplyRefineA`), here with
   `env.ctx.layout.WF` from `LayoutsWF c`. Main now carries O4's `withStorageExclusion` and the
   restated pairs (merged into this branch); state the `Lift`s against it.

## 12. Update 2026-10-30 (fourth session): O4 engine agreement, reduced to the per-receipt simulation

Lean: `Successor/TierO4.lean` (G0 fix), `Successor/TierO4Engine.lean` (new, default target). No
`sorry`; axioms of every new theorem: `propext`, `Classical.choice`, `Quot.sound`
(`o4-engine/axioms.txt`). No definition of any checker changed, so no verdict can move: no fixtures,
breakage control or before/after table are required (rules for remaining work), and `make pin-check`
is unaffected.

### Finding G0: `EngineAgree` was false as first stated (fixed)

`MainOutD2` has three observation-only fields (`committed`, `compute`, `detail`). The legacy engine
leaves them `none`; the recorder reports `committed := some …` and `compute := some …` on every
accept. `EngineRef` asked for `y = .ok out` with `out` the legacy output, so it could never hold on a
legacy accept: `EngineAgree` was false outright and the §10 tier theorem was vacuous. No check reads
these fields (the shell copies them into its `Observable`, which the `Unit`-valued checkers discard).

Fix (proof side only): `obsClear` erases them; `ExecutionDriver.clearObs` erases them from a driver's
main transition. `checkD2CoreWith_clearObs` and `checkD2CoreGWith_clearObs` prove the `Unit`-valued
shells equal at `d` and `d.clearObs` for **every** driver `d` (walk `umap_walk`: binds, flag `if`s,
`match`es, and the final `pure` under `Except.map (fun _ => ())`). `EngineAgree`, `EngineAgreeL` and
the `SimE` bridge are restated on `obsClear`-ed outputs, and the shell and tier theorems re-proved
on the cleared drivers.

### The simulation `Sim` (against the original engine, not the mirror)

`Sim e P φ x y`: from every recorder state satisfying `P`, if the original legacy computation `x`
(`Except String`) returns `a`, the recorder computation `y` (`M`) returns some `b` with `a = φ b` in a
state satisfying `P`; if `x` rejects with a non-exclusion, `y` rejects with the same string. `φ` puts
the revealed trie back into the recorder's states (`·.wt T`).

The §10 next steps planned a per-mirror trie-independence lemma (`f (o.wt t) = (f o).map (·.wt t)`)
for every logged mirror, because the mirror starts from a dummy trie and the recorder from the real
one. Relating the recorder to the **original** engine removes that obligation: each existing mirror
lemma `R_f` says `f (b.wt T) = (LM.ev (fL b)).map (·.wt T)` for *every* `b`, so `Sim.logged` turns
it into a simulation step directly, whatever trie the recorder's overlay carries. Rules: `pure`, `ok`,
`throw`, `error`, `bind`, `bind_id`, `logged`, `logged_ok_bind` (a logged read with a known value
against a pure read of the original), `liftE`, `okR`, `book`/`bind_book`/`pure_book` (recorder-only
bookkeeping, `Book`), `get`, `get_all`, `ite`, `ite_iff`, `foldlM`, `softExceeded_bind`. Lockstep
tactics: `main_walk`, `recv_walk`.

### Proved

| theorem | statement |
|---|---|
| `checkD2CoreWith_clearObs`, `checkD2CoreGWith_clearObs` | G0: the `Unit` shells ignore the observation fields (every driver) |
| `sim_processTxR` | a transaction: `logged processTxD2L` plus observation bookkeeping |
| `sim_applyNewChunkD2` | **phases 1–5 and 7** of the main transition (validator update, delayed indices, scheduler, buffer indices and metadata, transactions, yield indices, congestion, bandwidth requests, finalize, totals), value map `obsClear`, given the forwarding and receipt-phase simulations |
| `sim_processLocals`, `sim_processIncoming`, `sim_processDelayed` (`sim_processDelayedLoop`), `sim_yieldLoop` | the receipt loops: soft-limit tests false under `P` (`hSoft`), pipeline bookkeeping (`modifyPipe`, `pipeDecode`, `scheduleDelayed`) skipped, `delayPush`/`delayPop`/`forwardOrBuffer`/`get`/`contains` by their mirror lemmas, each receipt by `PWISim` |
| `fwdSim_v2` | forwarding on a V2 layout (`lastSplit = none`) |
| `engineAgree_of_obligations` | `(∀ merged e, e.store = mkHStore merged → EngineObligations cfg e) → EngineAgree cfg` |
| **`relSuccessor_runtimeLimits_storageResolution_of_obligations`** | `.runtimeLimits ⊑ .storageResolution` on `O4Witness` files, under the engine obligations |

### The remaining premises (`EngineObligations cfg e`, all named and documented in Lean)

| field | content | status |
|---|---|---|
| `P`, `init`, `frame` | an invariant of the recorder state reading only `recorder` and `softLimit` | free choice; trivial for the intended `P` |
| `reads` | `P` survives every logged read | provable for the intended `P` (below); not yet done |
| `soft` (**G1**) | `P r → r.recorder.size ≤ r.softLimit` | the G1 premise. Intended `P`: the recorder set holds only store hashes, `size = Σ set + 2000·k`, `base + 2000·k ≤ 4,000,000`. Logged reads keep it (they only record store-backed hashes, deduplicated); ContractData removals (`accountRemovals`, the VM's `removeRecord`) raise `k` — that is exactly G1. On a legacy accept within the size bound `k ≤ final cdRemovals` discharges it; on a legacy reject it stays a premise |
| `fwd` (**G4**) | the forwarding step | V2 layouts proved (`fwdSim_v2`); V3 layouts: premise (recorder forwards the parent buffer, then rejects "buffered receipts gas left" when every forwarded buffer is empty and `bufferedGas ≠ 0`) |
| `pwi` | `PWISim e P cfg`: `processWithInstant` of the recorder simulates the legacy one | **open**: `processWithTotals` → `processReceipt` → `applyActionReceipt` → `actionLoop` → `applyAction`; the action dispatch (`ordinaryAction` = `logged (applyActionL d2HooksL)` + `accountRemovals`) and `functionCallRecorded` vs `functionCall` (G2 fuel certificate, G3 pipeline `uncertain`, G5 magic hash; also the VM's chunk-scoped `acct`/`recd`/`recBefore` vs the legacy per-call fresh ones, which needs the PV86 equal-cost argument of `TrieAccounting.lean` and the per-receipt limit) live here |

### Data on the premises

`o4-engine/premise_proxies.py` (output `premise_proxies.json`) counts, over the §10 replays, the
verdict reasons by which a premise failure would surface on the recorder side (G2
`w.fuel_certificate`, G3 `e.code_prep_race`, G4 `buffered receipts gas left`, G1's VM half
`RecordedStorageExceeded`, G5 legacy-wallet redirection):

| population | cases | legacy decides | G1 (VM) | G2 | G3 | G4 | G5 |
|---|---|---|---|---|---|---|---|
| 577 fixtures | 577 | 294 | 0 | 0 | 0 | 0 | 0 |
| 3,138 census | 3,138 | 1,858 | 0 | 0 | 0 | 0 | 0 |
| 88 storage-limit fixtures | 88 | 70 | 0 | 0 | 0 | 0 | 0 |

G1's soft-limit half (receipts deferred) is silent in the verdict reason; it would show as an O4
violation, and §10 measured 0 after the legacy fix on all three populations. These are proxies, not
direct measurements of the premises: a direct count needs the checker to report the recorder size at
each soft-limit test (next step 4).

### Next steps (exact)

1. `PWISim`: walk `processWithInstant`/`processWithTotals` (`drain` by induction on its fuel),
   `processReceipt` (data, postponed, yield arms: `getR`/`containsR`/`decodeStoredRcptR` by mirror
   lemmas and `liftE`), `applyActionReceipt`, `emitReceipts` (`forwardOrBufferR`), in the style of
   `recv_walk`. Needed new rules: `startReceipt`, `curFail`/`vmErr`/`modifyDetail` as `Book`
   (`startReceipt` changes `receiptStart` only, so it is bookkeeping under `PFrame`).
2. `actionLoop`/`applyAction`: non-call actions are `logged (applyActionL d2HooksL)` against
   `D2.applyAction`'s non-call arms (mirror lemma `R_applyAction` with the D3 hooks), plus
   `accountRemovals` (needs `P` closed under it: G1); global actions are legacy exclusions.
3. `functionCallRecorded` vs `D3.functionCall`, under named premises G2 (`fuelCertified cfg code`),
   G3 (`Pipe.deterministic` true at the call), G5 (no non-ETH-implicit local magic hash; to be proved
   unreachable from deploys), and the VM agreement for differing `acct`/`recd`/`recBefore` (gas is
   equal at PV86, `TrieAccounting.lean` module note; the per-receipt limit needs a G1-style premise).
4. Instrument the checker to report the maximum recorder size at soft-limit tests and the
   per-receipt growth, and measure G1 directly on the 577 fixtures, the census and the storage-limit
   family.
5. The intended `P` and its `reads` lemma; V3 forwarding under G4.

## 13. Update 2026-10-30 (fifth O4 session): the per-receipt simulation, and why §12's obligations cannot be discharged

Lean: `Successor/TierO4Receipt.lean` (new, default target). No definition changed, so no verdict can
move. That means no fixtures, breakage control or before/after table are required, and
`make pin-check` is ok. No `sorry`. Axioms of every new theorem: `propext`, `Classical.choice`,
`Quot.sound` (`o4-receipt/axioms.txt`).

### Proved (steps 1 and 2 of §12)

| theorem | statement |
|---|---|
| `sim_emitReceipts`, `sim_actionLoop`, `sim_applyActionReceipt`, `sim_processReceipt`, `sim_processWithTotals`, `sim_drain` | Given the per-action simulation `ActSim`, the recorder's receipt level simulates the legacy one. The recorder-only steps are `Book`: `startReceipt`, the `vmErr`/`curFail`/`detail` updates, `pushAttrib` and `modifyPipe`. The distribution arm is a legacy exclusion (`Sim.excl`). Stored receipts decode with the same D2 decoder (`decodeStoredRcptR false`) |
| **`pwiSim_of_actSim`** | `ActSim e P cfg → PWISim e P cfg` (step 1) |
| `sim_ordinary` | A non-call, non-global action is the logged D2 action plus `accountRemovals`, given `RemClosed P`. The logged action uses `R_applyAction` with `d2Hooks`, which agree with `d3Hooks` everywhere except the call arm |
| **`actSim_of`**, **`pwiSim_of`** | `ActSim`, and so `PWISim`, follow from three obligations: `FCSim` (the `FunctionCall` hook, step 3), `GlobalSim` (G7, below) and `RemClosed` (G1). This is step 2 |
| `remClosed_soft_absurd` | `RemClosed P` and `EngineObligations.soft` cannot both hold for an inhabited `P` |

Engineering: the walk tactic is `o4r_walk`. Two lessons:

* Pure-bind rules must run under `with_reducible`, with `with_unfolding_all exact rfl` for the
  value equation. At default transparency the unifier unfolds the monad binds of the whole remaining
  program; the file then took over 15 minutes and 24 GB.
* A `split` hypothesis stated on the legacy discriminant (`(st.wt T).account`) must be `dsimp`ed
  before it can rewrite the recorder's `match` (`st.account`).

### Finding: §12's `EngineObligations` cannot be satisfied, so its tier theorem is vacuous

`PWISim e P cfg` quantifies over **every** `RS` and receipt. It also requires `P` to hold on the
recorder's output state. Take a receipt from account `A` to `A` with `DeleteAccount`, applied to an
`RS` whose overlay holds `k` ContractData keys of `A`. The legacy engine accepts it, and the
recorder adds `2000 · k` to its size (`accountRemovals`). For `k > 2000` the output violates `soft`
(`size ≤ softLimit`). So no `P` that satisfies `init` and `soft` makes `PWISim` true.

This is argued, not proved. The formal part is `remClosed_soft_absurd`: it shows that `RemClosed`,
the sufficient condition step 2 needs, contradicts `soft`. As a result,
`relSuccessor_runtimeLimits_storageResolution_of_obligations` (§12) holds vacuously, as §10's
theorem did before G0.

Nothing in this section depends on `soft`. The receipt level is proved for any `P`, including
`P := True`, where `RemClosed` and `reads` are trivial. The soft limit is tested only in the four
receipt loops (`processLocals`, `processIncoming`, `processDelayedLoop`, `yieldLoop`). So only
`sim_processLocals`, `sim_processIncoming`, `sim_processDelayed` and `sim_yieldLoop` need a
different argument.

Every premise stated "for every value" has the same problem: G2 (fuel certificate), G3 (pipeline
`uncertain`), G6 (VM agreement with the chunk-wide recorder state) and G7. Each is false over
arbitrary values and true only on reachable ones. Quantified the way `EngineAgree` is (every input
of every witness), they make the conditional theorem vacuous again.

### Finding G7 (new): global actions

The global actions are `deployGlobal`, `useGlobal` and `stateInit`. `D2.applyAction` runs the
existence and permission checks before it excludes one of them, and a failed check is an action
**failure**. The recorder with `globalActions = false` excludes at once (`applyGlobal`). So on a
value where a check fails, the legacy engine continues and the recorder excludes.

This shape is unreachable: the D2 decoders, `finishActs` and the transaction conversion never build
a global action, because `pBase` rejects the tags with `w.shape`. It is stated as the obligation
`GlobalSim`. Discharging it needs the same reachable-value invariant as O3's non-distribution
invariant (`MRQ` with a value predicate, §11).

### Status of the premises

| id | where it lives now | status |
|---|---|---|
| G1 soft limit | the four receipt loops (`softExceeded`) | Open. It must be run-level or coupled (see next steps). `RemClosed` itself is free with `P := True` |
| G1 per-receipt / G6 VM | inside `FCSim`. The VM gets `recd`/`acct`/`recBefore` from the recorder state; the legacy VM gets fresh ones | open |
| G2 fuel certificate | inside `FCSim` (`vmCall`) | Open. Data: the item-3 census, 0 failures in 236,871 corpus witnesses (`fuel-sufficiency/`) |
| G3 pipeline `uncertain` | inside `FCSim` (`resolveCodeBytes … timely`) | open |
| G4 V3 forwarding | `EngineObligations.fwd` | Open. V2 is proved (§12) |
| G5 magic hash | inside `FCSim` (`resolveCode`) | Open. Not yet proved unreachable |
| G7 global actions | `GlobalSim` | Open. Unreachable on decoded inputs |

Step 4 (instrumenting the checker) and the direct G1 measurement were not done this session.

### Next steps (exact)

1. **Make the premises run-level, per witness.** Two proof-side mechanisms:
   * **Variant drivers, for silent divergences (G1 soft limit, G6).**
     * Build `runNS`: a proof-side copy of the four loops plus `applyNewChunkD2`/`run` without the
       soft test, about 140 lines, in the style of `StorageExecutionOrig.lean`. Add a driver
       `recorderDriverNS` for it.
     * Premise G1 := on this witness, the storage-resolution checker equals the same shell at
       `recorderDriverNS`. This is a verdict-level equation, measurable by building the variant
       into the binary.
     * Then prove `EngineAgree` for `runNS` with `P := True`: no `soft`, and `RemClosed` is
       trivial. Reuse `sim_applyNewChunkD2` and the loop proofs with the `softExceeded_bind` step
       removed.
     * Treat G6 the same way, with a copy of the call stack whose VM gets a fresh `RealStore`.
       Alternatively, prove a universal VM lemma: results are equal modulo
       `real.acct`/`real.recd` unless one side reports `RecordedStorageExceeded`. This holds at
       PV86 by `ttn_costs_equal` once `payPer`'s split charge is shown to be equal.
   * **Verdict escapes, for exclusions (G2 `w.fuel_certificate`, G3 `e.code_prep_race`, G7
     `w.shape: global action`).**
     * Generalize `SimAt` with an escape set `X`: the recorder may fail with `s ∈ X` where the
       legacy engine decides. Generalize `EngineRef` and `Refines.engine_bind` the same way.
     * Copy `o4_lockstep` for `RefinesX x y := Refines x y ∨ ∃ s, y = .error s ∧ X s`. This needs
       about ten short rules, because the shells propagate engine errors unchanged.
     * Premise := the storage-resolution verdict is not an `X` exclusion. Data:
       `o4-engine/premise_proxies.json` already counts these reasons, with 0 on the 577 fixtures,
       the 3,138 census and the 88 storage-limit fixtures.
2. **`FCSim` (step 3).** Walk `functionCallRecorded fl0` against `D3.functionCallD3`. The
   differences:
   * the legacy ETH-implicit local-contract exclusion against `resolveCode` (G5: legacy magic hashes);
   * global code identifiers (legacy `w.shape`);
   * `resolveCodeBytes .coldPartial … timely` against the legacy `codeOf`, pre-state probe and
     `codeAvailable` (G3);
   * `vmCall`'s certificate (G2);
   * the VM's `RealStore` (G6);
   * the recorder update after the VM, which is free with `P := True`;
   * `getIndicesL`, by `R_getIndices'`;
   * `finishActs` and `manager`, which are identical at `fl0`.
3. **Step 4.** Add an observation-only flag to the binary that runs `runNS` (and the fresh-VM
   variant) next to the recorder. It reports the maximum recorder size at soft-limit tests and the
   per-receipt growth. Prove or check that verdicts are identical with the flag off. Measure on the
   577 fixtures, the census and the storage-limit family.
4. **Remaining pieces.**
   * Prove G5 unreachable: no deploy produces a magic hash, because the hash of deployed code is
     `sha256` of its bytes.
   * Prove G4 forwarding under its premise.
   * State the final theorem with only run-level premises.

## 14. Update 2026-10-30 (sixth session): O3 steps 5d–5f — invariant, recorded call, walk (part)

No definition was changed. New proof modules, all default `lake build` targets: `TierO3Inv`,
`TierO3Rec`, `TierO3Walk`. `TierO3Engine` generalized: `MRX X E Q` (lower errors in `X`), with
`MRQ := MRX Exc` (the rules are now `MRX.*`; `MRQ.logged` kept). No `sorry`. Axioms: only `propext`,
`Classical.choice`, `Quot.sound` (`axioms-o3-step5.txt`). `make pin-check` ok. No refinement was found
false on a real chunk; no nearcore replay was needed. §11's list is superseded by the one below.

### Step 1 (proved): the lower run never carries a distribution receipt (`TierO3Inv.lean`)

`ND l` (no distribution receipt in `l`); single-run facts `SOk`/`LOk Q x` on store programs (every
successful result satisfies `Q`), the `lok` walk, `LRQ.of_LR`/`LRQ.refl_of` (a two-run `LR` plus a
lower single-run fact is an `LRQ`), `MRX.loggedQ`. Proved: `forwardOrBufferL_nd` (on a
non-distribution receipt), `bufferReceiptL_nd`, `fwdLoopL_nd`, `forwardFromBufferToShardL_nd`,
`forwardFromBufferL_nd`, `forwardFromBufferV3L_nd`, `delayPushL_nd`, `delayPopL_nd`,
`processTxD2L_nd` (all keep `ND rs.outgoing`), `applyActionL_nd` (`d2HooksL`: the new receipts of
every non-call action), `refunds_nd`. The buffer and delayed queues need no invariant: they are read
through `decodeStored` (`decodeStored_not_distribution`).

### Step 2 (proved): the recorded call and the dispatch (`TierO3Rec.lean`)

* **`functionCallRecorded_global`**: `functionCallRecorded ⟨false, p⟩ w` against
  `functionCallRecorded ⟨true, p⟩ { w with globalActions := true }` (`w.globalActions = false`), as
  `MRX XU` (`XU`: exclusion, or an error starting with `unmodeled`), with `ND` of the new receipts.
  `liftE_timely` (`resolveCodeBytes … false` is `… true` or `raceExclusion`; `PipeRel.det`),
  `vm_step` (`vmF_global`, `vmCall_lowQ`), `managerGlobal_eq_manager`, `liftE_finishActs`
  (`finishActs_err`: the lower action-log errors are `w.shape`, `e.wasm-α` or
  `unmodeled: action re-encoding`; the upper then fails with `unmodeled: global action re-encoding`).
* `MRX.tryCatch_unmodeled`: `applyAction`'s handler turns `XU` into exclusions.
* **`applyAction_global`**: the dispatch as `MRQ` with `ND` of the new receipts (global actions:
  `applyGlobal_false`, the lower `w.shape`; others: `ordinaryAction_rr`).

### Step 3 (part): the engine walk (`TierO3Walk.lean`)

`MRQ` with `Q := ND rs.outgoing`, under `env.ctx.layout.WF` of the explicit environment (the reader
environment needs nothing; `E` is arbitrary): `fob_rr`, `delayPop_rr`, `ffb_rr`, `decRcpt_rr`,
`processTxR_rr`, `liftE_refunds`, `actionLoop_rr`, `emitReceipts_rr`, `applyActionReceipt_rr`,
`processReceipt_rr` (distribution arm: lower `oodGcd`), `processWithTotals_rr`, `drain_rr`,
`processWithInstant_rr`, `scheduleDelayed_rr` (`pipeFn_sched`), `processLocals_rr`,
`processIncoming_rr`.

Proof engineering: the walk tactics (`mrx` in `TierO3Rec`, `mrw` in `TierO3Walk`) must never let the
unifier compare the two runs' programs by unfolding (it runs the interpreter: `vmCall w` against
`vmCall { w with globalActions := true }`). Closers are `with_reducible exact` or guarded by
`lower_head`/`lower_has`/`lower_bind_has` (head-symbol checks on the lower program). A `split` is
followed by rewriting with the split's own equation (`simp_last_eq`), since the two runs' matches are
different terms. `pure` leaves are tried only on a `pure` head (`refine MRX.pure` against a bind chain
made `whnf` time out).

### What remains, in order (next steps)

1. **`processDelayedLoop_rr`** (fuel induction). The only new difficulty: `match (← get).pipe.next`
   reads the pipe, and `MRX.get_bind'` loses the state (the continuation is re-quantified over related
   states), so the case "lower pipe uncertain, the two `next` differ" cannot be closed after it. Add
   `MRX.get_pipe_step`: if `∀ r env, f r r env = (modifyPipe FL >>= k) r env`, likewise `g`/`FU`/`k'`,
   `PipeFn FL FU` and `MRX k k'`, then `MRX (get >>= f) (get >>= g)`. Take
   `stepF ga env rs p := match p.next with | some n => if n - 1 == 0 then schedFn (decoders of ga) … p
   else { p with next := some (n - 1) } | none => p`; `PipeFn` from `pipeFn_sched`, `pipeFn_next`,
   `schedFn_unc` (`PipeFn.of_unc`). The `f r r env` equation is by `cases r.pipe.next` and unfolding
   `scheduleDelayed`/`pipeDecode`; the do-notation join point `__do_jp` is the `k`. Then
   `processDelayed_rr` (`scheduleDelayed_rr`, then the loop).
2. **`yieldLoop_rr`** (fuel induction; `fob_rr` on `⟨acct, acct, rid, .data true d none⟩`, `nd_data`).
3. **`applyNewChunkD2_rr`**: `ffb_rr`, the transaction fold (`processTxR_rr`; `mrw`'s `foldlM` rule
   with `Q := ND ·.1.outgoing`), the three receipt phases, `yieldLoop_rr`; the output with
   `ND out.outgoing`. Then `run_global`: `Refines (run w … false p) (run {w with globalActions := true} … true p)`
   (as `run_rec_mono`, from `MRQ` at `RecRel.refl`) with the companion `run … = .ok out → ND out.outgoing`.
4. **Driver fields and `Lift`** (as §11 item 4): `decodeWitness_ref`, `validateRouting`/`receiptShard`
   on D2-decoded receipts, `recorderDriver_outgoingRoot_globals` with the engine's `ND`, the shells as
   O7 threads `StoreAuth` (`ApplyRefineA`) with `env.ctx.layout.WF` from `LayoutsWF c`, against main's
   `withStorageExclusion` and restated pairs; then `Lift` for `.storageResolution ⊑ .globalActions` and
   for `(Tier.cfg .resharding, {… with globalActions := true})`, discharging the premise of
   `relSuccessor_resharding_allFeatures_of` and, with `resharding_vlift_curveHosts` (`TierO6`), of
   `relSuccessor_curveHosts_allFeatures_of` under the layout hypothesis only.

## 15. Update 2026-10-30 (seventh session): O3 finished under the layout hypothesis

No definition was changed and no verdict can move. New proof modules, all default `lake build` targets:
`TierO3Run`, `TierO3Lift`, `TierO3Real`. No `sorry`. Axioms: only `propext`, `Classical.choice`,
`Quot.sound` (`axioms-o3-step6.txt`). `make pin-check` ok. No refinement was found false on a real
chunk; no nearcore replay was needed. §14's list is done; what stays open is listed at the end.

### Engine (`TierO3Run.lean`)

* `MRX.get_pipe_step`: a `get` whose continuation, run from the state it read, is a pipe update
  (`PipeFn`-related in the two runs) followed by a common continuation. The delayed loop does not use
  it directly: `pdl_succ` rewrites `processDelayedLoop`'s body so that the `match (← get).pipe.next`
  read is one `modifyPipe (stepF ga env rs)` (proved per run by `pdl_get_step`, the
  same equation `get_pipe_step` takes as premise), and `pipeFn_step` relates the two `stepF`s.
* `processDelayedLoop_rr`, `processDelayed_rr`, `yieldLoop_rr`, `applyNewChunkD2_rr` (with
  `ND out.outgoing`).
* **`run_global`**: `Refines (run w … false p) (run { w with globalActions := true } … true p)` on an
  environment with `env.ctx.layout.WF`; **`run_global_nd`**: the lower output carries no
  distribution receipt.

### Driver fields and shells (`TierO3Lift.lean`)

* `LayoutsWF c`: every layout of the decoded claim's epoch table that decodes is well formed (the §9
  hypothesis, stated on the claim bytes).
* `DrvRel d ap dw rs vr orr`: the upper driver's five fields against the lower driver's: witness
  decoder refines (`decodeWitness_ref`) and the lower decoder yields no distribution receipt
  (`decodeStateWitnessD2_nd`, `NDW`); `receiptShard` and `outgoingRoot` equal on non-distribution
  receipts; `validateRouting` equal on a well-formed layout and non-distribution receipts
  (`validateRouting_global`); `apply` refines on `env.ctx.layout.WF` with `ND` of the lower output.
  **`drvRel_of_lower`**: the global-action recorder driver against any driver with the lower
  recorder driver's five fields (so the resharding driver and the Gate-B variants too).
* Shells: `checkD2CoreWithObs_o3`, `checkD2CoreGWith_o3`, `checkReshardCoreObs_o3` (and the `Unit`
  forms). The walk `o3s` threads the layout fact from the claim decoding to `env.ctx.layout`, as O7
  threads store authentication: `hLc` at `decodeClaimE`, `hLwf : L.WF` at `decodeLayout` of the
  epoch-table entry `find?` returned, and for the resharding core's `Lmain` from
  `walkSegment_mainLayout` (the walk's main layout is an epoch-table layout). The source-proof loop
  carries `∀ e ∈ proofs, NDE e` (`Refines.forIn_inv`; unary side `eok`; `lookupLastD2_mem`,
  `shuffleWithSeed_mem`) so the receipt filter's two shard functions agree (`DrvRel.filter_eq`).
* **`Lift.globalActions_wf`**: on every configuration with `storageResolution`,
  `completeCodeWitness` or `resharding` set and `globalActions` off,
  `LayoutsWF c → Refines (checkSuccessor cfg c w) (checkSuccessor { cfg with globalActions := true } c w)`
  (stated against main's `withStorageExclusion`/whole-state dispatch; the whole-state branch never
  takes the storage-exclusion wrapper).
* Named: **`relSuccessor_storageResolution_globalActions_wf`** (`.storageResolution ⊑ .globalActions`),
  `lift_resharding_globalActions_wf` (the `hGA` premise of `relSuccessor_resharding_allFeatures_of`,
  per claim), **`relSuccessor_resharding_allFeatures_wf`**, and
  **`relSuccessor_curveHosts_allFeatures_wf`** (`.curveHosts ⊑ .allFeatures` at verdict level, with
  `resharding_vlift_curveHosts` from `TierO6`), each with `LayoutsWF c` as the only premise.

### Non-vacuity (`TierO3Real.lean`)

`layoutsWFb` decides `LayoutsWF` (`layoutsWF_of_b`). By `decide +kernel` (no `native_decide`):
`layoutsWF_06_h10006_s0` (the honest D3 chunk `d3c7/d3/06-h10006-s0`) and
`layoutsWF_seed37_00_h10085_s7` (a resharding chunk whose epoch table carries two distinct layouts,
`seed37_layouts_differ`). `storageResolution_globalActions_06_h10006_s0` and
`curveHosts_allFeatures_seed37_00_h10085_s7` instantiate the named pairs on them.

With O2 (`Lift.curveHosts`), the same module closes `relSuccessor_globalActions_allFeatures`
(`.globalActions ⊑ .allFeatures` at verdict level, no premise) and
`relSuccessor_storageResolution_allFeatures_wf` (`.storageResolution ⊑ .allFeatures` at verdict
level under `LayoutsWF`).

### Proof engineering

* `repeat` re-applies its tactic to the first goal only; a walk that branches needs `repeat'` (the
  O7 walks run twice for that reason).
* `lower_bind_has` failed on goals whose spine carries metadata (after a `have` in context); `lbh`/`lhd`
  strip metadata along the spine. Every `o3s` rule is guarded by them, including the
  `x = .error e` closer (guarded by a `throw` head), so no rule unifies the two runs' programs by
  unfolding.
* Elaboration order: `rfl` arguments whose type mentions a driver that only the goal determines must
  be `(by rfl)`.

### What remains open

* The unconditional `Lift`: `LayoutsWF` is a claim-admission fact (§9: nearcore's `ShardLayout`
  constructors assert it, and admission contract A1 rebuilds the trusted section from the verifier's
  own chain state), not something the checker checks. On a malformed layout the lower run routes by
  `shardOf` while the upper's `globalTarget` may fail, so the hypothesis cannot be dropped without a
  checker change.
* O3 is not needed for `.globalActions ⊑ .allFeatures` (closed above from O2 and O6). O4 (the
  storage-resolution engine change) is untouched by this session.


## 16. Update 2026-10-30 (sixth O4 session): removal ground truth, and O4 under per-witness premises

Lean: `Successor/TierO4NS.lean` (the proof-side recorder copy `NS`), `TierO4X.lean` (`SimX`,
`RefinesX`, the shell walk), `TierO4NSSim.lean` (the `FunctionCall` hook, actions, receipts),
`TierO4NSMain.lean` (loops, forwarding, main transition, final theorem). All four are default
targets. No `sorry`. Axioms of every new theorem: `propext`, `Classical.choice`, `Quot.sound`
(`o4-ns/axioms.txt`). No checker definition changed. `MainSuccessor.lean` gained an
observation-only mode, `--o4-premises`. `make pin-check` is ok. The oracle gained the opt-in
scenario `removal-soft` (`oracle/v3-successor/src/scenarios.rs`; no existing scenario changed).

### 14.1 Ground truth: ContractData removals past the soft limit

§13 argued that a `DeleteAccount` of an account with more than 2,000 ContractData keys makes the
recorder cross `main_storage_proof_size_soft_limit` while the witness stays small. This session
built that shape and its variants as whole chunks and judged them with the pinned cold nearcore
(2.13.4, `44f7ae6c`, PV86).

**Family `removal-soft`.** Quiet chain. Shard-0 accounts (layout shard id 3 or 0). Every probe chunk
also carries an incoming 1-yocto transfer from shard 1, and some carry a local "victim" receipt
(`R x`):

| shape | probe chunk | nearcore |
|---|---|---|
| `reinsert` (8 per seed) | three receipts, each with 700 `storage_remove`+`storage_write` pairs of the same keys (recorder bound 2,000 B per removal, 4.2 MB in total; witness about 46 KB) | the incoming transfer, and the victim when present, are deferred to the next chunk |
| `reinsert-one` (control) | one such receipt (1.4 MB) | the incoming transfer runs in the same chunk |
| `vm-delete` | two receipts with 1,200 first-time deletions each, then a victim | incoming and victim deferred |
| `delete-account` (4 per seed) | a 3.7 MB read plus `DeleteAccount` of an account with 190 one-byte entries (storage usage under the 10,000 B cap) | incoming deferred; witness values 3,705,070 B < 4,000,000 |
| `delete-account-large` (§13's literal shape) | 3.7 MB read plus `DeleteAccount` of a 2,100-key account | the action fails with `DeleteAccountWithLargeState` (`actions.rs:383`, `MAX_ACCOUNT_DELETION_STORAGE_USAGE` = 10,000 B). Nothing is removed and nothing is deferred |

**§13's literal shape cannot occur at PV86.** A `DeleteAccount` removes at most about 230 entries,
because storage usage is at most 10,000 B. The shape §13 needs does occur through VM
`storage_remove`, and through a capped `DeleteAccount` next to large reads.

Generation: `NEAR_SUCCESSOR_SCENARIO=removal-soft $B gen --domain d3 --seed S [--first-chain 1]
--chains 1 --blocks 80 --p-missing 0 --mutate-every 0 --code-mutant-p 0 --ood-cap 100000`. Seeds
1 and 2 use chain 0 (4 shards); seeds 3 and 4 use chain 1 (5 shards). Each seed shifts the start
height and the written fill byte. In total: 1,440 honest chunks (all `cold_ok`) and 5,856 mutants,
each mutant judged by nearcore (`verdict_source: nearcore(cold)`). Every probe chunk gets the full
mutant set. The probe outcomes of all 4 seeds (`removal-soft/probes.json`) agree with the table
above.

**Verdicts** (checker `2347323d…`, the main checker; `replay_successor.py`; per-case rows in
`removal-soft/*.results.jsonl.gz`; table `removal-soft/verdicts-table.json`):

| population | cases | `.storageResolution` acc / rej / ood | `.runtimeLimits` acc / rej / ood | `.signed` acc / rej / ood |
|---|---|---|---|---|
| crossing probes, honest (reinsert, vm-delete, delete-account) | 52 | 52 / 0 / 0 | **0 / 52 / 0** | **0 / 52 / 0** |
| crossing probes, mutants | 2,756 | 572 / 2,184 / 0 | **0 / 2,756 / 0** | **0 / 2,756 / 0** |
| controls (reinsert-one, delete-account-large), honest | 8 | 8 / 0 / 0 | 8 / 0 / 0 | 0 / 0 / 8 |
| controls, mutants | 400 | 88 / 312 / 0 | 88 / 312 / 0 | 0 / 172 / 228 |
| rest of the chains, honest / mutants | 1,380 / 2,700 | 1,380 / 0 / 0 · 600 / 2,100 / 0 | same | 1,362 / 0 / 18 · 600 / 2,100 / 0 |
| harness disagreements with nearcore | 7,296 | **0** | **624** | **624** |

* **Soundness: no Lean tier accepts a nearcore reject** (0 of 7,296 on all three tiers). The
  legacy shell's `w.size` guard (`base + 2000 · removals ≤ 4,000,000`, after the main transition)
  still excludes every successful legacy run on such a chunk. `base` bounds nearcore's recorded
  bytes, and the removal count only grows, so whenever nearcore defers, the legacy guard fails.
* **Completeness bug in the legacy-engine tiers, including `.signed`.** The 624 disagreements are
  the 52 honest crossing chunks and 572 nearcore-accepted mutants of them, for example
  `hdr.height_included(unchecked)`. On each, `.runtimeLimits` and `.signed` reject with
  `invalid: MissingTrieValue (account)` or `invalid: StorageInconsistentState(MissingTrieValue)`.
  The legacy engine has no soft limit: it runs the receipt nearcore deferred, and that receipt's
  values are not in the witness. `.floats` and `.genesis` give the same 52 rejects on the honest
  probes (`removal-soft/probe-honest-{floats,genesis}.jsonl`; the other narrow tiers
  share the engine). The §10 fix (`withStorageExclusion`) and the signed hand-over (`D3/Signed.lean`
  `handover`) both test `legacyMergedBytes w > 4,000,000`, and that test omits the 2,000 B charged
  per ContractData removal.
* **Not fixed.** The pre-approval covers the §10 kind of fix: make the narrower legacy tiers
  exclude, and keep the signed statement. That is not possible here, because the signed tier
  itself rejects these chunks. If only the narrow tiers excluded them, the proved pairs
  `.signed ⊑ .floats`, `.signed ⊑ .runtimeLimits` and `.signed ⊑ .genesisFloatsProtoGas` would
  become false, since `Refines` does not allow a signed reject against an exclusion. Any fix
  changes the signed checker's verdict on these witnesses, so the owner has to decide it.
  **Proposed fix:** extend the hand-over condition from `legacyMergedBytes w > 4,000,000` to
  `legacyMergedBytes w + 2000 · R > 4,000,000`, where `R` is the ContractData removal count of the
  recorder run on the same inputs (`MainOutD2.cdRemovals`), or `0` when that run fails. The signed
  tier then hands these chunks to the recorder, which accepts them as nearcore does. The narrow
  tiers report the `w.size` exclusion under the same condition, so the named pairs keep holding.
  Fixtures for that change: `removal-soft/cases.tar.gz` (60 honest probe chunks plus, for each, 2
  nearcore-accepted and 2 nearcore-rejected mutants; index and sha256 in
  `removal-soft/cases-index.json`). Breakage control: the current checker, which disagrees on all 52
  crossing chunks.

### 14.2 O4 under per-witness premises

§13's design, implemented:

* **The reference copy `NS`** (`TierO4NS.lean`) is the recorder at `fl0`, with four changes. It
  has no soft-limit test (G1). Each VM call gets a fresh `RealStore`, as in the legacy hook (G6). A
  call's code is excluded as `out of domain (e.code_attempted_only)` when only a rolled-back
  in-chunk deploy provides it (**G3b, new**: the legacy engine rejects with `MissingTrieValue`,
  while the recorder and nearcore serve it from the compiled-contract cache; reachable only if the
  witness does not reveal the receiver's pre-state account). Inside the hook, the computation after
  code selection runs in `Except` (`callTailNS`). `checkNS` is the storage-resolution shell at the
  `NS` driver.
* **Escapes.** `esc` names the strings by which `NS` (and the recorder) may fail where the legacy
  engine decides:
  * G2: `w.fuel_certificate`;
  * G3: `e.code_prep_race`;
  * G3b: `e.code_attempted_only`;
  * G4: `invalid: buffered receipts gas left …`, nearcore's `assert_eq!` in `forward_from_buffer`;
  * G7: `w.shape: global action`.

  `SimX`/`RefinesX` are `Sim`/`Refines` that additionally allow an `esc` failure on the recorder
  side. `o4x_lockstep` repeats the §10 shell walk for `RefinesX` (`checkD2CoreGWith_legacy_ns`,
  25 s).
* **`FCSim`, walked.** `functionCall_nf` puts `D3.functionCall` in a normal form (by `rfl` per
  contract and ETH-implicit case). `code_rel` relates the legacy code selection to
  `resolveColdCodeNS`: they agree, or the legacy one excludes (the in-chunk-deploy-served
  pre-state contract), or `NS` fails with G3/G3b. `tail_rel` relates the legacy VM tail to
  `callTailNS`: they agree, or `NS` fails G2. `simx_hook` handles the `unmodeled` wrapper and the
  value map; `HooksR_d3` shows that legacy hook values are fixed points of `·.wt T`.
* **G5 is unreachable** (`resolve_local_nonEth`). `Rci.resolve` redirects a local contract to the
  wallet only on an ETH-implicit account, and the legacy hook excludes every ETH-implicit account
  with a local contract before it resolves code. §10's description (a non-ETH-implicit account
  redirected) does not match the code.
* **G7** is an escape: `applyGlobal false` fails with `escG7` at once (`actSimNS`). No reachability
  argument is needed.
* **G4 is settled** (`fwdSimX`, every layout). V2 is `fwdSim_v2`. On V3, a non-empty buffer to a
  shard outside the layout is the legacy `c.same_layout` exclusion. An empty parent buffer forwards
  nothing (`ev_fwdToShard_empty`, `bufGet_outside`). The trailing empty-buffer assertion is the
  escape. The assertion is nearcore's own (`congestion_control.rs:281-284`, a panic), so on such a
  pre-state the recorder is the faithful one.
* **The receipt level, loops and main transition** are the §12/§13 walks repeated for `SimX`
  and `NS` with `P := True`. `RemClosed` and `soft` are no longer needed (`simx_*`,
  `simx_applyNewChunkD2`). **`engineAgreeX`** has no premise.

**Theorem** (`TierO4NSMain.lean`):

```
theorem relSuccessor_runtimeLimits_storageResolution (c w : Bytes) (hw : O4Witness w)
    (hNS : Tier.checker .storageResolution c w = checkNS c w)
    (hX : ∀ s, Tier.checker .storageResolution c w = .error s → esc s = false) :
    Refines (Tier.checker .runtimeLimits c w) (Tier.checker .storageResolution c w)
```

plus its verdict reading, `verdict_runtimeLimits_storageResolution`. Both premises are decidable
functions of `(c, w)`. **Non-vacuity:** `o4_premises_nonvacuous` exhibits `c = w = []`, with every
check run in the kernel (`decide +kernel`). That witness is trivial, because both shells stop at
the claim decoder. The measured rows below are the real-chunk instances.

### 14.3 The premises on data

`--o4-premises` (observation only) prints per case the `.runtimeLimits`, `.storageResolution` and
`NS` verdicts, `nsEq` (premise `hNS`) and `noEsc` (premise `hX`). It is a separate entry branch in
`main`; the tier path is unchanged. Its `.runtimeLimits`/`.storageResolution` columns match the
replays of checker `2347323d…` case for case (below). Checker `548f77c3…`. Rows:
`o4-ns/premises-*.jsonl.gz`; summary: `o4-ns/premises-summary.json`. `O4Witness` is not measured.
It holds on every original-format witness whose codes fit one code response, which covers every
case here.

| population | cases | `hNS` holds | `hX` holds | both | legacy decides | legacy decides, both hold | escapes seen | prediction violations |
|---|---|---|---|---|---|---|---|---|
| 577 fixtures | 577 | 577 | 577 | 577 | 294 | 294 | none | 0 |
| 3,138 census | 3,138 | 3,138 | 3,138 | 3,138 | 1,858 | 1,858 | none | 0 |
| storage-limit family: the 88 committed fixtures and 300 honest chunks sampled from 2,700 (seed 14) | 388 | 348 | 388 | 348 | 302 | 302 | none | 0 |
| `removal-soft`, honest chunks | 1,440 | 1,388 | 1,440 | 1,388 | 1,440 | 1,388 | none | 0 |
| `removal-soft`, the first 3,310 cases of the 7,296 in list order (run stopped) | 3,310 | 2,592 | 3,310 | 2,592 | 3,310 | 2,592 | none | 0 |

Where `hNS` fails: in the storage-limit sample, on 40 chunks, `.runtimeLimits` is excluded (the §10
`withStorageExclusion`). In `removal-soft`, on the 52 honest crossing chunks (718 of the 3,310
cases, mutants included), `.runtimeLimits` is wrong (§14.1). Neither is a theorem violation: the
theorem's premise fails there. Verdict identity of the instrumented columns: 577 + 3,138 + 1,440
cases against the replays (`.runtimeLimits` and `.storageResolution`), and 388 against the
storage-limit replays, all identical.

Where both premises hold, the theorem predicts `.runtimeLimits ⊑ .storageResolution`. The column
"prediction violations" checks that prediction against the verdicts. `nsEq` fails exactly on the
G1 shapes: the storage-limit probes and the `removal-soft` crossing chunks, where `NS`, like the
legacy engine, runs the deferred receipts. On those chunks `.runtimeLimits` is either excluded
(`withStorageExclusion`, storage-limit family) or wrong (§14.1). No escape string occurs in any
population.

### 14.4 What is open

* The §14.1 completeness bug of the legacy-engine tiers and `.signed`: the owner must decide the
  signed hand-over change (proposal above).
* O4 holds under `hNS` and `hX`. Discharging `hNS` would need a run-level argument that the soft
  limit and the per-receipt limit are never reached on a witness, or a VM lemma for G6 (results
  equal modulo `recd`/`acct` unless `RecordedStorageExceeded`). Neither is attempted. On the
  premise rows, `hNS` holds wherever the recorder's limits are not reached.
* G3b may deserve a recorder-side look. It is unreachable when the witness reveals the receiver's
  pre-state account, which the recorder itself records.

## 15. Update 2026-10-30 (sixth O4 session, continued): the removal-aware hand-over (§14.1 fixed)

This section implements the fix proposed in §14.1, on the coordinator's instruction under the user's
standing decision of 2026-10-27: a signed-tier reject of a valid chunk is fixed as a strengthening of
`checkD3`/`RelD3`.

Changed Lean:

* `D3/Signed.lean`: `removalProbe`, `recorderRemovals`, `storageCrossed`, and `handover e c w`, which
  now takes the claim;
* `Successor/Config.lean`: `withStorageExclusion r c w`;
* call sites and proofs in `TierProofs`, `TierRefine`, `TierMono`, `TierWholeWalk`, `TierO4` and
  `TierO4X`.

The full default build is ok (424 jobs). There is no `sorry`, and the axioms are unchanged.
`make pin-check` is ok. The v3.1 draft is regenerated with the new `w.size` text
(`spec/tools/near_chunk_v3_uq010.py`). The move is recorded as move (f) in owner map §3.4.

### The rule

A core error is handed over (signed tier) or excluded as `w.size` (narrower legacy tiers) when
`legacyMergedBytes w + 2000 · R > 4,000,000`, with `R = recorderRemovals c w`.

* **What `R` counts.** `R` is the number of ContractData removals in the main transition of the
  signed recorder engine, run on the same claim and witness. It uses `signedRecorderDriver` or
  `signedReshardDriver`, as the hand-over does.
* **How `R` is obtained.** A probe driver replaces the engine's `apply`. It stops right after the
  main transition and reports `cdRemovals` as its result. When the run stops before the main
  transition completes, `R = 0`.
* **Why the condition is not circular.** `R` depends only on `(c, w)`, not on the core's result.
* **When `R` is computed.** Only on a core error whose merged size alone is within the bound.
* **Why `R` is the right count.** The recorder runs the chunk as nearcore does. Up to the first
  receipt nearcore defers, its removals are nearcore's removals.

Both wrappers use the same condition, and it depends only on `(c, w)`. So `Refines.storage` still
gives every named pair: `.signed ⊑ .runtimeLimits`, `.signed ⊑ .floats`,
`.signed ⊑ .genesisFloatsProtoGas`, and the others. The O4 theorems now use
`withStorageExclusion_refines` in place of the old `_small` lemma.

### Evidence

* **After:** checker `9b583e3a…`, built from `61389b178`.
* **Before, and the breakage control:** the current checker `2347323d…`. It is semantically main's
  checker, because main has changed only proof modules since it was built.
* Per-case rows and the `ba.py` diffs are in `removal-handover/`.

| population | tier | cases | moves | toward nearcore | Lean accepts of a nearcore reject (after) | reject → OOD |
|---|---|---|---|---|---|---|
| `removal-soft`, all 7,296 (4 seeds) | signed | 7,296 | 624 `reject → accept`, all nearcore-valid (52 honest chunks + 572 accepted mutants). 956 nearcore rejects stay `reject`, now with the recorder's reason (`InvalidCongestionInfo`, header fields, post-state root) | 624 | 0 | 0 |

**PENDING.** These runs were still in progress at the time of this commit (`removal-handover/horun.sh`):

* signed on the full corpus (235,716 cases), diffed against `gateb-prefreeze/corpus-signed`;
* signed on shard 13 (1,223 chunks), before and after;
* signed and `runtimeLimits` on the 3,138 census and the 577 fixtures, with the before rows taken from
  `o4-replay/`;
* `runtimeLimits` on `removal-soft`. The expected result is 624 `reject → OOD (w.size)` moves, which
  is how the narrower tiers are designed to behave.
