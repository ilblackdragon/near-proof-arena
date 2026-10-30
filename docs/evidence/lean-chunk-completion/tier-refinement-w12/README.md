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
| O3 | global actions | open. Proved (§7, §9): interpreter two-run host call; the lower run's invariant over every host arm and run (`LowQ`); call level (`runCall_globalG`, `vmF_global`, `vmCall_lowQ`, `lineOutcome_XG`); decoder agreement on keys, base actions, delegate actions and transactions (`pActGlobal_of_pAct`, `pTxD2Global_of_pTxD2`); D2 exclusions on every newly accepted shape; manager/`finishActs` agreement; queue target. Open: stored-receipt decoder agreement, the engine walk with `ga` differing (needs a state relation on the pipeline, §8), driver fields, `Lift` under the well-formed-layout hypothesis | `callHost_RR_global` (`HostCommStep.lean`); `globalHyp` (`HostQStep.lean`); `TierO3.lean`, `TierO3Call.lean`, `TierO3Codec.lean`; routing: `recorderDriver_receiptShard_globals`, `recorderDriver_outgoingRoot_globals` (`TierMono.lean`) |
| O4 | storage resolution | **proved at shell and tier level given the engine agreement** (2026-10-30, §10), after a legacy-side fix (26 nearcore-valid chunks the narrower legacy tiers rejected); the engine agreement `EngineAgree` is open (phases E0, E1 proved) | `relSuccessor_runtimeLimits_storageResolution_of`, `checkD2CoreGWith_legacy_recorder`, `checkD2CoreG_ok_bound`, `engineAgree_of_logged`, `logged_run` (`TierO4.lean`) |
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
