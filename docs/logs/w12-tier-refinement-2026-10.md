# Lane W12: tier refinement (workplan item 5). Log, 2026-10-29/30

Worktree `agent-a5081ae59762de001`, branch `worktree-agent-a5081ae59762de001`, from main
`4f07a7fdf`. Host shared with 7 lanes (load average 160–180 on 32 cores during this work). Lean
runs used `LEAN_NUM_THREADS=8`; the full build ran under `heavy` with `HEAVY_MEM=24G`.

## 2026-10-29

* Read the workplan, `TierMono.lean` (O1–O7 list), `TierProofs.lean` (`Refines`,
  `refines_lockstep`), `Config.lean` (tiers), and `D3/FunctionCall.lean`, `Wasm/{Prepare,Exec}.lean`,
  `D2/{Actions,Receipts,RuntimeD2}.lean` and `Successor/StorageExecution.lean`.
* Triage of the obligations by the engine each named pair runs:
  * O1 floats: every pair that differs in `floats` runs the legacy engine (`checkD2Core` /
    `checkD2CoreG` with `d3Hooks`). Feasible: the flag is in `NearCfg` and read only by the three
    preparation guards.
  * O5: every tier sets `loadingLimits` (signed since 2026-10-27), so no named pair differs in it.
  * O2, O3, O7: the named pairs run the recorder engine (`StorageExecution`, a
    `StateT Recording` monad). O2's selector is in the interpreter state `St`, and O3/O7 change
    `Recording` fields. All three need a simulation with a state relation. Deferred.
  * O4 (engine agreement) and O6 (`ReshardCore` restructures the shell): dedicated
    correspondence proofs. Deferred.
* `TierHooks.lean`: `HooksRefine` and the lockstep walk of the legacy pipeline. The first version
  closed each step with a default-transparency `exact Refines.refl _`, which unfolded whole
  pipelines when subterms differed. The check had not finished after 40 min under the host load.
  Fix: `with_reducible` closers, plus a default-transparency `refl` only on leftover goals.
* `TierFloats.lean`, preparation: `PRef` with `pref_lockstep`. `sectionBody_floats` went through
  on the first try. A direct walk of `earlyPass` timed out (heartbeats), because its section
  `match` relates two different runs. Fix: `earlyPassWith` (a verbatim copy, `rfl`) and
  generalising both runs at the `match`.
* `TierFloats.lean`, hook: a direct walk of `D3.functionCall` made `split` case-split the two
  `contractOOD`/`runCallWithLimits` matches independently (≈ 20 incoherent goals). Fix:
  `functionCallWith` (verbatim copy, `rfl`) plus `CallRel`. On the left's `none` branch,
  `CallRel.none` rewrites the right side. `‹_›` and `obtain … := … hsplit` inside `first` log
  their errors instead of failing over to the next alternative, so the step is written with
  `refine (fun hx => ?_) (CallRel.none h (by assumption))`.

## 2026-10-30

* `TierFloats.lean` checks with no errors and no `sorry`.
* `TierRefine.lean`: `Lift.floats_legacy`, the named O1 pairs, O5 (`Tier.cfg_loadingLimits`,
  `relSuccessor_runtimeLimits_mono`), and the O7 resolve-level lemmas. Added to `defaultTargets`.
* `Lift.floats_legacy`: unfolding `checkSuccessor` and unifying against the unreduced right side
  timed out (heartbeats). Fix: `checkSuccessor_legacy_eq` normalises both sides first.
* The default `lake build` (315 jobs) completed. Build times with load average about 170: `TierFloats`
  1,194 s, `TierHooks` 166 s, `TierMono` 154 s (doc comment only), `TierRefine` 1 s. `make pin-check`
  is ok.
* Evidence: `docs/evidence/lean-chunk-completion/tier-refinement-w12/`.

## Axiom audit

See `docs/evidence/lean-chunk-completion/tier-refinement-w12/axioms.txt` (verbatim
`#print axioms` lines from the build).

## Open (reasons in the evidence README §2)

O2, O3, O4, O6, and O7 at chunk level. Floats on the whole-state engine (no named pair needs it).

## 2026-10-30 (continued, after the coordinator's follow-up)

* Merged main (fast-forward to `bc4637d80`).
* **Race arm fix (pre-approved).** `resolveCompleteCode` (CodeResolution.lean) sends the untimely
  committed-deploy arm to the cold policy's race exclusion. Only that arm changed; W08 owns the rest
  of the complete-code policy. Lean pieces: `complete_untimely_ood`, `complete_ok_coldPartial`, and
  `#guard` tests.
* **Fixture generator.** New opt-in scenario `pipeline-race` in `oracle/v3-successor`. It gave 4 runs
  (seeds 1201–1204, 110 blocks each, about 3 min per run) and 3,853 nearcore-judged cases, of which
  188 reach the arm. Replays: 3 tiers × {fixed, control} = 23,118. A1 (no unsound accept) and A2
  (race arm) pass; A3 (breakage control) is detected on 142 cases. Finding: every pre-fix accept on
  the arm agreed with nearcore. The family's races come from Lean's own `uncertain` flag (a
  global-contract call), and nearcore is deterministic there. The fix is the workplan rule applied,
  at the cost of 186 decided cases.
* **Machinery.** `TierWhole.lean` (`MRef`, `functionCallRecordedWith`) and `TierWholeWalk.lean` (the
  recorder-engine walk, the shells' `*_apply_mono`, and `Lift.floats` at every configuration). One
  lesson: Lean's `repeat` swallows the max-recursion error and stops a long walk silently, so a
  second `all_goals` pass is needed.
* **Corpus before/after.** The first attempt (every `ood` directory plus 10% of the code mutants,
  9,743 cases) was too slow on the loaded host (minutes per heavy `ood` chunk). It was restarted on
  the 10% code-mutant sample (2,739 cases).
* Open: O2, O3, O4, O6, and O7 at chunk level. Reasons are in
  `docs/evidence/lean-chunk-completion/tier-refinement-w12/README.md` §5.

## 2026-10-30, after the W08 merge

* Merged main `459a66c8a` (W08: completeCodeGlobal = cold policy). Conflicts:
  * `CodeResolution{,Tests}.lean`: main's version taken unchanged.
  * `d3gen.rs`: both scenarios kept (`code-cache` and `pipeline-race`).
  * `lakefile.toml`: main's targets plus `TierWholeWalk`.
* The W12 race-arm fix is superseded. The `TierRefine` O7 lemmas were restated for main's policy:
  `complete_untimely_ood`, `complete_ok_coldPartial`, `raceExclusion_isExclusion`. The pre-fix lemma
  `complete_accepts_untimely` is gone (main's policy never accepts the arm).
* The corpus before/after replay of the W12 fix was stopped (superseded).

## 2026-10-30, second session (flags refactor, O7 at chunk level)

* Merged main `5b505261b` (items 3, 6, 11, W01, W08). One conflict: `lakefile.toml` targets (main's
  list plus `TierStoreAuth`). Main had already repaired the W12 modules for its renames. Full default
  `lake build`: 391 jobs, ok (merge commit `eb057760e`).
* **Flag refactor (approved by the integrator).** `StorageExecution.Flags` replaces the
  `Recording.globalActions` / `Recording.codePolicy` fields. `StorageExecutionOrig.lean` keeps the
  pre-refactor engine (state `RecordingO extends Recording`); `TierFlagsEq.lean` proves
  `run_eq_orig`. Lessons:
  * every closer in the walk must be `with_reducible`: a default-transparency `exact Sim.leaf _ _`
    tried against an unrelated goal unfolds the engine and never returns;
  * the frozen copy's `match` auxiliaries are different constants (some shared with other modules
    by Lean's matcher cache), so `split` cased only one side. `orig_matchers` swaps each for the
    refactored side's auxiliary of the same type after an `isDefEq` check;
  * `fun (_, _) => ?_` inside `first` logs an error instead of failing over when the bound type is
    still a metavariable; the `foldlM`/`forIn`/`mapM` alternatives now come before it.
  * `applyActionReceipt`: nested `do` join points made the zeta-reducing walk exponential (25 min
    timeout). `sim_let` (an `elab` tactic) abstracts each join-point pair behind a `Sim` hypothesis;
    `sim_intro` only introduces syntactic `∀` (a plain `intro` unfolded `Sim`). `TierFlagsEq` now
    checks in about 15 minutes.
* Default `lake build`: 394 jobs, ok. `make pin-check` ok. `nearspec-v3-test-storage-resolution`
  updated for the new signatures (`processIncoming {} …`) and passes.
* Verdict identity of the refactored binary: 577 fixtures × 4 tiers and the 3,138 census × 2 tiers,
  0 verdicts and 0 reasons changed (README §6, `flags-replay/`).
* `TierWhole`/`TierWholeWalk` generalised: `functionCallRecordedWith` takes `ga` and the code
  resolution (`resOf`) as parameters; `RecRefine P ga p cfg p' cfg'` carries an environment
  predicate. O1 is the instance `P := True`.
* **O7 at chunk level proved** (`TierO7.lean`): `Lift.completeCode` on every whole-state
  configuration, both directions; `.completeCodeGlobal ⊑ .globalActions` and the converse.
* Open: O2, O3, O4, O6 (README §6 lists the precise remaining pieces).

## 2026-10-30, after the coordinator's follow-up (items 1–5 requested)

* Merged main `33114b3f0` (fast-forward of the W12 merge plus main's own changes).
* O3 pre-check (source reading): the D2 decoders exclude (`oodDeployGlobal`, `oodUseGlobal`,
  `oodStateInit`, `oodMlDsaKey`) where the global decoders accept. No reject finding so far.
* Stopped here because the context was long. The exact next steps are in README §6, "Next steps".

## 2026-10-30, third session (O2 proved, O3 components)

* Started from main `809e174be`. Lake cache copied from the previous W12 worktree (hash-checked by
  lake; only changed modules rebuilt).
* **Generator.** `HostComm.lean` was rewritten around a combined flag map `setF oc og`, following
  `Logged/WasmCR*.lean` (map `E σ`), which already had the full per-arm framework. Generated
  `HostCommArms.lean` (`gen/gen_hostcomm_arms.py`; arm list from `FuelHost.lean`): 89 arms, 35 s.
  Only two hand fixes: `thenDataIdsH`'s `modify` (a case split on `t.real`) and a missing helper,
  `yieldCreateWithIdH` (unbounded heartbeats). The ten lifted arms commute only with `og = none`.
* **Two-run steps** (`HostCommStep.lean`). The relation `RR X φ` records *which* message the lower
  run stopped with: a free `∃ w, lower = .unmodeled w` would have needed `lineOutcome` on a symbolic
  string, and `String.splitOn` is well-founded recursion (neither `decide` nor `decide +kernel`
  reduces it). With the 14 (O2) or 10 (O3) messages closed, `split_eval` (unfold `splitOnAux` by
  its equation lemma, then `decide`) evaluates each line.
* **O2 proved** (`TierO2.lean`): `instantiate_curve`, `runCall_curve`, `lineOutcome_XC`,
  `recRefine_curve`, `Lift.curveHosts` (every whole-state configuration),
  `relSuccessor_storageResolution_curveHosts`. Lessons:
  * `run` with a variable fuel does not unfold under `rfl` (smart unfolding), so
    `callEntry {cfg with curveHosts := b} = callEntry cfg` needs induction (`run_curve_cfg`);
    `step`, `prepare`, `fuelCertified`, `wasmFuel`, `contractOOD` are `rfl`.
  * `lk_split` on two runs whose discriminants differ splits each side separately and walks into the
    tail; naming the tail (`runCallT`/`runTail`, `rfl` copies) stops the walk at the right place.
  * A structure update as a function argument must be parenthesised, and its continuation lines must
    start at or right of the first field.
* **O3 decoder check finished** (README §7 table): every newly accepted shape is a D2 `w.shape`
  exclusion. Proved: `pPkGlobal_of_pPk`, `pBaseGlobal_of_pBase`, `pActGlobal_of_pBaseAct`, the four
  exclusion lemmas, `finishActsGlobal_of_finishActs`, `managerGlobal_eq_manager` (logs without raw
  actions), `globalTarget_of_not_distribution`. Gap: delegate/transaction re-serialization needs a borsh
  round-trip lemma; not a nearcore disagreement.
* No nearcore replay was needed: no refinement was found false; no definition changed, so no verdict
  can move (the checker binary is unchanged; the new modules are proof-only).
* Default `lake build`: 399 jobs, ok. `make pin-check` ok. Axioms: `axioms-o2-o3.txt`.
* Open: O3 composition (README §7 "what remains", steps 1–6), O4, O6.

## 2026-10-30, third session (O6)

* Branch from main `809e174be`. O6 is proved at verdict level (`TierO6.lean`, a default target;
  README §7): `checkSuccessor_resharding_vmono` (`VLift cfg {cfg with resharding := true}` on every
  whole-state configuration with the genesis main transition and the Gate-B bounds in force), named
  `.curveHosts ⊑ .resharding` (`relSuccessor_resharding_vmono`) and the resharding premises of the two
  `allFeatures` compositions (`relSuccessor_curveHosts_allFeatures_of_GA` now needs only O3,
  `relSuccessor_globalActions_allFeatures_of_C` only O2).
* Data first: `curveHosts` against `resharding` on the gap census, both resharding fixture sets and
  item 6's `l6-uq010` chains (all honest/ood cases, every tenth mutant): 17,050 cases (60 fixtures, 3,138 census, 9,300 honest, 4,492 mutants), 0 violations; one reject-reason difference, the known Finding 2 fixture. The raw split
  runs of `resharding-fixtures-2` are no longer on disk. No violation, so nothing to exhibit against
  nearcore and no definition changed.
* Lessons:
  * `simp only` with `throw_bind'`/`pure_bind'`/`ok_bind'` (all `rfl`) collapses the dead
    continuations that zeta-inlined `do` join points copy into every `throw` arm: the unfolded
    `checkD2CoreWithObs` goal went from 123k lines to 900, and the whole correspondence checks in
    seconds.
  * The two shells' `match`es are different auxiliary matchers, so `split` cases only one side.
    `cases h : discr` (both sides generalise) or `split` on one side plus `simp only [heq]` on the other
    work; lemmas about a match are applied with `exact` (defeq), never `rw`/`simp`.
  * `fun B => by try dsimp only; unfold …` parses as `try (dsimp only; unfold …)`; write
    `(try dsimp only); …`.
  * Loops with `mut` state were handled by abstract scan lemmas (`scan_phase0/1`, `scan_post`) whose
    step hypotheses are discharged on the concrete body after `refine` instantiates it.
* Default `lake build` (395 jobs) ok; `make pin-check` ok. Open in W12: O2, O3, O4.

## 2026-10-30, fourth session (O3 steps 1–3)

* Started from main `1a490cd64`; lake cache copied from the third session's worktree.
* Integrator decision recorded (README §8): O3 under the well-formed-layout hypothesis (nearcore's
  `ShardLayout` V2/V3 constructors assert `shard_ids.len() == boundary_accounts.len() + 1`; trusted
  claim fact under A1/UQ-013). No checker definition changes.
* Step 1: `HostQ.lean`, `HostQArms.lean` (generated; the arm walk checks in about 25 s), `HostQStep.lean`.
  Trick: the invariant on non-call instructions comes from commutation with `setX` read at `setX s s = s`,
  so the existing `sf` walk did the work.
* Step 2: `TierO3Call.lean` (about 6 min, mostly `lineOutcome_XG`'s ten `split_eval`s). The
  instantiated state's facts are kept by an elaborator that generalizes the `instantiate` call with
  its equation (`inst_gen`) before `lk_split` loses it.
* Step 3: `TierO3Codec.lean`. `pActGlobal_of_pAct`, `pTxD2Global_of_pTxD2`.
* Findings for step 5 (README §8): the pipeline state diverges where the D2 codec excludes a stored
  receipt (lower pipe `uncertain`), so the engine walk needs a state relation; `finishActs` errors
  are `unmodeled` and only become exclusions through `applyAction`'s catch.
* Open: README §8 steps 4–6, O4, O6.

## 2026-10-30, third session (O4, storage resolution)

* Started from main `809e174be` (worktree `worktree-agent-a4c8f20bec2a73f04`).
* **Statement first, then data.** `TierO4.lean`: `O4Witness` (original witness format, codes fit
  one code response), `EngineRef`/`EngineAgree` (engine obligation), and the shell walk
  `checkD2CoreWithObs_legacy_recorder` / `checkD2CoreGWith_legacy_recorder` (decode,
  code-response and size phases; `o4_lockstep` is `refines_lockstep` plus `Refines.engine_bind`
  and a right-only passing guard). Checked in about 10 s.
* **Data check** (`runtimeLimits` vs `storageResolution`, checker `54b8a117…`): 577 fixtures and
  3,138 census: 0 violations. Committed `storage-limit-fixtures` (88): **26 violations**, all
  nearcore `ok`: `runtimeLimits` rejects with `MissingTrieValue`/`StorageInconsistentState(MissingTrieValue)`,
  `storageResolution` accepts. Full honest storage-limit family (2,700 of the 3,098 cases still on
  disk): `runtimeLimits` rejects 44 nearcore-valid chunks.
* **Fix (legacy side, pre-approved: signed statement unchanged).** `Config.withStorageExclusion`
  on `checkSuccessor`'s non-hand-over legacy branches: a legacy reject on a witness above the
  legacy storage bound is the `w.size` exclusion. Proved: `checkD2CoreG_ok_bound` (`NoAcc` walk:
  the legacy shell never accepts above the bound), `relSuccessor_runtimeLimits_storageResolution_of`
  (given `EngineAgree`, on `O4Witness` files, no size premise). Restated the narrow named pairs on
  `checkSuccessor signedCfg`; `Refines.storage` congruence for the generic lifts; `FloatOverlap`
  re-proved from the hook refinement. Full default build: 395 jobs ok; `make pin-check` ok;
  gate-b-caps and storage-resolution test executables pass.
* **Engine phases E0, E1 proved**: `applyNewChunkD2_eq_logged`/`engineAgree_of_logged` (legacy
  engine = its logged mirror) and `logged_run`.
* **Engine agreement open**, and false over arbitrary stores: README §7 lists five shapes (G1–G5)
  where the recorder excludes or diverges and the legacy engine decides; none seen in data. G3
  (pipeline `uncertain` taints unrelated calls) is the likeliest on a real chain; its fix changes
  the recorder engine the signed hand-over runs, so it is left to the owner.
* Replay evidence and before/after tables: `docs/evidence/lean-chunk-completion/tier-refinement-w12/o4-replay/`.

## 2026-10-30, fifth session (O3 step 4, step 5 foundations)

Worktree `agent-a60a3c17715884969`, from main `bb6afecd0`; merged main `18c1c7fcc` (O4) before
handover. Lean runs under `heavy` with `HEAVY_MEM=32G`, `LEAN_NUM_THREADS=10`.

* **Step 4 proved** (`TierO3Dec.lean`): `XR` relation (equal, or the lower decoder fails in `X`);
  every receipt parser against its global version with `X = w.shape`, `decodeStoredRcpt_ref`,
  transactions and the witness with `X = exclusion` (`pTxD2_ref`, `decodeWitness_ref`); the D2
  decoders never produce distribution receipts. Engineering: two parsers that elaborate their
  `match` on the same discriminant through different matchers split separately; rewrite both to one
  parametrized copy (`decodeStoredW`, `rfl`) first. In `pTxD2`, case the signature tag with
  `rcases st with _ | _ | _ | st` and close the upper `match` by `split` on the small goal
  `y = .error e`.
* **Step 5a/5b/5c proved**: `TierO3Pipe.lean` (the pipe relation, all pipe updates),
  `TierO3Queue.lean` (`Layout.WF`, `SRel`/`LR`, the queue operations as policy instances,
  `PolRel` refinement), `TierO3Engine.lean` (`RecRel`, `MRQ`, monad and state rules).
  Engineering: in `do` code the continuation is pushed into `match` branches, so state relational
  lemmas on whole function bodies of one parametrized definition (the queue functions at two
  policies), rewrite the upper discriminant to the lower one, then `split` once.
* **Finding**: the engine walk needs the non-distribution invariant on every `RS` of the lower run
  (the shells' `outgoingRoot` reads `out.outgoing`), not only at `emitReceipts`. `MRQ` carries it as
  a value predicate. Next steps: README §11.

## 2026-10-30, fourth session (O4, engine agreement)

* Started from main `18c1c7fcc` (worktree `worktree-agent-a994ce707a5fba315`).
* **Finding G0**: `EngineAgree` as stated in §10 was false on every legacy accept (the recorder's
  output carries `committed`/`compute`, the legacy output does not), so the conditional tier theorem
  was vacuous. Fixed on the proof side: `obsClear`, `ExecutionDriver.clearObs`,
  `checkD2CoreWith_clearObs`/`checkD2CoreGWith_clearObs` (every driver); `EngineAgree`,
  `EngineAgreeL` and the `SimE` bridge restated on `obsClear`-ed outputs; shell and tier re-proved.
* **`TierO4Engine.lean`**: the simulation `Sim` against the original legacy engine (each mirror
  lemma `R_f` is a step, so no per-mirror trie-independence lemmas), lockstep tactics `main_walk`,
  `recv_walk`; proved the main transition (phases 1–5, 7), the receipt loops, yield timeouts, V2
  forwarding, and the bridge `engineAgree_of_obligations` /
  `relSuccessor_runtimeLimits_storageResolution_of_obligations`.
* Open: `PWISim` (per receipt, incl. the function call: G2, G3, G5 and the VM recorder state), the
  invariant's `reads` lemma and G1, V3 forwarding (G4). Premise proxies on the replays: all 0
  (`o4-engine/premise_proxies.json`). README §11.


## 2026-10-30, fifth O4 session (per-receipt simulation)

* Started from main `723b67bac` (worktree `worktree-agent-ab2ec38d0f005ec6d`).
* **`TierO4Receipt.lean`**:
  * `pwiSim_of_actSim` (step 1) covers `emitReceipts`, `actionLoop`, `applyActionReceipt`,
    `processReceipt`, `processWithTotals` and `drain`.
  * `actSim_of`/`pwiSim_of` (step 2) handle ordinary actions via `R_applyAction` with the D2 hooks
    plus `accountRemovals`.
  * Together they reduce `PWISim` to the hook obligation `FCSim`, `GlobalSim` (G7) and
    `RemClosed` (G1).
* **Finding**: §12's `EngineObligations` cannot be satisfied, because `PWISim` ranges over every
  value and must also meet `soft` (`remClosed_soft_absurd`). So the §12 tier theorem is vacuous.
  Every "for every value" premise has the same problem (G1, G2, G3, G6, G7). README §13 gives the
  fix: variant drivers for silent divergences, verdict escapes for exclusions, and premises stated
  per witness.
* **Finding G7** (global actions): the legacy engine records an action failure when the existence or
  permission check fails, while the recorder excludes at once. Unreachable on decoded inputs.
* Engineering: pure-bind walk rules need `with_reducible`. At default transparency the file took
  over 15 minutes and 24 GB.
* Not done: `FCSim` (step 3), checker instrumentation and the G1 measurement (step 4), step 5.

## 2026-10-30 — O3 steps 5d–5f (sixth session)

* Step 1 proved (`TierO3Inv.lean`): single-run store-program facts (`LOk`), `ND rs.outgoing` kept by
  every queue program and `processTxD2L`, no distribution receipt from `applyActionL d2HooksL` or
  `refunds`. `MRQ` generalized to `MRX X` (`TierO3Engine.lean`).
* Step 2 proved (`TierO3Rec.lean`): `functionCallRecorded_global` (up to exclusion-or-`unmodeled`),
  `applyAction_global` through the `try … catch`.
* Step 3 in part (`TierO3Walk.lean`): the walk through `applyActionReceipt`, `processReceipt`,
  `processWithInstant`, `processLocals`, `processIncoming`. Open: `processDelayedLoop` (pipe read; plan
  in README §12), `yieldLoop`, `applyNewChunkD2`/`run`, step 4. No `sorry`; axioms `propext`,
  `Classical.choice`, `Quot.sound`; `make pin-check` ok. No refinement found false on a real chunk.
* Engineering finding: a walk tactic that lets `exact`/`refine` unify the two runs' programs by
  unfolding times out (it evaluates the interpreter); every rule is guarded by the lower program's head.

## 2026-10-30 — O3 finished under the layout hypothesis (seventh session)

* Engine (`TierO3Run.lean`): `MRX.get_pipe_step`; the delayed loop's `pipe.next` read as one pipe
  update (`pdl_succ`, `stepF`, `pipeFn_step`); `processDelayedLoop_rr`, `yieldLoop_rr`,
  `applyNewChunkD2_rr`, **`run_global`** (refinement on `env.ctx.layout.WF`) and `run_global_nd`
  (no distribution receipt in the lower output).
* Shells and `Lift` (`TierO3Lift.lean`): `LayoutsWF`, `DrvRel`, `drvRel_of_lower`;
  `checkD2CoreWithObs_o3`, `checkD2CoreGWith_o3`, `checkReshardCoreObs_o3` thread the layout fact to
  `env.ctx.layout` (the resharding core's main layout via `walkSegment_mainLayout`);
  **`Lift.globalActions_wf`**, `relSuccessor_storageResolution_globalActions_wf`,
  `relSuccessor_resharding_allFeatures_wf`, `relSuccessor_curveHosts_allFeatures_wf`.
* Non-vacuity (`TierO3Real.lean`): `LayoutsWF` decided by `decide +kernel` on `d3c7/d3/06-h10006-s0`
  and on the resharding chunk `seed37-00-h10085-s7` (two distinct layouts). With O2:
  `relSuccessor_globalActions_allFeatures` (unconditional, verdict level) and
  `relSuccessor_storageResolution_allFeatures_wf`.
* No `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`; `make pin-check` ok. No refinement
  found false on a real chunk.
* Engineering: `repeat` only re-walks the first goal (use `repeat'`); `lower_bind_has` misses goals
  with metadata in the spine (`lbh`/`lhd`).


## 2026-10-30, sixth O4 session (removal ground truth, O4 under per-witness premises)

* Started from main `4d48255b9` (worktree `worktree-agent-a2e72e08b02b153e5`).
* **Ground truth first.** Added the opt-in scenario `removal-soft` (`oracle/v3-successor`).
  ContractData removals push the recorder past the 4,000,000 B soft limit while the witness values
  stay under it. Shapes: VM `storage_remove` with reinsertion, first-time VM deletions, and a capped
  `DeleteAccount` next to a 3.7 MB read; plus §13's literal shape (`DeleteAccount` of a 2,100-key
  account). 4 seeds, 7,296 cases, judged by cold nearcore 2.13.4.
  * The literal shape fails in nearcore with `DeleteAccountWithLargeState`: storage usage is capped
    at 10,000 B. The other shapes defer receipts.
  * **No Lean tier accepts a nearcore reject.**
  * `.runtimeLimits`, `.floats`, `.genesis` and **`.signed`** reject all 52 crossing honest chunks
    and 572 nearcore-valid mutants (`MissingTrieValue`). `.storageResolution` agrees with nearcore
    on all 7,296.
  * Not fixed. The signed tier has the bug too, and a narrow-tier-only exclusion would falsify
    `.signed ⊑ .runtimeLimits`/`.floats`/`.genesisFloatsProtoGas`. Proposed hand-over change and
    fixtures in README §14.1 and `removal-soft/`.
* **§13's design, implemented** (`TierO4NS`, `TierO4X`, `TierO4NSSim`, `TierO4NSMain`):
  * the reference copy `NS`: no soft test, a fresh VM store, and the G3b exclusion;
  * `SimX`/`RefinesX` with the escape set `esc` (G2, G3, G3b, G4, G7);
  * `FCSim` walked through a normal form of the legacy hook;
  * G5 shown unreachable; G4 proved on every layout;
  * `engineAgreeX` with no premise.
  * **`relSuccessor_runtimeLimits_storageResolution`** has two per-witness premises (`hNS`, `hX`).
    `o4_premises_nonvacuous` checks them in the kernel on a witness.
  * Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
* **New finding G3b**: code that only a rolled-back in-chunk deploy provides. The legacy engine
  rejects; the recorder and nearcore serve it from the compiled-contract cache. It needs the
  receiver's pre-state account to be unrevealed. It is an escape of `NS`.
* **Instrumentation**: `--o4-premises` (observation only; its tier columns are identical to the
  replays). Premise counts on the fixtures, the census, the storage-limit family and `removal-soft`
  are in README §14.3.
* Engineering: whole-module builds take 25 s (`TierO4X`), about 4 min (`TierO4NSSim`, mostly
  `simx_applyActionReceipt`) and about 2.5 min (`TierO4NSMain`). The legacy hook's do-block
  duplicates its continuation into every branch, so the walk goes through `functionCall_nf`. That
  lemma is proved by `rfl` per contract case, after destructuring `ActSt`/`Acct`, so that `simp`
  cannot rewrite fields.
