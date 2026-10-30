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
