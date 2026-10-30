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
