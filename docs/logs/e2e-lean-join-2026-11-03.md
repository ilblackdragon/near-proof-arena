# E2E lane E (Lean join, M11), 2026-11-03

Plan: [`docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md`](../zk-formal/E2E-GENERAL-CHUNK-PLAN.md) §3.5 (status
and circuit interface there). Target per owner decisions D-1..D-7: `Tier.rel .allFeatures`, unbounded;
statement `∃ secB w, Tier.rel .allFeatures (assemble chunk_inner secB secC) w`.

## What was built (`spec/lean/v3/NearSpecV3/E2E/`)

| file | content | in `defaultTargets` |
|---|---|---|
| `Engine.lean` | engine machine: `EPos`, `stepM`, `den`; `den_step`, `den_ok_iff`, `engine_run_ok_iff` | yes |
| `Machine.lean` | chunk machine `CM`: `Conf`, `CM.step`, `Steps`/`StepsN`, `Outputs`, `headerOk`; `cm_iff`, `steps_of_chain`, `stepsN_of_chain`, `cm_done_header` | yes |
| `Statement.lean` | `PublicStmt`, `assemble`, `E2EStmt`, `e2e_statement_iff`; obligations `NvFaithfulE2E`, `WrapFinalFaithful`, `SegSound`, `WitnessExtraction`; `e2e_sound`; `reexec` non-vacuity | yes |
| `RealChunk.lean` | `cm_run_06_h10006_s0` on the real chunk `d3c7/d3/06-h10006-s0` | no (on demand, `HEAVY_MEM=40G`) |

## Method: same computation, not a reimplementation

* Every step body is a verbatim slice of the original code. The slice equations are `rfl`:
  `applyNewChunkD2_split`, `processLocals_eq`, `processIncoming_eq`, `processDelayedLoop_succ`,
  `yieldLoop_succ`, `checkReshardCoreObs_split`.
* Slices that end in a continuation are written in CPS (`preludeK`, `delayedK`, `yieldK`, `intakeK`,
  `finK`). Their naturality in the continuation (`*_nat`) is proved by a lock-step walk (`nat_walk`).
* The checker's prefix is cut into four pieces (`intakeK`/`intakeB`/`intakeB2`/`intakeC`). Uncut, the
  do-notation join points of its `if … then check …` lines are inlined by `simp` and the walk is
  exponential; cut, every walk is linear and the whole module checks in about 10 s.
* `nat_walk` and `post_walk` match binds with reducible transparency only. Otherwise they unfold
  the next piece's definition and re-walk it at every leaf.
* Postconditions come from naturality plus congruence (`intakeC_post`, `intakeB2_post`), so the large
  pieces are never walked with hypotheses.

## Statements (all `[propext, Classical.choice, Quot.sound]`)

```
theorem cm_iff (cb wb : Bytes) : Tier.rel .allFeatures cb wb ↔ CMAccepts cb wb
theorem e2e_statement_iff (s : PublicStmt) :
  (∃ secB w, (assembleClaim s.ci secB s.secC).wf = true ∧ Tier.rel .allFeatures (assemble s.ci secB s.secC) w) ↔
  ∃ secB w, (assembleClaim s.ci secB s.secC).wf = true ∧
    ∃ cf, Steps (.init (assemble s.ci secB s.secC) w) cf ∧ FinalOutPub s cf
theorem e2e_sound (S W FinalVerify Bad) (ob1 : NvFaithfulE2E S W FinalVerify Bad)
  (ob1b : WrapFinalFaithful S W) (ob2 : SegSound S Bad) (ob4 : WitnessExtraction S W Bad)
  (s π) (hv : FinalVerify s π = true) : E2EStmt s ∨ Bad
```

## Non-vacuity (the `compose_pv86` question)

* None of `NvFaithfulE2E`, `WrapFinalFaithful`, `SegSound` or `WitnessExtraction` mentions
  `Tier.rel`, `checkSuccessor` or `CMAccepts`. They speak about traces, boundaries and `CM.step`.
* `reexec` is a concrete proof system whose segments are `CM` runs (`Holds := StepsN`). It
  discharges obligations 1, 2 and 4 directly (`reexec_ob1/1b/2/4`). `reexec_sound` then reaches
  `Tier.rel`, and the only bridge is the proved `cm_iff`.
* Its verifier does not accept everything (`reexec_rejects_zero_steps`), and every true statement
  has an accepting proof (`reexec_complete`).
* On a real chunk, `cm_run_06_h10006_s0` gives an accepting `CM` run of the honest
  `d3c7/d3/06-h10006-s0`. The run is non-genesis (`decide +kernel`) and ends in `done H o` with
  `headerOk`. The run is obtained through `cm_iff` from the kernel-checked
  `relAllFeatures_06_h10006_s0`; the machine is not re-run by `decide`. T1
  (`d3c8/d3/02-h10196-s3`) has no Lean data module yet.

## Open

1. Obligations 1, 2 and 4 (circuit and recursion lanes).
2. Mid-call Wasm cuts: one engine step is a whole receipt.
3. The genesis-segment path is a single atomic step.
4. A concrete `abs`: the SHA-384 boundary encoding and its round-trip.
5. The instance of obligation 1 from `ZkFormal.PQ.NvFaithful` (a separate Lake package).
