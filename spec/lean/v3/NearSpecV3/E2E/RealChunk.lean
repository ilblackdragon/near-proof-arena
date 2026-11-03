import NearSpecV3.E2E.Statement
import NearSpecV3.Examples.RealCaseD3

/-!
# E2E-M11 non-vacuity on a real chunk (on demand, not in `defaultTargets`)

The honest D3 chunk `d3c7/d3/06-h10006-s0` (an incoming FunctionCall to `d3ed`; nearcore `ok`)
is accepted by `Tier.rel .allFeatures` (`relAllFeatures_06_h10006_s0`, `decide +kernel` over the
whole checker in `Examples/RealCaseD3.lean`). Through the proved factorisation `cm_iff`, `CM` has
an accepting run on it, the run takes the segmented (non-genesis) path, and it has a finite clock.
So the premise of `e2e_sound`'s chain (an accepting `CM` run from `init`) is satisfied by a real
chunk, not only by hypothetical ones.

Build: `HEAVY_MEM=40G /data/illia/nearproof-deps/bin/heavy lake build NearSpecV3.E2E.RealChunk`
(the kernel evaluation of the checker dominates).
-/

namespace NearSpecV3.E2E
open NearSpecV3 NearSpecV3.Examples NearSpecV3.Successor

/-- `CM` accepts the real chunk. -/
theorem cm_accepts_06_h10006_s0 : CMAccepts claimD3_06_h10006_s0 witnessD3_06_h10006_s0 :=
  (cm_iff _ _).1 relAllFeatures_06_h10006_s0

set_option maxRecDepth 200000 in
/-- The real chunk takes the segmented path (`INTAKE` → engine steps → `FINAL`), not the atomic
genesis step. -/
theorem segment_no_genesis_06_h10006_s0 : segmentHasGenesis claimD3_06_h10006_s0 = false := by
  decide +kernel

/-- An accepting run with a finite global clock, ending in `done H o` with `FinalOut` true. -/
theorem cm_run_06_h10006_s0 :
    ∃ n H o, StepsN n (.init claimD3_06_h10006_s0 witnessD3_06_h10006_s0) (.done H o) ∧
      headerOk H o = true := by
  obtain ⟨cf, hs, ha⟩ := cm_accepts_06_h10006_s0
  obtain ⟨n, hn⟩ := steps_iff_stepsN.1 hs
  cases cf with
  | done H o => exact ⟨n, H, o, hn, ha⟩
  | doneG =>
    have := steps_init_doneG hs
    rw [segment_no_genesis_06_h10006_s0] at this
    cases this
  | _ => simp [Conf.accepting] at ha

#print axioms cm_run_06_h10006_s0

end NearSpecV3.E2E
