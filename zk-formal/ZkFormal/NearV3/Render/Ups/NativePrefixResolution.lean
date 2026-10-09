import ZkFormal.NearV3.Render.Ups.NativePrefixTwo

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near

/-- Pre-terminal rows depend only on path levels, not on the terminal target.
The off-path resolver can therefore be corrected without changing these rows. -/
theorem fourWalk_prefix_target_independent (I : UpsInst) (bm hv ek1 ek2 target1 pos1 target2 pos2 t : Nat)
    (hb : 1≤I.ts ∧ I.ts≤3) (ht : 1≤t ∧ t<I.ts) :
    (step (withFourWalk I bm hv ek1 ek2 target1 pos1) t).e=
      (step (withFourWalk I bm hv ek1 ek2 target2 pos2) t).e := by
  rcases (show I.ts=1 ∨ I.ts=2 ∨ I.ts=3 by omega) with hs|hs|hs
  · omega
  · have he : t=1 := by omega
    simp [step,withFourWalk,fourWalk,hs,he]
  · rcases (show t=1 ∨ t=2 by omega) with he|he <;>
      simp [step,withFourWalk,fourWalk,hs,he]

/-- The corrected occurrence resolver leaves every physical prefix edge intact. -/
theorem nativeInstance_prefix_resolution (recordId : PTrie→Nat) (valueId : Slot→Nat)
    (resolved1 resolved2 : PTrie→Nat) (baseI : UpsInst) {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (Qs : List UpsPartI) (t : Nat)
    (ht : 1≤t ∧ t<run.splitCursor [0,15]) :
    (step (nativeInstance recordId (nativeWalkBase recordId valueId resolved1 baseI root run v)
      root run v Qs) t).e=
    (step (nativeInstance recordId (nativeWalkBase recordId valueId resolved2 baseI root run v)
      root run v Qs) t).e := by
  let I := nativeInstance recordId baseI root run v Qs
  let target1 := nativeTerminalTarget valueId resolved1 run (recordId run.terminalSource)
  let target2 := nativeTerminalTarget valueId resolved2 run (recordId run.terminalSource)
  change (step (withFourWalk I (terminalBitmap run) (terminalHasVal run)
    (nativePathEdgeKind run 0) (nativePathEdgeKind run (if walkEnter1 I then 1 else 0)) target1.1 target1.2) t).e=
    (step (withFourWalk I (terminalBitmap run) (terminalHasVal run)
    (nativePathEdgeKind run 0) (nativePathEdgeKind run (if walkEnter1 I then 1 else 0)) target2.1 target2.2) t).e
  have hb := trace_fixedKey_bounds hr
  exact fourWalk_prefix_target_independent I _ _ _ _ _ _ _ _ t ⟨hb.2.2.1,hb.2.2.2⟩ ht

/-- All physical prefix rows still equal the checked native edge sequence under any
terminal resolver; its selected ancestor targets are fixed by the source levels. -/
theorem nativePrefixEdges_physical_resolved (recordId : PTrie→Nat) (valueId : Slot→Nat)
    (resolvedId : PTrie→Nat) (baseI : UpsInst) {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hf : root.find [0,15]≠none) (Qs : List UpsPartI) :
    let I := nativeInstance recordId (nativeWalkBase recordId valueId resolvedId baseI root run v)
      root run v Qs
    nativePrefixEdges recordId run=(List.range (I.ts-1)).map fun i=>(step I (i+1)).e := by
  rw [nativePrefixEdges_physical recordId valueId baseI hr hf Qs]
  unfold nativePhysicalPrefixEdges
  apply List.map_congr_left
  intro i hi
  have hb : i<run.splitCursor [0,15]-1 := List.mem_range.mp hi
  exact nativeInstance_prefix_resolution recordId valueId _ _ baseI hr Qs (i+1) (by omega)
end ZkFormal.NearV3.Render.UpsGen
