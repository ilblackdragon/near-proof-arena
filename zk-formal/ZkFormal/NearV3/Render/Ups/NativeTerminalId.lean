import ZkFormal.NearV3.Render.Ups.ForestTerminalSafe
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec NearSpecV3 UpsRows ZkFormal.Near Assembly

/-- The terminal message always names its actual source node, including BMAP cases. -/
theorem fourWalk_terminal_id (I : UpsInst) (bm hv ek1 ek2 target targetPos : Nat)
    (ht : 1≤I.ts ∧ I.ts≤3) :
    ((step (withFourWalk I bm hv ek1 ek2 target targetPos) I.ts).e).getD 0 0=I.N.getD I.D 0 := by
  rcases (show I.ts=1 ∨ I.ts=2 ∨ I.ts=3 by omega) with ht|ht|ht <;>
    simp [step,withFourWalk,fourWalk,ht]

theorem nativeInstance_terminal_id (recordId : PTrie→Nat) (valueId : Slot→Nat)
    (resolvedId : PTrie→Nat) (baseI : UpsInst) {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (Qs : List UpsPartI) :
    let I := nativeInstance recordId (nativeWalkBase recordId valueId resolvedId baseI root run v)
      root run v Qs
    ((step I I.ts).e).getD 0 0=recordId run.terminalSource := by
  dsimp only
  let I := nativeInstance recordId baseI root run v Qs
  let target := nativeTerminalTarget valueId resolvedId run (recordId run.terminalSource)
  have hb := trace_fixedKey_bounds hr
  have ht : 1≤I.ts ∧ I.ts≤3 := ⟨hb.2.2.1,hb.2.2.2⟩
  change ((step (withFourWalk I (terminalBitmap run) (terminalHasVal run)
    (nativePathEdgeKind run 0) (nativePathEdgeKind run (if walkEnter1 I then 1 else 0))
    target.1 target.2) I.ts).e).getD 0 0=recordId run.terminalSource
  rw [fourWalk_terminal_id I _ _ _ _ _ _ ht]
  exact sourceLevelIds_terminal recordId run
end ZkFormal.NearV3.Render.UpsGen
