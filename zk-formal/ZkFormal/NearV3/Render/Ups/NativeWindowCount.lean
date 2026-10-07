import ZkFormal.NearV3.Render.Ups.BytePlanShape
import ZkFormal.NearV3.Render.Ups.SplitKidCounts

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

private theorem occupancy_slots (kids : List NKid) (hlen : kids.length=16)
    (p : Nat → Prop) [DecidablePred p]
    (h : ∀ j, j<16 → (kids.getD j .none≠.none ↔ p j)) :
    kidOccupancy kids = (List.range 16).map (fun j => decide (p j)) := by
  apply List.ext_getElem
  · simp [kidOccupancy,hlen]
  · intro j hj hk
    have hj' : j<16 := by simpa [kidOccupancy,hlen] using hj
    simp only [kidOccupancy,List.getElem_map,List.getElem_range]
    apply Bool.eq_iff_iff.mpr
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (show j<kids.length by omega)] using h j hj'

/-- The split child-window count follows from occupied source/new child slots. -/
theorem ByteInput.split_windows {I : UpsInst} {Q : UpsPartI}
    (data : ByteInput I Q) (types : PartTypeFacts Q) (hk : Q.kind=10) :
    nWin Q.shape = if I.ci=6 ∨ I.ci=9 ∨ I.ci=10 then 2 else 1 := by
  have ht := types.tyBr (Or.inr (Or.inr (Or.inr hk)))
  have hw := data.output.wf
  have hs := data.splitBitmap.slots hk
  have hd := data.splitBitmap.distinct hk
  have hx := data.splitBitmap.xbound
  rw [data.output.shape,nonempty_node_shape,nodeFields_windows]
  cases hn : data.output.node with
  | leaf => simp [data.output.ty,hn,nodeTypeCode] at ht
  | ext => simp [data.output.ty,hn,nodeTypeCode] at ht
  | branch value kids mem =>
    simp only [hn,NodeV3.wf] at hw
    have hlen : kids.length=16 := hw.1
    simp only [hn,NodeGen3.kidsOf] at hs
    rw [nodeChildren,windows_present_count,occupancy_slots kids hlen _ hs]
    rcases (show I.x=0 ∨ I.x=1 ∨ I.x=2 ∨ I.x=3 ∨ I.x=4 ∨ I.x=5 ∨ I.x=6 ∨ I.x=7 ∨ I.x=8 ∨ I.x=9 ∨ I.x=10 ∨ I.x=11 ∨ I.x=12 ∨ I.x=13 ∨ I.x=14 ∨ I.x=15 by omega)
      with hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx <;>
      by_cases hc : I.ci=4 <;> by_cases hn : I.ci=6 ∨ I.ci=9 ∨ I.ci=10 <;>
      by_cases ht : I.ts=1 <;>
      simp_all [splitHasNew,splitNewSlot,List.range_succ]
end ZkFormal.NearV3.Render.UpsGen
