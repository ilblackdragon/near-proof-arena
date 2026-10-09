import ZkFormal.NearV3.Assembly.SchedulerPriorActualOverlay
import ZkFormal.NearV3.Candidates.ProcPriorComparatorRouting
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

theorem routed_overlay_selected :ProcPriorComparatorRoutedFamily.selected[19]?=
    some (ProcPriorComparatorRoutedFamily.routeTable ProcPriorCodecActualFamily.overlay) := rfl

/-- The SAME executable accepted overlay is locally valid in the repaired
shared-comparator family, retaining the actual presence bus60. Global routed
traffic/provider assembly remains separate. -/
theorem accepted_routed_prior_overlay {B : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w)
    (h:checkD0a B cb wb=.ok ()) (hB:B≤2000000) :
    ∃bs,PriorCore p B bs ∧ ∀t pub,
      TableLocal (ProcPriorComparatorRoutedFamily.selected[19]!) (priorOverlay bs) t pub := by
  obtain ⟨bs,hc,hl⟩:=accepted_actual_prior_overlay hp hk hw h hB
  refine ⟨bs,hc,?_⟩
  intro t pub
  change TableLocal (ProcPriorComparatorRoutedFamily.routeTable ProcPriorCodecActualFamily.overlay) _ _ _
  exact (ProcPriorComparatorRouting.local_iff _ _ _ _).mpr (hl t pub)
end ZkFormal.NearV3.Assembly.CodecDigest
