import ZkFormal.NearV3.Assembly.SchedulerRunCodecComparisons
import ZkFormal.NearV3.Assembly.SchedulerPriorRoutedComparator
import ZkFormal.NearV3.Candidates.ProcDistComparisonValid
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen Sched.Complete
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

theorem prior_core_old_comparisons {cb:Bytes} {hint:Hint} {p:Prep}
    (hp:prepD0 cb hint=.ok p) {B:Nat} (bs:List NativeBlock) (hc:PriorCore p B bs)
    (hcodec:∀b∈bs,∀q∈b.output.cmps,CmpOk q) :
    ∀q∈ProcNativeOldComparisonCapacity.requests bs,CmpOk q := by
  have hrun:=prior_core_run_comparisons p B bs hc
  have hdist:=ProcDistComparisonValid.prior_core hp bs hc
  intro q hq
  obtain ⟨b,hb,hq⟩:=List.mem_flatMap.mp hq
  simp only [List.mem_append] at hq
  rcases hq with (hq|hq)|hq
  · exact hrun b hb q hq
  · exact hcodec b hb q hq
  · exact hdist b hb q hq

/-- An accepted execution supplies a valid, capacity-safe installed comparator
for all native old and prior requests. Exact old producer traffic is a separate
join obligation, not a premise hidden in this witness. -/
theorem accepted_comparator {B:Nat} {cb wb:Bytes} {hint:Hint} {p:Prep}
    (hp:prepD0 cb hint=.ok p) {k:WalkD0} {w:StateWitness}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w)
    (h:checkD0a B cb wb=.ok ()) (hB:B≤2000000) :
    ∃bs,PriorCore p B bs ∧
      (ProcSharedComparator.requests (ProcNativeOldComparisonCapacity.requests bs) bs).length≤2^22 ∧
      (∀t pub,TableLocal (ProcPriorComparatorRoutedFamily.selected[12]!)
        (ProcSharedComparator.trace (ProcNativeOldComparisonCapacity.requests bs) bs) t pub) ∧
      (∀tc to pub msg,tableBusCount (ProcPriorComparatorRoutedFamily.selected[12]!).interactions
        (ProcSharedComparator.trace (ProcNativeOldComparisonCapacity.requests bs) bs) tc pub 40 false msg=
        ((ProcNativeOldComparisonCapacity.requests bs).map cmpMsg).count msg+
          tableBusCount (ProcPriorComparatorRoutedFamily.selected[19]!).interactions
            (priorOverlay bs) to pub 40 true msg) := by
  obtain ⟨bs,hc,hcodec⟩:=accepted_prior_comparison_core hp hk hw h hB
  have hok:=prior_core_old_comparisons hp bs hc hcodec
  exact ⟨bs,hc,ProcNativeOldComparisonCapacity.shared_capacity hp hB bs hc,
    routed_shared_comparator_local hp bs hc hB _ hok,
    routed_shared_comparator_balance hp bs hc hB _ (ProcNativeOldComparisonCapacity.native_bound hp bs hc).2⟩
end ZkFormal.NearV3.Assembly.CodecDigest
