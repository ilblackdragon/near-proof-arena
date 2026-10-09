import ZkFormal.NearV3.Candidates.ProcPriorComparatorRoutedFamily
import ZkFormal.NearV3.Assembly.SchedulerPriorComparisonCore
import ZkFormal.NearV3.Candidates.ProcCodecComparisonPhysical
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Sched.Complete

theorem routed_codec_interactions :
    (ProcPriorComparatorRoutedFamily.selected[8]!).interactions=ProcPriorCodecActual.table.interactions := by
  decide +kernel

theorem PriorCore.codec_comparison_count {B:Nat} {p:Prep} {bs:List NativeBlock}
    (hc:PriorCore p B bs) (t:Nat) (pub msg:List Fp) :
    tableBusCount (ProcPriorComparatorRoutedFamily.selected[8]!).interactions
      (SchedHeight.trace (nativeBlockRows bs) codecPad) t pub B_SCMP true msg=
      ((ProcNativeCodecComparisonBudget.requests bs).map cmpMsg).count msg := by
  rw [routed_codec_interactions]
  exact ProcCodecComparisonPhysical.count bs (by have:=hc.length;omega) hc.valid t pub msg

theorem accepted_codec_comparisons {B:Nat} {cb wb:Bytes} {hint:Hint} {p:Prep}
    (hp:prepD0 cb hint=.ok p) {k:WalkD0} {w:StateWitness}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w)
    (h:checkD0a B cb wb=.ok ()) (hB:B≤2000000) :
    ∃bs,PriorCore p B bs ∧
      (∀q∈ProcNativeCodecComparisonBudget.requests bs,CmpOk q) ∧
      (∀t pub msg,tableBusCount (ProcPriorComparatorRoutedFamily.selected[8]!).interactions
        (SchedHeight.trace (nativeBlockRows bs) codecPad) t pub B_SCMP true msg=
        ((ProcNativeCodecComparisonBudget.requests bs).map cmpMsg).count msg) := by
  obtain ⟨bs,hc,hvalid⟩:=accepted_prior_comparison_core hp hk hw h hB
  refine ⟨bs,hc,?_,hc.codec_comparison_count⟩
  intro q hq
  obtain ⟨b,hb,hq⟩:=List.mem_flatMap.mp hq
  exact hvalid b hb q hq
end ZkFormal.NearV3.Assembly.CodecDigest
