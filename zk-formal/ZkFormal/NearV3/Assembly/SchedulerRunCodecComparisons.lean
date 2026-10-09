import ZkFormal.NearV3.Assembly.SchedulerPriorComparisonCore
import ZkFormal.NearV3.Candidates.ProcActualComparisonValid
namespace ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Candidates Sched Sched.Gen Sched.Complete

theorem prior_core_run_comparisons (p : Prep) (B : Nat) (bs : List NativeBlock)
    (hc:PriorCore p B bs) : ∀b∈bs,∀q∈b.run.cmps,CmpOk q := by
  intro b hb
  obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hb
  exact ProcActualComparisonValid.run _ i b.run (hc.indexed i b hi).1.2

theorem accepted_run_codec_comparisons {B : Nat} {cb wb : Bytes} {hint : Hint} {p : Prep}
    (hp:prepD0 cb hint=.ok p) {k : WalkD0} {w : StateWitness}
    (hk:walkD0 cb=.ok k) (hw:decodeW wb=.ok w)
    (h:checkD0a B cb wb=.ok ()) (hB:B≤2000000) :
    ∃bs,PriorCore p B bs ∧ (∀b∈bs,∀q∈b.run.cmps,CmpOk q) ∧
      (∀b∈bs,∀q∈b.output.cmps,CmpOk q) := by
  obtain ⟨bs,hc,hcodec⟩:=accepted_prior_comparison_core hp hk hw h hB
  exact ⟨bs,hc,prior_core_run_comparisons p B bs hc,hcodec⟩
end ZkFormal.NearV3.Assembly.CodecDigest
