import ZkFormal.NearV3.Candidates.ProcActualRunComparisonBudget
import ZkFormal.NearV3.Candidates.ProcDistComparisonCost
import ZkFormal.NearV3.Candidates.ProcNativeCodecComparisonBudget
import ZkFormal.NearV3.Assembly.SchedulerPriorCore
namespace ZkFormal.NearV3.Candidates.ProcNativeOldComparisonBudget
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Assembly.CodecDigest

def requests (bs:List NativeBlock)(dist:NativeBlock→DistOut) : List (Nat×Nat×Nat) :=
  bs.flatMap (fun b=>b.run.cmps++b.output.cmps++(dist b).cmps)

theorem per_block {cb:NearSpec.Bytes}{hint:NearSpecV3.Hint}{p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p)(b:NativeBlock)(d:DistOut)(tau:Nat)
    (hb:b.Valid)(hn:b.run.n≤64)(hr:PreparedRun p tau b)
    (hd:distRows (ProcPreparedSequence.input b.pub b.old) b.run=.ok d) :
    (b.run.cmps++b.output.cmps++d.cmps).length≤91776 := by
  have hm:=List.mem_iff_getElem?.mpr ⟨tau,hr.1⟩
  have hs:=prepD0_sched hp b.pub hm
  have hrun:=ProcActualRunComparisonBudget.prepared_cost b.pub hs b.old tau b.run hr.2
  have hcodec:=ProcNativeCodecComparisonBudget.block b hb hn
  have hdist:=ProcDistComparisonCost.native_cost _ _ d hd hn
  simp only [List.length_append]
  omega

theorem list_bound {cb:NearSpec.Bytes}{hint:NearSpecV3.Hint}{p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p)(bs:List NativeBlock)(dist:NativeBlock→DistOut)
    (hb:∀b∈bs,b.Valid ∧ b.run.n≤64 ∧ ∃tau,PreparedRun p tau b)
    (hd:∀b∈bs,distRows (ProcPreparedSequence.input b.pub b.old) b.run=.ok (dist b)) :
    (requests bs dist).length≤91776*bs.length := by
  induction bs with
  | nil=>simp [requests]
  | cons b bs ih=>
    obtain ⟨hv,hn,tau,hr⟩:=hb b (by simp)
    have hh:=per_block hp b (dist b) tau hv hn hr (hd b (by simp))
    have ht:=ih (fun b hm=>hb b (by simp [hm])) (fun b hm=>hd b (by simp [hm]))
    simp only [requests,List.flatMap_cons,List.length_append,List.length_cons] at *
    omega

theorem core_bound {cb:NearSpec.Bytes}{hint:NearSpecV3.Hint}{p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p){B:Nat}(bs:List NativeBlock)(hc:PriorCore p B bs)
    (dist:NativeBlock→DistOut)
    (hd:∀b∈bs,distRows (ProcPreparedSequence.input b.pub b.old) b.run=.ok (dist b)) :
    (requests bs dist).length≤2936832 ∧ (requests bs dist).length≤3090136 := by
  have h:=list_bound hp bs dist (fun b hb=>by
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hb
    exact ⟨(hc.valid b hb).1,(hc.valid b hb).2,i,(hc.indexed i b hi).1⟩) hd
  have hl:=hc.length
  constructor <;> omega
end ZkFormal.NearV3.Candidates.ProcNativeOldComparisonBudget
