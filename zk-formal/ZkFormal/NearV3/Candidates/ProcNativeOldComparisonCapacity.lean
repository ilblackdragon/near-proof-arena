import ZkFormal.NearV3.Candidates.ProcDistGeneratorSuccess
import ZkFormal.NearV3.Candidates.ProcNativeOldComparisonBudget
import ZkFormal.NearV3.Candidates.ProcSharedComparator
namespace ZkFormal.NearV3.Candidates.ProcNativeOldComparisonCapacity
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Assembly.CodecDigest

def distribution (b:NativeBlock) : DistOut :=
  match distRows (ProcPreparedSequence.input b.pub b.old) b.run with
  | .ok d=>d
  | .error _=>⟨#[],#[],[]⟩

theorem distribution_eq (b:NativeBlock)(hn:b.run.n≤64) :
    distRows (ProcPreparedSequence.input b.pub b.old) b.run=.ok (distribution b) := by
  obtain ⟨d,hd⟩:=ProcDistGeneratorSuccess.generated (ProcPreparedSequence.input b.pub b.old) b.run hn
  simp only [distribution,hd]

def requests (bs:List NativeBlock) := ProcNativeOldComparisonBudget.requests bs distribution

theorem native_bound {cb:NearSpec.Bytes}{hint:NearSpecV3.Hint}{p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p){B:Nat}(bs:List NativeBlock)(hc:PriorCore p B bs) :
    (requests bs).length≤2936832 ∧ (requests bs).length≤3090136 :=
  ProcNativeOldComparisonBudget.core_bound hp bs hc distribution (fun b hb=>distribution_eq b (hc.valid b hb).2)

theorem shared_capacity {cb:NearSpec.Bytes}{hint:NearSpecV3.Hint}{p:NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p){B:Nat}(hB:B≤2000000)
    (bs:List NativeBlock)(hc:PriorCore p B bs) :
    (ProcSharedComparator.requests (requests bs) bs).length≤2^22 := by
  apply ProcSharedComparator.capacity (requests bs) bs (native_bound hp bs hc).2
  · intro b hb
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hb
    have hm:=List.mem_iff_getElem?.mpr ⟨i,(hc.indexed i b hi).1.1⟩
    exact (prepD0_sched hp b.pub hm).n64
  · exact hc.length
  · have hh:=hc.raw_bound
    omega
end ZkFormal.NearV3.Candidates.ProcNativeOldComparisonCapacity
