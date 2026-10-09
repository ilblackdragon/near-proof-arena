import ZkFormal.NearV3.Candidates.ProcCodecComparisonTotal
import ZkFormal.NearV3.Assembly.SchedulerCodecNativeBlocks
namespace ZkFormal.NearV3.Candidates.ProcNativeCodecComparisonBudget
open ZkFormal.NearV3.Assembly.CodecDigest

def requests (bs : List NativeBlock) := bs.flatMap (fun b=>b.output.cmps)

theorem block (b : NativeBlock) (hb:b.Valid) (hn:b.run.n≤64) : b.output.cmps.length≤24576 := by
  have hc:=ProcCodecComparisonTotal.generated_cost _ _ _ _ _ _ _ hb.2.2.2.2
  have hh:=Nat.mul_le_mul hn hn
  omega

theorem list_bound (bs : List NativeBlock) (hb:∀b∈bs,b.Valid ∧ b.run.n≤64) :
    (requests bs).length≤24576*bs.length := by
  induction bs with
  | nil=>simp [requests]
  | cons b bs ih=>
    have hh:=block b (hb b (by simp)).1 (hb b (by simp)).2
    have ht:=ih (fun b hm=>hb b (by simp [hm]))
    simp only [requests,List.flatMap_cons,List.length_append,List.length_cons] at *
    omega

theorem native_bound (bs : List NativeBlock) (hb:∀b∈bs,b.Valid ∧ b.run.n≤64) (hlen:bs.length≤32) :
    (requests bs).length≤786432 := by
  have h:=list_bound bs hb
  omega
end ZkFormal.NearV3.Candidates.ProcNativeCodecComparisonBudget
