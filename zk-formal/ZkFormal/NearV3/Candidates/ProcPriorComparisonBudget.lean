import ZkFormal.NearV3.Candidates.ProcPriorComparisonRequests
namespace ZkFormal.NearV3.Candidates.ProcPriorComparisonBudget
open ZkFormal.NearV3.Assembly.CodecDigest
open ProcPriorComparisonRequests

theorem charge (bs : List NativeBlock) (hn:∀b∈bs,b.pub.ids.length≤64) :
    12*(2*(ProcPriorNativeMemory.allRows bs).length+4*(ProcPriorOverlayBudget.idRows bs).length)≤
      5*(ProcRawConcatGeometry.rows bs).length+101376*bs.length := by
  induction bs with
  | nil=>simp [ProcPriorNativeMemory.allRows,ProcPriorOverlayBudget.idRows,ProcRawConcatGeometry.rows]
  | cons b bs ih=>
    have h64:=hn b (by simp)
    have hsquare:=Nat.mul_le_mul h64 h64
    have hm:=ProcPriorRows.rows_length b.pub.ids b.old.links
    have hid:=ProcPriorIdRows.rows_length b.pub.ids b.old.links
    have hraw:=ProcRawConcatGeometry.block_length b
    have ht:=ih (fun b hb=>hn b (by simp [hb]))
    simp only [ProcPriorNativeMemory.allRows,ProcPriorNativeMemory.tagged,
      ProcPriorOverlayBudget.idRows,ProcRawConcatGeometry.rows,List.flatMap_cons,
      List.length_append,List.length_cons,List.length_map] at ht ⊢
    unfold ProcRawConcatGeometry.blockLength ProcPriorRawSlots.length at hraw
    omega

theorem requests_charge (bs : List NativeBlock) (hn:∀b∈bs,b.pub.ids.length≤64) :
    12*(requests bs).length≤5*(ProcRawConcatGeometry.rows bs).length+101376*bs.length := by
  have h:=length_bound bs
  have hc:=charge bs hn
  omega

theorem capacity (bs : List NativeBlock) (hn:∀b∈bs,b.pub.ids.length≤64)
    (hlen:bs.length≤32) (hraw:(ProcRawConcatGeometry.rows bs).length≤2001184) :
    (requests bs).length≤1104168 := by
  have h:=requests_charge bs hn
  omega
end ZkFormal.NearV3.Candidates.ProcPriorComparisonBudget
