import ZkFormal.NearV3.Assembly.RcptCandidateViewPositions
-- Source IndexedBytes.lean SHA256: 6336b012ebed34c9addaa797513039585b97182ca2dbe426395eacccf504d467.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.ViewPositions

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Recursive byte accounting equals the indexed prefix-sum form used by the final view. -/
theorem chainByteMsgs_indexed (tr : Trace Fp) (tt : Nat) (pub : List Fp) (bs : List ListBlock)
    (jN rN bodyN : Nat) : chainByteMsgs tr tt pub bs jN rN bodyN=
    (List.range bs.length).flatMap (fun j => blockByteMsgs tr tt pub (bs.getD j ⟨0,[]⟩)
      (jN+j) (rN+((bs.take j).map fun B => B.receipts.length).sum)
      (bodyN+((bs.take j).map fun B => B.refundBytes tr tt).sum)) := by
  induction bs generalizing jN rN bodyN with
  | nil => rfl
  | cons B bs ih =>
    simp only [chainByteMsgs,List.length_cons,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,
      List.getD_cons_zero,List.take_zero,List.map_nil,List.sum_nil,Nat.add_zero]
    rw [ih]
    congr 1
    apply flatMap_congr'
    intro k _
    simp only [List.getD_cons_succ,List.take_succ_cons,List.map_cons,List.sum_cons,Nat.succ_eq_add_one,
      Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

/-- A selected block's positioned byte view is exactly the final semantic API's contribution. -/
theorem blockByteMsgs_view (tr : Trace Fp) (tt : Nat) (pub : List Fp) (bs : List ListBlock)
    (j : Nat) (hj : j<bs.length) :
    blockByteMsgs tr tt pub bs[j] j (((bs.take j).map fun B => B.receipts.length).sum)
      (8+((bs.take j).map fun B => B.refundBytes tr tt).sum)=
    emitAt (msgId K_RC j) 0 (hdrBytes pub ((bs.map (ListBlock.view tr tt)).getD j default)) ++
      (located (bs.map (ListBlock.view tr tt)) j).flatMap
        (fun (r,o,x) => rSends pub (flatR (bs.map (ListBlock.view tr tt))) j r o x B_BYTES) := by
  have hget : (bs.map (ListBlock.view tr tt)).getD j default=bs[j].view tr tt := by
    rw [getD_eq_getElem' _ default (by simpa using hj),List.getElem_map]
  unfold blockByteMsgs located
  simp only [hget,ListBlock.view_length,List.flatMap_map]
  apply congrArg (List.append (emitAt (msgId K_RC j) 0 (hdrBytes pub (bs[j].view tr tt))))
  apply flatMap_congr'
  intro k hk
  have hk := List.mem_range.mp hk
  unfold receiptByteMsgs
  rw [getD_eq_getElem' bs[j].receipts default hk]
  have hgetR : (bs[j].view tr tt).rs.getD k default=rcptOf tr tt bs[j].receipts[k] := by
    change (bs[j].receipts.map (rcptOf tr tt)).getD k default=_
    rw [getD_eq_getElem' _ default (by simpa using hk),List.getElem_map]
  rw [hgetR,view_lOffs]
  simp only [rSends,ite_true,rcptBytesV]
  rw [view_bOffs tr tt bs j hj k (by omega),view_baseR]

/-- The extracted byte-message list is the unchanged semantic `rcptSends3` BYTES list. -/
theorem chainByteMsgs_eq_view (tr : Trace Fp) (tt : Nat) (pub : List Fp) (bs : List ListBlock) :
    chainByteMsgs tr tt pub bs 0 0 8=rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_BYTES := by
  rw [chainByteMsgs_indexed]
  simp only [rcptSends3,List.length_map,show B_BYTES≠B_RCL by decide,ite_true,ite_false,List.append_nil,Nat.zero_add]
  apply flatMap_congr'
  intro j hj
  have hj := List.mem_range.mp hj
  rw [getD_eq_getElem' bs ⟨0,[]⟩ hj]
  exact blockByteMsgs_view tr tt pub bs j hj

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
