import ZkFormal.NearV3.Assembly.RcptCandidateMemoryReads
-- Source IndexedTraffic.lean SHA256: 4ff5696ec1ff8f89f5a653a48a912c55fbe7904da4ecb28064f1c3138b425115.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.MemoryReads

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Natural global receipt index of a concrete extracted receipt. -/
def receiptIndex (bs : List ListBlock) (j k : Nat) : Nat :=
  ((bs.take j).map fun B => B.receipts.length).sum+k

/-- Indexed physical receipt messages, retaining both list and receipt positions. -/
def indexedReceiptMsgs (tr : Trace Fp) (tt : Nat) (bs : List ListBlock)
    (g : Nat→RcptE→List Msg) : List Msg :=
  (List.range bs.length).flatMap fun j =>
    let B := bs.getD j ⟨0,[]⟩
    (List.range B.receipts.length).flatMap fun k =>
      g (receiptIndex bs j k) (rcptOf tr tt (B.receipts.getD k default))

/-- Natural indexed messages agree with the unchanged located-view enumeration. -/
theorem indexedReceiptMsgs_view (tr : Trace Fp) (tt : Nat) (bs : List ListBlock)
    (g : Nat→RcptE→List Msg) :
    indexedReceiptMsgs tr tt bs g=
      (List.range (bs.map (ListBlock.view tr tt)).length).flatMap (fun j =>
        (located (bs.map (ListBlock.view tr tt)) j).flatMap (fun (r,_,x) => g r x)) := by
  simp only [indexedReceiptMsgs,List.length_map]
  apply flatMap_congr'
  intro j hj
  have hj := List.mem_range.mp hj
  have hv : (bs.map (ListBlock.view tr tt)).getD j default=bs[j].view tr tt := by
    rw [getD_eq_getElem' _ default (by simpa using hj),List.getElem_map]
  unfold located
  rw [getD_eq_getElem' bs ⟨0,[]⟩ hj,hv]
  simp only [ListBlock.view_length,List.flatMap_map]
  apply flatMap_congr'
  intro k hk
  have hk := List.mem_range.mp hk
  have hx : (bs[j].view tr tt).rs.getD k default=rcptOf tr tt bs[j].receipts[k] := by
    change (bs[j].receipts.map (rcptOf tr tt)).getD k default=_
    rw [getD_eq_getElem' _ default (by simpa using hk),List.getElem_map]
  rw [getD_eq_getElem' bs[j].receipts default hk,hx,view_baseR]
  rfl

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- The actual first-row receipt counter equals its ordinary flattened index. -/
theorem ListChain.receipt_index {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e)
    (j : Nat) (hj : j<bs.length) (k : Nat) (hk : k<bs[j].receipts.length) :
    tr.cell tt bs[j].receipts[k].s RcptV3.r=((receiptIndex bs j k:Nat):Fp) := by
  have hh := ListBlockWf.receipt_indices hL (h.blocks bs[j] (List.getElem_mem hj)) k hk
  rw [ListChain.zero_global_counts hL h j hj,←natCast_add] at hh
  exact hh

/-- Generic whole-table indexed traffic composition. Header/padding silence and
each actual receipt interval are the only bus-specific obligations. -/
theorem ListChain.indexed_traffic {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e)
    (f : Nat→List (List Fp)) (g : Nat→RcptE→List Msg)
    (hh : ∀ B∈bs,(List.range' B.start 12).flatMap f=[])
    (hp : ∀ q,q<tr.height tt → tr.cell tt q RcptV3.act=0 → f q=[])
    (hr : ∀ j,(hj:j<bs.length) → ∀ k,(hk:k<bs[j].receipts.length) →
      (List.range' bs[j].receipts[k].s bs[j].receipts[k].tot).flatMap f=
        (g (receiptIndex bs j k) (rcptOf tr tt bs[j].receipts[k])).map Msg.toFp) :
    (List.range (tr.height tt)).flatMap f=(indexedReceiptMsgs tr tt bs g).map Msg.toFp := by
  rw [ListChain.receipt_spans_full hL h f hh hp]
  letI : Inhabited ListBlock := ⟨⟨0,[]⟩⟩
  rw [flatMap_eq_range bs]
  unfold indexedReceiptMsgs
  rw [List.map_flatMap]
  apply flatMap_congr'
  intro j hj
  have hj := List.mem_range.mp hj
  rw [getD_eq_getElem' bs default hj,getD_eq_getElem' bs ⟨0,[]⟩ hj]
  rw [flatMap_eq_range bs[j].receipts,List.map_flatMap]
  apply flatMap_congr'
  intro k hk
  have hk := List.mem_range.mp hk
  rw [getD_eq_getElem' bs[j].receipts default hk]
  exact hr j hj k hk

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
