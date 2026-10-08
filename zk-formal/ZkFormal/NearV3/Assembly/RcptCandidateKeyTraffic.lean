import ZkFormal.NearV3.Assembly.RcptCandidateKeyReceipt
-- Source KeyTraffic.lean SHA256: c6ecbadc375e0e194940edb497dd42f2004ac13fdb5aa4324fe5c4ef7536c73b.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.KeyReceipt

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def keyReceiptMsgs (r : Nat) (x : RcptE) : List Msg :=
  RcptE.keyMsgs r x.keySyms++if x.ee then RcptE.keyMsgs (W_AK+r) x.akSyms else []

theorem keyReceiptMsgs_view (tr : Trace Fp) (tt : Nat) (pub : List Fp) (bs : List ListBlock) :
    indexedReceiptMsgs tr tt bs keyReceiptMsgs=rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_KEYNIB := by
  rw [indexedReceiptMsgs_view]
  simp only [rcptSends3,show B_KEYNIB≠B_BYTES by decide,show B_KEYNIB≠B_RCL by decide,ite_false,List.nil_append]
  apply flatMap_congr'
  intro j _
  apply flatMap_congr'
  intro x _
  simp [rSends,keyReceiptMsgs,B_BYTES,B_KEYNIB,B_MEM]

theorem key_receive_empty (tr : Trace Fp) (tt : Nat) (pub : List Fp) (q : Nat) :
    rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB false=[] := by
  rw [rowT]
  simp [B_BYTES,B_DIGEST,B_KEYNIB,B_FINAL,B_MEM,B_RIDS,B_MPOS,B_RCL,B_SREC,B_AKC,B_BND]

theorem key_view_receive_empty (ls : RcptV3Vs) : rcptRecvs3 ls B_KEYNIB=[] := by
  simp [rcptRecvs3,rRecvs,B_KEYNIB,B_BYTES,B_DIGEST,B_FINAL,B_MEM,B_SREC,B_AKC,B_BND]

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- All physical account and access-key messages equal the canonical receipt-view
multiset, including every marker and byte nibble with its exact natural position. -/
theorem ListChain.key_traffic {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    ((List.range (tr.height tt)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true)).Perm
      ((rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_KEYNIB).map Msg.toFp) := by
  rw [←keyReceiptMsgs_view]
  apply ListChain.indexed_traffic_perm hL h
  · intro B hB
    exact ListBlockWf.header_key hL (h.blocks B hB)
  · intro q hq ha
    exact inactive_key hL hq ha
  · intro j hj k hk
    have hw := (h.blocks bs[j] (List.getElem_mem hj)).layouts bs[j].receipts[k] (List.getElem_mem hk)
    exact Layout.key_traffic hL hw (ListChain.receipt_index hL h j hj k hk)

/-- Both KEYNIB directions of the complete physical table traffic contract. -/
theorem ListChain.key_view_traffic {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e)
    (m : List Fp) :
    tableBusCount RcptV3.interactions tr tt pub B_KEYNIB true m=
      ((rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_KEYNIB).map Msg.toFp).count m ∧
    tableBusCount RcptV3.interactions tr tt pub B_KEYNIB false m=
      ((rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_KEYNIB).map Msg.toFp).count m := by
  constructor
  · rw [tableBusCount_eq]
    exact (ListChain.key_traffic hL h).count_eq m
  · rw [tableBusCount_eq,key_view_receive_empty]
    have hz : (List.range (tr.height tt)).flatMap
        (fun q => rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB false)=[] :=
      List.flatMap_eq_nil_iff.mpr (by intro q _; exact key_receive_empty tr tt pub q)
    rw [hz]
    rfl

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
