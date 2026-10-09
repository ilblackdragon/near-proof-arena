import ZkFormal.NearV3.Assembly.RcptCandidateMemoryWrites
-- Source ReceiptIdsTraffic.lean SHA256: e0a4aef6fd03e45ccf2896516b4ac6437307cb8f167aaaa43a5743b9dfd52517.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.MemoryWrites

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def receiptIdMsgs (r : Nat) (x : RcptE) : List Msg :=
  (List.range 32).map fun i => [r,i,x.rid.getD i 0]

theorem receiptIdMsgs_view (tr : Trace Fp) (tt : Nat) (pub : List Fp) (bs : List ListBlock) :
    indexedReceiptMsgs tr tt bs receiptIdMsgs=rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_RIDS := by
  rw [indexedReceiptMsgs_view]
  simp only [rcptSends3,show B_RIDS≠B_BYTES by decide,show B_RIDS≠B_RCL by decide,ite_false,List.nil_append]
  apply flatMap_congr'
  intro j _
  apply flatMap_congr'
  intro x _
  simp [rSends,receiptIdMsgs,B_MEM,B_BYTES,B_KEYNIB,B_RIDS,B_MPOS]

theorem rids_receive_empty (tr : Trace Fp) (tt : Nat) (pub : List Fp) (q : Nat) :
    rowTraffic RcptV3.interactions tr tt q pub B_RIDS false=[] := by
  rw [rowT]
  simp [B_BYTES,B_DIGEST,B_KEYNIB,B_FINAL,B_MEM,B_RIDS,B_MPOS,B_RCL,B_SREC,B_AKC,B_BND]

theorem rids_view_receive_empty (ls : RcptV3Vs) : rcptRecvs3 ls B_RIDS=[] := by
  simp [rcptRecvs3,rRecvs,B_DIGEST,B_FINAL,B_MEM,B_RIDS,B_SREC,B_AKC,B_BND]

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Every list header is silent on receipt IDs. -/
theorem ListBlockWf.header_rids {B : ListBlock} (h : ListBlockWf tr tt B) :
    (List.range' B.start 12).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_RIDS true)=[] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro q hq
  obtain ⟨k,hk,hq⟩ := List.mem_range'.mp hq
  simp only [Nat.one_mul] at hq
  subst q
  have hs := h.header.st k hk
  have hfin := h.header_fin
  have hz := (oneHot hL (r:=B.start+k) (by omega) (by simp [states]) hs).2 sRID
    (by simp [states]) (by decide)
  rw [rowT_rids]
  exact gt_zero hz _

/-- Whole physical receipt-ID sends match exact indexed native receipt IDs. -/
theorem ListChain.rids_view {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_RIDS true)=
      (rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_RIDS).map Msg.toFp := by
  rw [←receiptIdMsgs_view]
  apply ListChain.indexed_traffic hL h
  · intro B hB
    exact ListBlockWf.header_rids hL (h.blocks B hB)
  · intro q hq ha
    rw [rowT_rids]
    exact gt_zero (noState hL hq ha sRID (by simp [states])) _
  · intro j hj k hk
    have hw := (h.blocks bs[j] (List.getElem_mem hj)).layouts bs[j].receipts[k] (List.getElem_mem hk)
    exact rcpt_rids hL hw (ListChain.receipt_index hL h j hj k hk)

/-- Both receipt-ID traffic directions agree with the unchanged view API. -/
theorem ListChain.rids_view_traffic {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) (sd : Bool) :
    (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_RIDS sd)=
      ((if sd then rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_RIDS
        else rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_RIDS).map Msg.toFp) := by
  cases sd with
  | false => simp [rids_receive_empty,rids_view_receive_empty]
  | true => exact ListChain.rids_view hL h

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
