import ZkFormal.NearV3.Assembly.RcptCandidateDigestTrafficMetadata
-- Source DigestTraffic.lean SHA256: 9b89d0b0ff07d440db99a5afa6e56064d348243ad23ee3d89fada1043ee27e0b.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.DigestTrafficMetadata

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def digestMsgs (r : Nat) (x : RcptE) : List Msg :=
  (if x.hr then [digMsg (msgId K_RID r) 48 x.rfid] else [])++
    [digMsg (msgId K_PEO r) x.peo.length x.peoh]

theorem digestMsgs_view (tr : Trace Fp) (tt : Nat) (bs : List ListBlock) :
    indexedReceiptMsgs tr tt bs digestMsgs=rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_DIGEST := by
  rw [indexedReceiptMsgs_view]
  unfold rcptRecvs3
  apply flatMap_congr'
  intro j _
  apply flatMap_congr'
  intro x _
  simp [rRecvs,digestMsgs]

theorem digest_send_empty (tr : Trace Fp) (tt : Nat) (pub : List Fp) (q : Nat) :
    rowTraffic RcptV3.interactions tr tt q pub B_DIGEST true=[] := by
  rw [rowT]
  simp [B_BYTES,B_DIGEST,B_KEYNIB,B_FINAL,B_MEM,B_RIDS,B_MPOS,B_RCL,B_SREC,B_AKC,B_BND]

theorem digest_view_send_empty (pub : List Fp) (ls : RcptV3Vs) : rcptSends3 pub ls B_DIGEST=[] := by
  simp [rcptSends3,rSends,B_DIGEST,B_BYTES,B_KEYNIB,B_MEM,B_RIDS,B_MPOS,B_RCL,B_SREC,B_AKC,B_BND]

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

theorem Layout.digest_traffic {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {rN : Nat} (hr : tr.cell tt y.s RcptV3.r=(rN:Fp)) :
    (List.range' y.s y.tot).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_DIGEST false)=
      (digestMsgs rN (rcptOf tr tt y)).map Msg.toFp := by
  rw [Layout.digest_rows hL h,Layout.outcome_digest hL h hr]
  simp only [digestMsgs,List.map_append,List.map_cons,List.map_nil]
  cases he : y.h with
  | false => simp only [rcptOf,he,Bool.false_eq_true,ite_false,List.map_nil,List.nil_append]
  | true =>
    rw [if_pos rfl,Layout.refund_digest hL h hr he]
    simp only [rcptOf,he,ite_true,List.map_cons,List.map_nil]

/-- Every actual SHA digest receive has the exact receipt ID, input length, and
loaded 32-byte output; there are no other receipt digest messages. -/
theorem ListChain.digest_traffic {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_DIGEST false)=
      (rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_DIGEST).map Msg.toFp := by
  rw [←digestMsgs_view]
  apply ListChain.indexed_traffic hL h
  · intro B hB
    exact ListBlockWf.header_digest hL (h.blocks B hB)
  · intro q hq ha
    have hn := noState hL hq ha
    exact digest_silent hL hq (hn sXRI (by simp [states])) (hn sXLH (by simp [states]))
  · intro j hj k hk
    have hw := (h.blocks bs[j] (List.getElem_mem hj)).layouts bs[j].receipts[k] (List.getElem_mem hk)
    exact Layout.digest_traffic hL hw (ListChain.receipt_index hL h j hj k hk)

theorem ListChain.digest_view_traffic {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) (sd : Bool) :
    (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_DIGEST sd)=
      ((if sd then rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_DIGEST
        else rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_DIGEST).map Msg.toFp) := by
  cases sd with
  | false => exact ListChain.digest_traffic hL h
  | true => simp [digest_send_empty,digest_view_send_empty]

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
