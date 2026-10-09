import ZkFormal.NearV3.Assembly.RcptCandidateReceiptIdsTraffic
-- Source ReceiptPositionsTraffic.lean SHA256: 0462fd4066db103d4caf002eb84121218be8befeceac97d97f8a551928404732.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptIdsTraffic

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def receiptPositionMsgs (r : Nat) (_x : RcptE) : List Msg := [[0,r,msgId K_LEAF r,68]]

theorem receiptPositionMsgs_view (tr : Trace Fp) (tt : Nat) (pub : List Fp) (bs : List ListBlock) :
    indexedReceiptMsgs tr tt bs receiptPositionMsgs=rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_MPOS := by
  rw [indexedReceiptMsgs_view]
  simp only [rcptSends3,show B_MPOS≠B_BYTES by decide,show B_MPOS≠B_RCL by decide,ite_false,List.nil_append]
  apply flatMap_congr'
  intro j _
  apply flatMap_congr'
  intro x _
  simp [rSends,receiptPositionMsgs,B_MEM,B_BYTES,B_KEYNIB,B_RIDS,B_MPOS]

theorem mpos_receive_empty (tr : Trace Fp) (tt : Nat) (pub : List Fp) (q : Nat) :
    rowTraffic RcptV3.interactions tr tt q pub B_MPOS false=[] := by
  rw [rowT]
  simp [B_BYTES,B_DIGEST,B_KEYNIB,B_FINAL,B_MEM,B_RIDS,B_MPOS,B_RCL,B_SREC,B_AKC,B_BND]

theorem mpos_view_receive_empty (ls : RcptV3Vs) : rcptRecvs3 ls B_MPOS=[] := by
  simp [rcptRecvs3,rRecvs,B_DIGEST,B_FINAL,B_MEM,B_MPOS,B_SREC,B_AKC,B_BND]

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- No Merkle-position record appears outside a predecessor-length start state. -/
theorem mpos_silent {q : Nat} (hq : q<tr.height tt) (hs : tr.cell tt q sPL=0) :
    rowTraffic RcptV3.interactions tr tt q pub B_MPOS true=[] := by
  rw [rowT_mpos]
  simp only [gt,C]
  by_cases hf : tr.cell tt q rf=1
  ·
    have hh := (bounds hL hq).2.1 hf
    rw [hs] at hh
    exact False.elim (fp_zero_ne_one hh.1)
  · simp only [hf,ite_false]

theorem ListBlockWf.header_mpos {B : ListBlock} (h : ListBlockWf tr tt B) :
    (List.range' B.start 12).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_MPOS true)=[] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro q hq
  obtain ⟨k,hk,hq⟩ := List.mem_range'.mp hq
  simp only [Nat.one_mul] at hq
  subst q
  have hs := h.header.st k hk
  have hfin := h.header_fin
  exact mpos_silent hL (by omega) ((oneHot hL (r:=B.start+k) (by omega)
    (by simp [states]) hs).2 sPL (by simp [states]) (by decide))

/-- Every receipt emits exactly one globally indexed receipt-leaf position. -/
theorem ListChain.mpos_view {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_MPOS true)=
      (rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_MPOS).map Msg.toFp := by
  rw [←receiptPositionMsgs_view]
  apply ListChain.indexed_traffic hL h
  · intro B hB
    exact ListBlockWf.header_mpos hL (h.blocks B hB)
  · intro q hq ha
    exact mpos_silent hL hq (noState hL hq ha sPL (by simp [states]))
  · intro j hj k hk
    have hw := (h.blocks bs[j] (List.getElem_mem hj)).layouts bs[j].receipts[k] (List.getElem_mem hk)
    exact rcpt_mpos hL hw (ListChain.receipt_index hL h j hj k hk) (Layout.start_flags hL hw).2.2

theorem ListChain.mpos_view_traffic {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) (sd : Bool) :
    (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_MPOS sd)=
      ((if sd then rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_MPOS
        else rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_MPOS).map Msg.toFp) := by
  cases sd with
  | false => simp [mpos_receive_empty,mpos_view_receive_empty]
  | true => exact ListChain.mpos_view hL h

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
