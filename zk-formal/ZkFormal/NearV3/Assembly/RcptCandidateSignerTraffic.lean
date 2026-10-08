import ZkFormal.NearV3.Assembly.RcptCandidateSignerTrafficField
-- Source SignerTraffic.lean SHA256: dbeac65ea551369ec1ef52a6bea2836b67cfc56eda866c0f04a726c106e2e588.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.SignerTrafficField

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def signerMsgs (sd : Bool) (r : Nat) (x : RcptE) : List Msg :=
  if sd then ((List.range x.v.length).filter fun i => x.gv.getD i false).map fun i => [r,i,x.v.getD i 0]
  else ((List.range x.s.length).filter fun i => x.gs.getD i false).map fun i => [r,i,x.sx.getD i 0]

theorem signerMsgs_view (tr : Trace Fp) (tt : Nat) (pub : List Fp) (bs : List ListBlock) (sd : Bool) :
    indexedReceiptMsgs tr tt bs (signerMsgs sd)=
      (if sd then rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_SREC
        else rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_SREC) := by
  rw [indexedReceiptMsgs_view]
  cases sd <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,rcptSends3,rcptRecvs3,
      show B_SREC≠B_BYTES by decide,show B_SREC≠B_RCL by decide,List.nil_append]
  all_goals
    apply flatMap_congr'
    intro j _
    apply flatMap_congr'
    intro x _
    simp [rSends,rRecvs,signerMsgs,B_MEM,B_BYTES,B_KEYNIB,B_RIDS,B_MPOS,B_SREC,B_AKC,B_FINAL,B_DIGEST]

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Selected receiver/signature character messages match the actual view, with
no assumed equality, selection completeness, or byte-content premise. -/
theorem Layout.signer_traffic {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {rN : Nat} (hr : tr.cell tt y.s RcptV3.r=(rN:Fp)) (sd : Bool) :
    (List.range' y.s y.tot).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_SREC sd)=
      (signerMsgs sd rN (rcptOf tr tt y)).map Msg.toFp := by
  cases sd with
  | true =>
    rw [Layout.srec_receiver_window hL h,srec_field hL true (h.flds (sV,8+y.Lp,y.Lv) (by simp [plan])) hr]
    simp only [signerMsgs,ite_true,rcptOf,colAt_len,List.map_map]
    rw [←gated_list,←gated_list]
    apply flatMap_congr'
    intro k hk
    have hk := List.mem_range.mp hk
    simp only [Function.comp_def,colAt_get _ _ _ _ _ _ hk]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hk,Option.map_some,
      Option.getD_some,colAt_get _ _ _ _ _ _ hk]
  | false =>
    rw [Layout.srec_signer_window hL h,srec_field hL false (h.flds (sS,45+y.Lp+y.Lv,y.Ls) (by simp [plan])) hr]
    simp only [signerMsgs,Bool.false_eq_true,ite_false,rcptOf,colAt_len,List.map_map]
    rw [←gated_list,←gated_list]
    apply flatMap_congr'
    intro k hk
    have hk := List.mem_range.mp hk
    simp only [Function.comp_def,colAt_get _ _ _ _ _ _ hk]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hk,Option.map_some,
      Option.getD_some,colAt_get _ _ _ _ _ _ hk]

/-- Whole selected signer/receiver traffic agrees with the unchanged semantic
API, including every empty list header and all physical padding. -/
theorem ListChain.signer_traffic {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) (sd : Bool) :
    (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_SREC sd)=
      ((if sd then rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_SREC
        else rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_SREC).map Msg.toFp) := by
  rw [←signerMsgs_view]
  apply ListChain.indexed_traffic hL h
  · intro B hB
    exact ListBlockWf.header_srec hL (h.blocks B hB) sd
  · intro q hq ha
    exact srec_silent hL hq sd (noState hL hq ha (if sd then sV else sS) (by cases sd <;> simp [states]))
  · intro j hj k hk
    have hw := (h.blocks bs[j] (List.getElem_mem hj)).layouts bs[j].receipts[k] (List.getElem_mem hk)
    exact Layout.signer_traffic hL hw (ListChain.receipt_index hL h j hj k hk) sd

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
