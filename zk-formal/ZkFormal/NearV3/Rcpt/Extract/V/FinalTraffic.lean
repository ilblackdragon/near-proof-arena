import ZkFormal.NearV3.Rcpt.Extract.V.FinalTrafficValues

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def finalMsgs (r : Nat) (x : RcptE) : List Msg :=
  [r,0,FK_VAL,x.kslot]::(if x.ee then [[W_AK+r,0,x.akf,x.akk]] else [])

theorem finalMsgs_view (tr : Trace Fp) (tt : Nat) (bs : List ListBlock) :
    indexedReceiptMsgs tr tt bs finalMsgs=rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_FINAL := by
  rw [indexedReceiptMsgs_view]
  unfold rcptRecvs3
  apply flatMap_congr'
  intro j _
  apply flatMap_congr'
  intro x _
  simp [rRecvs,finalMsgs,B_FINAL,B_DIGEST]

theorem final_send_empty (tr : Trace Fp) (tt : Nat) (pub : List Fp) (q : Nat) :
    rowTraffic RcptV3.interactions tr tt q pub B_FINAL true=[] := by
  rw [rowT]
  simp [B_BYTES,B_DIGEST,B_KEYNIB,B_FINAL,B_MEM,B_RIDS,B_MPOS,B_RCL,B_SREC,B_AKC,B_BND]

theorem final_view_send_empty (pub : List Fp) (ls : RcptV3Vs) : rcptSends3 pub ls B_FINAL=[] := by
  simp [rcptSends3,rSends,B_FINAL,B_BYTES,B_KEYNIB,B_MEM,B_RIDS,B_MPOS,B_RCL,B_SREC,B_AKC,B_BND]

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

theorem Layout.final_traffic {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {rN : Nat} (hr : tr.cell tt y.s RcptV3.r=(rN:Fp)) :
    (List.range' y.s y.tot).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_FINAL false)=
      (finalMsgs rN (rcptOf tr tt y)).map Msg.toFp := by
  rw [h.final_rows hL,h.account_final hL hr,h.access_final hL hr]
  rfl

/-- Whole physical final-result receives are exactly the account and optional
access-key walk results of the indexed receipt view. -/
theorem ListChain.final_traffic {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_FINAL false)=
      (rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_FINAL).map Msg.toFp := by
  rw [←finalMsgs_view]
  apply h.indexed_traffic hL
  · intro B hB
    exact (h.blocks B hB).header_final hL
  · intro q hq ha
    have hn := noState hL hq ha
    exact final_silent hL hq (hn sPL (by simp [states])) (hn sT0 (by simp [states]))
  · intro j hj k hk
    have hw := (h.blocks bs[j] (List.getElem_mem hj)).layouts bs[j].receipts[k] (List.getElem_mem hk)
    exact hw.final_traffic hL (h.receipt_index hL j hj k hk)

theorem ListChain.final_view_traffic {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) (sd : Bool) :
    (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_FINAL sd)=
      ((if sd then rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_FINAL
        else rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_FINAL).map Msg.toFp) := by
  cases sd with
  | false => exact h.final_traffic hL
  | true => simp [final_send_empty,final_view_send_empty]

end ZkFormal.NearV3.RcptV3Proof
