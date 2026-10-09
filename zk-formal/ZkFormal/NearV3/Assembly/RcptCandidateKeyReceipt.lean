import ZkFormal.NearV3.Assembly.RcptCandidateKeyLayoutFields
-- Source KeyReceipt.lean SHA256: dd3dffe5f8ce468261910ecd7ecb7c9af54d642ea8bd7d91e2b6d1a2811c7ed5.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.KeyLayoutFields

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Exact physical KEYNIB messages of a complete receipt, before reordering the separator. -/
theorem Layout.key_physical {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {rN : Nat} (hr : tr.cell tt y.s RcptV3.r=(rN:Fp)) :
    (List.range' y.s y.tot).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true)=
      (RcptE.keyMsgs rN (rcptOf tr tt y).keySyms++
        if (rcptOf tr tt y).ee then accessPhysicalMsgs (W_AK+rN) (rcptOf tr tt y) else []).map Msg.toFp := by
  have hv : (rcptOf tr tt y).v.length=y.Lv := colAt_len _ _ _ _ _
  have hs : (rcptOf tr tt y).s.length=y.Ls := colAt_len _ _ _ _ _
  have hk : (rcptOf tr tt y).kt=y.kt := rfl
  have hpref : keyFieldTraffic tr tt pub y.s (4+y.Lp) 4=[[rN,0,0,0],[rN,1,0,0]].map Msg.toFp :=
    Layout.key_prefix_field hL lay hr
  have hend : keyFieldTraffic tr tt pub y.s (8+y.Lp+y.Lv) 32=[[rN,2+2*y.Lv,SYM_END,1]].map Msg.toFp :=
    Layout.key_receiver_end_field hL lay hr
  rw [Layout.key_partition hL lay,hpref,Layout.key_receiver_view_field hL lay hr,hend,key_account_canonical]
  have hfin := lay.fin
  have hpos : 0<total y.h y.Lp y.Lv y.Ls y.kt := by unfold total Vt; split <;> omega
  rcases isBool hL (r:=y.s) (by omega) (x:=ee) (by simp [boolCols]) with he|he
  · have heView : (rcptOf tr tt y).ee=false := by simp [rcptOf,he]
    rw [Layout.key_disabled_field hL lay he (X:=sT0) (off:=40+y.Lp+y.Lv) (len:=1) (by simp [plan]) (by simp)]
    rw [Layout.key_disabled_field hL lay he (X:=sSL) (off:=41+y.Lp+y.Lv) (len:=4) (by simp [plan]) (by simp)]
    rw [Layout.key_disabled_field hL lay he (X:=sS) (off:=45+y.Lp+y.Lv) (len:=y.Ls) (by simp [plan]) (by simp)]
    rw [Layout.key_disabled_field hL lay he (X:=sKT) (off:=45+y.Lp+y.Lv+y.Ls) (len:=1) (by simp [plan]) (by simp)]
    rw [Layout.key_disabled_field hL lay he (X:=sPK) (off:=46+y.Lp+y.Lv+y.Ls) (len:=32+32*y.kt) (by simp [plan]) (by simp)]
    rw [Layout.key_disabled_field hL lay he (X:=sGP) (off:=78+Vt y.Lp y.Lv y.Ls y.kt) (len:=16) (by simp [plan]) (by simp)]
    simp only [heView,Bool.false_eq_true,ite_false,List.append_nil,List.map_append,hv]
  · have heView : (rcptOf tr tt y).ee=true := by simp [rcptOf,he]
    have h_access_type : keyFieldTraffic tr tt pub y.s (40+y.Lp+y.Lv) 1=([[W_AK+rN,0,0,0],[W_AK+rN,1,2,0]] : List Msg).map Msg.toFp :=
      Layout.key_access_type_field hL lay hr he
    have h_access_separator : keyFieldTraffic tr tt pub y.s (41+y.Lp+y.Lv) 4=([[W_AK+rN,2+2*y.Ls,0,0],[W_AK+rN,3+2*y.Ls,2,0]] : List Msg).map Msg.toFp :=
      Layout.key_access_separator_field hL lay hr he
    have h_access_kind : keyFieldTraffic tr tt pub y.s (45+y.Lp+y.Lv+y.Ls) 1=([[W_AK+rN,4+2*y.Ls,0,0],[W_AK+rN,5+2*y.Ls,y.kt,0]] : List Msg).map Msg.toFp :=
      Layout.key_access_kind_field hL lay hr he
    have h_access_end : keyFieldTraffic tr tt pub y.s (78+Vt y.Lp y.Lv y.Ls y.kt) 16=([[W_AK+rN,70+2*y.Ls+64*y.kt,SYM_END,1]] : List Msg).map Msg.toFp :=
      Layout.key_access_end_field hL lay hr he
    rw [h_access_type,h_access_separator,Layout.key_signer_view_field hL lay hr he,
      h_access_kind,Layout.key_public_view_field hL lay hr he,h_access_end]
    simp only [heView,ite_true,accessPhysicalMsgs,List.map_append,hv,hs,hk,List.append_assoc]

/-- The complete receipt's key traffic is exactly the semantic message multiset. -/
theorem Layout.key_traffic {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {rN : Nat} (hr : tr.cell tt y.s RcptV3.r=(rN:Fp)) :
    ((List.range' y.s y.tot).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true)).Perm
      ((RcptE.keyMsgs rN (rcptOf tr tt y).keySyms++
        if (rcptOf tr tt y).ee then RcptE.keyMsgs (W_AK+rN) (rcptOf tr tt y).akSyms else []).map Msg.toFp) := by
  rw [Layout.key_physical hL lay hr]
  apply List.Perm.map
  apply List.Perm.append_left
  split
  · exact accessPhysicalMsgs_perm _ _ lay.kt1 (colAt_len _ _ _ _ _)
  · exact .refl _

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
