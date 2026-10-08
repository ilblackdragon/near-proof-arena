import ZkFormal.NearV3.Assembly.RcptCandidateKeyPartition
-- Source KeyLayoutFields.lean SHA256: 04aa9f8d6a0796daacc37022cb24f2cda503e7b19947eedbf99a8145b9f29918.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.KeyPartition

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Full receiver field traffic expressed through the extracted receipt view. -/
theorem Layout.key_receiver_view_field {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {rN : Nat} (hr : tr.cell tt y.s RcptV3.r=(rN:Fp)) :
    keyFieldTraffic tr tt pub y.s (8+y.Lp) (y.Lv)=
      (symbolMsgs (rN) (2) ((rcptOf tr tt y).v.flatMap (fun ch => [ch/16,ch%16]))).map Msg.toFp := by
  have hm : (sV,8+y.Lp,y.Lv)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have hfin := lay.fin
  have hle := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  simp only at hle
  exact key_receiver_field hL (lay.flds _ hm) (by omega) hr

/-- Full signer field traffic expressed through the extracted receipt view. -/
theorem Layout.key_signer_view_field {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {rN : Nat} (hr : tr.cell tt y.s RcptV3.r=(rN:Fp)) (he : tr.cell tt y.s ee=1) :
    keyFieldTraffic tr tt pub y.s (45+y.Lp+y.Lv) (y.Ls)=
      (symbolMsgs (W_AK+rN) (2) ((rcptOf tr tt y).s.flatMap (fun ch => [ch/16,ch%16]))).map Msg.toFp := by
  have hm : (sS,45+y.Lp+y.Lv,y.Ls)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have hfin := lay.fin
  have hle := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  simp only at hle
  exact key_signer_field hL (lay.flds _ hm) (by omega) hr he

/-- Full public field traffic expressed through the extracted receipt view. -/
theorem Layout.key_public_view_field {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {rN : Nat} (hr : tr.cell tt y.s RcptV3.r=(rN:Fp)) (he : tr.cell tt y.s ee=1) :
    keyFieldTraffic tr tt pub y.s (46+y.Lp+y.Lv+y.Ls) (32+32*y.kt)=
      (symbolMsgs (W_AK+rN) (6+2*y.Ls) ((rcptOf tr tt y).pk.flatMap (fun ch => [ch/16,ch%16]))).map Msg.toFp := by
  have hm : (sPK,46+y.Lp+y.Lv+y.Ls,32+32*y.kt)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have hfin := lay.fin
  have hle := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  simp only at hle
  exact key_public_field hL (lay.flds _ hm) (by omega) hr lay.cLs he

/-- Disabled refunds produce no symbols in any complete access-key field. -/
theorem Layout.key_disabled_field {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (he : tr.cell tt y.s ee=0) {X off len : Nat}
    (hm : (X,off,len)∈plan y.h y.Lp y.Lv y.Ls y.kt)
    (hx : X∈[sT0,sSL,sS,sKT,sPK,sGP]) :
    keyFieldTraffic tr tt pub y.s off len=[] := by
  have F : RFld tr tt y.s (y.s+off) len X := lay.flds _ hm
  have hfin := lay.fin
  have hle := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  simp only at hle
  apply List.flatMap_eq_nil_iff.mpr
  intro q hq
  obtain ⟨k,hk,hq⟩ := List.mem_range'.mp hq
  simp only [Nat.one_mul] at hq
  subst q
  have hq : y.s+off+k<tr.height tt := by omega
  have hEq : tr.cell tt (y.s+off+k) ee=0 := (F.consts k hk ee (by simp [rconsts])).trans he
  have hs := F.fld.st k hk
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
  · exact key_access_byte_silent hL hq (by simp) hs hEq
  · exact key_access_marker_silent hL hq (Or.inl rfl) hs (Or.inl hEq)
  · exact key_access_byte_silent hL hq (by simp) hs hEq
  · exact key_access_byte_silent hL hq (by simp) hs hEq
  · exact key_access_byte_silent hL hq (by simp) hs hEq
  · exact key_access_marker_silent hL hq (Or.inr rfl) hs (Or.inl hEq)

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
