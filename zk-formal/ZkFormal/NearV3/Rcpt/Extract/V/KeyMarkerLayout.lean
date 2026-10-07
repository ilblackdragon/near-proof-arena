import ZkFormal.NearV3.Rcpt.Extract.V.KeyMarkerValues

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Exact natural messages for the complete receiver end field. -/
theorem Layout.key_receiver_end_field {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {rN : Nat} (hr : tr.cell tt y.s RcptV3.r=(rN:Fp)) :
    (List.range' (y.s+(8+y.Lp+y.Lv)) 32).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true)=
      ([[rN,2+2*y.Lv,SYM_END,1]] : List Msg).map Msg.toFp := by
  have hm : (sRID,8+y.Lp+y.Lv,32)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have F : RFld tr tt y.s (y.s+(8+y.Lp+y.Lv)) 32 sRID := lay.flds _ hm
  have hfin := lay.fin
  have hle := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  simp only at hle
  have hq : y.s+(8+y.Lp+y.Lv)<tr.height tt := by omega
  have hs : tr.cell tt (y.s+(8+y.Lp+y.Lv)) sRID=1 := by simpa only [Nat.add_zero] using F.fld.st 0 (by decide)
  have hfs : tr.cell tt (y.s+(8+y.Lp+y.Lv)) fs=1 := by simpa only [Nat.add_zero,ite_true] using F.fld.fs 0 (by decide)
  have hc : ∀ x∈rconsts,tr.cell tt (y.s+(8+y.Lp+y.Lv)) x=tr.cell tt y.s x := by
    intro x hx; simpa only [Nat.add_zero] using F.consts 0 (by decide) x hx
  rw [key_marker_field hL F (by omega) (Or.inl rfl)]
  apply key_receiver_end_value hL hq hs hfs ((hc _ (by simp [rconsts])).trans hr)
  · exact (hc _ (by simp [rconsts])).trans lay.cLv

/-- Exact natural messages for the complete access type field. -/
theorem Layout.key_access_type_field {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {rN : Nat} (hr : tr.cell tt y.s RcptV3.r=(rN:Fp)) (he : tr.cell tt y.s ee=1) :
    (List.range' (y.s+(40+y.Lp+y.Lv)) 1).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true)=
      ([[W_AK+rN,0,0,0],[W_AK+rN,1,2,0]] : List Msg).map Msg.toFp := by
  have hm : (sT0,40+y.Lp+y.Lv,1)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have F : RFld tr tt y.s (y.s+(40+y.Lp+y.Lv)) 1 sT0 := lay.flds _ hm
  have hfin := lay.fin
  have hle := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  simp only at hle
  have hq : y.s+(40+y.Lp+y.Lv)<tr.height tt := by omega
  have hs : tr.cell tt (y.s+(40+y.Lp+y.Lv)) sT0=1 := by simpa only [Nat.add_zero] using F.fld.st 0 (by decide)
  have hfs : tr.cell tt (y.s+(40+y.Lp+y.Lv)) fs=1 := by simpa only [Nat.add_zero,ite_true] using F.fld.fs 0 (by decide)
  have hc : ∀ x∈rconsts,tr.cell tt (y.s+(40+y.Lp+y.Lv)) x=tr.cell tt y.s x := by
    intro x hx; simpa only [Nat.add_zero] using F.consts 0 (by decide) x hx
  simp only [List.range'_one,List.flatMap_singleton]
  apply key_access_type_value hL hq hs hfs ((hc _ (by simp [rconsts])).trans hr)
  · exact (hc _ (by simp [rconsts])).trans he

/-- Exact natural messages for the complete access separator field. -/
theorem Layout.key_access_separator_field {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {rN : Nat} (hr : tr.cell tt y.s RcptV3.r=(rN:Fp)) (he : tr.cell tt y.s ee=1) :
    (List.range' (y.s+(41+y.Lp+y.Lv)) 4).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true)=
      ([[W_AK+rN,2+2*y.Ls,0,0],[W_AK+rN,3+2*y.Ls,2,0]] : List Msg).map Msg.toFp := by
  have hm : (sSL,41+y.Lp+y.Lv,4)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have F : RFld tr tt y.s (y.s+(41+y.Lp+y.Lv)) 4 sSL := lay.flds _ hm
  have hfin := lay.fin
  have hle := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  simp only at hle
  have hq : y.s+(41+y.Lp+y.Lv)<tr.height tt := by omega
  have hs : tr.cell tt (y.s+(41+y.Lp+y.Lv)) sSL=1 := by simpa only [Nat.add_zero] using F.fld.st 0 (by decide)
  have hfs : tr.cell tt (y.s+(41+y.Lp+y.Lv)) fs=1 := by simpa only [Nat.add_zero,ite_true] using F.fld.fs 0 (by decide)
  have hc : ∀ x∈rconsts,tr.cell tt (y.s+(41+y.Lp+y.Lv)) x=tr.cell tt y.s x := by
    intro x hx; simpa only [Nat.add_zero] using F.consts 0 (by decide) x hx
  rw [key_marker_field hL F (by omega) (Or.inr (Or.inl rfl))]
  apply key_access_separator_value hL hq hs hfs ((hc _ (by simp [rconsts])).trans hr)
  · exact (hc _ (by simp [rconsts])).trans he
  · exact (hc _ (by simp [rconsts])).trans lay.cLs

/-- Exact natural messages for the complete access kind field. -/
theorem Layout.key_access_kind_field {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {rN : Nat} (hr : tr.cell tt y.s RcptV3.r=(rN:Fp)) (he : tr.cell tt y.s ee=1) :
    (List.range' (y.s+(45+y.Lp+y.Lv+y.Ls)) 1).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true)=
      ([[W_AK+rN,4+2*y.Ls,0,0],[W_AK+rN,5+2*y.Ls,y.kt,0]] : List Msg).map Msg.toFp := by
  have hm : (sKT,45+y.Lp+y.Lv+y.Ls,1)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have F : RFld tr tt y.s (y.s+(45+y.Lp+y.Lv+y.Ls)) 1 sKT := lay.flds _ hm
  have hfin := lay.fin
  have hle := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  simp only at hle
  have hq : y.s+(45+y.Lp+y.Lv+y.Ls)<tr.height tt := by omega
  have hs : tr.cell tt (y.s+(45+y.Lp+y.Lv+y.Ls)) sKT=1 := by simpa only [Nat.add_zero] using F.fld.st 0 (by decide)
  have hfs : tr.cell tt (y.s+(45+y.Lp+y.Lv+y.Ls)) fs=1 := by simpa only [Nat.add_zero,ite_true] using F.fld.fs 0 (by decide)
  have hc : ∀ x∈rconsts,tr.cell tt (y.s+(45+y.Lp+y.Lv+y.Ls)) x=tr.cell tt y.s x := by
    intro x hx; simpa only [Nat.add_zero] using F.consts 0 (by decide) x hx
  simp only [List.range'_one,List.flatMap_singleton]
  apply key_access_kind_value hL hq hs hfs ((hc _ (by simp [rconsts])).trans hr)
  · exact (hc _ (by simp [rconsts])).trans he
  · exact (hc _ (by simp [rconsts])).trans lay.cLs
  · exact (hc _ (by simp [rconsts])).trans lay.ckt

/-- Exact natural messages for the complete access end field. -/
theorem Layout.key_access_end_field {y : RS} (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {rN : Nat} (hr : tr.cell tt y.s RcptV3.r=(rN:Fp)) (he : tr.cell tt y.s ee=1) :
    (List.range' (y.s+(78+Vt y.Lp y.Lv y.Ls y.kt)) 16).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_KEYNIB true)=
      ([[W_AK+rN,70+2*y.Ls+64*y.kt,SYM_END,1]] : List Msg).map Msg.toFp := by
  have hm : (sGP,78+Vt y.Lp y.Lv y.Ls y.kt,16)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have F : RFld tr tt y.s (y.s+(78+Vt y.Lp y.Lv y.Ls y.kt)) 16 sGP := lay.flds _ hm
  have hfin := lay.fin
  have hle := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  simp only at hle
  have hq : y.s+(78+Vt y.Lp y.Lv y.Ls y.kt)<tr.height tt := by omega
  have hs : tr.cell tt (y.s+(78+Vt y.Lp y.Lv y.Ls y.kt)) sGP=1 := by simpa only [Nat.add_zero] using F.fld.st 0 (by decide)
  have hfs : tr.cell tt (y.s+(78+Vt y.Lp y.Lv y.Ls y.kt)) fs=1 := by simpa only [Nat.add_zero,ite_true] using F.fld.fs 0 (by decide)
  have hc : ∀ x∈rconsts,tr.cell tt (y.s+(78+Vt y.Lp y.Lv y.Ls y.kt)) x=tr.cell tt y.s x := by
    intro x hx; simpa only [Nat.add_zero] using F.consts 0 (by decide) x hx
  rw [key_marker_field hL F (by omega) (Or.inr (Or.inr rfl))]
  apply key_access_end_value hL hq hs hfs ((hc _ (by simp [rconsts])).trans hr)
  · exact (hc _ (by simp [rconsts])).trans he
  · exact (hc _ (by simp [rconsts])).trans lay.cLs
  · exact (hc _ (by simp [rconsts])).trans lay.ckt

end ZkFormal.NearV3.RcptV3Proof
