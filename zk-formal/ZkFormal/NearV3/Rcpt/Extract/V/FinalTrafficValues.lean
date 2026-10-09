import ZkFormal.NearV3.Rcpt.Extract.V.FinalTrafficRows

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Receipt start consumes its exact successful account walk result. -/
theorem Layout.account_final {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {rN : Nat} (hr : tr.cell tt y.s RcptV3.r=(rN:Fp)) :
    rowTraffic RcptV3.interactions tr tt y.s pub B_FINAL false=
      [Msg.toFp [rN,0,FK_VAL,(rcptOf tr tt y).kslot]] := by
  have hfin := h.fin
  have hp : tr.cell tt y.s sPL=1 := by simpa using h.start_field.st 0 (by decide)
  have ht := (oneHot hL (r:=y.s) (by omega) (by simp [states]) hp).2 sT0 (by simp [states]) (by decide)
  have hf := (h.start_flags hL).2.2
  have hg := final_gate hL (q:=y.s) (by omega)
  rw [hf,ht] at hg
  have hfk := con hL (r:=y.s) (by omega) (e:=.mul (c rf) (c fkF)) (mem_ky (by simp [cKey]))
  have hk := con hL (r:=y.s) (by omega) (e:=.mul (c rf) (sub (c kF) (c kslot))) (mem_ky (by simp [cKey]))
  simp only [eval_mul,eval_sub,eval_c,hf] at hfk hk
  have hf0 : tr.cell tt y.s fkF=0 := by grind
  have hk0 : tr.cell tt y.s kF=tr.cell tt y.s kslot := by grind
  have hg1 : tr.cell tt y.s gF=1 := by grind
  rw [rowT_final]
  simp only [C,hg1,gt_one,hr,ht,hf0,hk0]
  simp only [Msg.toFp,List.map_cons,List.map_nil,rcptOf,cv,FK_VAL,Fp.ofNat_toNat,←natCast_eq]
  simp only [natCast_eq,Fp.ofNat_toNat]
  congr 3 <;> grind

/-- The optional access-key final message uses its actual flag and record key. -/
theorem Layout.access_final {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {rN : Nat} (hr : tr.cell tt y.s RcptV3.r=(rN:Fp)) :
    rowTraffic RcptV3.interactions tr tt (y.s+(40+y.Lp+y.Lv)) pub B_FINAL false=
      ((if (rcptOf tr tt y).ee then [[W_AK+rN,0,(rcptOf tr tt y).akf,(rcptOf tr tt y).akk]] else []) : List Msg).map Msg.toFp := by
  have hm : (sT0,40+y.Lp+y.Lv,1)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have F := h.flds _ hm
  have hfin := h.fin
  have hl := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  simp only at hl
  have hq : y.s+(40+y.Lp+y.Lv)<tr.height tt := by omega
  have hs : tr.cell tt (y.s+(40+y.Lp+y.Lv)) sT0=1 := by simpa using F.fld.st 0 (by simp)
  have he : tr.cell tt (y.s+(40+y.Lp+y.Lv)) ee=tr.cell tt y.s ee := by
    simpa using F.consts 0 (by simp) ee (by simp [rconsts])
  have hn : tr.cell tt (y.s+(40+y.Lp+y.Lv)) RcptV3.r=(rN:Fp) := by
    simpa only [Nat.add_zero,hr] using F.consts 0 (by simp) RcptV3.r (by simp [rconsts])
  have hf := rf_row hL h (h.start_flags hL).2.2 (40+y.Lp+y.Lv) (by omega)
  rw [if_neg (by omega)] at hf
  have hg := final_gate hL hq
  rw [hf,hs,he] at hg
  rw [rowT_final]
  have hg' : tr.cell tt (y.s+(40+y.Lp+y.Lv)) gF=tr.cell tt y.s ee := by grind
  simp only [C,hg',hs,hn,rcptOf,gt,decide_eq_true_eq]
  by_cases hee : tr.cell tt y.s ee=1
  · simp only [hee,ite_true,List.map_cons,List.map_nil,Msg.toFp,cv,←natCast_eq,natCast_add]
    simp only [natCast_eq,Fp.ofNat_toNat]
    have add_swap (a b : Fp) : a+b*1=b+a := by grind
    rw [add_swap]
  · simp only [hee,ite_false,List.map_nil]

end ZkFormal.NearV3.RcptV3Proof
