import ZkFormal.NearV3.Rcpt.Extract.V.SystemString

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 NearSpec
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- The V3 system gate forces the native six-byte predecessor length. -/
theorem system_length (hL : TableLocal RcptV3.table tr tt pub) {y : RS}
    (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (hs : tr.cell tt y.s RcptV3.sys=1) : y.Lp=6 := by
  have hm : (sP,4,y.Lp)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have F : RFld tr tt y.s (y.s+4) y.Lp sP := lay.flds _ hm
  have hl := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  have hf := lay.fin
  have hp := F.fld.pos
  simp only at hl
  have hq : y.s+4<tr.height tt := by omega
  have hst : tr.cell tt (y.s+4) sP=1 := by simpa using F.fld.st 0 hp
  have ho := oneHot hL hq (by simp [states]) hst
  have hsys : tr.cell tt (y.s+4) RcptV3.sys=1 := by
    rw [show y.s+4=y.s+4+0 by omega,F.consts 0 hp _ (by simp [rconsts]),hs]
  have hc : tr.cell tt (y.s+4) RcptV3.Lp=((y.Lp:Nat):Fp) := by
    rw [show y.s+4=y.s+4+0 by omega,F.consts 0 hp _ LpC,lay.cLp]
  have cc := con hL hq (e:=mul3 rowE (c RcptV3.sys) (sub (c RcptV3.Lp) (k 6))) (mem_ch (by simp [cChars]))
  simp only [rowE,eval_mul3,eval_sub,eval_c,eval_k] at cc
  rw [ho.1,ho.2 sCL (by simp [states]) (by decide),hsys,hc] at cc
  have he : ((y.Lp:Nat):Fp)=(6:Fp) := by grind
  apply ofNat_inj (by have := hP hL; omega) (by decide)
  exact he

/-- Exact native/V3 system-predecessor equivalence, with no external string premise. -/
theorem system_of (hL : TableLocal RcptV3.table tr tt pub) {y : RS}
    (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    (rcptOf tr tt y).sys=true ↔ toBytes (rcptOf tr tt y).p=AccountId.system := by
  have hm : (sP,4,y.Lp)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have F : RFld tr tt y.s (y.s+4) y.Lp sP := lay.flds _ hm
  have hl := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  have hf := lay.fin
  have hp := F.fld.pos
  simp only at hl
  have hH : y.s+4+y.Lp<tr.height tt := by omega
  have hc : ∀ k,k<y.Lp → tr.cell tt (y.s+4+k) RcptV3.Lp=((y.Lp:Nat):Fp) := by
    intro k hk
    rw [F.consts k hk _ LpC,lay.cLp]
  have hs : ∀ k,k<y.Lp → tr.cell tt (y.s+4+k) RcptV3.sys=tr.cell tt y.s RcptV3.sys := by
    intro k hk
    exact F.consts k hk _ (by simp [rconsts])
  change decide (tr.cell tt y.s RcptV3.sys=1)=true ↔ toBytes (colAt tr tt (y.s+4) y.Lp b)=AccountId.system
  rw [decide_eq_true_eq]
  constructor
  · intro hs0
    have hn := system_length hL lay hs0
    have F6 : RFld tr tt y.s (y.s+4) 6 sP := hn ▸ F
    have hc6 : ∀ k,k<6 → tr.cell tt (y.s+4+k) RcptV3.Lp=(6:Fp) := by
      intro k hk
      rw [hc k (by omega),hn]
      rfl
    rw [hn]
    apply system_string_of_flag hL F6 (by omega) hc6
    rw [hs 5 (by omega),hs0]
  · intro he
    have ht := system_flag_of_string hL F hH hc he
    rw [hs (y.Lp-1) (by omega)] at ht
    exact ht

end ZkFormal.NearV3.RcptV3Proof
