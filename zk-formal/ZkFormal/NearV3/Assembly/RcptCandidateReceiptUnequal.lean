import ZkFormal.NearV3.Assembly.RcptCandidateReceiptEquality
-- Source ReceiptUnequal.lean SHA256: b04d5bbfe8da1ea8c2e3ea006f24e6b384a2224ed5bddeba0097002ea7caba6c.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptEquality

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 NearSpec
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- Unequal-account mode exhibits a length difference or a selected unequal signer byte. -/
theorem neq_of (hL : TableLocal receiptArithmeticCandidate tr tt pub) {y : RS}
    (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    let x := rcptOf tr tt y
    x.sys=true → x.ee=false → x.s.length≠x.v.length ∨
      ∃ i<x.s.length,x.gs.getD i false=true ∧ x.sx.getD i 0≠x.s.getD i 0 := by
  intro x hsys hee
  have hs : tr.cell tt y.s RcptV3.sys=1 := by simpa only [x,rcptOf,decide_eq_true_eq] using hsys
  have hn : tr.cell tt y.s RcptV3.ee≠1 := by simpa only [x,rcptOf,decide_eq_false_iff_not] using hee
  have hf := lay.fin
  have hp := total_pos y.h y.Lp y.Lv y.Ls y.kt
  have hq : y.s<tr.height tt := by omega
  have he : tr.cell tt y.s RcptV3.ee=0 := (isBool hL hq (by simp [boolCols])).resolve_right hn
  have hr := layout_row_flags hL lay 0 (by unfold RS.tot; omega)
  simp only [Nat.add_zero] at hr
  have cd := con hL hq (e:=.mul rowE (sub (c dd) (mul3 (c RcptV3.sys) (Dsl.not (c RcptV3.ee)) (c dm))))
    (mem_sy (by simp [cSys]))
  simp only [rowE,eval_mul,eval_mul3,eval_sub,eval_not,eval_c,hr.1,hr.2,hs,he] at cd
  have hd : tr.cell tt y.s dd=tr.cell tt y.s dm := by grind
  rcases isBool hL hq (x:=dm) (by simp [boolCols]) with hm|hm
  · left
    intro hlen
    have hlen' : y.Ls=y.Lv := by simpa only [x,rcptOf,colAt_len] using hlen
    have cf := con hL hq (e:=.mul (c rf) (.mul dzE (sub (.mul (sub (c RcptV3.Ls) (c RcptV3.Lv)) (c invL)) (k 1))))
      (mem_sy (by simp [cSys]))
    have hrf := (layout_start_flags hL lay).2.2
    simp only [dzE,eval_mul,eval_sub,eval_c,eval_k,hrf,hs,he,hd,hm,lay.cLs,lay.cLv,hlen'] at cf
    grind
  · right
    have hd1 : tr.cell tt y.s dd=1 := hd.trans hm
    have mS : (sS,45+y.Lp+y.Lv,y.Ls)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
    have lS := plan_le y.h y.Lp y.Lv y.Ls y.kt _ mS
    simp only at lS
    have F : RFld tr tt y.s (y.s+(45+y.Lp+y.Lv)) y.Ls sS := lay.flds _ mS
    have hpos := F.fld.pos
    let s0 := y.s+(45+y.Lp+y.Lv)
    have hH : s0+y.Ls<tr.height tt := by dsimp [s0]; omega
    have hex : ∃ i,i<y.Ls ∧ tr.cell tt (s0+i) gS=1 := by
      classical
      apply Classical.byContradiction
      intro hh
      have hg : ∀ i,i<y.Ls → tr.cell tt (s0+i) gS=0 := by
        intro i hi
        have hb := isBool hL (r:=s0+i) (by omega) (x:=gS) (by simp [boolCols])
        exact hb.resolve_right (fun h => hh ⟨i,hi,h⟩)
      have hz : ∀ i,i<y.Ls → tr.cell tt (s0+i) scnt=0 := by
        intro i
        induction i with
        | zero =>
          intro hi
          have cc := con hL (r:=s0) (by omega)
            (e:=mul3 (c sS) (c fs) (sub (c scnt) (c gS))) (mem_sy (by simp [cSys]))
          have hst : tr.cell tt s0 sS=1 := by simpa [s0] using F.fld.st 0 hpos
          have hfs : tr.cell tt s0 fs=1 := by simpa [s0] using F.fld.fs 0 hpos
          have hgg : tr.cell tt s0 gS=0 := by simpa using hg 0 hpos
          simp only [eval_mul3,eval_sub,eval_c,hst,hfs,hgg] at cc
          simp only [Nat.add_zero]
          grind
        | succ i ih =>
          intro hi
          have cc := con hL (r:=s0+i) (by omega)
            (e:=mul3 (c sS) (Dsl.not (c fe)) (sub (n scnt) (.add (c scnt) (n gS)))) (mem_sy (by simp [cSys]))
          simp only [eval_mul3,eval_not,eval_sub,eval_add,eval_c,eval_n,nxt (show s0+i+1<tr.height tt by omega)] at cc
          rw [F.fld.st i (by omega),F.fld.fe i (by omega),if_neg (by omega),ih (by omega),
            show s0+i+1=s0+(i+1) by omega,hg (i+1) hi] at cc
          grind
      have cc := con hL (r:=s0+(y.Ls-1)) (by omega)
        (e:=.mul (mul3 (c sS) (c fe) (c dd)) (Dsl.not (c scnt))) (mem_sy (by simp [cSys]))
      simp only [eval_mul,eval_mul3,eval_not,eval_c] at cc
      rw [F.fld.st (y.Ls-1) (by omega),F.fld.fe (y.Ls-1) (by omega),if_pos (by omega),
        F.consts (y.Ls-1) (by omega) _ (by simp [rconsts]),hd1,hz (y.Ls-1) (by omega)] at cc
      grind
    obtain ⟨i,hi,hg⟩ := hex
    have cb := con hL (r:=s0+i) (by omega)
      (e:=.mul (.mul (c dd) (c gS)) (sub (.mul (sub (c b) (c RcptV3.sx)) (c invD)) (k 1)))
      (mem_sy (by simp [cSys]))
    simp only [eval_mul,eval_sub,eval_c,eval_k] at cb
    rw [F.consts i hi _ (by simp [rconsts]),hd1,hg] at cb
    have hne : cv tr tt (s0+i) RcptV3.sx≠cv tr tt (s0+i) b := by
      intro eq
      have eq' : tr.cell tt (s0+i) RcptV3.sx=tr.cell tt (s0+i) b := by
        rw [cell_eq_cast tr tt (s0+i) RcptV3.sx,cell_eq_cast tr tt (s0+i) b,eq]
      rw [eq'] at cb
      grind
    refine ⟨i,?_,?_,?_⟩
    · simpa only [x,rcptOf,colAt_len] using hi
    · simpa [x,rcptOf,List.getD,hi,s0] using hg
    · simpa [x,rcptOf,colAt,List.getD,hi,s0] using hne

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
