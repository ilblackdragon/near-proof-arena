import ZkFormal.NearV3.Assembly.RcptCandidateRowFlags
import ZkFormal.NearV3.Assembly.RcptCandidateReceiptSystem
-- Source ReceiptEquality.lean SHA256: dcd60670cb618e5da363316e8d2928adaa26b2611b2206775478ab3e8f517ef6.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptSystem
import ZkFormal.NearV3.Rcpt.Extract.V.ListInterior

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 NearSpec
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- Equal-account mode supplies the exact native view's SREC gates and signer bytes. -/
theorem ee_of (hL : TableLocal receiptArithmeticCandidate tr tt pub) {y : RS}
    (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    let x := rcptOf tr tt y
    x.ee=true → x.sys=true ∧ x.s.length=x.v.length ∧
    (∀ i<x.v.length,x.gv.getD i false=true) ∧
    (∀ i<x.s.length,x.gs.getD i false=true) ∧
    ∀ i<x.s.length,x.sx.getD i 0=x.s.getD i 0 := by
  intro x he
  have he0 : tr.cell tt y.s RcptV3.ee=1 := by simpa only [x,rcptOf,decide_eq_true_eq] using he
  have hf := lay.fin
  have hp := total_pos y.h y.Lp y.Lv y.Ls y.kt
  have hq : y.s<tr.height tt := by omega
  have hr := layout_row_flags hL lay 0 (by unfold RS.tot; omega)
  simp only [Nat.add_zero] at hr
  have cs := con hL hq (e:=mul3 rowE (c RcptV3.ee) (Dsl.not (c RcptV3.sys))) (mem_sy (by simp [cSys]))
  have cl := con hL hq (e:=mul3 rowE (c RcptV3.ee) (sub (c RcptV3.Ls) (c RcptV3.Lv))) (mem_sy (by simp [cSys]))
  simp only [rowE,eval_mul3,eval_sub,eval_not,eval_c,hr.1,hr.2,he0] at cs cl
  rw [lay.cLs,lay.cLv] at cl
  have hs : tr.cell tt y.s RcptV3.sys=1 := by grind
  have mV : (sV,8+y.Lp,y.Lv)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have mS : (sS,45+y.Lp+y.Lv,y.Ls)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have lV := plan_le y.h y.Lp y.Lv y.Ls y.kt _ mV
  have lS := plan_le y.h y.Lp y.Lv y.Ls y.kt _ mS
  simp only at lV lS
  have FV : RFld tr tt y.s (y.s+(8+y.Lp)) y.Lv sV := lay.flds _ mV
  have FS : RFld tr tt y.s (y.s+(45+y.Lp+y.Lv)) y.Ls sS := lay.flds _ mS
  have hlen : y.Ls=y.Lv := by
    apply ofNat_inj (by have := hP hL; omega) (by have := hP hL; omega)
    grind
  have hV : ∀ i,i<y.Lv → tr.cell tt (y.s+(8+y.Lp)+i) gV=1 := by
    intro i hi
    have cc := con hL (r:=y.s+(8+y.Lp)+i) (by omega)
      (e:=mul3 (c RcptV3.ee) (c sV) (Dsl.not (c gV))) (mem_sy (by simp [cSys]))
    simp only [eval_mul3,eval_not,eval_c] at cc
    rw [FV.consts i hi _ (by simp [rconsts]),he0,FV.fld.st i hi] at cc
    grind
  have hS : ∀ i,i<y.Ls → tr.cell tt (y.s+(45+y.Lp+y.Lv)+i) gS=1 ∧
      tr.cell tt (y.s+(45+y.Lp+y.Lv)+i) RcptV3.sx=tr.cell tt (y.s+(45+y.Lp+y.Lv)+i) b := by
    intro i hi
    have cc := con hL (r:=y.s+(45+y.Lp+y.Lv)+i) (by omega)
      (e:=mul3 (c RcptV3.ee) (c sS) (Dsl.not (c gS))) (mem_sy (by simp [cSys]))
    have cb := con hL (r:=y.s+(45+y.Lp+y.Lv)+i) (by omega)
      (e:=mul3 (c RcptV3.ee) (c sS) (sub (c RcptV3.sx) (c b))) (mem_sy (by simp [cSys]))
    simp only [eval_mul3,eval_not,eval_sub,eval_c] at cc cb
    rw [FS.consts i hi _ (by simp [rconsts]),he0,FS.fld.st i hi] at cc cb
    grind
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [x,rcptOf,decide_eq_true_eq] using hs
  · simpa only [x,rcptOf,colAt_len] using hlen
  · intro i hi
    have hi' : i<y.Lv := by simpa only [x,rcptOf,colAt_len] using hi
    simp [x,rcptOf,List.getD,hi',hV i hi']
  · intro i hi
    have hi' : i<y.Ls := by simpa only [x,rcptOf,colAt_len] using hi
    simp [x,rcptOf,List.getD,hi',(hS i hi').1]
  · intro i hi
    have hi' : i<y.Ls := by simpa only [x,rcptOf,colAt_len] using hi
    simp [x,rcptOf,colAt,List.getD,hi',cv,(hS i hi').2]

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
