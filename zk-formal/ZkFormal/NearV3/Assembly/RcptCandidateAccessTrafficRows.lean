import ZkFormal.NearV3.Assembly.RcptCandidateReceiptPositionsTraffic
-- Source AccessTrafficRows.lean SHA256: 39d71ac3243f408649d5c10c72f53f2c3bc2fa7cea5b017655615e56db229e35.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptPositionsTraffic

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- Access-counter send/receive differ only by the successor counter. -/
theorem rowT_akc (q : Nat) (sd : Bool) :
    rowTraffic RcptV3.interactions tr tt q pub B_AKC sd=
      gt (tr.cell tt q gAK) [tr.cell tt q kF,tr.cell tt q uak+(if sd then 1 else 0)] := by
  rw [rowT]
  cases sd <;> simp [B_BYTES,B_DIGEST,B_KEYNIB,B_FINAL,B_MEM,B_RIDS,B_MPOS,B_RCL,B_SREC,B_AKC,B_BND,C] <;> congr 3 <;> grind

variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- The active gate equation prevents arbitrary access-counter traffic. -/
theorem akc_gate {q : Nat} (hq : q<tr.height tt) :
    tr.cell tt q gAK=tr.cell tt q ee*tr.cell tt q sT0*(1-tr.cell tt q fkF) := by
  have hh := con hL hq (e:=sub (c gAK) (mul3 (c ee) (c sT0) (Dsl.not (c fkF))))
    (mem_ky (by simp [cKey]))
  simp only [eval_sub,eval_c,eval_mul3,eval_not] at hh
  grind

/-- Every non-T0 row is silent on both access-counter bus directions. -/
theorem akc_silent {q : Nat} (hq : q<tr.height tt) (hs : tr.cell tt q sT0=0) (sd : Bool) :
    rowTraffic RcptV3.interactions tr tt q pub B_AKC sd=[] := by
  rw [rowT_akc,akc_gate hL hq,hs]
  have hz : tr.cell tt q ee*0*(1-tr.cell tt q fkF)=0 := by grind
  exact gt_zero hz _

theorem ListBlockWf.header_akc {B : ListBlock} (h : ListBlockWf tr tt B) (sd : Bool) :
    (List.range' B.start 12).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_AKC sd)=[] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro q hq
  obtain ⟨k,hk,hq⟩ := List.mem_range'.mp hq
  simp only [Nat.one_mul] at hq
  subst q
  have hs := h.header.st k hk
  have hfin := h.header_fin
  exact akc_silent hL (by omega) ((oneHot hL (r:=B.start+k) (by omega)
    (by simp [states]) hs).2 sT0 (by simp [states]) (by decide)) sd

/-- A complete receipt interval has only its actual access-key T0 lookup row. -/
theorem Layout.akc_window {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) (sd : Bool) :
    (List.range' y.s y.tot).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_AKC sd)=
      rowTraffic RcptV3.interactions tr tt (y.s+(40+y.Lp+y.Lv)) pub B_AKC sd := by
  have hm : (sT0,40+y.Lp+y.Lv,1)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have hl := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  have hf := h.fin
  simp only at hl
  rw [flatMap_window _ y.s y.tot (40+y.Lp+y.Lv) 1 (by exact hl)]
  · simp only [List.range'_one,List.flatMap_singleton]
  · intro j hj hout
    exact akc_silent hL (by unfold RS.tot at hj; omega) (st_row hL h hm j hj hout) sd

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
