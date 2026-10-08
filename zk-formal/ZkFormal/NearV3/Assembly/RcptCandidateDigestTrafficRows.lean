import ZkFormal.NearV3.Assembly.RcptCandidateFinalTraffic
-- Source DigestTrafficRows.lean SHA256: 2d212296df9e27b30ec4a680d25e93d4ec6c4ca1607eca29e8f7e4726d4354f7.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.FinalTraffic

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem rowT_digest (q : Nat) :
    rowTraffic RcptV3.interactions tr tt q pub B_DIGEST false=
      gt (tr.cell tt q gDg) ([tr.cell tt q dI,tr.cell tt q dL]++regsAt tr tt q) := by
  rw [rowT]
  simp [B_BYTES,B_DIGEST,B_KEYNIB,B_FINAL,B_MEM,B_RIDS,B_MPOS,B_RCL,B_SREC,B_AKC,B_BND,C]

variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

theorem digest_gate {q : Nat} (hq : q<tr.height tt) :
    tr.cell tt q gDg=tr.cell tt q fs*(tr.cell tt q sXRI+tr.cell tt q sXLH) := by
  have hh := con hL hq (e:=sub (c gDg) (.mul (c fs) (.add (c sXRI) (c sXLH)))) (mem_en (by simp [cEnd]))
  simp only [eval_sub,eval_mul,eval_add,eval_c] at hh
  grind

theorem digest_silent {q : Nat} (hq : q<tr.height tt)
    (hx : tr.cell tt q sXRI=0) (hl : tr.cell tt q sXLH=0) :
    rowTraffic RcptV3.interactions tr tt q pub B_DIGEST false=[] := by
  rw [rowT_digest]
  have hg := digest_gate hL hq
  rw [hx,hl] at hg
  exact gt_zero (by change tr.cell tt q gDg=0; grind) _

theorem ListBlockWf.header_digest {B : ListBlock} (h : ListBlockWf tr tt B) :
    (List.range' B.start 12).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_DIGEST false)=[] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro q hq
  obtain ⟨k,hk,hq⟩ := List.mem_range'.mp hq
  simp only [Nat.one_mul] at hq
  subst q
  have hs := h.header.st k hk
  have hfin := h.header_fin
  have ho := (oneHot hL (r:=B.start+k) (by omega) (by simp [states]) hs).2
  exact digest_silent hL (by omega) (ho sXRI (by simp [states]) (by decide))
    (ho sXLH (by simp [states]) (by decide))

/-- First-row gate of any actual receipt field is exactly its single starting offset. -/
theorem Layout.field_start_gate {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {X off len : Nat} (hm : (X,off,len)∈plan y.h y.Lp y.Lv y.Ls y.kt)
    (j : Nat) (hj : j<y.tot) :
    tr.cell tt (y.s+j) fs*tr.cell tt (y.s+j) X=(if j=off then 1 else 0) := by
  rw [cell_state hL h hm j hj]
  by_cases hin : off≤j ∧ j<off+len
  · rw [if_pos hin]
    have F := (h.flds _ hm).fld
    have hf := F.fs (j-off) (by exact Nat.sub_lt_left_of_lt_add hin.1 hin.2)
    simp only at hf
    rw [show y.s+off+(j-off)=y.s+j by omega] at hf
    rw [hf]
    by_cases he : j=off
    · subst j; simp only [Nat.sub_self,ite_true]; grind
    · rw [if_neg (by omega),if_neg he]; grind
  · rw [if_neg hin]
    have hp := (h.flds _ hm).fld.pos
    have he : j≠off := by intro he; subst j; apply hin; simp only at hp; omega
    rw [if_neg he]
    grind

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
