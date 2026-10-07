import ZkFormal.NearV3.Rcpt.Extract.V.AccessTraffic

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- Receiver and signer character traffic use their exact selected rows. -/
theorem rowT_srec (q : Nat) (sd : Bool) :
    rowTraffic RcptV3.interactions tr tt q pub B_SREC sd=
      gt (tr.cell tt q (if sd then gV else gS))
        [tr.cell tt q RcptV3.r,tr.cell tt q idx,tr.cell tt q (if sd then b else sx)] := by
  rw [rowT]
  cases sd <;> simp [B_BYTES,B_DIGEST,B_KEYNIB,B_FINAL,B_MEM,B_RIDS,B_MPOS,B_RCL,B_SREC,B_AKC,B_BND,C]

/-- A filtered list is exactly the concatenation of enabled singleton messages. -/
theorem gated_list {α β : Type} (xs : List α) (p : α→Bool) (f : α→β) :
    xs.flatMap (fun x => if p x then [f x] else [])=(xs.filter p).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [hp,ih]

variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Character gates cannot emit outside their respective account string state. -/
theorem srec_silent {q : Nat} (hq : q<tr.height tt) (sd : Bool)
    (hs : tr.cell tt q (if sd then sV else sS)=0) :
    rowTraffic RcptV3.interactions tr tt q pub B_SREC sd=[] := by
  have hc : .mul (c (if sd then gV else gS)) (Dsl.not (c (if sd then sV else sS)))∈cSys := by
    cases sd <;> simp [cSys]
  have hh := con hL hq (mem_sy hc)
  simp only [eval_mul,eval_not,eval_c,hs] at hh
  have hz : tr.cell tt q (if sd then gV else gS)=0 := by grind
  rw [rowT_srec]
  exact gt_zero hz _

/-- Actual list headers emit/receive no selected signer-character messages. -/
theorem ListBlockWf.header_srec {B : ListBlock} (h : ListBlockWf tr tt B) (sd : Bool) :
    (List.range' B.start 12).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_SREC sd)=[] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro q hq
  obtain ⟨k,hk,hq⟩ := List.mem_range'.mp hq
  simp only [Nat.one_mul] at hq
  subst q
  have hs := h.header.st k hk
  have hfin := h.header_fin
  apply srec_silent hL (by omega) sd
  exact (oneHot hL (r:=B.start+k) (by omega) (by simp [states]) hs).2
    (if sd then sV else sS) (by cases sd <;> simp [states]) (by cases sd <;> decide)

end ZkFormal.NearV3.RcptV3Proof
