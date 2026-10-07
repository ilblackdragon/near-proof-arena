import ZkFormal.NearV3.Rcpt.Extract.V.DigestTrafficRows

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Exact two-message decomposition at arbitrary disjoint row offsets. -/
theorem flatMap_two_offsets {α : Type} (f : Nat→List α) (s T a b : Nat)
    (hab : a<b) (hb : b<T) (hz : ∀ k,k<T → k≠a → k≠b → f (s+k)=[]) :
    (List.range' s T).flatMap f=f (s+a)++f (s+b) := by
  rw [flatMap_window f s T a (T-a) (by omega) (by intro k hk ho; exact hz k hk (by omega) (by omega))]
  have hh := flatMap_two_rows f (s+a) (T-a) (b-a) (by omega) (by omega)
    (by intro k hk h0 hB; rw [show s+a+k=s+(a+k) by omega]; exact hz (a+k) (by omega) (by omega) (by omega))
  rw [hh,show s+a+(b-a)=s+b by omega]

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- A state absent from the actual receipt plan cannot appear in its rows. -/
theorem Layout.absent_state {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    {X : Nat} (hx : X∈states) (hn : X∉(plan y.h y.Lp y.Lv y.Ls y.kt).map Prod.fst)
    (j : Nat) (hj : j<y.tot) : tr.cell tt (y.s+j) X=0 := by
  obtain ⟨f,hf,hlo,hhi⟩ := plan_cover y.h y.Lp y.Lv y.Ls y.kt j hj
  have hs := (h.flds f hf).fld.st (j-f.2.1) (by omega)
  rw [show y.s+f.2.1+(j-f.2.1)=y.s+j by omega] at hs
  have hfin := h.fin
  exact (oneHot hL (r:=y.s+j) (by unfold RS.tot at hj; omega)
    (plan_states y.h y.Lp y.Lv y.Ls y.kt f hf).1 hs).2 X hx
    (by intro he; apply hn; exact List.mem_map.mpr ⟨f,hf,he.symm⟩)

/-- Digest lookup traffic is zero away from its enabled digest starts. -/
theorem Layout.digest_zero {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (j : Nat) (hj : j<y.tot)
    (hx : y.h=false ∨ j≠127+Vt y.Lp y.Lv y.Ls y.kt)
    (hl : j≠144+32*hN y.h+Vt y.Lp y.Lv y.Ls y.kt) :
    rowTraffic RcptV3.interactions tr tt (y.s+j) pub B_DIGEST false=[] := by
  have ml : (sXLH,144+32*hN y.h+Vt y.Lp y.Lv y.Ls y.kt,32)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have gl := h.field_start_gate hL ml j hj
  rw [if_neg hl] at gl
  have gx : tr.cell tt (y.s+j) fs*tr.cell tt (y.s+j) sXRI=0 := by
    cases he : y.h with
    | false =>
      have hh := h.absent_state hL (X:=sXRI) (by simp [states]) (by simp [he,plan]; decide) j hj
      rw [hh]; grind
    | true =>
      have mx : (sXRI,127+Vt y.Lp y.Lv y.Ls y.kt,32)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [he,plan]
      have hh := h.field_start_gate hL mx j hj
      rw [if_neg (by simpa [he] using hx)] at hh
      exact hh
  have hfin := h.fin
  have hg := digest_gate hL (q:=y.s+j) (by unfold RS.tot at hj; omega)
  rw [rowT_digest]
  exact gt_zero (by change tr.cell tt (y.s+j) gDg=0; grind) _

/-- A refund receipt has two digest starts; a non-refund receipt has only the
partial-outcome digest start. Both use the actual physical receipt intervals. -/
theorem Layout.digest_rows {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    (List.range' y.s y.tot).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_DIGEST false)=
      (if y.h then rowTraffic RcptV3.interactions tr tt (y.s+(127+Vt y.Lp y.Lv y.Ls y.kt)) pub B_DIGEST false else [])++
      rowTraffic RcptV3.interactions tr tt (y.s+(144+32*hN y.h+Vt y.Lp y.Lv y.Ls y.kt)) pub B_DIGEST false := by
  cases he : y.h with
  | false =>
    simp only [Bool.false_eq_true,ite_false,List.nil_append,hN,Nat.mul_zero,Nat.add_zero]
    rw [flatMap_window _ y.s y.tot (144+Vt y.Lp y.Lv y.Ls y.kt) 1
      (by unfold RS.tot total; rw [he]; simp <;> omega)]
    · simp only [List.range'_one,List.flatMap_singleton]
    · intro j hj hout
      exact h.digest_zero hL j hj (Or.inl he) (by simpa [he,hN] using (show j≠144+Vt y.Lp y.Lv y.Ls y.kt by omega))
  | true =>
    simp only [ite_true]
    apply flatMap_two_offsets _ y.s y.tot (127+Vt y.Lp y.Lv y.Ls y.kt)
      (144+32*hN true+Vt y.Lp y.Lv y.Ls y.kt) (by unfold hN; omega)
      (by unfold RS.tot total; rw [he]; simp [hN] <;> omega)
    intro j hj hx hl
    exact h.digest_zero hL j hj (Or.inr hx) (by simpa only [he] using hl)

end ZkFormal.NearV3.RcptV3Proof
