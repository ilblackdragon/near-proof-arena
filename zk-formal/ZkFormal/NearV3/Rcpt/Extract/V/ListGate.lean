import ZkFormal.NearV3.Rcpt.Extract.V.ListInterior

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Before the end of a consecutive receipt sequence, its rows have no list-end gate. -/
theorem receipt_sequence_le_zero (xs : List RS) (s q : Nat)
    (hc : Consec s (segsOf xs))
    (hl : ∀ y∈xs, Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (hq : s≤q) (he : q+1<segEnd s (segsOf xs)) : tr.cell tt q le=0 := by
  induction xs generalizing s with
  | nil => simp only [segsOf,List.map_nil,segEnd] at he; omega
  | cons y ys ih =>
    obtain ⟨hs,hcon⟩ := hc
    have hy := hl y (by simp)
    have hcon : Consec (y.s+y.tot) (segsOf ys) := by simpa only [←hs,segsOf] using hcon
    by_cases hlt : q<y.s+y.tot
    · by_cases hlast : q+1=y.s+y.tot
      · cases ys with
        | nil => simp only [segsOf,List.map_cons,List.map_nil,segEnd] at he; omega
        | cons z zs =>
          have hz := hl z (by simp)
          have hzs : z.s=y.s+y.tot := hcon.1
          have hh := hy.followed_le_zero hL hz hzs
          simpa only [show y.s+y.tot-1=q by omega] using hh
      · have hh := hy.interior_le_zero hL (q-y.s) (by omega)
        simpa only [show y.s+(q-y.s)=q by omega] using hh
    · exact ih (y.s+y.tot) hcon (by intro z hz; exact hl z (by simp [hz])) (by omega) he

/-- Exactly the last physical row of a list block enables the RCL gate. -/
theorem ListBlockWf.le_gate {B : ListBlock} (h : ListBlockWf tr tt B)
    {q : Nat} (hlo : B.start≤q) (hhi : q<B.stop) :
    tr.cell tt q le=if q+1=B.stop then 1 else 0 := by
  by_cases hlast : q+1=B.stop
  · rw [if_pos hlast]
    simpa only [show B.stop-1=q by omega] using h.terminal_le hL
  · rw [if_neg hlast]
    by_cases hheader : q<B.start+12
    · by_cases hend : q=B.start+11
      · cases he : B.receipts with
        | nil =>
          have hs : B.stop=B.start+12 := by simp [ListBlock.stop,he,segsOf,segEnd]
          omega
        | cons y ys =>
          have hc := h.consecutive
          rw [he] at hc
          have hy := h.layouts y (by simp [he])
          have hs : y.s=B.start+12 := hc.1
          have hf := (hy.start_flags hL).2.2
          have hfin := h.header_fin
          have hh := (le_eq hL (r := q) (by omega)).1
          rw [show q+1=y.s by omega,hf] at hh
          rw [hh]
          grind
      · have hh := h.header_interior_le_zero hL (q-B.start) (by omega)
        simpa only [show B.start+(q-B.start)=q by omega] using hh
    · exact receipt_sequence_le_zero hL B.receipts (B.start+12) q h.consecutive h.layouts
        (by omega) (by change q+1<B.stop; omega)

end ZkFormal.NearV3.RcptV3Proof
