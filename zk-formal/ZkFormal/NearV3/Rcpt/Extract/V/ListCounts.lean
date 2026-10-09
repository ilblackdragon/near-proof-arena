import ZkFormal.NearV3.Rcpt.Extract.V.ListIndices

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Each receipt boundary increments the actual per-list receipt count. -/
theorem Layout.next_count {y z : RS}
    (hy : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (hz : Layout tr tt z.s z.h z.Lp z.Lv z.Ls z.kt)
    (hnext : z.s=y.s+y.tot) : tr.cell tt z.s cj=tr.cell tt y.s cj+1 := by
  have hp := total_pos y.h y.Lp y.Lv y.Ls y.kt
  have hf := hz.start_flags hL
  have hfin := hy.fin
  have he : y.s+y.tot-1+1=z.s := by unfold RS.tot at *; omega
  have hstep := brkStep hL (r := y.s+y.tot-1) (by unfold RS.tot; omega)
    (by unfold RS.tot; rw [hy.endRl,lay_last_ncl hL hy]; grind)
    (by simpa only [he] using hf.1)
  have hh := (hstep.2.1 (by simpa only [he] using hf.2.2)).1
  rw [he] at hh
  unfold RS.tot at hh
  rw [(lay_last hL hy).2 cj cjC] at hh
  exact hh

/-- The count at the final receipt is its initial count plus the remaining receipt count. -/
theorem receipt_sequence_count (xs : List RS) (s : Nat) (off : Fp)
    (hn : xs≠[]) (hc : Consec s (segsOf xs))
    (hl : ∀ y∈xs, Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (ho : ∀ y ys, xs=y::ys → tr.cell tt y.s cj=off) :
    tr.cell tt (segEnd s (segsOf xs)-1) cj=off+((xs.length-1 : Nat) : Fp) := by
  induction xs generalizing s off with
  | nil => exact False.elim (hn rfl)
  | cons y ys ih =>
    have hy := hl y (by simp)
    have hoy := ho y ys rfl
    obtain ⟨hs,hcon⟩ := hc
    have hcon : Consec (y.s+y.tot) (segsOf ys) := by simpa only [←hs,segsOf] using hcon
    cases ys with
    | nil =>
      have hh := (lay_last hL hy).2 cj cjC
      simp only [segsOf,List.map_cons,List.map_nil,segEnd,List.length_cons,List.length_nil]
      unfold RS.tot
      rw [hh,hoy]
      grind
    | cons z zs =>
      have hz := hl z (by simp)
      have hnxt := hy.next_count hL hz hcon.1
      have hh := ih (y.s+y.tot) (tr.cell tt y.s cj+1) (by simp) hcon
        (by intro w hw; exact hl w (by simp [hw])) (by intro w ws he; cases he; exact hnxt)
      change tr.cell tt (segEnd (y.s+y.tot) (segsOf (z::zs))-1) cj=_
      rw [hh,hoy]
      simp only [List.length_cons,Nat.add_sub_cancel,natCast_add]
      grind

/-- The terminal count equals the exact number of extracted receipts, including zero. -/
theorem ListBlockWf.terminal_count {B : ListBlock} (h : ListBlockWf tr tt B) :
    tr.cell tt (B.stop-1) cj=(B.receipts.length : Fp) := by
  cases he : B.receipts with
  | nil =>
    have hs : B.stop-1=B.start+11 := by simp [ListBlock.stop,he,segsOf,segEnd]
    rw [hs,List.length_nil]
    exact (h.header_end hL).2.1
  | cons y ys =>
    have hc := h.consecutive
    rw [he] at hc
    have hy := h.layouts y (by simp [he])
    have ho := (h.first_offset hL hy hc.1).2
    have hh := receipt_sequence_count hL (y::ys) (B.start+12) (1 : Fp)
      (by simp) hc (by simpa only [he] using h.layouts) (by intro z zs hz; cases hz; exact ho)
    change tr.cell tt (segEnd (B.start+12) (segsOf B.receipts)-1) cj=_
    rw [he,hh]
    simp only [List.length_cons,Nat.add_sub_cancel,natCast_add]
    grind

/-- The header's declared count is forced to equal the extracted receipt count in the field. -/
theorem ListBlockWf.header_count {B : ListBlock} (h : ListBlockWf tr tt B) :
    tr.cell tt B.start nj=(B.receipts.length : Fp) := by
  have hp := h.bound
  have hh := (leFacts hL (r := B.stop-1) (by omega) (h.terminal_le hL)).1
  have hc := h.constants hL (B.stop-1-B.start) (by omega) nj (by simp [lconsts])
  rw [show B.start+(B.stop-1-B.start)=B.stop-1 by omega] at hc
  rw [h.terminal_count hL,hc] at hh
  exact hh.symm

end ZkFormal.NearV3.RcptV3Proof
