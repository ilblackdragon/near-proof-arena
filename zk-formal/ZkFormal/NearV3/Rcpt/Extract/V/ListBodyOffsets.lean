import ZkFormal.NearV3.Rcpt.Extract.V.BodyOffsets

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

theorem receipt_sequence_body_end (xs : List RS) (s : Nat) (off : Fp)
    (hn : xs≠[]) (hc : Consec s (segsOf xs))
    (hl : ∀ y∈xs, Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (ho : ∀ y ys, xs=y::ys → tr.cell tt y.s o2=off) :
    tr.cell tt (segEnd s (segsOf xs)-1) o2End=
      off+(((xs.map fun y => rfLen (rcptOf tr tt y)).sum : Nat) : Fp) := by
  induction xs generalizing s off with
  | nil => exact False.elim (hn rfl)
  | cons y ys ih =>
    have hy := hl y (by simp)
    have hoy := ho y ys rfl
    obtain ⟨hys,hcon⟩ := hc
    have hcon : Consec (y.s+y.tot) (segsOf ys) := by simpa only [←hys,segsOf] using hcon
    cases ys with
    | nil =>
      simp only [segsOf,List.map_cons,List.map_nil,segEnd,List.sum_cons,List.sum_nil,Nat.add_zero]
      simpa only [hoy] using hy.last_body_end hL
    | cons z zs =>
      have hz := hl z (by simp)
      have hnz : z.s=y.s+y.tot := hcon.1
      have hnxt := hy.next_body_offset hL hz hnz
      have htail := ih (y.s+y.tot) (tr.cell tt y.s o2+(rfLen (rcptOf tr tt y) : Fp))
        (by simp) hcon (by intro w hw; exact hl w (by simp [hw]))
        (by intro w ws he; cases he; exact hnxt)
      change tr.cell tt (segEnd (y.s+y.tot) (segsOf (z::zs))-1) o2End=_
      rw [htail,hoy]
      simp only [List.map_cons,List.sum_cons,natCast_add]
      grind


/-- Total enabled refund bytes belonging to an extracted list. -/
def ListBlock.refundBytes (tr : Trace Fp) (tt : Nat) (B : ListBlock) : Nat :=
  (B.receipts.map fun y => rfLen (rcptOf tr tt y)).sum

/-- Terminal body position includes precisely this list's extracted refunds. -/
theorem ListBlockWf.body_end {B : ListBlock} (h : ListBlockWf tr tt B) :
    tr.cell tt (B.stop-1) o2End=tr.cell tt B.start o2+((B.refundBytes tr tt : Nat) : Fp) := by
  cases he : B.receipts with
  | nil =>
    have hs : B.stop-1=B.start+11 := by simp [ListBlock.stop,he,segsOf,segEnd]
    have hfin := h.header_fin
    have hh := (hdrRow hL (r := B.start+11) (by omega) (h.header.st 11 (by omega))).2.2.1
    rw [(h.header_counters hL 11 (by omega)).2] at hh
    rw [hs,hh]
    simp only [ListBlock.refundBytes,he,List.map_nil,List.sum_nil]
    grind
  | cons y ys =>
    have hc := h.consecutive
    rw [he] at hc
    have hy := h.layouts y (by simp [he])
    have ho := (h.first_counters hL hy hc.1).2
    have hh := receipt_sequence_body_end hL (y::ys) (B.start+12) (tr.cell tt B.start o2)
      (by simp) hc (by simpa only [he] using h.layouts) (by intro z zs hz; cases hz; exact ho)
    simpa only [ListBlock.stop,ListBlock.refundBytes,he] using hh

/-- The following list header inherits the exact completed refund-body position. -/
theorem ListBlockWf.next_body_offset {B C : ListBlock} (h : ListBlockWf tr tt B)
    (hc : ListBlockWf tr tt C) (hs : C.start=B.stop) :
    tr.cell tt C.start o2=tr.cell tt B.start o2+((B.refundBytes tr tt : Nat) : Fp) := by
  have hp := h.bound
  have he : B.stop-1+1=C.start := by omega
  have ha := hc.header.act 0 (by decide)
  have hh := (brkStep hL (r := B.stop-1) (by omega) (h.terminal_break hL)
    (by simpa only [Nat.add_zero,he] using ha)).2.2
  rw [he,h.body_end hL] at hh
  exact hh

end ZkFormal.NearV3.RcptV3Proof
