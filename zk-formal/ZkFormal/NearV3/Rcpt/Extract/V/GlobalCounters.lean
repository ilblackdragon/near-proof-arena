import ZkFormal.NearV3.Rcpt.Extract.V.ListCounts

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Global receipt and body counters are constant through a list header. -/
theorem ListBlockWf.header_counters {B : ListBlock} (h : ListBlockWf tr tt B)
    (k : Nat) (hk : k<12) :
    tr.cell tt (B.start+k) RcptV3.r=tr.cell tt B.start RcptV3.r ∧
    tr.cell tt (B.start+k) o2=tr.cell tt B.start o2 := by
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    have hfin := h.header_fin
    have he : tr.cell tt (B.start+k) fe=0 := by
      rw [h.header.fe k (by omega),if_neg (by omega)]
    have hh := hdrCarry hL (r := B.start+k) (by omega) (h.header.st k (by omega)) he
    have hi := ih (by omega)
    simpa only [Nat.add_assoc] using And.intro (hh.1.trans hi.1) (hh.2.trans hi.2)

/-- The first receipt inherits the global counters from its own list header. -/
theorem ListBlockWf.first_counters {B : ListBlock} (h : ListBlockWf tr tt B)
    {y : RS} (hy : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) (hs : y.s=B.start+12) :
    tr.cell tt y.s RcptV3.r=tr.cell tt B.start RcptV3.r ∧
    tr.cell tt y.s o2=tr.cell tt B.start o2 := by
  have hh := h.header_end hL
  have hfin := h.header_fin
  have hf := hy.start_flags hL
  have he : B.start+11+1=y.s := by omega
  have ht := brkStep hL (r := B.start+11) (by omega) hh.2.2.2 (by simpa only [he] using hf.1)
  have hc := h.header_counters hL 11 (by omega)
  have hdr := hdrRow hL (r := B.start+11) (by omega) (h.header.st 11 (by omega))
  rw [he,hh.2.2.1,hdr.2.2.1,hc.1,hc.2] at ht
  exact ⟨by have := ht.1; grind,ht.2.2⟩

/-- The global receipt counter increments across every receipt boundary. -/
theorem Layout.next_receipt_counter {y z : RS}
    (hy : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (hz : Layout tr tt z.s z.h z.Lp z.Lv z.Ls z.kt)
    (hs : z.s=y.s+y.tot) : tr.cell tt z.s RcptV3.r=tr.cell tt y.s RcptV3.r+1 := by
  have hp := total_pos y.h y.Lp y.Lv y.Ls y.kt
  have hfin := hy.fin
  have he : y.s+y.tot-1+1=z.s := by unfold RS.tot at *; omega
  have ht := brkStep hL (r := y.s+y.tot-1) (by unfold RS.tot; omega)
    (by unfold RS.tot; rw [hy.endRl,lay_last_ncl hL hy]; grind)
    (by simpa only [he] using (hz.start_flags hL).1)
  have hh := ht.1
  rw [he] at hh
  unfold RS.tot at hh
  rw [hy.endRl,(lay_last hL hy).2 RcptV3.r rC] at hh
  exact hh

/-- Global receipt numbering follows the natural position within a consecutive receipt sequence. -/
theorem receipt_sequence_indices (xs : List RS) (s : Nat) (off : Fp)
    (hc : Consec s (segsOf xs))
    (hl : ∀ y∈xs, Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (ho : ∀ y ys, xs=y::ys → tr.cell tt y.s RcptV3.r=off) :
    ∀ k (hk : k<xs.length), tr.cell tt xs[k].s RcptV3.r=off+(k : Fp) := by
  induction xs generalizing s off with
  | nil => intro k hk; simp at hk
  | cons y ys ih =>
    intro k hk
    have hy := hl y (by simp)
    have hoy := ho y ys rfl
    obtain ⟨hs,hcon⟩ := hc
    have hcon : Consec (y.s+y.tot) (segsOf ys) := by simpa only [←hs,segsOf] using hcon
    cases k with
    | zero => simp only [List.getElem_cons_zero]; rw [hoy]; grind
    | succ k =>
      have hh := ih (y.s+y.tot) (tr.cell tt y.s RcptV3.r+1) hcon
        (by intro z hz; exact hl z (by simp [hz]))
        (by
          intro z zs he
          have hz := hl z (by simp [he])
          have hc := hcon
          rw [he] at hc
          exact hy.next_receipt_counter hL hz hc.1) k (by simpa using hk)
      simp only [List.getElem_cons_succ]
      rw [hh,hoy,natCast_add]
      grind

/-- Actual global receipt counters inside an extracted list start at its header counter. -/
theorem ListBlockWf.receipt_indices {B : ListBlock} (h : ListBlockWf tr tt B) :
    ∀ k (hk : k<B.receipts.length),
      tr.cell tt B.receipts[k].s RcptV3.r=tr.cell tt B.start RcptV3.r+(k : Fp) := by
  apply receipt_sequence_indices hL B.receipts (B.start+12) _ h.consecutive h.layouts
  intro y ys he
  have hc := h.consecutive
  rw [he] at hc
  have hy := h.layouts y (by simp [he])
  exact (h.first_counters hL hy hc.1).1

/-- Final global receipt index of a consecutive nonempty sequence. -/
theorem receipt_sequence_last_index (xs : List RS) (s : Nat) (off : Fp)
    (hn : xs≠[]) (hc : Consec s (segsOf xs))
    (hl : ∀ y∈xs, Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (ho : ∀ y ys, xs=y::ys → tr.cell tt y.s RcptV3.r=off) :
    tr.cell tt (segEnd s (segsOf xs)-1) RcptV3.r=off+((xs.length-1 : Nat) : Fp) := by
  induction xs generalizing s off with
  | nil => exact False.elim (hn rfl)
  | cons y ys ih =>
    have hy := hl y (by simp)
    have hoy := ho y ys rfl
    obtain ⟨hs,hcon⟩ := hc
    have hcon : Consec (y.s+y.tot) (segsOf ys) := by simpa only [←hs,segsOf] using hcon
    cases ys with
    | nil =>
      have hh := (lay_last hL hy).2 RcptV3.r rC
      simp only [segsOf,List.map_cons,List.map_nil,segEnd,List.length_cons,List.length_nil]
      unfold RS.tot
      rw [hh,hoy]
      grind
    | cons z zs =>
      have hz := hl z (by simp)
      have hnxt := hy.next_receipt_counter hL hz hcon.1
      have hh := ih (y.s+y.tot) (tr.cell tt y.s RcptV3.r+1) (by simp) hcon
        (by intro w hw; exact hl w (by simp [hw])) (by intro w ws he; cases he; exact hnxt)
      change tr.cell tt (segEnd (y.s+y.tot) (segsOf (z::zs))-1) RcptV3.r=_
      rw [hh,hoy]
      simp only [List.length_cons,Nat.add_sub_cancel,natCast_add]
      grind


end ZkFormal.NearV3.RcptV3Proof
