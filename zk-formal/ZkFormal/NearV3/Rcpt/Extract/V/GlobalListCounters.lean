import ZkFormal.NearV3.Rcpt.Extract.V.GlobalCounters

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- At a list end, r+rl counts every receipt in the list exactly once. -/
theorem ListBlockWf.terminal_global_count {B : ListBlock} (h : ListBlockWf tr tt B) :
    tr.cell tt (B.stop-1) RcptV3.r+tr.cell tt (B.stop-1) rl=
      tr.cell tt B.start RcptV3.r+(B.receipts.length : Fp) := by
  cases he : B.receipts with
  | nil =>
    have hs : B.stop-1=B.start+11 := by simp [ListBlock.stop,he,segsOf,segEnd]
    rw [hs,(h.header_end hL).2.2.1,(h.header_counters hL 11 (by omega)).1,List.length_nil]
    rfl
  | cons y ys =>
    have hc := h.consecutive
    rw [he] at hc
    have hy := h.layouts y (by simp [he])
    have ho := (h.first_counters hL hy hc.1).1
    have hh := receipt_sequence_last_index hL (y::ys) (B.start+12) (tr.cell tt B.start RcptV3.r)
      (by simp) hc (by simpa only [he] using h.layouts) (by intro z zs hz; cases hz; exact ho)
    have hrl : tr.cell tt (B.stop-1) rl=1 := by
      obtain ⟨z,hz,hend⟩ := receipt_sequence_last B.receipts (B.start+12) (by simp [he])
      change B.stop=z.s+z.tot at hend
      rw [hend]
      exact (h.layouts z hz).endRl
    rw [hrl]
    change tr.cell tt (segEnd (B.start+12) (segsOf B.receipts)-1) RcptV3.r+_= _
    rw [he,hh]
    simp only [List.length_cons,Nat.add_sub_cancel,natCast_add]
    grind

/-- A following list header inherits the total global count of the preceding list. -/
theorem ListBlockWf.next_global_count {B C : ListBlock} (h : ListBlockWf tr tt B)
    (hc : ListBlockWf tr tt C) (hs : C.start=B.stop) :
    tr.cell tt C.start RcptV3.r=tr.cell tt B.start RcptV3.r+(B.receipts.length : Fp) := by
  have hp := h.bound
  have he : B.stop-1+1=C.start := by omega
  have ha := hc.header.act 0 (by decide)
  have hh := (brkStep hL (r := B.stop-1) (by omega) (h.terminal_break hL)
    (by simpa only [Nat.add_zero,he] using ha)).1
  rw [he,h.terminal_global_count hL] at hh
  exact hh

/-- Global receipt counters at list headers equal the exact preceding receipt count. -/
theorem ListChain.global_counts {s e : Nat} {bs : List ListBlock} (h : ListChain tr tt s bs e) :
    ∀ k (hk : k<bs.length), tr.cell tt bs[k].start RcptV3.r=
      tr.cell tt s RcptV3.r+((((bs.take k).map fun B => B.receipts.length).sum : Nat) : Fp) := by
  induction h with
  | last hw _ =>
    intro k hk
    have hz : k=0 := by simp only [List.length_singleton] at hk; omega
    subst k
    simp only [List.getElem_cons_zero,List.take_zero,List.map_nil,List.sum_nil]
    grind
  | @cons B tail stop hw ht ih =>
    intro k hk
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero,List.take_zero,List.map_nil,List.sum_nil]
      grind
    | succ k =>
      obtain ⟨C,hs,hc⟩ := ht.first_wf
      have hn := hw.next_global_count hL hc hs
      rw [hs] at hn
      have hh := ih k (by simpa using hk)
      simp only [List.getElem_cons_succ,List.take_succ_cons,List.map_cons,List.sum_cons,natCast_add]
      rw [hh,hn]
      grind

/-- Row-zero global counters are natural prefix counts without an arbitrary offset. -/
theorem ListChain.zero_global_counts {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    ∀ k (hk : k<bs.length), tr.cell tt bs[k].start RcptV3.r=
      ((((bs.take k).map fun B => B.receipts.length).sum : Nat) : Fp) := by
  intro k hk
  have hh := h.global_counts hL k hk
  have hp := height_ge hL
  rw [(first0 hL (by omega)).2.1] at hh
  grind

end ZkFormal.NearV3.RcptV3Proof
