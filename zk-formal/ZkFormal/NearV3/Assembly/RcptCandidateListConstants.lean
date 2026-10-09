import ZkFormal.NearV3.Assembly.RcptCandidateListGate
-- Source ListConstants.lean SHA256: 2b3e325c9379178fca3e16d2852a3b76c106e15110935bf74e302f43bbaaf767.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.ListGate

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

theorem receipt_sequence_active (xs : List RS) (s q : Nat)
    (hc : Consec s (segsOf xs))
    (hl : ∀ y∈xs, Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (hlo : s≤q) (hhi : q<segEnd s (segsOf xs)) : tr.cell tt q act=1 := by
  induction xs generalizing s with
  | nil => simp only [segsOf,List.map_nil,segEnd] at hhi; omega
  | cons y ys ih =>
    obtain ⟨hs,hcon⟩ := hc
    have hy := hl y (by simp)
    by_cases hh : q<y.s+y.tot
    · have hf := (Layout.row_flags hL hy (q-y.s) (by omega)).1
      simpa only [show y.s+(q-y.s)=q by omega] using hf
    · apply ih (y.s+y.tot)
      · simpa only [←hs,segsOf] using hcon
      · intro z hz; exact hl z (by simp [hz])
      · omega
      · exact hhi

theorem ListBlockWf.active {B : ListBlock} (h : ListBlockWf tr tt B)
    {q : Nat} (hlo : B.start≤q) (hhi : q<B.stop) : tr.cell tt q act=1 := by
  by_cases hh : q<B.start+12
  · have hf := h.header.act (q-B.start) (by omega)
    simpa only [show B.start+(q-B.start)=q by omega] using hf
  · exact receipt_sequence_active hL B.receipts (B.start+12) q h.consecutive h.layouts (by omega) hhi

/-- All list constants, including j and nj, equal the values at the actual header start. -/
theorem ListBlockWf.constants {B : ListBlock} (h : ListBlockWf tr tt B)
    (k : Nat) (hk : B.start+k<B.stop) (x : Nat) (hx : x∈lconsts) :
    tr.cell tt (B.start+k) x=tr.cell tt B.start x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp := h.bound.2
    have ha := ListBlockWf.active hL h (q := B.start+k) (by omega) (by omega)
    have he := ListBlockWf.le_gate hL h (q := B.start+k) (by omega) (by omega)
    rw [if_neg (by omega)] at he
    have hh := lconst hL (r := B.start+k) (by omega) ha he x hx
    rw [show B.start+k+1=B.start+(k+1) by omega] at hh
    exact hh.trans (ih (by omega))

/-- A following header increments j exactly once. -/
theorem ListBlockWf.next_index {B C : ListBlock} (h : ListBlockWf tr tt B)
    (hc : ListBlockWf tr tt C) (hs : C.start=B.stop) :
    tr.cell tt C.start j=tr.cell tt B.start j+1 := by
  have hp := h.bound
  have hh := leFacts hL (r := B.stop-1) (by omega) (ListBlockWf.terminal_le hL h)
  have ha := hc.header.act 0 (by decide)
  have he : B.stop-1+1=C.start := by omega
  have hn := hh.2 (by simpa only [Nat.add_zero,he] using ha)
  have hj := ListBlockWf.constants hL h (B.stop-1-B.start) (by omega) j (by simp [lconsts])
  rw [show B.start+(B.stop-1-B.start)=B.stop-1 by omega] at hj
  rw [he,hj] at hn
  exact hn

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
