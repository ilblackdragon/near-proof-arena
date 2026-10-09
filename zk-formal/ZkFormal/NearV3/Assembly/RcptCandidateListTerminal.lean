import ZkFormal.NearV3.Assembly.RcptCandidateEncodedOffsets
-- Source ListTerminal.lean SHA256: 5f2bbec2320d1381327c5a54aecde021610e36f53f134bb5b2a7944d1ade8d74.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.EncodedOffsets

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- A nonempty sequence ends at the end of one of its actual receipt intervals. -/
theorem receipt_sequence_last (xs : List RS) (s : Nat) (hn : xs≠[]) :
    ∃ y∈xs, segEnd s (segsOf xs)=y.s+y.tot := by
  induction xs generalizing s with
  | nil => exact False.elim (hn rfl)
  | cons y ys ih =>
    cases ys with
    | nil => exact ⟨y,by simp,rfl⟩
    | cons z zs =>
      obtain ⟨w,hw,he⟩ := ih (y.s+y.tot) (by simp)
      exact ⟨w,by simp [hw],he⟩

variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

theorem BlockEnd.rf_zero {e : Nat} (he : BlockEnd tr tt e) : tr.cell tt e rf=0 := by
  rcases isBool hL he.1 (x := rf) (by simp [boolCols]) with hz|ho
  · exact hz
  · have hs := (bounds hL he.1).2.1 ho
    have hhot := oneHot hL he.1 (by simp [states]) hs.1
    rcases he.2 with hp|⟨hc,_,_⟩
    · exact False.elim (fp_zero_ne_one (hp.symm.trans hhot.1))
    · have hzero := hhot.2 sCL (by simp [states]) (by decide)
      exact False.elim (fp_zero_ne_one (hzero.symm.trans hc))

/-- The final physical row of each extracted list is a real break row. -/
theorem ListBlockWf.terminal_break {B : ListBlock} (h : ListBlockWf tr tt B) :
    tr.cell tt (B.stop-1) rl+tr.cell tt (B.stop-1) sCL*tr.cell tt (B.stop-1) fe=1 := by
  by_cases he : B.receipts=[]
  · have hs : B.stop-1=B.start+11 := by simp [ListBlock.stop,he,segsOf,segEnd]
    rw [hs]
    exact (ListBlockWf.header_end hL h).2.2.2
  · obtain ⟨y,hy,hend⟩ := receipt_sequence_last B.receipts (B.start+12) he
    have hlay := h.layouts y hy
    have hnc := lay_last_ncl hL hlay
    change B.stop=y.s+y.tot at hend
    rw [hend]
    unfold RS.tot
    rw [hlay.endRl,hnc]
    grind

/-- Local constraints enable the list-end message on every extracted terminal row. -/
theorem ListBlockWf.terminal_le {B : ListBlock} (h : ListBlockWf tr tt B) :
    tr.cell tt (B.stop-1) le=1 := by
  have hb := h.bound
  have hp : B.stop-1+1=B.stop := by omega
  have hh := (le_eq hL (r := B.stop-1) (by omega)).1
  rw [hp,ListBlockWf.terminal_break hL h,BlockEnd.rf_zero hL h.boundary] at hh
  rw [hh]
  grind

/-- The actual terminal RCL send contains the nonwrapping extracted encoding length. -/
theorem ListBlockWf.terminal_rcl {B : ListBlock} (h : ListBlockWf tr tt B) :
    rowTraffic RcptV3.interactions tr tt (B.stop-1) pub B_RCL true=
      [[tr.cell tt (B.stop-1) j,
        ((lOffs (B.viewReceipts tr tt) (B.viewReceipts tr tt).length : Nat) : Fp)]] := by
  rw [rowT]
  simp [B_RCL,B_BYTES,B_DIGEST,B_KEYNIB,B_FINAL,B_MEM,B_RIDS,B_MPOS,B_SREC,B_AKC,B_BND,
    B_SIZE,
    List.nil_append,List.append_nil,C,gt,ListBlockWf.terminal_le hL h,ListBlockWf.encoded_end hL h]

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
