import ZkFormal.NearV3.Assembly.RcptCandidateHeaderOffsets
-- Source EncodedOffsets.lean SHA256: 9028973b2938fed0c4be23f9941da4bc7629f4524ecfb069798de5741c80f4b6.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.HeaderOffsets

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Exact telescoping of emitted offsets over consecutive receipt layouts. -/
theorem receipt_sequence_encoded_end (xs : List RS) (s : Nat) (off : Fp)
    (hn : xs≠[]) (hc : Consec s (segsOf xs))
    (hl : ∀ y∈xs, Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (ho : ∀ y ys, xs=y::ys → tr.cell tt y.s o=off) :
    tr.cell tt (segEnd s (segsOf xs)-1) oEnd=
      off+(((xs.map fun y => (rcptOf tr tt y).enc.length).sum : Nat) : Fp) := by
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
      simpa only [hoy] using Layout.last_encoded_end hL hy
    | cons z zs =>
      have hz := hl z (by simp)
      have hnz : z.s=y.s+y.tot := hcon.1
      have hnxt := Layout.next_offset hL hy hz hnz
      have htail := ih (y.s+y.tot) (tr.cell tt y.s o+((rcptOf tr tt y).enc.length : Fp))
        (by simp) hcon (by intro w hw; exact hl w (by simp [hw]))
        (by intro w ws he; cases he; exact hnxt)
      change tr.cell tt (segEnd (y.s+y.tot) (segsOf (z::zs))-1) oEnd=_
      rw [htail,hoy]
      simp only [List.map_cons,List.sum_cons,natCast_add]
      grind

/-- The terminal end-offset cell is the exact encoding length of the extracted list. -/
theorem ListBlockWf.encoded_end {B : ListBlock} (h : ListBlockWf tr tt B) :
    tr.cell tt (B.stop-1) oEnd=
      ((lOffs (B.viewReceipts tr tt) (B.viewReceipts tr tt).length : Nat) : Fp) := by
  have h12 : ((12 : Nat) : Fp)=(12 : Fp) := by decide
  cases he : B.receipts with
  | nil => simpa only [lOffs,ListBlock.viewReceipts,he,List.map_nil,List.length_nil,
      List.take_zero,List.sum_nil,Nat.add_zero,h12] using ListBlockWf.empty_end hL h he
  | cons y ys =>
    have hc := h.consecutive
    rw [he] at hc
    have hs : y.s=B.start+12 := hc.1
    have hy := h.layouts y (by simp [he])
    have ho := (ListBlockWf.first_offset hL h hy hs).1
    have hh := receipt_sequence_encoded_end hL (y::ys) (B.start+12) (12 : Fp)
      (by simp) hc (by simpa only [he] using h.layouts)
      (by intro z zs hz; cases hz; exact ho)
    simpa only [ListBlock.stop,ListBlock.viewReceipts,lOffs,List.take_length,List.map_map,
      Function.comp_def,he,natCast_add,h12] using hh

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
