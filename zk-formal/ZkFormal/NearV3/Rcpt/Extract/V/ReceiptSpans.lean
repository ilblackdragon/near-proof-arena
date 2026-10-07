import ZkFormal.NearV3.Rcpt.Extract.V.TableWellformed

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- List traffic whose header is silent decomposes exactly into physical receipt
intervals, without assuming any semantic bus contract. -/
theorem ListBlockWf.receipt_spans {tr : Trace Fp} {tt : Nat} {B : ListBlock}
    (h : ListBlockWf tr tt B) {α : Type} (f : Nat→List α)
    (hh : (List.range' B.start 12).flatMap f=[]) :
    (List.range' B.start B.rows).flatMap f=
      B.receipts.flatMap (fun y => (List.range' y.s y.tot).flatMap f) := by
  have hs := range'_segs (segsOf B.receipts) (B.start+12) h.consecutive
  rw [receipt_end_sum B.receipts (B.start+12) h.consecutive,Nat.add_sub_cancel_left] at hs
  unfold ListBlock.rows
  rw [←List.range'_append_1,List.flatMap_append,hh,List.nil_append,hs]
  simp only [segsOf,List.flatMap_map,List.flatMap_assoc]

/-- Concatenating actual list intervals preserves every receipt message once. -/
theorem ListChain.receipt_spans {tr : Trace Fp} {tt s e : Nat} {bs : List ListBlock}
    (h : ListChain tr tt s bs e) {α : Type} (f : Nat→List α)
    (hh : ∀ B∈bs,(List.range' B.start 12).flatMap f=[]) :
    (List.range' s (e-s)).flatMap f=
      bs.flatMap (fun B => B.receipts.flatMap (fun y => (List.range' y.s y.tot).flatMap f)) := by
  induction h with
  | last hw _ =>
    rw [hw.stop_eq,Nat.add_sub_cancel_left,hw.receipt_spans f (hh _ (by simp))]
    simp
  | @cons B tail stop hw ht ih =>
    have hs := hw.stop_eq
    have htr := ht.rows
    have hn : stop-B.start=B.rows+(stop-B.stop) := by omega
    rw [hn,←List.range'_append_1,List.flatMap_append,show B.start+B.rows=B.stop from hs.symm]
    rw [hw.receipt_spans f (hh B (by simp)),ih (by intro C hC; exact hh C (by simp [hC]))]
    rfl

/-- Whole physical traffic equals the receipt intervals when both list headers
and actual padding are silent. Applies uniformly to remaining receipt buses. -/
theorem ListChain.receipt_spans_full {tr : Trace Fp} {pub : List Fp} {tt e : Nat} {bs : List ListBlock}
    (hL : TableLocal RcptV3.table tr tt pub) (h : ListChain tr tt 0 bs e)
    {α : Type} (f : Nat→List α)
    (hh : ∀ B∈bs,(List.range' B.start 12).flatMap f=[])
    (hp : ∀ q,q<tr.height tt → tr.cell tt q RcptV3.act=0 → f q=[]) :
    (List.range (tr.height tt)).flatMap f=
      bs.flatMap (fun B => B.receipts.flatMap (fun y => (List.range' y.s y.tot).flatMap f)) := by
  have he := h.end_padding.1
  have hz : (List.range' e (tr.height tt-e)).flatMap f=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro q hq
    obtain ⟨i,hi,hqi⟩ := List.mem_range'.mp hq
    simp only [Nat.one_mul] at hqi
    exact hp q (by omega) (h.padding hL (by omega) (by omega))
  rw [List.range_eq_range',range'_split e (tr.height tt) (by omega),List.flatMap_append,hz,List.append_nil]
  simpa only [Nat.sub_zero] using h.receipt_spans f hh

end ZkFormal.NearV3.RcptV3Proof
