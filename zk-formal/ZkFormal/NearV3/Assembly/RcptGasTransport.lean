import ZkFormal.NearV3.Assembly.RcptRegGates

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem gasToken_transport (tr pair : Trace Fp) (t pos pt pp : Nat) (pub : List Fp)
    (hc : ∀c,tr.cell t pos c=pair.cell pt pp c)
    (hn : ∀j,j<16→tr.cell t ((pos+1)%tr.height t) (tok j)=
      pair.cell pt ((pp+1)%pair.height pt) (tok j))
    (hl : ∀e∈gasTokenConstraints,e.eval pair pt pp pub=0) :
    ∀e∈gasTokenConstraints,e.eval tr t pos pub=0 := by
  intro e he
  have hh := hl e he
  simp only [gasTokenConstraints,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with he|rfl
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
    have hj' := List.mem_range.mp hj
    simp only [eval_mul,eval_sub,eval_c,eval_n] at hh ⊢
    rw [hc,hc,hn j (by omega)]
    exact hh
  · simp only [eval_mul,eval_sub,eval_c,eval_n] at hh ⊢
    rw [hc,hn 15 (by decide),currentExpr_eval tr pair t pos pt pp pub hc (bitsX 31 8) (by decide)]
    exact hh

theorem GP_segment_last (p : ReceiptPlan) (a : PlannedRow)
    (ha : (SegmentPlan.receipt p sGP).rows.getLast?=some a) :
    a=.receipt p ⟨sGP,15,16⟩ := by
  obtain ⟨row,hs,hl,hi,he⟩ := (SegmentPlan.receipt p sGP).last a ha
  have hlen : (SegmentPlan.receipt p sGP).length=16 := rfl
  have hr : row=⟨sGP,15,16⟩ := by
    cases row with
    | mk state index len =>
      change state=sGP at hs
      dsimp only at hl hi
      rw [hlen] at hl hi
      have hindex : index=15 := by omega
      simp_all
  simpa only [hr,SegmentPlan.wrap] using he

/-- Target segment starts at the exact new native total after GP, regardless
of its row annotation. -/
theorem GP_boundary_next_tokens (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (q : SegmentPlan) (hpq : Neighbors (plannedSegments lists) (.receipt p sGP) q)
    (b : PlannedRow) (hb : q.rows.head?=some b) (j : Nat) (hj : j<16) :
    nativePlannedCell own ctx lists constants pub digests fallback headerFallback b (tok j)=
      Fp.ofNat (((receiptPlanToken ctx lists p).newBytes.getD j 0).toNat) := by
  obtain ⟨hp,hq⟩ := List.of_mem_zip hpq
  have hq' := List.mem_of_mem_drop hq
  rw [q.head b hb,segment_first_token_cell _ _ _ _ _ _ _ _ q hq' j hj,
    ←plannedSegments_neighbor_indices lists _ q hpq]
  have hend : (SegmentPlan.receipt p sGP).endIndex=p.receiptIndex+1 := by
    simp [SegmentPlan.endIndex]
  rw [hend,receiptPlanToken_new ctx lists p sGP hp]

end ZkFormal.NearV3.Assembly.RcptSkeleton
