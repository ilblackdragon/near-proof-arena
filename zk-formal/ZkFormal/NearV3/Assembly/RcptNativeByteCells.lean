import ZkFormal.NearV3.Assembly.RcptNativeFieldPositions
import ZkFormal.NearV3.Assembly.RcptEntityFlags

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

/-- Every concrete planned receipt has a contiguous block in the full physical
plan. This includes all preceding list headers, even headers for empty lists. -/
theorem receipt_block_exists (lists : List (List Input)) (p : ReceiptPlan)
    (hp : EntityPlan.receipt p∈entityPlans lists) :
    ∃pre post : List PlannedRow, plannedRows lists=pre++plannedReceiptRows p++post := by
  obtain ⟨a,b,h⟩ := List.mem_iff_append.mp hp
  refine ⟨a.flatMap EntityPlan.rows,b.flatMap EntityPlan.rows,?_⟩
  rw [←entityPlans_rows,h]
  simp only [List.flatMap_append,List.flatMap_cons,EntityPlan.rows,List.append_assoc]

/-- Locate a receipt field in the actual full row list, including preceding
list headers and empty lists. The decomposition retains its physical offset. -/
theorem receipt_block_lookup (lists : List (List Input)) (p : ReceiptPlan)
    (pre post : List PlannedRow) (h : plannedRows lists=pre++plannedReceiptRows p++post)
    (i : Nat) (a : PlannedRow) (hi : (plannedReceiptRows p)[i]?=some a) :
    (plannedRows lists)[pre.length+i]?=some a := by
  have hn : i<(plannedReceiptRows p).length := List.getElem?_eq_some_iff.mp hi |>.1
  rw [h,List.append_assoc,List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hn]
  exact hi

theorem native_rid_cell (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos i : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan)
    (ha : (plannedRows lists)[pos]?=some (.receipt p ⟨sRID,i,32⟩)) :
    (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos b=
      Fp.ofNat ((p.input.receipt.receiptId.getD i 0).toNat) := by
  rw [booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests fallback headerFallback _ ha b (by decide)]
  rfl

theorem native_peoh_cell (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos i : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan)
    (ha : (plannedRows lists)[pos]?=some (.receipt p ⟨sXLH,i,32⟩)) :
    (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos b=
      (digests p sXLH).getD i 0 := by
  rw [booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests fallback headerFallback _ ha b (by decide)]
  rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
