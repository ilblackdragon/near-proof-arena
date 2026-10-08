import ZkFormal.NearV3.Assembly.RcptSkeletonEncoding

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3

theorem receipt_indices (xs : List Input) (j nj r cj o o2 : Nat) (ll : Bool) :
    (planReceipts j nj r cj o o2 ll xs).map ReceiptPlan.receiptIndex=List.range' r xs.length := by
  induction xs generalizing r cj o o2 with
  | nil => rfl
  | cons x xs ih => simp only [planReceipts,List.map_cons,ih,List.length_cons,List.range'_succ]

theorem within_list_indices (xs : List Input) (j nj r cj o o2 : Nat) (ll : Bool) :
    (planReceipts j nj r cj o o2 ll xs).map ReceiptPlan.withinList=List.range' cj xs.length := by
  induction xs generalizing r cj o o2 with
  | nil => rfl
  | cons x xs ih => simp only [planReceipts,List.map_cons,ih,List.length_cons,List.range'_succ]

theorem list_indices (lists : List (List Input)) (j r o2 : Nat) :
    (planLists j r o2 lists).map ListPlan.listIndex=List.range' j lists.length := by
  induction lists generalizing j r o2 with
  | nil => rfl
  | cons xs lists ih => simp only [planLists,List.map_cons,ih,List.length_cons,List.range'_succ]

theorem receipt_list_constants (xs : List Input) (j nj r cj o o2 : Nat) (ll : Bool)
    {plan : ReceiptPlan} (hp : plan∈planReceipts j nj r cj o o2 ll xs) :
    plan.listIndex=j ∧ plan.listCount=nj ∧ plan.lastList=ll := by
  induction xs generalizing r cj o o2 with
  | nil => cases hp
  | cons x xs ih =>
    simp only [planReceipts,List.mem_cons] at hp
    rcases hp with rfl|hp
    · exact ⟨rfl,rfl,rfl⟩
    · exact ih _ _ _ _ hp

/-- The generated annotated trace retains each source list exactly once and
keeps its order; in particular no empty or repeated list is discarded. -/
theorem planLists_inputs (lists : List (List Input)) (j r o2 : Nat) :
    (planLists j r o2 lists).map ListPlan.inputs=lists := by
  induction lists generalizing j r o2 with
  | nil => rfl
  | cons xs lists ih => simp only [planLists,List.map_cons,ih]

end ZkFormal.NearV3.Assembly.RcptSkeleton
