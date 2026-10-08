import ZkFormal.NearV3.Assembly.RcptNativeLeaf

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3

def EntityPlan.input? : EntityPlan→Option Input
  | .header _=>none
  | .receipt p=>some p.input

theorem listEntities_inputs (p : ListPlan) :
    (listEntities p).filterMap EntityPlan.input?=p.inputs := by
  simp only [listEntities,List.filterMap_cons,EntityPlan.input?,List.filterMap_map,Function.comp_def,EntityPlan.input?,List.filterMap_eq_map']
  exact planReceipts_inputs _ _ _ _ _ _ _ _

theorem planLists_flat_inputs (lists : List (List Input)) (j r o : Nat) :
    (planLists j r o lists).flatMap ListPlan.inputs=lists.flatten := by
  induction lists generalizing j r o with
  | nil => rfl
  | cons xs lists ih => simp only [planLists,List.flatMap_cons,ih,List.flatten_cons]

/-- Filtering only header entities preserves all native receipts in exact order,
including repeated entries, system receipts, and empty source lists. -/
theorem entityPlans_inputs (lists : List (List Input)) :
    (entityPlans lists).filterMap EntityPlan.input?=lists.flatten := by
  simp only [entityPlans,List.filterMap_flatMap,listEntities_inputs]
  exact planLists_flat_inputs lists 0 0 8

theorem planned_outcomes (prims : Prims) (ctx : ApplyCtx) (t : PTrie)
    (lists : List (List Input)) (out : MainOut)
    (h : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out) :
    out.outcomes=((entityPlans lists).filterMap EntityPlan.input?).map
      (fun x=>nativeOutcome ctx x.receipt) := by
  rw [entityPlans_inputs]
  rw [applyNewChunk_outcomes prims h,List.map_map]
  rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
