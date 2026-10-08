import ZkFormal.NearV3.Assembly.RcptNativeLocations
namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3
private def receiptIndex? : EntityPlan→Option Nat
  | .header _=>none
  | .receipt p=>some p.receiptIndex
private theorem location_indices (es : List EntityPlan) (start : Nat) :
    (receiptLocations start es).map (fun x=>x.2.receiptIndex)=es.filterMap receiptIndex? := by
  induction es generalizing start with
  | nil=>rfl
  | cons e es ih=>cases e <;> simp only [receiptLocations,List.map_cons,List.filterMap_cons,receiptIndex?,ih]
private theorem plan_indices (xs : List Input) (j nj r cj o o2 : Nat) (ll : Bool) :
    (planReceipts j nj r cj o o2 ll xs).map ReceiptPlan.receiptIndex=List.range' r xs.length := by
  induction xs generalizing r cj o o2 with
  | nil=>simp [planReceipts]
  | cons x xs ih=>simp [planReceipts,ih,List.range'_succ]
private theorem lists_indices (lists : List (List Input)) (j r o : Nat) :
    ((planLists j r o lists).flatMap listEntities).filterMap receiptIndex?=List.range' r lists.flatten.length := by
  induction lists generalizing j r o with
  | nil=>simp [planLists]
  | cons xs lists ih=>
    simp only [planLists,List.flatMap_cons,List.filterMap_append,ih,listEntities,
      List.filterMap_cons,receiptIndex?,List.filterMap_map,Option.bind_some,Option.bind_none]
    have hm:(List.filterMap (fun p=>receiptIndex? (EntityPlan.receipt p))
      (planReceipts j xs.length r 1 12 o lists.isEmpty xs))=
      List.range' r xs.length:=by
      simpa [receiptIndex?,List.filterMap_eq_map] using plan_indices xs j xs.length r 1 12 o lists.isEmpty
    simp only [Function.comp_def]
    rw [hm]
    simpa only [List.flatten_cons,List.length_append,Nat.one_mul] using
      (List.range'_append (s:=r) (m:=xs.length) (n:=lists.flatten.length) (step:=1))
/-- Physical receipt locations preserve every global receipt index in order,
including repeated and empty source lists. -/
theorem native_locations_indices (lists : List (List Input)) :
    (receiptLocations 0 (entityPlans lists)).map (fun x=>x.2.receiptIndex)=List.range lists.flatten.length := by
  rw [location_indices]
  simpa [entityPlans,List.range_eq_range'] using lists_indices lists 0 0 8

/-- Aggregation keeps one packet group per receipt occurrence, in native order. -/
theorem native_locations_flatMap {α : Type} (lists : List (List Input))
    (f : Nat×ReceiptPlan→List α) (g : Nat→List α)
    (h:∀x∈receiptLocations 0 (entityPlans lists),f x=g x.2.receiptIndex) :
    (receiptLocations 0 (entityPlans lists)).flatMap f=
      (List.range lists.flatten.length).flatMap g := by
  rw [←native_locations_indices lists,List.flatMap_map]
  exact congrArg List.flatten (List.map_congr_left h)
end ZkFormal.NearV3.Assembly.RcptSkeleton
