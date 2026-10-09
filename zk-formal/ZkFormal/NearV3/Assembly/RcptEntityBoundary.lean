import ZkFormal.NearV3.Assembly.RcptEntityPlan

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3

theorem planReceipts_last_totals (xs : List Input) (j nj r cj o o2 : Nat) (ll : Bool)
    (p : ReceiptPlan) (hp : (planReceipts j nj r cj o o2 ll xs).getLast?=some p) :
    p.listIndex=j ∧ p.listCount=nj ∧ p.receiptIndex+1=r+xs.length ∧
    p.withinList+1=cj+xs.length ∧ p.bodyOffset+refundLength p.input=o2+(xs.map refundLength).sum ∧
    p.lastInList=true ∧ p.lastList=ll := by
  induction xs generalizing r cj o o2 p with
  | nil => simp [planReceipts] at hp
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp only [planReceipts,List.getLast?_singleton,Option.some.injEq] at hp
      subst p
      simp
    | cons y ys =>
      rw [planReceipts,List.getLast?_cons_of_ne_nil (by simp [planReceipts])] at hp
      have hh := ih (r+1) (cj+1) (o+rcLength x) (o2+refundLength x) p hp
      simp only [List.length_cons,List.map_cons,List.sum_cons] at hh ⊢
      obtain ⟨hj,hn,hr,hcj,hbody,hlast,hll⟩ := hh
      exact ⟨hj,hn,by omega,by omega,by omega,hlast,hll⟩

theorem listEntities_last_totals (p : ListPlan) (a : EntityPlan)
    (ha : (listEntities p).getLast?=some a) :
    a.listIndex=p.listIndex ∧ a.listCount=p.inputs.length ∧
    a.receiptIndex+(if a.isHeader then 0 else 1)=p.receiptIndex+p.inputs.length ∧
    a.withinList=p.inputs.length ∧ a.bodyEnd=p.bodyOffset+(p.inputs.map refundLength).sum ∧
    a.lastInList=true ∧ a.lastList=p.lastList := by
  by_cases hx : p.inputs=[]
  · simp only [listEntities,hx,planReceipts,List.map_nil,List.getLast?_singleton,Option.some.injEq] at ha
    subst a
    simp [EntityPlan.listIndex,EntityPlan.listCount,EntityPlan.receiptIndex,EntityPlan.withinList,
      EntityPlan.bodyEnd,EntityPlan.lastInList,EntityPlan.lastList,EntityPlan.isHeader,hx]
  · have hn : planReceipts p.listIndex p.inputs.length p.receiptIndex 1 12 p.bodyOffset p.lastList p.inputs≠[] := by
      cases hp : p.inputs with
      | nil => exact False.elim (hx hp)
      | cons => simp [planReceipts]
    rw [listEntities,List.getLast?_cons_of_ne_nil (by simpa using hn),List.getLast?_map] at ha
    obtain ⟨rp,hr,he⟩ := Option.map_eq_some_iff.mp ha
    subst a
    obtain ⟨hj,hn,hr,hcj,hbody,hlast,hll⟩ := planReceipts_last_totals p.inputs _ _ _ _ _ _ _ rp hr
    exact ⟨hj,hn,hr,by change rp.withinList=p.inputs.length;omega,hbody,hlast,hll⟩

theorem listEntities_first (p : ListPlan) : (listEntities p).head?=some (.header p) := rfl

theorem planLists_entity_boundaries (lists : List (List Input)) (j r o2 : Nat) (p q : ListPlan)
    (hpq : Neighbors (planLists j r o2 lists) p q)
    (a : EntityPlan) (ha : (listEntities p).getLast?=some a) :
    EntityBoundary a (.header q) := by
  induction lists generalizing j r o2 p q with
  | nil => simp [Neighbors,planLists] at hpq
  | cons xs lists ih =>
    rw [planLists,neighbors_cons] at hpq
    rcases hpq with ⟨hp,hq⟩|hpq
    · cases lists with
      | nil => simp [planLists] at hq
      | cons ys rest =>
        simp only [planLists,List.head?_cons,Option.some.injEq] at hq
        subst p q
        obtain ⟨hj,hn,hr,hcj,hbody,hlast,hll⟩ := listEntities_last_totals _ a ha
        simp only [EntityBoundary,EntityPlan.listIndex,EntityPlan.receiptIndex,EntityPlan.bodyStart,
          EntityPlan.isHeader,EntityPlan.withinList,EntityPlan.rcStart,EntityPlan.listCount,hlast,Bool.true_and,
          ite_true,Bool.false_eq_true,Bool.true_eq_false,false_implies,true_and]
        exact ⟨congrArg (fun n=>n+1) hj.symm,hr.symm,hbody.symm,hll,True.intro⟩
    · exact ih _ _ _ p q hpq ha

theorem entityPlans_boundaries (lists : List (List Input)) (a b : EntityPlan)
    (hab : Neighbors (entityPlans lists) a b) : EntityBoundary a b := by
  rcases neighbors_flatMap_nonempty listEntities (planLists 0 0 8 lists) a b
      (fun p _=>by simp [listEntities]) hab with ⟨p,_,hh⟩|⟨p,q,hpq,hp,hq⟩
  · exact listEntities_neighbors p a b hh
  · rw [listEntities_first,Option.some.injEq] at hq
    subst b
    exact planLists_entity_boundaries lists 0 0 8 p q hpq a hp

end ZkFormal.NearV3.Assembly.RcptSkeleton
