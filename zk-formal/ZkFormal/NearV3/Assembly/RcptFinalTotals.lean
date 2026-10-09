import ZkFormal.NearV3.Assembly.RcptNativeDigestCheckpoint

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3

/-- Exact final plan totals, including a terminal empty source list. -/
theorem planLists_last_totals (lists : List (List Input)) (j r o2 : Nat) (p : ListPlan)
    (h : (planLists j r o2 lists).getLast?=some p) :
    p.receiptIndex+p.inputs.length=r+lists.flatten.length ∧
    p.bodyOffset+(p.inputs.map refundLength).sum=o2+(lists.flatten.map refundLength).sum := by
  induction lists generalizing j r o2 with
  | nil => simp [planLists] at h
  | cons xs lists ih =>
    cases lists with
    | nil =>
      simp only [planLists,List.getLast?_singleton,Option.some.injEq] at h
      cases h
      simp
    | cons ys rest =>
      have hh := ih (j+1) (r+xs.length) (o2+(xs.map refundLength).sum)
        (by simpa only [planLists,List.getLast?_cons_cons] using h)
      simp only [List.flatten_cons,List.length_append,List.map_append,List.sum_append] at hh ⊢
      omega

theorem entityPlans_final_totals (lists : List (List Input)) (a : EntityPlan)
    (ha : (entityPlans lists).getLast?=some a) :
    a.receiptIndex+(if a.isHeader then 0 else 1)=lists.flatten.length ∧
    a.bodyEnd=8+(lists.flatten.map refundLength).sum := by
  obtain ⟨lp,hl,hla⟩ := flatMap_last_nonempty listEntities (planLists 0 0 8 lists) a
    (fun p _=>by simp [listEntities]) ha
  obtain ⟨_,_,hr,_,hb,_,_⟩ := listEntities_last_totals lp a hla
  obtain ⟨hr',hb'⟩ := planLists_last_totals lists 0 0 8 lp hl
  exact ⟨by omega,by omega⟩

end ZkFormal.NearV3.Assembly.RcptSkeleton
