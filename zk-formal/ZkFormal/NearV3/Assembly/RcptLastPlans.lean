import ZkFormal.NearV3.Assembly.RcptActiveBoundaryRegs

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
universe u v
variable {α : Type u} {β : Type v}

theorem flatMap_last_nonempty (f : α→List β) (xs : List α) (a : β)
    (hn : ∀x∈xs,f x≠[]) (h : (xs.flatMap f).getLast?=some a) :
    ∃x,xs.getLast?=some x ∧ (f x).getLast?=some a := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    cases xs with
    | nil => exact ⟨x,rfl,by simpa using h⟩
    | cons y ys =>
      have hny := hn y (by simp)
      have hnys : ((y::ys).flatMap f)≠[] := by
        intro hh
        exact hny (List.eq_nil_of_append_eq_nil hh).1
      have hlast : ((y::ys).flatMap f).getLast?≠none := by intro hh;exact hnys (List.getLast?_eq_none_iff.mp hh)
      simp only [List.flatMap_cons,List.getLast?_append] at h
      cases he : ((y::ys).flatMap f).getLast? with
      | none => exact False.elim (hlast he)
      | some b =>
        have ha : b=a := by
          have hh : (f x ++ (y::ys).flatMap f).getLast?=some a := by
            simpa only [List.flatMap_cons,List.getLast?_append] using h
          rw [List.getLast?_append,he] at hh
          exact Option.some.inj hh
        subst b
        obtain ⟨z,hz,hh⟩ := ih (fun z hz=>hn z (by simp [hz])) he
        exact ⟨z,by simpa only [List.getLast?_cons_cons] using hz,hh⟩

theorem planLists_last_flag (lists : List (List Input)) (j r o2 : Nat) (p : ListPlan)
    (h : (planLists j r o2 lists).getLast?=some p) : p.lastList=true := by
  induction lists generalizing j r o2 with
  | nil => simp [planLists] at h
  | cons xs lists ih =>
    cases lists with
    | nil =>
      simp only [planLists,List.getLast?_singleton,Option.some.injEq] at h
      cases h
      rfl
    | cons ys lists =>
      apply ih (j+1) (r+xs.length) (o2+(xs.map refundLength).sum)
      simpa only [planLists,List.getLast?_cons_cons] using h

theorem planReceipts_last_flag (xs : List Input) (j nj r cj o o2 : Nat) (ll : Bool) (p : ReceiptPlan)
    (h : (planReceipts j nj r cj o o2 ll xs).getLast?=some p) : p.lastInList=true := by
  induction xs generalizing r cj o o2 with
  | nil => simp [planReceipts] at h
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp only [planReceipts,List.getLast?_singleton,Option.some.injEq] at h
      cases h
      rfl
    | cons y ys =>
      apply ih (r+1) (cj+1) (o+rcLength x) (o2+refundLength x)
      simpa only [planReceipts,List.getLast?_cons_cons] using h

end ZkFormal.NearV3.Assembly.RcptSkeleton
