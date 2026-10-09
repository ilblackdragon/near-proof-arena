import ZkFormal.NearV3.Assembly.RcptSegmentPlan

namespace ZkFormal.NearV3.Assembly.RcptSkeleton

universe u v
variable {α : Type u} {β : Type v}

private theorem flatMap_last (f : α→List β) (xs : List α) (a : β)
    (h : (xs.flatMap f).getLast?=some a) : ∃ x∈xs,(f x).getLast?=some a := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.getLast?_append] at h
    cases he : (xs.flatMap f).getLast? with
    | none =>
      simp only [he,Option.or] at h
      exact ⟨x,by simp,h⟩
    | some b =>
      simp only [he,Option.or,Option.some.injEq] at h
      subst b
      obtain ⟨y,hy,hh⟩ := ih he
      exact ⟨y,by simp [hy],hh⟩

/-- The last active row is a segment endpoint, even if later conceptual
segments are empty. This is the boundary used before zero padding. -/
theorem planned_last_shape (lists : List (List Input)) (a : PlannedRow)
    (h : (plannedRows lists).getLast?=some a) :
    ∃ p∈plannedSegments lists,∃ row,row.state=p.state ∧ row.length=p.length ∧
      row.index+1=p.length ∧ a=p.wrap row := by
  rw [←plannedSegments_rows] at h
  obtain ⟨p,hp,hh⟩ := flatMap_last SegmentPlan.rows _ a h
  obtain ⟨row,hs,hl,hi,ha⟩ := p.last a hh
  exact ⟨p,hp,row,hs,hl,hi,ha⟩

/-- If the next indexed row is absent, the current row is the actual last row;
there is no unproved assertion that the segment happens to end there. -/
theorem planned_before_padding (lists : List (List Input)) (i : Nat) (a : PlannedRow)
    (ha : (plannedRows lists)[i]?=some a) (hn : (plannedRows lists)[i+1]?=none) :
    ∃ p∈plannedSegments lists,∃ row,row.state=p.state ∧ row.length=p.length ∧
      row.index+1=p.length ∧ a=p.wrap row := by
  have hi := (List.getElem?_eq_some_iff.mp ha).1
  have hn' := List.getElem?_eq_none_iff.mp hn
  have he : (plannedRows lists).length-1=i := by omega
  apply planned_last_shape lists a
  rw [List.getLast?_eq_getElem?,he]
  exact ha

end ZkFormal.NearV3.Assembly.RcptSkeleton
