import ZkFormal.NearV3.Assembly.RcptSegmentLedger

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
universe u v
variable {α : Type u} {β : Type v}

/-- Nonempty blocks let physical boundary neighbors recover the actual adjacent
block pair, rather than an arbitrary later nonempty suffix. -/
theorem neighbors_flatMap_nonempty (f : α→List β) (xs : List α) (a b : β)
    (hn : ∀x∈xs,f x≠[]) (h : Neighbors (xs.flatMap f) a b) :
    (∃x∈xs,Neighbors (f x) a b) ∨
    (∃p q,Neighbors xs p q ∧ (f p).getLast?=some a ∧ (f q).head?=some b) := by
  induction xs with
  | nil => simp [Neighbors] at h
  | cons x xs ih =>
    simp only [List.flatMap_cons] at h
    rcases neighbors_append (f x) (xs.flatMap f) a b h with hl|hr|⟨ha,hb⟩
    · exact Or.inl ⟨x,by simp,hl⟩
    · rcases ih (fun y hy=>hn y (by simp [hy])) hr with ⟨y,hy,hh⟩|⟨p,q,hpq,hp,hq⟩
      · exact Or.inl ⟨y,by simp [hy],hh⟩
      · exact Or.inr ⟨p,q,(neighbors_cons x xs p q).mpr (Or.inr hpq),hp,hq⟩
    · cases xs with
      | nil => simp at hb
      | cons y ys =>
        have hny := hn y (by simp)
        have hhead : (f y).head?=some b := by
          cases hy : f y with
          | nil => exact False.elim (hny hy)
          | cons z zs => simpa [List.flatMap_cons,hy] using hb
        exact Or.inr ⟨x,y,(neighbors_cons x (y::ys) x y).mpr (Or.inl ⟨rfl,rfl⟩),ha,hhead⟩

theorem plannedSegments_positive (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) :
    ∀p∈plannedSegments lists,0<p.length := by
  intro p hp
  obtain ⟨lp,hl,hp⟩ := List.mem_flatMap.mp hp
  simp only [listSegments,List.mem_cons] at hp
  rcases hp with rfl|hp
  · change 0<12; decide
  · obtain ⟨rp,hr,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hp
    have hm := List.mem_of_getElem? (global_plan_receipt lists lp hl rp hr)
    obtain ⟨xs,hxs,hx⟩ := List.mem_flatten.mp hm
    exact fields_positive rp.input (hw xs hxs rp.input hx) s hs

theorem plannedSegments_nonempty (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) :
    ∀p∈plannedSegments lists,p.rows≠[] := by
  intro p hp
  have hn := plannedSegments_positive lists hw p hp
  have hl : p.rows.length=p.length := by simp [SegmentPlan.rows,segment_length]
  intro he
  rw [he] at hl
  simp only [List.length_nil] at hl
  omega

/-- Complete active-row split with exact source/target segment indices at every
boundary, using only native receipt well-formedness for nonempty fields. -/
theorem planned_neighbors_indexed (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (a b : PlannedRow)
    (h : Neighbors (plannedRows lists) a b) :
    (∃p∈plannedSegments lists,Neighbors p.rows a b) ∨
    (∃p q,Neighbors (plannedSegments lists) p q ∧
      p.rows.getLast?=some a ∧ q.rows.head?=some b ∧ p.endIndex=q.startIndex) := by
  rw [←plannedSegments_rows] at h
  rcases neighbors_flatMap_nonempty SegmentPlan.rows _ a b (plannedSegments_nonempty lists hw) h with
    hi|⟨p,q,hpq,hp,hq⟩
  · exact Or.inl hi
  · exact Or.inr ⟨p,q,hpq,hp,hq,plannedSegments_neighbor_indices lists p q hpq⟩

end ZkFormal.NearV3.Assembly.RcptSkeleton
