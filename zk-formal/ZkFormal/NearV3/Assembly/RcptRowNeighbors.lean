import ZkFormal.NearV3.Assembly.RcptBoundaryTokens

namespace ZkFormal.NearV3.Assembly.RcptSkeleton

universe u v
variable {α : Type u} {β : Type v}

/-- Consecutive list elements; multiplicity and original order are retained. -/
def Neighbors (xs : List α) (a b : α) : Prop := (a,b)∈xs.zip (xs.drop 1)

theorem neighbors_cons (x : α) (xs : List α) (a b : α) :
    Neighbors (x::xs) a b ↔ (x=a ∧ xs.head?=some b) ∨ Neighbors xs a b := by
  cases xs <;> simp [Neighbors,Prod.mk.injEq,and_comm,eq_comm]

theorem neighbors_append (xs ys : List α) (a b : α)
    (h : Neighbors (xs++ys) a b) :
    Neighbors xs a b ∨ Neighbors ys a b ∨
      xs.getLast?=some a ∧ ys.head?=some b := by
  induction xs with
  | nil => exact Or.inr (Or.inl h)
  | cons x xs ih =>
    rw [List.cons_append,neighbors_cons] at h
    rcases h with ⟨hx,hb⟩|ht
    · cases xs with
      | nil => exact Or.inr (Or.inr ⟨by simpa using congrArg some hx,hb⟩)
      | cons y xs =>
        apply Or.inl
        rw [neighbors_cons]
        exact Or.inl ⟨hx,hb⟩
    · rcases ih ht with hl|hr|⟨ha,hb⟩
      · exact Or.inl ((neighbors_cons x xs a b).mpr (Or.inr hl))
      · exact Or.inr (Or.inl hr)
      · apply Or.inr ∘ Or.inr
        refine ⟨?_,hb⟩
        cases xs with
        | nil => simp at ha
        | cons y ys => simpa using ha

/-- Every physical neighbor lies inside a block or crosses a block boundary.
No nonempty assumption is needed: skipped empty blocks are represented by the
explicit suffix's first row. -/
theorem neighbors_flatMap (f : α→List β) (xs : List α) (a b : β)
    (h : Neighbors (xs.flatMap f) a b) :
    (∃ x∈xs,Neighbors (f x) a b) ∨
    (∃ pre x post,xs=pre++x::post ∧ (f x).getLast?=some a ∧
      (post.flatMap f).head?=some b) := by
  induction xs with
  | nil => simp [Neighbors] at h
  | cons x xs ih =>
    simp only [List.flatMap_cons] at h
    rcases neighbors_append (f x) (xs.flatMap f) a b h with hl|hr|hb
    · exact Or.inl ⟨x,by simp,hl⟩
    · rcases ih hr with ⟨y,hy,hh⟩|⟨pre,y,post,he,ha,hb⟩
      · exact Or.inl ⟨y,by simp [hy],hh⟩
      · exact Or.inr ⟨x::pre,y,post,by simp [he],ha,hb⟩
    · exact Or.inr ⟨[],x,xs,rfl,hb⟩

theorem neighbors_get (xs : List α) (a b : α) (h : Neighbors xs a b) :
    ∃ i,xs[i]?=some a ∧ xs[i+1]?=some b := by
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp h
  obtain ⟨ha,hb⟩ := List.getElem?_zip_eq_some.mp hi
  exact ⟨i,ha,by simpa [List.getElem?_drop,Nat.add_comm] using hb⟩

theorem segment_neighbors (s len : Nat) (a b : Coord)
    (h : Neighbors (segment s len) a b) :
    a.state=s ∧ a.length=len ∧ a.index+1<len ∧ b=advance a := by
  obtain ⟨i,ha,hb⟩ := neighbors_get _ a b h
  have hbnd := (List.getElem?_eq_some_iff.mp hb).1
  have hib : i+1<len := by simpa [segment_length] using hbnd
  rw [segment_get s len i (by omega)] at ha
  rw [segment_get s len (i+1) hib] at hb
  cases ha
  cases hb
  exact ⟨rfl,rfl,hib,rfl⟩

theorem segment_last (s len : Nat) (a : Coord) (h : (segment s len).getLast?=some a) :
    a.state=s ∧ a.length=len ∧ a.index+1=len := by
  simp only [segment,List.getLast?_map,List.getLast?_range] at h
  split at h
  · simp at h
  · rename_i hn
    simp only [Option.map_some,Option.some.injEq] at h
    subst a
    exact ⟨rfl,rfl,by change len-1+1=len; omega⟩

theorem segment_head (s len : Nat) (a : Coord) (h : (segment s len).head?=some a) :
    a.state=s ∧ a.length=len ∧ a.index=0 := by
  simp only [segment,List.head?_map,List.head?_range] at h
  split at h
  · simp at h
  · simp only [Option.map_some,Option.some.injEq] at h
    subst a
    exact ⟨rfl,rfl,rfl⟩

theorem neighbors_of_get (xs : List α) (a b : α) (i : Nat)
    (ha : xs[i]?=some a) (hb : xs[i+1]?=some b) : Neighbors xs a b := by
  apply List.mem_of_getElem? (i:=i)
  apply List.getElem?_zip_eq_some.mpr
  exact ⟨ha,by simpa [List.getElem?_drop,Nat.add_comm] using hb⟩

theorem neighbors_map (f : α→β) (xs : List α) (a b : β)
    (h : Neighbors (xs.map f) a b) :
    ∃ x y,Neighbors xs x y ∧ f x=a ∧ f y=b := by
  obtain ⟨i,ha,hb⟩ := neighbors_get _ a b h
  rw [List.getElem?_map] at ha hb
  obtain ⟨x,hx,ha⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨y,hy,hb⟩ := Option.map_eq_some_iff.mp hb
  exact ⟨x,y,neighbors_of_get xs x y i hx hy,ha,hb⟩

end ZkFormal.NearV3.Assembly.RcptSkeleton
