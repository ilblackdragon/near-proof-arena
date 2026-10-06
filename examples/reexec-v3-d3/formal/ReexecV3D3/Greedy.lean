import ReexecV3D3.Canon

/-!
# Dropping unnecessary values: termination, fixed points, invariants

* `pass X` either returns `X` or strictly shrinks it (`pass_size`); `iterP` with
  `poolSize X + 1` passes ends at a fixed point of `pass` (`iterP_fixed`).
* A removal is kept only if `checkD3` accepts the result (`iterP_accepts`), and every pool of the
  result is a sub-list of the start's (`iterP_sub`).
* `pass X = X` iff every value of `X` is necessary (`pass_eq_iff`), which is what the parallel
  `allNeeded` decides (`allNeeded_iff`; `passPar = pass`).
-/

namespace ReexecV3D3

open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## Sizes -/

def sumLen (L : List (List Bytes)) : Nat := (L.map List.length).sum

theorem poolSize_eq (X : Pools) : poolSize X = X.1.length + sumLen X.2 := rfl

theorem erase_cases (l : List Bytes) (v : Bytes) :
    (v ∈ l ∧ (l.erase v).length + 1 = l.length) ∨ (v ∉ l ∧ l.erase v = l) := by
  by_cases h : v ∈ l
  · left
    refine ⟨h, ?_⟩
    rw [List.length_erase_of_mem h]
    have : 0 < l.length := List.length_pos_of_mem h
    omega
  · right; exact ⟨h, List.erase_of_not_mem h⟩

theorem modAt_length {α : Type} (f : α → α) : ∀ (i : Nat) (L : List α), (modAt f i L).length = L.length
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, _ :: _ => rfl
  | i + 1, _ :: xs => by simp [modAt, modAt_length f i xs]

theorem modAt_erase_cases (v : Bytes) : ∀ (i : Nat) (L : List (List Bytes)),
    (i < L.length ∧ v ∈ L.getD i [] ∧ sumLen (modAt (·.erase v) i L) + 1 = sumLen L) ∨
      modAt (·.erase v) i L = L
  | 0, [] => Or.inr rfl
  | _ + 1, [] => Or.inr rfl
  | 0, x :: xs => by
    rcases erase_cases x v with ⟨hm, hl⟩ | ⟨-, he⟩
    · left
      refine ⟨by simp, by simpa using hm, ?_⟩
      simp only [modAt, sumLen, List.map_cons, List.sum_cons]
      omega
    · right; simp [modAt, he]
  | i + 1, x :: xs => by
    rcases modAt_erase_cases v i xs with ⟨hi, hm, hl⟩ | he
    · left
      refine ⟨by simp; omega, by simpa using hm, ?_⟩
      simp only [modAt, sumLen, List.map_cons, List.sum_cons] at hl ⊢
      omega
    · right; simp [modAt, he]

/-- A removal either changes nothing or removes one value. -/
theorem removeItem_cases (X : Pools) (it : Item) :
    removeItem X it = X ∨ poolSize (removeItem X it) + 1 = poolSize X := by
  obtain ⟨o, v⟩ := it
  cases o with
  | none =>
    rcases erase_cases X.1 v with ⟨-, hl⟩ | ⟨-, he⟩
    · right; simp only [removeItem, poolSize]; omega
    · left; simp only [removeItem, he]
  | some i =>
    rcases modAt_erase_cases v i X.2 with ⟨-, -, hl⟩ | he
    · right; simp only [removeItem, poolSize]; unfold sumLen at hl; omega
    · left; simp only [removeItem, he]

theorem mem_items {X : Pools} {it : Item} (h : it ∈ items X) :
    (it.1 = none ∧ it.2 ∈ X.1) ∨ (∃ i, it.1 = some i ∧ i < X.2.length ∧ it.2 ∈ X.2.getD i []) := by
  unfold items at h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
    exact Or.inl ⟨rfl, hv⟩
  · obtain ⟨i, hi, h⟩ := List.mem_flatMap.mp h
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
    exact Or.inr ⟨i, rfl, List.mem_range.mp hi, hv⟩

/-- Removing a listed candidate removes one value. -/
theorem removeItem_lt {X : Pools} {it : Item} (h : it ∈ items X) :
    poolSize (removeItem X it) + 1 = poolSize X := by
  obtain ⟨o, v⟩ := it
  rcases mem_items h with ⟨ho, hv⟩ | ⟨i, ho, hi, hv⟩
  · simp only at ho hv; subst ho
    rcases erase_cases X.1 v with ⟨-, hl⟩ | ⟨hn, -⟩
    · simp only [removeItem, poolSize]; omega
    · exact absurd hv hn
  · simp only at ho hv; subst ho
    rcases modAt_erase_cases v i X.2 with ⟨-, -, hl⟩ | he
    · simp only [removeItem, poolSize]; unfold sumLen at hl; omega
    · exfalso
      rcases erase_cases (X.2.getD i []) v with ⟨-, hl⟩ | ⟨hn, -⟩
      · -- the `i`-th pool shrinks, so `modAt` changes the list
        have key : ∀ (i : Nat) (L : List (List Bytes)), i < L.length →
            (modAt (·.erase v) i L).getD i [] = (L.getD i []).erase v := by
          intro i L
          induction L generalizing i with
          | nil => intro h; simp at h
          | cons x xs ih =>
            intro h
            cases i with
            | zero => rfl
            | succ i => simp only [modAt, List.getD_cons_succ]; exact ih i (by simpa using h)
        have := key i X.2 hi
        rw [he] at this
        rw [← this] at hl
        omega
      · exact hn hv

/-! ## One pass -/

variable (cb sw : Bytes)

theorem stepP_cases (X : Pools) (it : Item) :
    stepP cb sw X it = X ∨ poolSize (stepP cb sw X it) < poolSize X := by
  unfold stepP
  dsimp only
  split
  · rcases removeItem_cases X it with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  · exact Or.inl rfl

theorem foldl_stepP_cases : ∀ (L : List Item) (X : Pools),
    L.foldl (stepP cb sw) X = X ∨ poolSize (L.foldl (stepP cb sw) X) < poolSize X
  | [], _ => Or.inl rfl
  | it :: L, X => by
    simp only [List.foldl_cons]
    rcases stepP_cases cb sw X it with h | h
    · rw [h]; exact foldl_stepP_cases L X
    · rcases foldl_stepP_cases L (stepP cb sw X it) with h' | h'
      · exact Or.inr (by rw [h']; exact h)
      · exact Or.inr (by omega)

theorem pass_cases (X : Pools) : pass cb sw X = X ∨ poolSize (pass cb sw X) < poolSize X :=
  foldl_stepP_cases cb sw (items X) X

/-- The test of one candidate. -/
def needed (X : Pools) (it : Item) : Prop := acceptsD3 cb (encP cb sw (removeItem X it)) = false

theorem foldl_stepP_fixed : ∀ (L : List Item) (X : Pools), (∀ it ∈ L, needed cb sw X it) →
    L.foldl (stepP cb sw) X = X
  | [], _, _ => rfl
  | it :: L, X, h => by
    simp only [List.foldl_cons]
    have : stepP cb sw X it = X := by
      have hn := h it List.mem_cons_self
      unfold needed at hn
      unfold stepP; dsimp only; rw [hn]; rfl
    rw [this]
    exact foldl_stepP_fixed L X (fun i hi => h i (List.mem_cons_of_mem _ hi))

theorem foldl_stepP_needed : ∀ (L : List Item) (X : Pools),
    (∀ it ∈ L, poolSize (removeItem X it) + 1 = poolSize X) →
    L.foldl (stepP cb sw) X = X → ∀ it ∈ L, needed cb sw X it
  | [], _, _, _ => by simp
  | it :: L, X, hs, h => by
    simp only [List.foldl_cons] at h
    by_cases ht : acceptsD3 cb (encP cb sw (removeItem X it)) = true
    · exfalso
      have e : stepP cb sw X it = removeItem X it := by unfold stepP; simp [ht]
      rw [e] at h
      have h1 := hs it List.mem_cons_self
      rcases foldl_stepP_cases cb sw L (removeItem X it) with h' | h'
      · rw [h] at h'; have := congrArg poolSize h'; omega
      · rw [h] at h'; omega
    · have hn : needed cb sw X it := by simpa [needed] using ht
      have e : stepP cb sw X it = X := by unfold stepP; simp [Bool.not_eq_true _ ▸ ht]
      rw [e] at h
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hn
      · exact foldl_stepP_needed L X (fun j hj => hs j (List.mem_cons_of_mem _ hj)) h i hi

/-- **A pass changes nothing iff every candidate is necessary.** -/
theorem pass_eq_iff (X : Pools) : pass cb sw X = X ↔ ∀ it ∈ items X, needed cb sw X it :=
  ⟨fun h => foldl_stepP_needed cb sw (items X) X (fun _ hi => removeItem_lt hi) h,
   fun h => foldl_stepP_fixed cb sw (items X) X h⟩

theorem task_get {α : Type} (f : Unit → α) (p : Task.Priority) : (Task.spawn f p).get = f () := rfl

theorem allNeeded_iff (X : Pools) :
    allNeeded cb sw X = true ↔ ∀ it ∈ items X, needed cb sw X it := by
  unfold allNeeded needed
  rw [List.all_map]
  simp only [List.all_eq_true, Function.comp, task_get, Bool.not_eq_true']

theorem passPar_eq (X : Pools) : passPar cb sw X = pass cb sw X := by
  unfold passPar
  split
  · rename_i h
    exact ((pass_eq_iff cb sw X).mpr ((allNeeded_iff cb sw X).mp h)).symm
  · rfl

/-! ## Iteration -/

theorem iterP_fixed : ∀ (f : Nat) (X : Pools), poolSize X < f →
    pass cb sw (iterP cb sw f X) = iterP cb sw f X
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, X, h => by
    unfold iterP
    dsimp only
    rw [passPar_eq]
    split
    · rename_i he; exact of_decide_eq_true he
    · rename_i he
      have he : ¬ pass cb sw X = X := fun e => he (decide_eq_true e)
      rcases pass_cases cb sw X with h' | h'
      · exact absurd h' he
      · exact iterP_fixed f _ (by omega)

theorem pass_accepts (X : Pools) (h : acceptsD3 cb (encP cb sw X) = true) :
    acceptsD3 cb (encP cb sw (pass cb sw X)) = true := by
  unfold pass
  generalize items X = L
  induction L generalizing X with
  | nil => exact h
  | cons it L ih =>
    simp only [List.foldl_cons]
    apply ih
    unfold stepP
    dsimp only
    split
    · assumption
    · exact h

theorem iterP_succ (f : Nat) (X : Pools) :
    iterP cb sw (f + 1) X = if pass cb sw X = X then X else iterP cb sw f (pass cb sw X) := by
  rw [iterP, passPar_eq]
  simp only [decide_eq_true_eq]

theorem iterP_accepts (f : Nat) : ∀ (X : Pools), acceptsD3 cb (encP cb sw X) = true →
    acceptsD3 cb (encP cb sw (iterP cb sw f X)) = true := by
  induction f with
  | zero => intro X h; rw [iterP]; exact h
  | succ f ih =>
    intro X h
    rw [iterP_succ]
    by_cases he : pass cb sw X = X
    · rw [if_pos he]; exact h
    · rw [if_neg he]; exact ih _ (pass_accepts cb sw X h)

/-! ## Sub-pools -/

def SubL : List (List Bytes) → List (List Bytes) → Prop
  | [], [] => True
  | a :: as, b :: bs => a.Sublist b ∧ SubL as bs
  | _, _ => False

theorem SubL.refl : ∀ L : List (List Bytes), SubL L L
  | [] => trivial
  | a :: as => ⟨List.Sublist.refl a, SubL.refl as⟩

theorem SubL.trans : ∀ {A B C : List (List Bytes)}, SubL A B → SubL B C → SubL A C
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h1, h2⟩, ⟨h3, h4⟩ => ⟨h1.trans h3, SubL.trans h2 h4⟩
  | [], [], _ :: _, _, h => h.elim
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim
  | _ :: _, _ :: _, [], _, h => h.elim

theorem SubL.mem : ∀ {A B : List (List Bytes)}, SubL A B → ∀ a ∈ A, ∃ b ∈ B, a.Sublist b
  | [], [], _, _, h => by simp at h
  | a :: as, b :: bs, ⟨h1, h2⟩, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, List.mem_cons_self, h1⟩
    · obtain ⟨y, hy, hs⟩ := SubL.mem h2 x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hs⟩
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim

theorem SubL.length : ∀ {A B : List (List Bytes)}, SubL A B → A.length = B.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, h⟩ => by simp [SubL.length h]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem modAt_subL (v : Bytes) : ∀ (i : Nat) (L : List (List Bytes)), SubL (modAt (·.erase v) i L) L
  | 0, [] => trivial
  | _ + 1, [] => trivial
  | 0, x :: xs => ⟨List.erase_sublist, SubL.refl xs⟩
  | i + 1, x :: xs => ⟨List.Sublist.refl x, modAt_subL v i xs⟩

def SubP (X Y : Pools) : Prop := X.1.Sublist Y.1 ∧ SubL X.2 Y.2

theorem SubP.refl (X : Pools) : SubP X X := ⟨List.Sublist.refl _, SubL.refl _⟩

theorem SubP.trans {X Y Z : Pools} (h1 : SubP X Y) (h2 : SubP Y Z) : SubP X Z :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem removeItem_sub (X : Pools) (it : Item) : SubP (removeItem X it) X := by
  obtain ⟨o, v⟩ := it
  cases o with
  | none => exact ⟨List.erase_sublist, SubL.refl _⟩
  | some i => exact ⟨List.Sublist.refl _, modAt_subL v i X.2⟩

theorem pass_sub (X : Pools) : SubP (pass cb sw X) X := by
  unfold pass
  generalize items X = L
  suffices ∀ Y, SubP Y X → SubP (L.foldl (stepP cb sw) Y) X from this X (SubP.refl X)
  induction L with
  | nil => intro Y h; exact h
  | cons it L ih =>
    intro Y h
    simp only [List.foldl_cons]
    apply ih
    unfold stepP
    dsimp only
    split
    · exact (removeItem_sub Y it).trans h
    · exact h

theorem iterP_sub : ∀ (f : Nat) (X : Pools), SubP (iterP cb sw f X) X
  | 0, X => SubP.refl X
  | f + 1, X => by
    unfold iterP
    dsimp only
    rw [passPar_eq]
    split
    · exact SubP.refl X
    · exact (iterP_sub f _).trans (pass_sub cb sw X)

end ReexecV3D3
