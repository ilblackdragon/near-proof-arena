import ArenaCore

/-!
# ZkFormal.Udr.Count — counting toolkit for the unique-decoding IOP facts

Classical `count` (from `ArenaCore.Security.Prob`) over explicit lists:
uniqueness bounds, extraction of witnesses, union bounds through a list,
double counting and Markov's inequality, all in `Nat`.
-/

namespace ZkFormal.Udr

open ArenaCore.Security

theorem count_le_one_of_unique {α : Type} {l : List α} (hl : l.Nodup) (P : α → Prop)
    (h : ∀ a b, P a → P b → a = b) : count l P ≤ 1 := by
  classical
  induction l with
  | nil => simp [count]
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [count_cons]
    by_cases ha : P a
    · have : count l P ≤ count l (fun _ => False) :=
        count_mono_mem l fun b hb hPb => absurd (h a b ha hPb ▸ hb) hl.1
      rw [count_const] at this
      simp only [ite_false, Nat.le_zero] at this
      simp [ha, this]
    · simp only [ha, ite_false, Nat.add_zero]; exact ih hl.2

theorem count_eq_length_filter {α : Type} (l : List α) (P : α → Prop) :
    count l P = (open Classical in l.filter fun a => decide (P a)).length := by
  classical
  unfold count
  rw [List.countP_eq_length_filter]

/-- A positive count yields a witness. -/
theorem exists_of_count_pos {α : Type} {l : List α} {P : α → Prop} (h : 0 < count l P) :
    ∃ a ∈ l, P a := by
  classical
  unfold count at h
  obtain ⟨a, ha, hP⟩ := List.countP_pos_iff.mp h
  exact ⟨a, ha, by simpa using hP⟩

/-- Two distinct witnesses from a count of at least two. -/
theorem two_of_count {α : Type} {l : List α} (P : α → Prop) (hl : l.Nodup)
    (h : 2 ≤ count l P) : ∃ a b, a ≠ b ∧ P a ∧ P b := by
  classical
  induction l with
  | nil => simp [count] at h
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [count_cons] at h
    by_cases ha : P a
    · simp only [ha, ite_true] at h
      obtain ⟨b, hb, hPb⟩ := exists_of_count_pos (l := l) (P := P) (by omega)
      exact ⟨a, b, fun hab => hl.1 (hab ▸ hb), ha, hPb⟩
    · simp only [ha, ite_false, Nat.add_zero] at h
      exact ih hl.2 h

/-- `count l P ≤ count l (P ∧ Q) + count l (¬Q)`. -/
theorem count_le_and_add_not {α : Type} (l : List α) (P Q : α → Prop) :
    count l P ≤ count l (fun a => P a ∧ Q a) + count l (fun a => ¬ Q a) := by
  refine Nat.le_trans (count_mono l (F := fun a => (P a ∧ Q a) ∨ ¬ Q a) ?_) (count_or_le _ _ _)
  intro a hP
  by_cases hQ : Q a
  · exact Or.inl ⟨hP, hQ⟩
  · exact Or.inr hQ

/-- Union bound through a list of indices. -/
theorem count_exists_mem_le {α β : Type} (l : List α) (I : List β) (R : β → α → Prop) :
    count l (fun a => ∃ i ∈ I, R i a) ≤ (I.map fun i => count l (R i)).sum := by
  induction I with
  | nil =>
    have : count l (fun a => ∃ i ∈ ([] : List β), R i a) ≤ count l (fun _ => False) :=
      count_mono _ fun _ ⟨_, hi, _⟩ => absurd hi (List.not_mem_nil)
    rw [count_const] at this
    simpa using this
  | cons b I ih =>
    simp only [List.map_cons, List.sum_cons]
    refine Nat.le_trans (count_mono l (F := fun a => R b a ∨ ∃ i ∈ I, R i a) ?_)
      (Nat.le_trans (count_or_le _ _ _) (Nat.add_le_add_left ih _))
    rintro a ⟨i, hi, hR⟩
    rcases List.mem_cons.mp hi with rfl | hi
    · exact Or.inl hR
    · exact Or.inr ⟨i, hi, hR⟩

theorem sum_le_of_le {α : Type} (l : List α) (f g : α → Nat) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (List.mem_cons_self ..))
      (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem sum_le_length_mul {α : Type} (l : List α) (f : α → Nat) (b : Nat)
    (h : ∀ a ∈ l, f a ≤ b) : (l.map f).sum ≤ l.length * b := by
  have := sum_le_of_le l f (fun _ => b) h
  rw [sum_map_const] at this
  exact this

theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map fun a => f a + g a).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- Double counting. -/
theorem sum_count_swap {α β : Type} (A : List α) (B : List β) (R : α → β → Prop) :
    (A.map fun a => count B (R a)).sum = (B.map fun b => count A (fun a => R a b)).sum := by
  classical
  induction A with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    have : ∀ b ∈ B, count ([] : List α) (fun a => R a b) = 0 := fun _ _ => by simp [count]
    rw [List.map_congr_left this, sum_map_const, Nat.mul_zero]
  | cons a A ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    have e : (B.map fun b => count (a :: A) (fun a' => R a' b)) =
        (B.map fun b => count A (fun a' => R a' b) + (if R a b then 1 else 0)) :=
      List.map_congr_left fun b _ => by rw [count_cons]
    rw [e, sum_map_add, sum_map_ite, Nat.mul_one, Nat.add_comm]

/-- Markov: the number of entries with `c ≤ f a` times `c` is at most the sum. -/
theorem count_ge_mul_le_sum {α : Type} (l : List α) (f : α → Nat) (c : Nat) :
    count l (fun a => c ≤ f a) * c ≤ (l.map f).sum := by
  classical
  induction l with
  | nil => simp [count]
  | cons a l ih =>
    rw [count_cons]
    simp only [List.map_cons, List.sum_cons]
    by_cases h : c ≤ f a
    · simp only [h, ite_true, Nat.add_mul, Nat.one_mul]; omega
    · simp only [h, ite_false, Nat.add_zero]; omega

theorem count_add_count_not {α : Type} (l : List α) (P : α → Prop) :
    count l P + count l (fun a => ¬ P a) = l.length := by
  classical
  induction l with
  | nil => simp [count]
  | cons a l ih =>
    rw [count_cons, count_cons, List.length_cons, ← ih]
    by_cases h : P a <;> simp [h] <;> omega

/-- The filtered sublist realizing a count. -/
theorem filter_props {α : Type} (l : List α) (P : α → Prop) :
    ∃ l' : List α, l'.length = count l P ∧ (∀ a ∈ l', a ∈ l ∧ P a) ∧ (l.Nodup → l'.Nodup) := by
  classical
  refine ⟨l.filter fun a => decide (P a), (count_eq_length_filter l P).symm, fun a ha => ?_,
    fun h => h.filter _⟩
  have := List.mem_filter.mp ha
  exact ⟨this.1, by simpa using this.2⟩

end ZkFormal.Udr
