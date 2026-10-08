import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22Tables

namespace ZkFormal.NearV3.Rcpt.Candidates.SourceLog22

/-- Logical rows owned by each partition; boundary copies are not owned twice. -/
def slices {α : Type} : Nat → Nat → List α → List (List α)
  | 0, _, xs => [xs]
  | n+1, cap, xs => xs.take cap :: slices n cap (xs.drop cap)

theorem slices_reconstruct {α : Type} (n cap : Nat) (xs : List α) :
    (slices n cap xs).flatten = xs := by
  induction n generalizing xs with
  | zero => simp [slices]
  | succ n ih => simp only [slices,List.flatten_cons,ih,List.take_append_drop]

theorem slices_count {α : Type} (n cap : Nat) (xs : List α) :
    (slices n cap xs).length = n+1 := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp [slices,ih]

theorem slices_capacity {α : Type} (n cap : Nat) (xs : List α)
    (h : xs.length ≤ (n+1)*cap) :
    ∀ ys ∈ slices n cap xs, ys.length ≤ cap := by
  induction n generalizing xs with
  | zero => simpa [slices] using h
  | succ n ih =>
    intro ys hy
    simp only [slices,List.mem_cons] at hy
    rcases hy with rfl|hy
    · simp only [List.length_take]; exact Nat.min_le_left _ _
    · apply ih (xs.drop cap) ?_ ys hy
      simp only [List.length_drop]
      simp only [Nat.add_mul,Nat.one_mul] at h ⊢
      omega

/-- The actual source row envelope yields four bounded, ordered slices. Adding
one physical overlap/padding row to each slice stays within log22. -/
theorem source_slices {α : Type} (xs : List α) (h : xs.length ≤ 16334272) :
    (slices 3 (2^22-1) xs).length = 4 ∧
    (slices 3 (2^22-1) xs).flatten = xs ∧
    ∀ ys ∈ slices 3 (2^22-1) xs, ys.length+1 ≤ 2^22 := by
  refine ⟨slices_count _ _ _,slices_reconstruct _ _ _,?_⟩
  intro ys hy
  have hh := slices_capacity 3 (2^22-1) xs (by omega) ys hy
  omega

end ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
