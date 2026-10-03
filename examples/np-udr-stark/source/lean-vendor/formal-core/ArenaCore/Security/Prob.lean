/-!
# ArenaCore.Security.Prob — probability as counting over finite tapes

All randomness in the arena's games is a uniformly random *tape*: a list of
`n` symbols, each in `[0, R)`.  `allTapes n R` enumerates the `R^n` tapes and
a probability bound `Pr[E] ≤ num/den` is the purely arithmetical statement

  `#{t ∈ allTapes n R | E t} * den ≤ num * R^n`.

No real numbers, measure theory or Mathlib: just `List.countP` and `Nat`.
Events are `Prop`s (decided classically when counting), so games may refer
to non-decidable predicates such as "the claim is in the language".
-/

namespace ArenaCore.Security

/-- All tapes of length `n` over the alphabet `[0, R)`. -/
def allTapes : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | n + 1, R => (List.range R).flatMap fun a => (allTapes n R).map (a :: ·)

/-- Number of elements of `l` satisfying `E`. -/
noncomputable def count {α : Type} (l : List α) (E : α → Prop) : Nat :=
  open Classical in l.countP fun x => decide (E x)

/-- `Pr_{t ← [0,R)^n}[E t] ≤ num / den`.  The denominator must be positive
(otherwise `num/0` would make every bound trivially true). -/
def PrLE (n R : Nat) (E : List Nat → Prop) (num den : Nat) : Prop :=
  0 < den ∧ count (allTapes n R) E * den ≤ num * R ^ n

theorem length_flatMap_cons (l : List Nat) (L : List (List Nat)) :
    (l.flatMap fun a => L.map (a :: ·)).length = l.length * L.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih, Nat.succ_mul, Nat.add_comm]

theorem allTapes_length (n R : Nat) : (allTapes n R).length = R ^ n := by
  induction n with
  | zero => simp [allTapes]
  | succ n ih =>
    simp only [allTapes, length_flatMap_cons, List.length_range, ih]
    rw [Nat.pow_succ, Nat.mul_comm]

theorem mem_allTapes_length {n R : Nat} {t : List Nat} (h : t ∈ allTapes n R) : t.length = n := by
  induction n generalizing t with
  | zero => simp [allTapes] at h; simp [h]
  | succ n ih =>
    simp only [allTapes, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a, _, t', ht', rfl⟩ := h
    simp [ih ht']

theorem count_mono {α : Type} (l : List α) {E F : α → Prop} (h : ∀ x, E x → F x) :
    count l E ≤ count l F := by
  classical
  unfold count
  apply List.countP_mono_left
  intro x _ hx
  simp only [decide_eq_true_eq] at hx ⊢
  exact h x hx

theorem count_le_length {α : Type} (l : List α) (E : α → Prop) : count l E ≤ l.length := by
  classical
  unfold count
  exact List.countP_le_length

/-- Monotonicity of probability bounds in the event. -/
theorem PrLE.mono {n R : Nat} {E F : List Nat → Prop} {num den : Nat}
    (hEF : ∀ t, E t → F t) (h : PrLE n R F num den) : PrLE n R E num den :=
  ⟨h.1, Nat.le_trans (Nat.mul_le_mul_right _ (count_mono _ hEF)) h.2⟩

/-- Probabilities are at most one. -/
theorem PrLE.one (n R : Nat) (E : List Nat → Prop) : PrLE n R E 1 1 := by
  unfold PrLE
  have := count_le_length (allTapes n R) E
  rw [allTapes_length] at this
  exact ⟨Nat.one_pos, by simpa using this⟩

/-- Sanity (non-vacuity of the encoding): the sure event has probability
bound `num/den` only if `0 < den ≤ num` (for a nonempty alphabet). -/
theorem PrLE.sure_iff (n R num den : Nat) (hR : 0 < R) :
    PrLE n R (fun _ => True) num den ↔ 0 < den ∧ den ≤ num := by
  classical
  unfold PrLE count
  rw [List.countP_eq_length.mpr (by simp), allTapes_length]
  rw [Nat.mul_comm (R ^ n)]
  exact and_congr_right fun _ => Nat.mul_le_mul_right_iff (Nat.pow_pos hR)

end ArenaCore.Security
