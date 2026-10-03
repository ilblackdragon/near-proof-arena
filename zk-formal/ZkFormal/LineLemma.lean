import ArenaCore

/-!
# ZkFormal.LineLemma — the strong line lemma (radius `d/3`), Mathlib-free

The IOP-side core of the design (DESIGN.md §6.4).  For a linear code `C` of
length `n` and minimum distance `d` over a field `K`, a pair of words
`u0, u1` and radius `e` with `3e < d`:

> for all but at most `max 1 n` challenges `z`, whenever `u0 + z·u1` agrees
> with a codeword `c` on all but `e` positions, there are codewords
> `v0, v1` such that `u0 = v0` and `u1 = v1` on **every** position where
> `u0 + z·u1 = c`.

This "agreement-set containment" form is what the FRI query-phase argument
needs (each fold `f_e + β·f_o`, each batching step and each roll-in is such a
line), and it needs no weighted correlated agreement.  The proof is
elementary: two good challenges determine `v0, v1`; `3e < d` forces every
other good challenge's codeword onto the line `v0 + z·v1`; a position where
`(u0,u1) ≠ (v0,v1)` agrees with that line for at most one `z`.

The `d/2` radius (target parameters) replaces the `3e < d` step by the
Berlekamp–Welch correlated-agreement theorem; the containment step is the
same.  Field reasoning is done by core Lean's `grind` over
`Lean.Grind.Field` — no Mathlib.
-/

namespace ZkFormal.LineLemma

open ArenaCore.Security
open Lean.Grind

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [DecidableEq K]

/-- Hamming distance on positions `[0, n)`. -/
def dist (n : Nat) (u v : Nat → K) : Nat := (List.range n).countP fun i => u i ≠ v i

/-- A linear code of length `n` with minimum distance `d`. -/
structure LinCode (K : Type) [Field K] [DecidableEq K] (n d : Nat) where
  mem : (Nat → K) → Prop
  lin : ∀ u v a b, mem u → mem v → mem fun i => a * u i + b * v i
  sep : ∀ u v, mem u → mem v → dist n u v < d → ∀ i, i < n → u i = v i

/-- `u0 + z·u1`. -/
def line (u0 u1 : Nat → K) (z : K) : Nat → K := fun i => u0 i + z * u1 i

/-- `z` is good: the line point is `e`-close to the code. -/
def Good {n d : Nat} (C : LinCode K n d) (e : Nat) (u0 u1 : Nat → K) (z : K) : Prop :=
  ∃ c, C.mem c ∧ dist n (line u0 u1 z) c ≤ e

/-- The strong (containment) conclusion at `z`. -/
def Strong {n d : Nat} (C : LinCode K n d) (e : Nat) (u0 u1 : Nat → K) (z : K) : Prop :=
  ∀ c, C.mem c → dist n (line u0 u1 z) c ≤ e →
    ∃ v0 v1, C.mem v0 ∧ C.mem v1 ∧
      ∀ i, i < n → line u0 u1 z i = c i → u0 i = v0 i ∧ u1 i = v1 i

/-! ## Distance lemmas -/

theorem dist_mono {n : Nat} {u v u' v' : Nat → K}
    (h : ∀ i, i < n → u i ≠ v i → u' i ≠ v' i) : dist n u v ≤ dist n u' v' := by
  unfold dist
  apply List.countP_mono_left
  intro i hi huv
  simp only [decide_eq_true_eq] at huv ⊢
  exact h i (List.mem_range.mp hi) huv

theorem countP_or_le {α : Type} (l : List α) (p q : α → Bool) :
    l.countP (fun a => p a || q a) ≤ l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    cases p a <;> cases q a <;> simp <;> omega

/-- Triangle inequality (through an explicit "or" of disagreements). -/
theorem dist_triangle (n : Nat) (u v w : Nat → K) : dist n u w ≤ dist n u v + dist n v w := by
  unfold dist
  refine Nat.le_trans ?_ (countP_or_le (List.range n) (fun i => decide (u i ≠ v i))
    (fun i => decide (v i ≠ w i)))
  apply List.countP_mono_left
  intro i _ h
  simp only [decide_eq_true_eq, Bool.or_eq_true] at h ⊢
  by_cases huv : u i = v i
  · exact Or.inr (huv ▸ h)
  · exact Or.inl huv

theorem dist_comm (n : Nat) (u v : Nat → K) : dist n u v = dist n v u := by
  unfold dist
  congr 1
  funext i
  simp [eq_comm]

/-! ## Counting helpers (classical `count` from ArenaCore) -/

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
      have h1 : 0 < count l P := by omega
      unfold count at h1
      obtain ⟨b, hb, hPb⟩ := List.countP_pos_iff.mp h1
      simp only [decide_eq_true_eq] at hPb
      exact ⟨a, b, fun hab => hl.1 (hab ▸ hb), ha, hPb⟩
    · simp only [ha, ite_false, Nat.add_zero] at h
      exact ih hl.2 h

/-! ## The lemma -/

/-- **Strong line lemma, radius `d/3`.**  Among any list `Ks` of distinct
challenges, at most `max 1 n` fail the containment conclusion. -/
theorem strong_line {n d : Nat} (C : LinCode K n d) (e : Nat) (he : 3 * e < d)
    (u0 u1 : Nat → K) (Ks : List K) (hKs : Ks.Nodup) :
    count Ks (fun z => ¬ Strong C e u0 u1 z) ≤ max 1 n := by
  classical
  -- ¬Strong ⇒ Good
  have hsg : ∀ z, ¬ Strong C e u0 u1 z → Good C e u0 u1 z := by
    intro z hz
    exact Classical.byContradiction fun hg => hz fun c hc hd => absurd ⟨c, hc, hd⟩ hg
  by_cases hfew : count Ks (Good C e u0 u1) ≤ 1
  · exact Nat.le_trans (count_mono _ hsg) (Nat.le_trans hfew (Nat.le_max_left _ _))
  · -- two good challenges determine the line
    obtain ⟨z1, z2, hz12, ⟨c1, hc1, hd1⟩, ⟨c2, hc2, hd2⟩⟩ :=
      two_of_count (Good C e u0 u1) hKs (by omega)
    have hz : z1 - z2 ≠ 0 := by intro h; exact hz12 (by grind)
    let v1 : Nat → K := fun i => (z1 - z2)⁻¹ * c1 i + (-(z1 - z2)⁻¹) * c2 i
    let v0 : Nat → K := fun i => 1 * c1 i + (-z1) * v1 i
    have hv1 : C.mem v1 := C.lin _ _ _ _ hc1 hc2
    have hv0 : C.mem v0 := C.lin _ _ _ _ hc1 hv1
    -- outside the error sets of c1, c2, (u0, u1) = (v0, v1)
    have hsolve : ∀ i, line u0 u1 z1 i = c1 i → line u0 u1 z2 i = c2 i →
        u0 i = v0 i ∧ u1 i = v1 i := by
      intro i h1 h2
      simp only [line] at h1 h2
      simp only [v0, v1]
      constructor <;> grind
    -- every good challenge's codeword is on the line
    have honline : ∀ z c, C.mem c → dist n (line u0 u1 z) c ≤ e →
        ∀ i, i < n → c i = line v0 v1 z i := by
      intro z c hc hdc
      have hw : C.mem (line v0 v1 z) := by
        have := C.lin _ _ 1 z hv0 hv1
        have e : (fun i => 1 * v0 i + z * v1 i) = line v0 v1 z := by
          funext i; simp only [line]; grind
        rw [e] at this; exact this
      apply C.sep c _ hc hw
      have h2e : dist n (line u0 u1 z) (line v0 v1 z) ≤ 2 * e := by
        have hm : dist n (line u0 u1 z) (line v0 v1 z) ≤
            dist n (line u0 u1 z1) c1 + dist n (line u0 u1 z2) c2 := by
          unfold dist
          refine Nat.le_trans ?_ (countP_or_le (List.range n)
            (fun i => decide (line u0 u1 z1 i ≠ c1 i)) (fun i => decide (line u0 u1 z2 i ≠ c2 i)))
          apply List.countP_mono_left
          intro i _ h
          simp only [decide_eq_true_eq, Bool.or_eq_true] at h ⊢
          refine Classical.byContradiction fun hno => ?_
          simp only [_root_.not_or, Classical.not_not] at hno
          obtain ⟨e0, e1⟩ := hsolve i hno.1 hno.2
          exact h (by simp only [line]; rw [e0, e1])
        omega
      have := dist_triangle n c (line u0 u1 z) (line v0 v1 z)
      have hk := dist_comm n c (line u0 u1 z)
      omega
    -- a containment failure needs a disagreeing position on the line
    have hfail : ∀ z, ¬ Strong C e u0 u1 z →
        ∃ i, i < n ∧ ((u0 i ≠ v0 i ∨ u1 i ≠ v1 i) ∧ line u0 u1 z i = line v0 v1 z i) := by
      intro z hz
      refine Classical.byContradiction fun hno => ?_
      apply hz
      intro c hc hdc
      refine ⟨v0, v1, hv0, hv1, fun i hi hci => ?_⟩
      have hc' := honline z c hc hdc i hi
      refine Classical.byContradiction fun hne => ?_
      apply hno
      refine ⟨i, hi, ?_, hci.trans hc'⟩
      by_cases h0 : u0 i = v0 i
      · exact Or.inr fun h1 => hne ⟨h0, h1⟩
      · exact Or.inl h0
    -- each disagreeing position is on the line for at most one challenge
    have hone : ∀ i, i < n → count Ks (fun z =>
        (u0 i ≠ v0 i ∨ u1 i ≠ v1 i) ∧ line u0 u1 z i = line v0 v1 z i) ≤ 1 := by
      intro i _
      apply count_le_one_of_unique hKs
      rintro a b ⟨hne, ha⟩ ⟨_, hb⟩
      simp only [line] at ha hb
      refine Classical.byContradiction fun hab => ?_
      have hab' : a - b ≠ 0 := fun h => hab (by grind)
      have hu1 : u1 i = v1 i := by
        have : (u1 i - v1 i) * (a - b) = 0 := by grind
        have hinv := Field.mul_inv_cancel hab'
        grind
      have hu0 : u0 i = v0 i := by grind
      rcases hne with h | h
      · exact h hu0
      · exact h hu1
    have hcount := count_exists_lt_le Ks
      (fun i z => (u0 i ≠ v0 i ∨ u1 i ≠ v1 i) ∧ line u0 u1 z i = line v0 v1 z i) 1 n hone
    refine Nat.le_trans (count_mono _ hfail) (Nat.le_trans hcount ?_)
    rw [Nat.mul_one]; exact Nat.le_max_right _ _

end ZkFormal.LineLemma
