import Mathlib

/-!
# Qrom.Transition — ANALYSIS Lemma 1: the one-query transition bound

Companion to `research/near-compression/weak-binding/ANALYSIS.md` §3, Lemma 1. It bounds
`‖A · cO_{xŷ} · B‖²` for the compressed oracle's one-point unitary, and is the single
quantitative input to the QROM game.

**Research package, not `zk-formal`.** `zk-formal` may not depend on Mathlib (DESIGN.md F4), so
anything proved here must be re-proved there before entering a certificate. Doing it here first
establishes the lemma is true as stated and pins the constants.

## The model

The output alphabet is `Y = Fin M` and the database register is `Ȳ = Option (Fin M)`, `none` being
`⊥`. ANALYSIS Fact B (CFHL21 Lemma 4.3) gives the **squared** entry bounds

* `⊥ → ⊥` is `0`,
* `|γ_{⊥,r}|² = |γ_{u,⊥}|² = 1/M`   (`u, r ∈ Y`),
* `|γ_{u,r}|² ≤ 9/M²`               (`u, r ∈ Y`, **`u ≠ r`**).

For zero frequency the query is the identity; its blocks between disjoint levels vanish.
All bounds below require disjoint source/target blocks.

The block norm is bounded by the Frobenius norm over the block, `Σ_{u∈A, r∈B} |γ_{u,r}|²`, which is
ANALYSIS's step 1.

## Results

`block_le_a`, `block_le_b`, `block_le_c` are the three cases of Lemma 1, proved directly on the
double sum. `consequence_chg` is the "changed set" form the weak-binding theorems consume.
-/

namespace Qrom

open scoped BigOperators

/-- `Ȳ = Option (Fin M)`: the database register's alphabet, `none` is `⊥`. -/
abbrev DB (M : ℕ) := Option (Fin M)

/-- Squared entries of a nonzero-frequency one-point query. Diagonal entries are
unrestricted. These are bounds on an actual entry function, not a model of a
unitary by a constant off-diagonal matrix. CFHL21 Lemma 4.3 supplies the bounds;
constructing its operator and the global database remains a separate obligation. -/
structure EntryBounds (M : ℕ) where
  entry : DB M → DB M → ℝ
  nonneg : ∀ u r, 0 ≤ entry u r
  bot_bot : entry none none = 0
  bot_r : ∀ r, entry none (some r) = 1 / (M : ℝ)
  u_bot : ∀ u, entry (some u) none = 1 / (M : ℝ)
  off_diag : ∀ u r, u ≠ r → entry (some u) (some r) ≤ 9 / ((M : ℝ) * M)

def amp {M : ℕ} (E : EntryBounds M) : DB M → DB M → ℝ := E.entry

theorem amp_nonneg {M : ℕ} (E : EntryBounds M) (u r : DB M) : 0 ≤ amp E u r :=
  E.nonneg u r

theorem amp_bot_r {M : ℕ} (E : EntryBounds M) (r : Fin M) : amp E none (some r) = 1 / (M : ℝ) :=
  E.bot_r r

theorem amp_u_bot {M : ℕ} (E : EntryBounds M) (u : Fin M) : amp E (some u) none = 1 / (M : ℝ) :=
  E.u_bot u

theorem amp_u_r_le {M : ℕ} (E : EntryBounds M) (u r : Fin M) (hne : u ≠ r) :
    amp E (some u) (some r) ≤ 9 / ((M : ℝ) * M) :=
  E.off_diag u r hne

/-- Different potential levels give disjoint blocks, hence no diagonal entries. -/
theorem disjoint_entry_ne {M : ℕ} {A B : Finset (DB M)} (hAB : Disjoint A B)
    {u r : DB M} (hu : u ∈ A) (hr : r ∈ B) : u ≠ r := by
  intro h
  subst r
  exact Finset.disjoint_left.mp hAB hu hr

/-- The Frobenius block sum `Σ_{u∈A, r∈B} |γ_{u,r}|²`. -/
noncomputable def blockSum {M : ℕ} (E : EntryBounds M) (A B : Finset (DB M)) : ℝ :=
  ∑ u ∈ A, ∑ r ∈ B, amp E u r

theorem blockSum_nonneg {M : ℕ} (E : EntryBounds M) (A B : Finset (DB M)) :
    0 ≤ blockSum E A B :=
  Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun r _ => amp_nonneg E u r

/-- `|Y| = M` bounds the size of any subset of the non-`⊥` values. -/
theorem card_some_le {M : ℕ} (S : Finset (DB M)) (hS : ∀ r ∈ S, r ≠ none) : S.card ≤ M := by
  have hsub : S ⊆ (Finset.univ.filter (fun r : DB M => r ≠ none)) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hS r hr
  have hcard : (Finset.univ.filter (fun r : DB M => r ≠ none)).card = M := by
    rw [Finset.card_filter]
    simp [Finset.card_univ, Fintype.card_option]
  calc S.card ≤ _ := Finset.card_le_card hsub
    _ = M := hcard

/-! ## Lemma 1(c): both sets avoid `⊥` -/

/-- **Lemma 1(c).** Every term is `u_r ≤ 9/M²`, and `|A|, |B| ≤ M`. -/
theorem block_le_c {M : ℕ} (hM : 0 < M) (E : EntryBounds M)
    (A B : Finset (DB M)) (hAB : Disjoint A B) (hA : ∀ u ∈ A, u ≠ none) (hB : ∀ r ∈ B, r ≠ none) :
    blockSum E A B ≤ 9 * (A.card : ℝ) * (B.card : ℝ) / ((M : ℝ) * (M : ℝ)) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hM2 : (0 : ℝ) < (M : ℝ) * (M : ℝ) := mul_pos hMpos hMpos
  have hbound : ∀ u ∈ A, ∀ r ∈ B, amp E u r ≤ 9 / ((M : ℝ) * (M : ℝ)) := by
    intro u hu r hr
    obtain ⟨a, rfl⟩ := Option.ne_none_iff_exists'.mp (hA u hu)
    obtain ⟨b, rfl⟩ := Option.ne_none_iff_exists'.mp (hB r hr)
    apply amp_u_r_le E a b
    intro hab
    apply disjoint_entry_ne hAB hu hr
    exact congrArg some hab
  calc blockSum E A B
      ≤ ∑ _u ∈ A, ∑ _r ∈ B, 9 / ((M : ℝ) * (M : ℝ)) := by
        refine Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun r hr => hbound u hu r hr
    _ = (A.card : ℝ) * ((B.card : ℝ) * (9 / ((M : ℝ) * (M : ℝ)))) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ = 9 * (A.card : ℝ) * (B.card : ℝ) / ((M : ℝ) * (M : ℝ)) := by ring

/-! ## Lemma 1(a): `⊥ ∉ A` -/

/-- **Lemma 1(a).** With `⊥ ∉ A`, each `u ∈ A` contributes `1/M` for `r = ⊥` (at most one such
`r`) and at most `9/M` across the `r ∈ Y` (at most `M` of them). -/
theorem block_le_a {M : ℕ} (hM : 0 < M) (E : EntryBounds M)
    (A B : Finset (DB M)) (hAB : Disjoint A B) (hA : ∀ u ∈ A, u ≠ none) :
    blockSum E A B ≤ (A.card : ℝ) * (1 / (M : ℝ) + 9 / (M : ℝ)) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hM2 : (0 : ℝ) < (M : ℝ) * (M : ℝ) := mul_pos hMpos hMpos
  -- split B by whether the value is ⊥
  have hsplit : blockSum E A B
      = ∑ u ∈ A, (∑ r ∈ B.filter (fun r => r = none), amp E u r
                + ∑ r ∈ B.filter (fun r => r ≠ none), amp E u r) := by
    unfold blockSum
    refine Finset.sum_congr rfl fun u _ => ?_
    have := Finset.sum_filter_add_sum_filter_not (s := B) (p := fun r => r = none)
      (f := fun r => amp E u r)
    simpa [eq_comm] using this.symm
  -- the ⊥ part: at most one value, contributing u_bot = 1/M
  have hbot : ∀ u ∈ A, ∑ r ∈ B.filter (fun r => r = none), amp E u r ≤ 1 / (M : ℝ) := by
    intro u hu
    obtain ⟨a, rfl⟩ := Option.ne_none_iff_exists'.mp (hA u hu)
    have hcard : (B.filter (fun r => r = none)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    have : ∑ r ∈ B.filter (fun r => r = none), amp E (some a) r
        = ((B.filter (fun r => r = none)).card : ℝ) * (1 / (M : ℝ)) := by
      have hconst : ∀ r ∈ B.filter (fun r => r = none), amp E (some a) r = 1 / (M : ℝ) := by
        intro r hr
        have hr' : r = none := (Finset.mem_filter.mp hr).2
        subst hr'
        exact amp_u_bot E a
      rw [Finset.sum_congr rfl hconst]
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [this]
    have : ((B.filter (fun r => r = none)).card : ℝ) ≤ 1 := by exact_mod_cast hcard
    calc ((B.filter (fun r => r = none)).card : ℝ) * (1 / (M : ℝ))
        ≤ 1 * (1 / (M : ℝ)) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = 1 / (M : ℝ) := one_mul _
  -- the Y part: at most M terms each ≤ 9/M²
  have hY : ∀ u ∈ A, ∑ r ∈ B.filter (fun r => r ≠ none), amp E u r ≤ 9 / (M : ℝ) := by
    intro u hu
    obtain ⟨a, rfl⟩ := Option.ne_none_iff_exists'.mp (hA u hu)
    have hbound : ∀ r ∈ B.filter (fun r => r ≠ none), amp E (some a) r ≤ 9 / ((M:ℝ)*(M:ℝ)) := by
      intro r hr
      obtain ⟨b, rfl⟩ := Option.ne_none_iff_exists'.mp (Finset.mem_filter.mp hr).2
      apply amp_u_r_le E a b
      intro hab
      apply disjoint_entry_ne hAB hu (Finset.mem_filter.mp hr).1
      exact congrArg some hab
    calc ∑ r ∈ B.filter (fun r => r ≠ none), amp E (some a) r
        ≤ ∑ _r ∈ B.filter (fun r => r ≠ none), 9 / ((M : ℝ) * (M : ℝ)) :=
          Finset.sum_le_sum hbound
      _ = ((B.filter (fun r => r ≠ none)).card : ℝ) * (9 / ((M : ℝ) * (M : ℝ))) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (M : ℝ) * (9 / ((M : ℝ) * (M : ℝ))) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have : (B.filter (fun r => r ≠ none)).card ≤ M :=
            card_some_le _ (fun r hr => (Finset.mem_filter.mp hr).2)
          exact_mod_cast this
      _ = 9 / (M : ℝ) := by field_simp
  calc blockSum E A B
      = ∑ u ∈ A, ((∑ r ∈ B.filter (fun r => r = none), amp E u r)
                + ∑ r ∈ B.filter (fun r => r ≠ none), amp E u r) := hsplit
    _ ≤ ∑ _u ∈ A, (1 / (M : ℝ) + 9 / (M : ℝ)) := by
        refine Finset.sum_le_sum fun u hu => add_le_add (hbot u hu) (hY u hu)
    _ = (A.card : ℝ) * (1 / (M : ℝ) + 9 / (M : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## Lemma 1(b): `⊥ ∈ A` -/

/-- **Lemma 1(b).** With `⊥ ∈ A` and `⊥ ∉ B`, the `u = ⊥` row contributes `1/M` per `r ∈ B`, and
each other row at most `9/M²` per `r ∈ B`. -/
theorem block_le_b {M : ℕ} (hM : 0 < M) (E : EntryBounds M)
    (A B : Finset (DB M)) (hAB : Disjoint A B) (hAb : none ∈ A) (hBn : none ∉ B) :
    blockSum E A B ≤ 10 * (B.card : ℝ) / (M : ℝ) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hM2 : (0 : ℝ) < (M : ℝ) * (M : ℝ) := mul_pos hMpos hMpos
  have hBY : ∀ r ∈ B, r ≠ none := fun r hr h => hBn (h ▸ hr)
  -- the ⊥ row
  have hbot : ∑ r ∈ B, amp E none r = (B.card : ℝ) * (1 / (M : ℝ)) := by
    have hconst : ∀ r ∈ B, amp E none r = 1 / (M : ℝ) := by
      intro r hr
      obtain ⟨b, rfl⟩ := Option.ne_none_iff_exists'.mp (hBY r hr)
      exact amp_bot_r E b
    rw [Finset.sum_congr rfl hconst]
    simp [Finset.sum_const, nsmul_eq_mul]
  -- the other rows: each ≤ |B| * 9/M²
  have hrow : ∀ u ∈ A.erase none, ∑ r ∈ B, amp E u r
      ≤ (B.card : ℝ) * (9 / ((M:ℝ)*(M:ℝ))) := by
    intro u hu
    have hun : u ≠ none := Finset.ne_of_mem_erase hu
    obtain ⟨a, rfl⟩ := Option.ne_none_iff_exists'.mp hun
    have hb : ∀ r ∈ B, amp E (some a) r ≤ (9 / ((M : ℝ) * (M : ℝ)) : ℝ) := by
      intro r hr
      obtain ⟨b, rfl⟩ := Option.ne_none_iff_exists'.mp (hBY r hr)
      apply amp_u_r_le E a b
      intro hab
      apply disjoint_entry_ne hAB (Finset.mem_erase.mp hu).2 hr
      exact congrArg some hab
    calc ∑ r ∈ B, amp E (some a) r
        ≤ ∑ _r ∈ B, (9 / ((M : ℝ) * (M : ℝ)) : ℝ) := Finset.sum_le_sum hb
      _ = (B.card : ℝ) * (9 / ((M : ℝ) * (M : ℝ))) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have hother : ∑ u ∈ A.erase none, ∑ r ∈ B, amp E u r
      ≤ ((A.erase none).card : ℝ) * ((B.card : ℝ) * (9 / ((M:ℝ)*(M:ℝ)))) := by
    calc ∑ u ∈ A.erase none, ∑ r ∈ B, amp E u r
        ≤ ∑ _u ∈ A.erase none, ((B.card : ℝ) * (9 / ((M:ℝ)*(M:ℝ))) : ℝ) :=
          Finset.sum_le_sum hrow
      _ = ((A.erase none).card : ℝ) * ((B.card : ℝ) * (9 / ((M:ℝ)*(M:ℝ)))) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have hcardErase : ((A.erase none).card : ℝ) ≤ (M : ℝ) := by
    have : (A.erase none).card ≤ M :=
      card_some_le _ (fun r hr => Finset.ne_of_mem_erase hr)
    exact_mod_cast this
  calc blockSum E A B
      = (∑ r ∈ B, amp E none r) + ∑ u ∈ A.erase none, ∑ r ∈ B, amp E u r := by
        unfold blockSum
        rw [← Finset.add_sum_erase A (fun u => ∑ r ∈ B, amp E u r) hAb]
    _ ≤ (B.card : ℝ) * (1 / (M : ℝ))
          + (M : ℝ) * ((B.card : ℝ) * (9 / ((M : ℝ) * (M : ℝ)))) := by
        rw [hbot]
        have hstep : ∑ u ∈ A.erase none, ∑ r ∈ B, amp E u r
            ≤ (M : ℝ) * ((B.card : ℝ) * (9 / ((M : ℝ) * (M : ℝ)))) :=
          le_trans hother (mul_le_mul_of_nonneg_right hcardErase (by positivity))
        linarith
    _ = 10 * (B.card : ℝ) / (M : ℝ) := by field_simp; ring

/-- Changed-set form used by a potential argument. The off-diagonal condition
is derived from i < j, not assumed of arbitrary matrix entries. -/
theorem consequence_chg {M : ℕ} (hM : 0 < M) (E : EntryBounds M)
    (κ : DB M → ℕ) (i j : ℕ) (hij : i < j) (Chg : Finset (DB M))
    (hstable : ∀ r, r ∉ Chg → κ r = κ none) :
    blockSum E (Finset.univ.filter fun r => j ≤ κ r)
      (Finset.univ.filter fun r => κ r = i) ≤ 10 * (Chg.card : ℝ) / (M : ℝ) := by
  classical
  let A := Finset.univ.filter fun r => j ≤ κ r
  let B := Finset.univ.filter fun r => κ r = i
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro r ha hb
    have ha' : j ≤ κ r := (Finset.mem_filter.mp ha).2
    have hb' : κ r = i := (Finset.mem_filter.mp hb).2
    omega
  have hpos : (0 : ℝ) < M := by exact_mod_cast hM
  change blockSum E A B ≤ _
  by_cases hnone : none ∈ A
  · have hBn : none ∉ B := fun hb => Finset.disjoint_left.mp hAB hnone hb
    have hsub : B ⊆ Chg := by
      intro r hr
      by_contra hn
      have hr' : κ r = i := (Finset.mem_filter.mp hr).2
      have hb : j ≤ κ none := (Finset.mem_filter.mp hnone).2
      have heq := hstable r hn
      omega
    have hc : (B.card : ℝ) ≤ Chg.card := by exact_mod_cast Finset.card_le_card hsub
    exact (block_le_b hM E A B hAB hnone hBn).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num)) (by positivity))
  · have hAn : ∀ r ∈ A, r ≠ none := fun r hr heq => hnone (heq ▸ hr)
    have hsub : A ⊆ Chg := by
      intro r hr
      by_contra hn
      apply hnone
      have heq := hstable r hn
      have hr' : j ≤ κ r := (Finset.mem_filter.mp hr).2
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hc : (A.card : ℝ) ≤ Chg.card := by exact_mod_cast Finset.card_le_card hsub
    have heq : (A.card : ℝ) * (1 / (M : ℝ) + 9 / M) = 10 * A.card / M := by ring
    have h := block_le_a hM E A B hAB hAn
    rw [heq] at h
    exact h.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num)) (by positivity))

/-- A zero-frequency query is the identity and cannot change the potential level. -/
theorem identity_block_zero {M : ℕ} (A B : Finset (DB M)) (hAB : Disjoint A B) :
    (∑ u ∈ A, ∑ r ∈ B, (if u = r then (1 : ℝ) else 0)) = 0 := by
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro r hr
  simp [disjoint_entry_ne hAB hu hr]

end Qrom
