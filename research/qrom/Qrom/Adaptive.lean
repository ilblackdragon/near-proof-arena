import Mathlib

/-!
# Adaptive exceptional-set counting for classical verifier challenges

The exceptional set can depend on the complete preceding challenge history.
A uniform bound over histories gives a union bound without assuming those
exceptional sets are fixed in advance. This is a classical finite-sampling
lemma; it does not replace the quantum Fiat--Shamir reduction or establish
that the implemented sampler has this distribution.
-/
namespace Qrom.Adaptive
open scoped BigOperators
variable {F : Type} [Fintype F] [DecidableEq F]

def prepend {n : ℕ} (x : F) (rest : Fin n → F) : Fin (n+1) → F := Fin.cons x rest

def badRuns (bad : List F → Finset F) (hist : List F) :
    (n : ℕ) → Finset (Fin n → F)
  | 0 => ∅
  | n+1 =>
      ((bad hist) ×ˢ (Finset.univ : Finset (Fin n → F))).image
        (fun p => (prepend p.1 p.2 : Fin (n+1) → F)) ∪
      Finset.univ.biUnion (fun x => (badRuns bad (hist ++ [x]) n).image (prepend x))

theorem cons_mem_badRuns (bad : List F → Finset F) (hist : List F)
    (n : ℕ) (x : F) (rest : Fin n → F) :
    prepend x rest ∈ badRuns bad hist (n+1) ↔
      x ∈ bad hist ∨ rest ∈ badRuns bad (hist ++ [x]) n := by
  simp [badRuns, prepend, Fin.cons_inj]

def budgetSum (E : ℕ → ℕ) (start : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => E start + budgetSum E (start+1) n

/-- Every history is charged its own exceptional set. Overlaps between bad
levels only make the bound more conservative. -/
theorem badRuns_card (bad : List F → Finset F) (E : ℕ → ℕ)
    (hE : ∀ hist, (bad hist).card ≤ E hist.length)
    (hist : List F) (n : ℕ) :
    (badRuns bad hist n).card ≤
      Fintype.card F ^ (n-1) * budgetSum E hist.length n := by
  induction n generalizing hist with
  | zero => simp [badRuns, budgetSum]
  | succ n ih =>
    have hhead :
        (((bad hist) ×ˢ (Finset.univ : Finset (Fin n → F))).image
          (fun p => (prepend p.1 p.2 : Fin (n+1) → F))).card ≤ E hist.length * Fintype.card F ^ n := by
      refine (Finset.card_image_le).trans ?_
      simp only [Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
      exact Nat.mul_le_mul_right _ (hE hist)
    have htail :
        (Finset.univ.biUnion fun x => (badRuns bad (hist ++ [x]) n).image (prepend x)).card ≤
          Fintype.card F * (Fintype.card F ^ (n-1) * budgetSum E (hist.length+1) n) := by
      refine Finset.card_biUnion_le.trans ?_
      calc
        _ ≤ ∑ _x : F, Fintype.card F ^ (n-1) * budgetSum E (hist.length+1) n := by
          refine Finset.sum_le_sum fun x _ => ?_
          exact Finset.card_image_le.trans (by simpa using ih (hist ++ [x]))
        _ = _ := by simp
    have hu := Finset.card_union_le
      (((bad hist) ×ˢ (Finset.univ : Finset (Fin n → F))).image
        (fun p => (prepend p.1 p.2 : Fin (n+1) → F)))
      (Finset.univ.biUnion fun x => (badRuns bad (hist ++ [x]) n).image (prepend x))
    change (badRuns bad hist (n+1)).card ≤ _ at hu
    have hc := hu.trans (Nat.add_le_add hhead htail)
    cases n with
    | zero =>
        simpa [budgetSum] using hc
    | succ n =>
        calc
          _ ≤ E hist.length * Fintype.card F ^ (n+1) +
              Fintype.card F * (Fintype.card F ^ n * budgetSum E (hist.length+1) (n+1)) :=
            by simpa only [Nat.add_sub_cancel] using hc
          _ = _ := by simp only [budgetSum, Nat.add_sub_cancel, pow_succ]; ring

/-- Normalized uniform-challenge bound, with explicit nonempty alphabet and
positive sequence length. This permits adaptive received words via `hist`. -/
theorem badRuns_probability [Nonempty F] (bad : List F → Finset F) (E : ℕ → ℕ)
    (hE : ∀ hist, (bad hist).card ≤ E hist.length)
    (hist : List F) (n : ℕ) (hn : 0 < n) :
    ((badRuns bad hist n).card : ℚ) / (Fintype.card F : ℚ)^n ≤
      (budgetSum E hist.length n : ℚ) / (Fintype.card F : ℚ) := by
  cases n with
  | zero => omega
  | succ n =>
      have hN : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
      have hc : ((badRuns bad hist (n+1)).card : ℚ) ≤
          (Fintype.card F : ℚ)^n * (budgetSum E hist.length (n+1) : ℚ) := by
        exact_mod_cast (badRuns_card bad E hE hist (n+1))
      apply (div_le_div_iff₀ (pow_pos hN _) hN).mpr
      calc
        _ ≤ ((Fintype.card F : ℚ)^n * (budgetSum E hist.length (n+1) : ℚ)) *
            (Fintype.card F : ℚ) := mul_le_mul_of_nonneg_right hc hN.le
        _ = _ := by rw [pow_succ]; ring

end Qrom.Adaptive

#print axioms Qrom.Adaptive.badRuns_card
#print axioms Qrom.Adaptive.badRuns_probability
