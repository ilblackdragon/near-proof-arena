import Mathlib

/-!
# The native field sampler's accepted fibers

`ShaTranscript::sample` accepts a uniform 32-bit candidate below `2*p` and
returns its residue modulo p. Every residue has exactly two accepted preimages.
This establishes the counting ingredient for uniform field sampling. It does
not justify a bound on rejection-loop length or quantum-selected-key sampling.
-/
namespace Qrom.Sampler

theorem accepted_fiber (p r : ℕ) (hp : 0 < p) (hr : r < p) :
    ((Finset.range (2*p)).filter fun n => n % p = r) = {r, r+p} := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hn, hm⟩
    by_cases hlt : n < p
    · rw [Nat.mod_eq_of_lt hlt] at hm
      exact Or.inl hm
    · have hle : p ≤ n := by omega
      have hsub : n-p < p := by omega
      rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt hsub] at hm
      right
      omega
  · rintro (rfl | rfl)
    · exact ⟨by omega, Nat.mod_eq_of_lt hr⟩
    · refine ⟨by omega, ?_⟩
      simp [Nat.mod_eq_of_lt hr]

theorem accepted_fiber_card (p r : ℕ) (hp : 0 < p) (hr : r < p) :
    ((Finset.range (2*p)).filter fun n => n % p = r).card = 2 := by
  rw [accepted_fiber p r hp hr]
  have hne : r ≠ r+p := by omega
  exact Finset.card_pair_eq_two_iff.mpr hne

theorem conditional_residue_probability (p r : ℕ) (hp : 0 < p) (hr : r < p) :
    (((Finset.range (2*p)).filter fun n => n % p = r).card : ℚ) / (2*p : ℕ) =
      1 / (p : ℚ) := by
  rw [accepted_fiber_card p r hp hr]
  have hne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  field_simp

end Qrom.Sampler

#print axioms Qrom.Sampler.conditional_residue_probability
