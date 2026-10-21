import Mathlib

/-!
# Qrom.FactA — the real-oracle → measured-database step

Companion to `research/near-compression/weak-binding/ANALYSIS.md` §3, Fact A (Zhandry; CFHL21
Cor 4.2), and to `PROOF.md` Theorem 6.4 step 7:

  `√p ≤ √p' + √(ℓ/N_min)`,

where `p` is the probability that the real oracle agrees with the adversary's claimed answers at
`ℓ` points, and `p'` the same probability for the *measured* compressed-oracle database.

## Scope

`hits_le` and `fibre_card` prove finite counting facts. They do not prove the
quantum replacement inequality. `Replacement` names the cited square-root
inequality exactly; `fact_a` squares it without dropping the cross term.
The earlier probability-additive premise `p ≤ p' + ℓ/N` was stronger than the
cited result and has been removed from this interface.

This package is research (`Qrom`, Mathlib allowed); `zk-formal` may not depend on Mathlib.
-/

namespace Qrom

open scoped BigOperators
open Finset

/-- `√(a + b) ≤ √a + √b` for nonnegative reals. -/
theorem sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h : Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  rwa [Real.sqrt_sq (by positivity)] at h

/-- `√b ≤ √b` — the slack term is nonnegative, so the bound is the natural one. -/
theorem sqrt_le_add_sqrt (p p' slack : ℝ) (hp : 0 ≤ p) (hp' : 0 ≤ p')
    (h : p ≤ p' + slack) (hslack : 0 ≤ slack) :
    Real.sqrt p ≤ Real.sqrt p' + Real.sqrt slack := by
  calc Real.sqrt p ≤ Real.sqrt (p' + slack) := Real.sqrt_le_sqrt h
    _ ≤ Real.sqrt p' + Real.sqrt slack := sqrt_add_le p' slack hp' hslack

/-- The number of `t`-coordinate functions disagreeing with a fixed point at coordinate `x` is
`N^(t-1)`: fixing one coordinate leaves `t−1` free. -/
theorem card_ne (t : ℕ) (x : Fin t) : Fintype.card {y : Fin t // y ≠ x} = t - 1 := by
  rw [Fintype.card_subtype]
  have : Finset.univ.filter (fun y : Fin t => ¬ y = x) = Finset.univ.erase x := by
    ext y; simp [Finset.mem_erase]
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_fin]

/-- Each single-point fibre has exactly `N^(t-1)` functions. -/
theorem fibre_card (t N : ℕ) (hN : 0 < N) (x : Fin t) :
    Fintype.card { f : Fin t → Fin N // f x = ⟨0, hN⟩ } = N ^ (t - 1) := by
  have h : { f : Fin t → Fin N // f x = ⟨0, hN⟩ } ≃ ({y : Fin t // y ≠ x} → Fin N) := by
    refine ⟨fun f y => f.1 y.1, fun g => ⟨fun z => if hz : z = x then ⟨0, hN⟩ else g ⟨z, hz⟩, ?_⟩,
      ?_, ?_⟩
    · simp
    · intro f; ext z; by_cases hz : z = x
      · subst hz; simp [f.2]
      · simp [hz]
    · intro g; ext y; simp [y.2]
  rw [Fintype.card_congr h, Fintype.card_fun, card_ne, Fintype.card_fin]

/-- **The counting step (union bound over queried points).**

The number of oracles that hit a prescribed value at *any* of `T`'s coordinates is at most
`|T| · N^(t−1)`: the union bound over the per-coordinate fibres. -/
theorem hits_le (t N : ℕ) (hN : 0 < N) (T : Finset (Fin t)) :
    (Finset.univ.filter (fun f : Fin t → Fin N => ∃ x ∈ T, f x = ⟨0, hN⟩)).card
      ≤ T.card * N ^ (t - 1) := by
  classical
  set bad := fun x : Fin t => Finset.univ.filter (fun f : Fin t → Fin N => f x = ⟨0, hN⟩)
    with hbad
  have hunion : (Finset.univ.filter (fun f : Fin t → Fin N => ∃ x ∈ T, f x = ⟨0, hN⟩))
      ⊆ T.biUnion bad := by
    intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨x, hx, hfx⟩ := hf
    exact Finset.mem_biUnion.mpr ⟨x, hx, by simp [hbad, hfx]⟩
  have hfib : ∀ x ∈ T, (bad x).card = N ^ (t - 1) := by
    intro x _
    rw [hbad]
    simp only
    rw [← Fintype.card_subtype]
    exact fibre_card t N hN x
  calc (Finset.univ.filter (fun f : Fin t → Fin N => ∃ x ∈ T, f x = ⟨0, hN⟩)).card
      ≤ (T.biUnion bad).card := Finset.card_le_card hunion
    _ ≤ ∑ x ∈ T, (bad x).card := Finset.card_biUnion_le
    _ = ∑ _x ∈ T, N ^ (t - 1) := Finset.sum_congr rfl hfib
    _ = T.card * N ^ (t - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        push_cast
        ring

/-- The replacement inequality is supplied in its actual CFHL21 Corollary 4.2
form. It is not a probability-additive inequality: squaring produces a cross term.
This declaration is an interface, not a proof of the oracle replacement theorem. -/
def Replacement (p p' slack : ℝ) : Prop :=
  Real.sqrt p ≤ Real.sqrt p' + Real.sqrt slack

/-- Convert the cited square-root bound to a probability bound, retaining the cross term. -/
theorem fact_a (p p' slack : ℝ) (hp : 0 ≤ p)
    (hreplace : Replacement p p' slack) :
    p ≤ (Real.sqrt p' + Real.sqrt slack) ^ 2 := by
  have hs := Real.sq_sqrt hp
  have hn := Real.sqrt_nonneg p
  have hn' := Real.sqrt_nonneg p'
  have hns := Real.sqrt_nonneg slack
  unfold Replacement at hreplace
  nlinarith

end Qrom
