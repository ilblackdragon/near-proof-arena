import Mathlib

/-!
# A fixed concrete hash is not an independent random oracle

Split a finite random function at one fixed input: its output is `Y`, and all
other outputs/random coins are `Z`. `Equiv.funSplitAt` supplies this product
representation for a finite oracle domain. Acceptance may depend arbitrarily
on the distinguished output; we do not condition its distribution on acceptance.

If an accepting execution contains a fixed concrete pair `(m, fixed)`, oracle
consistency implies the first coordinate equals `fixed`. At most 1/|Y| of the
whole probability space can satisfy this. A runtime limit does not change this
count. Applying it to a protocol still requires proving that the fixed pair
occurs in the extracted trace and establishing completeness. This is not an
attack on concrete SHA-384 or on the recursive protocol.
-/
namespace Qrom.OracleBridge
variable {Y Z : Type} [Fintype Y] [Fintype Z] [DecidableEq Y] [DecidableEq Z]

def consistent (fixed : Y) : Finset (Y × Z) :=
  ({fixed} : Finset Y) ×ˢ Finset.univ

theorem consistent_card (fixed : Y) :
    (consistent (Z := Z) fixed).card = Fintype.card Z := by
  simp [consistent]

theorem accepted_consistent_card (accepted : Finset (Y × Z)) (fixed : Y) :
    (accepted ∩ consistent fixed).card ≤ Fintype.card Z := by
  calc
    _ ≤ (consistent (Z := Z) fixed).card := Finset.card_le_card Finset.inter_subset_right
    _ = _ := consistent_card fixed

theorem acceptance_le_failure_add_fiber (accepted : Finset (Y × Z)) (fixed : Y) :
    accepted.card ≤ (accepted \ consistent fixed).card + Fintype.card Z := by
  have h := Finset.card_sdiff_add_card_inter accepted (consistent fixed)
  have hc := accepted_consistent_card accepted fixed
  omega

noncomputable def probability (event : Finset (Y × Z)) : ℝ :=
  (event.card : ℝ) / (Fintype.card (Y × Z) : ℝ)

theorem consistency_probability [Nonempty Y] [Nonempty Z] (fixed : Y) :
    probability (consistent (Z := Z) fixed) = 1 / (Fintype.card Y : ℝ) := by
  have hz : (Fintype.card Z : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hy : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [probability, consistent_card, Fintype.card_prod, Nat.cast_mul]
  field_simp

/-- Acceptance ≥ 1-δ implies bridge failure ≥ 1-δ-1/|Y|, provided consistency
requires this fixed pair. No efficient soundness attack is asserted. -/
theorem bridge_failure_lower_bound [Nonempty Y] [Nonempty Z]
    (accepted : Finset (Y × Z)) (fixed : Y) (δ : ℝ)
    (haccept : 1 - δ ≤ probability accepted) :
    1 - δ - 1 / (Fintype.card Y : ℝ) ≤
      probability (accepted \ consistent fixed) := by
  have hd : (0 : ℝ) < Fintype.card (Y × Z) := by
    exact_mod_cast Fintype.card_pos
  have h := acceptance_le_failure_add_fiber accepted fixed
  have hc : (accepted.card : ℝ) ≤
      ((accepted \ consistent fixed).card : ℝ) + (Fintype.card Z : ℝ) := by
    exact_mod_cast h
  have hh := div_le_div_of_nonneg_right hc hd.le
  rw [add_div] at hh
  have he : (Fintype.card Z : ℝ) / (Fintype.card (Y × Z) : ℝ) =
      1 / (Fintype.card Y : ℝ) := by
    simpa only [probability, consistent_card] using
      (consistency_probability (Z := Z) fixed)
  rw [he] at hh
  unfold probability at haccept ⊢
  linarith

end Qrom.OracleBridge

#print axioms Qrom.OracleBridge.bridge_failure_lower_bound

namespace Qrom.OracleBridge
open MeasureTheory

/-- The same obstruction for arbitrary probability spaces (including arbitrary
acceptance randomness), once the oracle's marginal bound is supplied. -/
theorem bridge_failure_measure {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (accepted consistent : Set Ω)
    (δ marginal : ℝ) (haccept : 1 - δ ≤ μ.real accepted)
    (hconsistent : μ.real consistent ≤ marginal) :
    1 - δ - marginal ≤ μ.real (accepted \ consistent) := by
  have hsub : accepted ⊆ (accepted \ consistent) ∪ consistent := by
    intro x hx
    by_cases hc : x ∈ consistent
    · exact Or.inr hc
    · exact Or.inl ⟨hx, hc⟩
  have h : μ accepted ≤ μ (accepted \ consistent) + μ consistent :=
    (measure_mono hsub).trans (measure_union_le _ _)
  have ht : μ (accepted \ consistent) + μ consistent ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, measure_ne_top μ _⟩
  have hr := ENNReal.toReal_mono ht h
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hr
  change μ.real accepted ≤ μ.real (accepted \ consistent) + μ.real consistent at hr
  linarith

end Qrom.OracleBridge

#print axioms Qrom.OracleBridge.bridge_failure_measure
