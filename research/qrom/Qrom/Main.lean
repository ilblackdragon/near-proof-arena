import Mathlib
import Qrom.Path
import Qrom.FactA
import Qrom.Operator
import Qrom.Instantiate

/-!
# Conditional operator-to-probability bound

This theorem composes contraction/block bounds, the path lemma, a measured-event
projection bound, and the *square-root* replacement inequality. `Ahat` bounds an
amplitude, not a probability. The squared conclusion keeps that distinction.

This is not yet an instantiation for the paper's transcript family. The concrete
database, potential, block estimates, measured-event inclusion and replacement
must be supplied; they do not follow from the algebraic theorem alone.
-/
namespace Qrom
open scoped BigOperators
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Operator-level premises, rather than an assumed mass recurrence. A complex
Hilbert space can be regarded as a real normed space for this argument.
`step` includes the adversary's inter-query evolution; proving its block bounds
requires showing that this evolution preserves database levels. -/
structure PotentialEvolution (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℕ → ℕ → ℝ) where
  tail : ℕ → E →L[ℝ] E
  exactLevel : ℕ → E →L[ℝ] E
  tail_contract : ∀ j, ‖tail j‖ ≤ 1
  exact_idem : ∀ i, exactLevel i ∘L exactLevel i = exactLevel i
  decompose : ∀ j ψ, ψ = tail j ψ + ∑ i ∈ Finset.range j, exactLevel i ψ
  exact_le_tail : ∀ i ψ, ‖exactLevel i ψ‖ ≤ ‖tail i ψ‖
  step : ℕ → E →L[ℝ] E
  step_contract : ∀ s, ‖step s‖ ≤ 1
  ψ : ℕ → E
  evolves : ∀ s, ψ (s+1) = step s (ψ s)
  init : ∀ j, ‖tail j (ψ 0)‖ ≤ Ahat G 0 j
  block : ∀ s j i, i < j → ‖tail j ∘L step s ∘L exactLevel i‖ ≤ G i j

theorem PotentialEvolution.recurrence {G : ℕ → ℕ → ℝ}
    (S : PotentialEvolution E G) (hG : ∀ i j, 0 ≤ G i j) (s j : ℕ) :
    ‖S.tail j (S.ψ (s+1))‖ ≤ ‖S.tail j (S.ψ s)‖ +
      ∑ i ∈ Finset.range j, G i j * ‖S.tail i (S.ψ s)‖ := by
  rw [S.evolves]
  have h := mass_recurrence (S.tail j) (S.tail_contract j) (S.step s)
    (S.step_contract s) S.exactLevel S.exact_idem j (fun i => G i j)
    (S.decompose j) (fun i hi => S.block s j i (Finset.mem_range.mp hi)) (S.ψ s)
  refine h.trans (add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_))
  exact mul_le_mul_of_nonneg_left (S.exact_le_tail i (S.ψ s)) (hG i j)

theorem PotentialEvolution.amplitude_bound {G : ℕ → ℕ → ℝ}
    (S : PotentialEvolution E G) (hG : ∀ i j, 0 ≤ G i j) (t level : ℕ) :
    ‖S.tail level (S.ψ t)‖ ≤ Ahat G t level :=
  path_bound G hG (fun s j => ‖S.tail j (S.ψ s)‖) S.init (S.recurrence hG) t level

/-- The measured bad event is contained in the projected bad subspace. The
replacement premise is the cited square-root form. There is no assumed final
probability bound; it is derived from the operators. -/
theorem qrom_bound (G : ℕ → ℕ → ℝ) (hG : ∀ i j, 0 ≤ G i j)
    (S : PotentialEvolution E G) (t level : ℕ) (p p' slack : ℝ)
    (hp : 0 ≤ p) (hp' : 0 ≤ p')
    (hmeasured : p' ≤ ‖S.tail level (S.ψ t)‖ ^ 2)
    (hreplace : Replacement p p' slack) :
    p ≤ (Ahat G t level + Real.sqrt slack) ^ 2 := by
  have hmass := S.amplitude_bound hG t level
  have hroot : Real.sqrt p' ≤ ‖S.tail level (S.ψ t)‖ := by
    have h := Real.sqrt_le_sqrt hmeasured
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  have hprob : Real.sqrt p ≤ Ahat G t level + Real.sqrt slack := by
    exact hreplace.trans (add_le_add (hroot.trans hmass) le_rfl)
  have ha := Ahat_nonneg hG t level
  have hs := Real.sqrt_nonneg slack
  have hpRoot := Real.sqrt_nonneg p
  have hpSq := Real.sq_sqrt hp
  nlinarith
/-- The level-zero amplitude majorant is one. -/
theorem Ahat_level_zero (G : ℕ → ℕ → ℝ) (t : ℕ) : Ahat G t 0 = 1 := by
  induction t with
  | zero => simp [Ahat, W]
  | succ t ih => rw [Ahat_step]; simpa using ih

/-- Boolean bad events have a single crossing: the amplitude bound is q·g. -/
theorem Ahat_level_one (G : ℕ → ℕ → ℝ) (t : ℕ) :
    Ahat G t 1 = (t : ℝ) * G 0 1 := by
  induction t with
  | zero => simp [Ahat, W]
  | succ t ih =>
    rw [Ahat_step, ih]
    simp [Ahat_level_zero, Nat.cast_add, Nat.cast_one, add_mul]

/-- The exact conditional numerical shape used by a zero-tolerance database
argument. No protocol-specific estimate on G 0 1 is asserted here. -/
theorem qrom_binary_bound (G : ℕ → ℕ → ℝ) (hG : ∀ i j, 0 ≤ G i j)
    (S : PotentialEvolution E G) (t : ℕ) (p p' slack : ℝ)
    (hp : 0 ≤ p) (hp' : 0 ≤ p')
    (hmeasured : p' ≤ ‖S.tail 1 (S.ψ t)‖ ^ 2)
    (hreplace : Replacement p p' slack) :
    p ≤ ((t : ℝ) * G 0 1 + Real.sqrt slack) ^ 2 := by
  simpa only [Ahat_level_one] using qrom_bound G hG S t 1 p p' slack hp hp' hmeasured hreplace

end Qrom
