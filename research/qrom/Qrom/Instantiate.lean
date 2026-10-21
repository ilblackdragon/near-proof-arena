import Mathlib
import Qrom.Path

/-!
# Qrom.Instantiate — a Hilbert-space model of the QROM potential

`Qrom.Path` proves the path lemma (ANALYSIS Lemma 2) for abstract nonnegative sequences. This
file builds those sequences from an actual state in a real Hilbert space, which is the gap
`README.md` used to list.

## The model

The compressed-oracle state space is `H = EuclideanSpace ℝ ι`, where `ι` indexes the
(orthogonal) potential levels together with the database content. For a level predicate `P`, the
**coordinate projection** `proj P` zeroes every coordinate outside `P`; it is the diagonal
projector of the analysis.

* `norm_proj_sq` — `‖proj P x‖² = Σ_{i ∈ P} x_i²`, i.e. the projector is an orthogonal projection
  and its norm is the mass it keeps.
* `norm_proj_le` — `‖proj P x‖ ≤ ‖x‖` (the projector is a contraction).
* `norm_proj_mono` — nested level predicates give monotone masses, which is what makes
  `a s j = ‖Π_{≥j} ψ_s‖` decreasing in `j`.

## The step

`mass_recurrence` derives a norm recurrence from supplied contractions, projector
idempotence, decomposition, and block bounds. `LevelStep` is an older abstract
interface that assumes the recurrence. The capstone in `Main.lean` instead uses
`PotentialEvolution` and derives it from operator premises.

No adversary unitary or compressed-oracle operator is constructed here.
Adversary operations act on the workspace/query registers, not on the database;
their commutation with database-level projectors must be established in an actual
quantum instantiation. The real coordinate model here is illustrative.
-/

namespace Qrom

open scoped BigOperators
open Finset


variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Coordinate projection onto a predicate. -/
noncomputable def proj (P : ι → Prop) [DecidablePred P] (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.equiv 2 (ι → ℝ) |>.symm (fun i => if P i then x.ofLp i else 0)

@[simp] theorem proj_ofLp (P : ι → Prop) [DecidablePred P] (x : EuclideanSpace ℝ ι) (i : ι) :
    (proj P x).ofLp i = if P i then x.ofLp i else 0 := rfl

theorem norm_sq_eq_sum (x : EuclideanSpace ℝ ι) :
    ‖x‖ ^ 2 = ∑ i, (x.ofLp i) ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

theorem norm_proj_sq (P : ι → Prop) [DecidablePred P] (x : EuclideanSpace ℝ ι) :
    ‖proj P x‖ ^ 2 = ∑ i, if P i then (x.ofLp i) ^ 2 else 0 := by
  rw [norm_sq_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [proj_ofLp]
  by_cases h : P i <;> simp [h]

theorem norm_proj_le (P : ι → Prop) [DecidablePred P] (x : EuclideanSpace ℝ ι) :
    ‖proj P x‖ ≤ ‖x‖ := by
  have h : ‖proj P x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_proj_sq, norm_sq_eq_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases h : P i
    · simp [h]
    · simp only [h, if_false, Pi.zero_apply]; positivity
  nlinarith [norm_nonneg (proj P x), norm_nonneg x]

theorem norm_proj_nonneg (P : ι → Prop) [DecidablePred P] (x : EuclideanSpace ℝ ι) :
    0 ≤ ‖proj P x‖ := norm_nonneg _

/-- Nested projections: monotone in the predicate. -/
theorem norm_proj_mono {P Q : ι → Prop} [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ i, P i → Q i) (x : EuclideanSpace ℝ ι) :
    ‖proj P x‖ ≤ ‖proj Q x‖ := by
  have h : ‖proj P x‖ ^ 2 ≤ ‖proj Q x‖ ^ 2 := by
    rw [norm_proj_sq, norm_proj_sq]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hP : P i
    · have hQ := hPQ i hP
      simp [hP, hQ]
    · simp [hP]; positivity
  nlinarith [norm_nonneg (proj P x), norm_nonneg (proj Q x)]

/-- The coordinate projection is idempotent: this is what makes it a *projector* rather than an
arbitrary contraction, and it is the hypothesis `mass_recurrence` needs. -/
theorem proj_idem (P : ι → Prop) [DecidablePred P] (x : EuclideanSpace ℝ ι) :
    proj P (proj P x) = proj P x := by
  ext i
  simp only [proj_ofLp]
  by_cases h : P i <;> simp [h]

/-! ## Deriving the per-level recurrence from block operator norms

ANALYSIS §3 says: "for diagonal `Π`, `‖Π_{≥j} cO Π_{=i} P_{≤s}‖` is the maximum over the block
norms in Lemma 1". This is the step from Lemma 1 to the recurrence `path_bound` consumes.

The subtlety, which the prose does not spell out: the level operators `Π_{=i}` are **idempotent
projectors**. Without idempotence the step is false — the block bound controls `cO` applied to
`Π_{=i}ψ`, not to `ψ`. With it, `(Π_j ∘ cO ∘ Π_{=i})(Π_{=i}ψ) = (Π_j ∘ cO ∘ Π_{=i})ψ`, and
`le_opNorm` can be applied at `Π_{=i}ψ`.
-/

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- The fix: P i must be IDEMPOTENT (it is a projector), so that
-- (Pj ∘L cO ∘L Pi) (Pi ψ) = (Pj ∘L cO ∘L Pi) ψ, letting le_opNorm be applied at Pi ψ.
theorem mass_recurrence (Pj : E →L[ℝ] E) (hPj : ‖Pj‖ ≤ 1) (cO : E →L[ℝ] E)
    (hCO : ‖cO‖ ≤ 1)
    (P : ℕ → E →L[ℝ] E) (hidem : ∀ i, P i ∘L P i = P i) (n : ℕ) (g : ℕ → ℝ)
    (hdecomp : ∀ ψ, ψ = Pj ψ + ∑ i ∈ Finset.range n, P i ψ)
    (hblock : ∀ i ∈ Finset.range n, ‖Pj ∘L cO ∘L P i‖ ≤ g i) (ψ : E) :
    ‖Pj (cO ψ)‖ ≤ ‖Pj ψ‖ + ∑ i ∈ Finset.range n, g i * ‖P i ψ‖ := by
  have h1 : ‖Pj (cO ψ)‖ ≤ ‖Pj (cO (Pj ψ))‖ + ‖Pj (cO (∑ i ∈ Finset.range n, P i ψ))‖ := by
    have heq : cO ψ = cO (Pj ψ) + cO (∑ i ∈ Finset.range n, P i ψ) := by
      conv_lhs => rw [hdecomp ψ]; rw [map_add]
    rw [heq, map_add]; exact norm_add_le _ _
  have h2 : ‖Pj (cO (Pj ψ))‖ ≤ ‖Pj ψ‖ := by
    calc ‖Pj (cO (Pj ψ))‖ ≤ ‖Pj‖ * ‖cO (Pj ψ)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖cO (Pj ψ)‖ := by gcongr
      _ ≤ 1 * (‖cO‖ * ‖Pj ψ‖) := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (1 * ‖Pj ψ‖) := by gcongr
      _ = ‖Pj ψ‖ := by ring
  have h3 : ‖Pj (cO (∑ i ∈ Finset.range n, P i ψ))‖ ≤ ∑ i ∈ Finset.range n, g i * ‖P i ψ‖ := by
    rw [map_sum, map_sum]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i hi => ?_)
    -- the idempotence trick: (Pj∘cO∘Pi)(Pi ψ) = (Pj∘cO∘Pi) ψ
    have hid : (Pj ∘L cO ∘L P i) (P i ψ) = Pj (cO (P i ψ)) := by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_comp', Function.comp_apply]
      rw [show P i (P i ψ) = (P i ∘L P i) ψ from rfl, hidem i]
    calc ‖Pj (cO (P i ψ))‖ = ‖(Pj ∘L cO ∘L P i) (P i ψ)‖ := by rw [hid]
      _ ≤ ‖Pj ∘L cO ∘L P i‖ * ‖P i ψ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ g i * ‖P i ψ‖ := by gcongr; exact hblock i hi
  linarith [add_le_add h2 h3]
/-! ## The level structure on a real Hilbert space -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The mass at level `≥ j`: the norm of the projection of the state onto the level-`≥j` part. -/
noncomputable def mass (lev : ι → ℕ) (ψ : EuclideanSpace ℝ ι) (j : ℕ) : ℝ :=
  ‖proj (fun i => j ≤ lev i) ψ‖

theorem mass_nonneg (lev : ι → ℕ) (ψ : EuclideanSpace ℝ ι) (j : ℕ) : 0 ≤ mass lev ψ j :=
  norm_proj_nonneg _ _

/-- Masses are decreasing in the level: `Π_{≥j'}` is a sub-projection of `Π_{≥j}` for `j ≤ j'`. -/
theorem mass_antitone (lev : ι → ℕ) (ψ : EuclideanSpace ℝ ι) {j j' : ℕ} (h : j ≤ j') :
    mass lev ψ j' ≤ mass lev ψ j :=
  norm_proj_mono (fun i hi => le_trans h hi) ψ

/-- **A level step from an actual state.** `ψ` is the state sequence and `step` is the
transition bound the compressed-oracle analysis establishes for it. -/
structure LevelStep (G : ℕ → ℕ → ℝ) (lev : ι → ℕ) where
  /-- the state after `s` queries -/
  ψ : ℕ → EuclideanSpace ℝ ι
  /-- the per-level transition bound (from Lemma 1 + the `cO` operator) -/
  step : ∀ s j, mass lev (ψ (s+1)) j ≤ mass lev (ψ s) j + ∑ i ∈ Finset.range j, G i j * mass lev (ψ s) i
  /-- the initial state sits at level `0` -/
  init : ∀ j, mass lev (ψ 0) j ≤ Ahat G 0 j

/-- **Lemma 2 for a real state.** The masses of an actual Hilbert-space state sequence are bounded
by the chain sum. This is `path_bound` applied to `mass lev ∘ ψ`, with nonnegativity supplied by
`mass_nonneg` rather than assumed. -/
theorem instantiate (G : ℕ → ℕ → ℝ) (hG : ∀ i j, 0 ≤ G i j) (lev : ι → ℕ)
    (S : LevelStep G lev) :
    ∀ t j, mass lev (S.ψ t) j ≤ Ahat G t j :=
  path_bound G hG (fun s j => mass lev (S.ψ s) j) S.init S.step

end Qrom
