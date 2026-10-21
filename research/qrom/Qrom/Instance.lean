import Mathlib
import Qrom.Transition
import Qrom.Operator
import Qrom.Main

/-!
# Qrom.Instance — a concrete family instance of the potential evolution

`Qrom.Main.qrom_bound` is conditional on a `PotentialEvolution`. This file builds
**one concrete instance** of it, so that every remaining premise is a statement
about a named object rather than an opaque parameter.

## The model, stated precisely

* The Hilbert space is the complex database register at **one** oracle point,
  `H M = EuclideanSpace ℂ (Option (Fin M))`. There is no adversary workspace and
  no Fourier query register; the model is the one-point query-only sub-model.
* The query operator is the **one-point compressed-oracle reflection**
  `R = 2·P_w - I`, where `w = -|⊥⟩ + M^{-1/2} Σ_{r∈Y} |r⟩` is a unit-norm
  vector scaled by `√2` (`‖w‖² = 2`). `R` is an isometry because it is
  Mathlib's `Submodule.reflection`, not because of a bounded-entry assumption.
  This directly answers `Qrom.old_entry_model_not_unitary`.
* The concrete entries of `R` are `conj(w j) * w i - δ_{ij}`, i.e.
  `0` on `⊥,⊥`, `M^{-1/2}` on the `⊥` edges, and `1/M` off the diagonal. So the
  squared entries are `0`, `1/M`, `1/M`, `1/M² ≤ 9/M²`: exactly the
  `EntryBounds` shape of `Qrom.Transition` (CFHL21 Lemma 4.3).
* The potential level is an arbitrary `κ : DB M → ℕ`; `tail j` and `exact i`
  are the coordinate projectors of `Qrom.Instantiate`, lifted to complex
  coordinates and to real scalars.

## Honest scope

This is a *model*, not the paper's family. The state is one point's database
register, the step operator is the same reflection at every query, and `κ` is
supplied rather than derived from the transcript. The measured event is
**derived** here (`p' = ‖tail 1 ψ t‖²` is the definition of the measurement
probability in this model), which is strictly better than assuming it. The
replacement premise `Replacement` is still the cited CFHL21 Cor 4.2 interface.
-/

namespace Qrom

open scoped BigOperators
open Finset

/-- The one-point database Hilbert space. -/
abbrev H (M : ℕ) := EuclideanSpace ℂ (DB M)

instance (M : ℕ) : Nonempty (H M) := ⟨0⟩

/-! ## Complex coordinate projections -/

/-- Coordinate projection onto a predicate on the database alphabet. -/
noncomputable def cproj {M : ℕ} (P : DB M → Prop) [DecidablePred P] (x : H M) : H M :=
  WithLp.equiv 2 (DB M → ℂ) |>.symm (fun i => if P i then x i else 0)

@[simp] theorem cproj_apply {M : ℕ} (P : DB M → Prop) [DecidablePred P] (x : H M) (i : DB M) :
    (cproj P x : H M) i = if P i then x i else 0 := rfl

theorem cproj_idem {M : ℕ} (P : DB M → Prop) [DecidablePred P] (x : H M) :
    cproj P (cproj P x) = cproj P x := by
  ext i
  simp only [cproj_apply]
  by_cases h : P i <;> simp [h]

theorem norm_sq_cproj {M : ℕ} (P : DB M → Prop) [DecidablePred P] (x : H M) :
    ‖cproj P x‖ ^ 2 = ∑ i, if P i then ‖x i‖ ^ 2 else 0 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [cproj_apply]
  by_cases h : P i <;> simp [h]

theorem norm_cproj_le {M : ℕ} (P : DB M → Prop) [DecidablePred P] (x : H M) :
    ‖cproj P x‖ ≤ ‖x‖ := by
  have h : ‖cproj P x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_sq_cproj, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hp : P i
    · simp [hp]
    · simp only [hp, if_false]; exact sq_nonneg _
  nlinarith [norm_nonneg (cproj P x), norm_nonneg x]

theorem norm_cproj_mono {M : ℕ} {P Q : DB M → Prop} [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ i, P i → Q i) (x : H M) : ‖cproj P x‖ ≤ ‖cproj Q x‖ := by
  have h : ‖cproj P x‖ ^ 2 ≤ ‖cproj Q x‖ ^ 2 := by
    rw [norm_sq_cproj, norm_sq_cproj]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hp : P i
    · have hq := hPQ i hp
      simp [hp, hq]
    · simp only [hp, if_false]
      positivity
  nlinarith [norm_nonneg (cproj P x), norm_nonneg (cproj Q x)]

/-- The projection as a **real-linear** continuous map, which is what
`PotentialEvolution` consumes. -/
noncomputable def cprojR {M : ℕ} (P : DB M → Prop) [DecidablePred P] : H M →L[ℝ] H M :=
  LinearMap.mkContinuous
    { toFun := cproj P
      map_add' := by
        intro x y
        ext i
        simp only [cproj_apply, Pi.add_apply]
        by_cases h : P i <;> simp [h]
      map_smul' := by
        intro c x
        ext i
        simp only [cproj_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        by_cases h : P i <;> simp [h] } 1
    (fun x => by simpa using norm_cproj_le P x)

@[simp] theorem cprojR_apply {M : ℕ} (P : DB M → Prop) [DecidablePred P] (x : H M) :
    cprojR P x = cproj P x := rfl

theorem cprojR_contract {M : ℕ} (P : DB M → Prop) [DecidablePred P] :
    ‖cprojR P‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    simpa [one_mul] using norm_cproj_le P x)

theorem cprojR_idem {M : ℕ} (P : DB M → Prop) [DecidablePred P] :
    cprojR P ∘L cprojR P = cprojR P := by
  refine ContinuousLinearMap.ext fun x => ?_
  show cproj P (cproj P x) = cproj P x
  exact cproj_idem P x

end Qrom
