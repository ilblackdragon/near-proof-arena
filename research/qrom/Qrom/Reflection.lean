import Mathlib
import Qrom.Instance

/-!
# Qrom.Reflection — an explicit unitary with the CFHL21 Lemma 4.3 entry shape

`Qrom.Transition.EntryBounds` is an *interface*: it posits an entry function with
the right magnitudes, and `Qrom.Audit.old_entry_model_not_unitary` shows no
unitary has an all-off-diagonal entry model. This file closes that gap for the
one-point database register by constructing the operator.

## Construction

Let `w ∈ H M` be `w none = 1` and `w (some r) = -(√M)⁻¹`, so `‖w‖² = 2`. The
one-point compressed-oracle squeezing operator is the reflection in `ℂ ∙ w`,

  `qop = 2 • P_w - I = |w⟩⟨w| - I`,

a complex linear isometry by `Submodule.reflection`; `qr` is its real-scalar
restriction, so `‖qr‖ ≤ 1`. Its components are `qr_apply`:

  `(qr x) i = (∑ j, x j * conj (w j)) * w i - x i`.

Hence the entries `w i * conj (w j) - δ_{ij}` have squared magnitude `0` on
`(⊥,⊥)`, `1/M` on the `⊥` edges, and `1/M` on the diagonal of `Y × Y` (where
`w i * conj (w i) = 1/M`), and `1/M²` off the diagonal of `Y × Y`. The off
diagonal bound is `1/M² ≤ 9/M²`, exactly `EntryBounds`'s CFHL21 shape.

## The block identity, and why it is better than Frobenius

Because `qop` is a rank-one update of `-I`, on **disjoint** level sets the
`-I` part of a source-supported vector is killed by the target projection, so

  `‖Π_S (qr x)‖² = ‖w|_S‖² · |∑_{j∈T} x j · conj (w j)|²`

whenever `x` is supported in `T` (`block_norm_sq`). Cauchy–Schwarz gives
`block_le` with constant `‖w|_S‖²‖w|_T‖²`. With the `Chg` stability hypothesis
this is at most `2|Chg|/M`, versus CFHL21's Frobenius constant `10|Chg|/M`.

## Scope

One oracle point. The multi-point lifting (a step that acts on coordinate `s` of
`Fin q → DB M` and a collision-count potential) is **not** constructed here; see
`docs/logs/pq-family-qrom-2026-10-21.md`.
-/

set_option maxHeartbeats 1600000

namespace Qrom

open scoped BigOperators
open Finset

/-! ## The vector `w` and its weights -/

/-- `w none = 1`, `w (some r) = -(√M)⁻¹`. -/
noncomputable def wvec (M : ℕ) : H M :=
  WithLp.equiv 2 (DB M → ℂ) |>.symm (fun i => if i = none then 1 else -((Real.sqrt M : ℂ))⁻¹)

@[simp] theorem wvec_none (M : ℕ) : (wvec M : DB M → ℂ) none = 1 := by
  simp [wvec]

@[simp] theorem wvec_some (M : ℕ) (r : Fin M) :
    (wvec M : DB M → ℂ) (some r) = -((Real.sqrt M : ℂ))⁻¹ := by
  simp [wvec]

/-- `|(√M)⁻¹|² = 1/M`. -/
theorem norm_sqrt_inv_sq_pos {M : ℕ} (hM : 0 < M) :
    ‖((Real.sqrt M : ℂ))⁻¹‖ ^ 2 = 1 / (M : ℝ) := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast hM
  have hsq : (Real.sqrt (M:ℝ)) ^ 2 = (M:ℝ) := Real.sq_sqrt hMpos.le
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.mpr hMpos), inv_pow, hsq]
  have hMne : (M:ℝ) ≠ 0 := hMpos.ne'
  field_simp

/-- `|-(√M)⁻¹|² = 1/M`. -/
theorem norm_sqrt_inv_sq {M : ℕ} (hM : 0 < M) :
    ‖-((Real.sqrt M : ℂ))⁻¹‖ ^ 2 = 1 / (M : ℝ) := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast hM
  have hsq : (Real.sqrt (M:ℝ)) ^ 2 = (M:ℝ) := Real.sq_sqrt hMpos.le
  rw [norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.mpr hMpos), inv_pow, hsq]
  have hMne : (M:ℝ) ≠ 0 := hMpos.ne'
  field_simp

theorem wvec_norm_sq {M : ℕ} (hM : 0 < M) : ‖wvec M‖ ^ 2 = 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_option]
  have h0 : ‖(wvec M : DB M → ℂ) none‖ ^ 2 = 1 := by rw [wvec_none]; norm_num
  have h1 : ∀ r : Fin M, ‖(wvec M : DB M → ℂ) (some r)‖ ^ 2 = 1 / (M:ℝ) :=
    fun r => by rw [wvec_some]; exact norm_sqrt_inv_sq hM
  rw [h0, Finset.sum_congr rfl (fun r _ => h1 r), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hMpos : (0:ℝ) < M := by exact_mod_cast hM
  have hMne : (M:ℝ) ≠ 0 := hMpos.ne'
  field_simp
  norm_num

/-- The weight of a value set: `‖w|_S‖² = [⊥ ∈ S] + |S ∩ Y|/M`. -/
theorem sum_no_bot (M : ℕ) (hM : 0 < M) (S : Finset (DB M))
    (hS : ∀ i ∈ S, i ≠ none) :
    ∑ i ∈ S, ‖(wvec M : DB M → ℂ) i‖ ^ 2 = (S.card : ℝ) * (1 / (M:ℝ)) := by
  have hpt : ∀ i ∈ S, ‖(wvec M : DB M → ℂ) i‖ ^ 2 = 1 / (M:ℝ) := by
    intro i hi
    obtain ⟨r, rfl⟩ := Option.ne_none_iff_exists'.mp (hS i hi)
    rw [wvec_some]; exact norm_sqrt_inv_sq hM
  rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul]

/-- The total weight is two. -/
theorem weight_univ (M : ℕ) (hM : 0 < M) :
    ∑ i, ‖(wvec M : DB M → ℂ) i‖ ^ 2 = 2 := by
  rw [← EuclideanSpace.norm_sq_eq]; exact wvec_norm_sq hM

/-- Any value set has weight at most two. -/
theorem weight_le_two (M : ℕ) (hM : 0 < M) (S : Finset (DB M)) :
    ∑ i ∈ S, ‖(wvec M : DB M → ℂ) i‖ ^ 2 ≤ 2 := by
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun i _ _ => sq_nonneg _)).trans_eq ?_
  exact weight_univ M hM

/-! ## The reflection -/

/-- `w` is nonzero. -/
theorem wvec_ne_zero (M : ℕ) : wvec M ≠ 0 := by
  intro h
  have := wvec_none M
  rw [h] at this
  simp at this

/-- The one-point compressed-oracle unitary: reflection in `ℂ ∙ w`. -/
noncomputable def qop (M : ℕ) : H M ≃ₗᵢ[ℂ] H M := (ℂ ∙ wvec M).reflection

/-- Value of the reflection: a rank-one update of `-I`, because `‖w‖² = 2`.
In the database coordinates the inner product `inner (wvec M) x` is the
coefficient `∑ j, x j * conj (w j)` of `question`. -/
theorem qop_coeff {M : ℕ} (x : H M) :
    inner ℂ (wvec M) x
      = ∑ j, x j * (starRingEnd ℂ) ((wvec M : DB M → ℂ) j) := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun j _ => RCLike.inner_apply _ _

/-- The scalar identity behind `‖w‖² = 2`: `2 · (I/‖w‖²) · w = I · w`. -/
theorem scalar_norm_sq {M : ℕ} (hw : ‖wvec M‖ ^ 2 = 2) (S w : ℂ) :
    (2 : ℕ) • (S / (((↑‖wvec M‖ : ℂ)) ^ 2)) • w = S • w := by
  have hz : ((↑‖wvec M‖ : ℂ) ^ 2) = (2:ℂ) := by
    rw [← Complex.ofReal_pow, hw]; norm_num
  rw [hz]
  simp only [smul_eq_mul]
  ring

/-- Component form of the reflection: a rank-one update of `-I`. This is where
`‖w‖² = 2` enters: in coordinates it is the scalar identity
`2 · (I/‖w‖²) · w i = I · w i`. -/
theorem qop_apply_apply {M : ℕ} (hM : 0 < M) (x : H M) (i : DB M) :
    (qop M x : H M) i = (∑ j, x j * (starRingEnd ℂ) ((wvec M : DB M → ℂ) j))
      * ((wvec M : DB M → ℂ) i) - x i := by
  rw [qop, Submodule.reflection_singleton_apply, qop_coeff x]
  have hw := wvec_norm_sq hM
  simp only [PiLp.sub_apply, PiLp.smul_apply]
  congr 1
  exact scalar_norm_sq hw _ _

/-- The step operator, restricted to real scalars. -/
noncomputable def qr (M : ℕ) : H M →L[ℝ] H M :=
  ((qop M).toContinuousLinearEquiv : H M →L[ℂ] H M).restrictScalars ℝ

/-- The step is a contraction: it is an isometry. -/
theorem qr_norm_map (M : ℕ) (x : H M) : ‖qr M x‖ = ‖x‖ := by
  show ‖(qop M).toContinuousLinearEquiv x‖ = ‖x‖
  exact (qop M).norm_map x

theorem qr_contract (M : ℕ) : ‖qr M‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    rw [qr_norm_map, one_mul])

theorem qr_apply_apply {M : ℕ} (hM : 0 < M) (x : H M) (i : DB M) :
    (qr M x : H M) i = (∑ j, x j * (starRingEnd ℂ) ((wvec M : DB M → ℂ) j))
      * ((wvec M : DB M → ℂ) i) - x i := qop_apply_apply hM x i

/-- A value set avoiding `⊥` has weight `|S|/M`. -/
theorem weight_of_no_bot (M : ℕ) (hM : 0 < M) (S : Finset (DB M))
    (hS : ∀ i ∈ S, i ≠ none) :
    ∑ i ∈ S, ‖(wvec M : DB M → ℂ) i‖ ^ 2 = (S.card : ℝ) * (1 / (M:ℝ)) := by
  have hpt : ∀ i ∈ S, ‖(wvec M : DB M → ℂ) i‖ ^ 2 = 1 / (M:ℝ) := by
    intro i hi
    obtain ⟨r, rfl⟩ := Option.ne_none_iff_exists'.mp (hS i hi)
    rw [wvec_some]; exact norm_sqrt_inv_sq hM
  rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul]

/-! ## Exact block norm on disjoint level sets -/

/-- If `x` is supported in `T` and `S` is disjoint from `T`, the `-I` part is
killed, so the block is the rank-one map `|w|_S⟩⟨w|_T|`. Exact identity. -/
theorem block_norm_sq {M : ℕ} (hM : 0 < M) (S T : Finset (DB M)) (hST : Disjoint S T)
    (x : H M) (hx : ∀ i, i ∉ T → x i = 0) :
    ∑ i ∈ S, ‖(qr M x : H M) i‖ ^ 2
      = (∑ i ∈ S, ‖(wvec M : DB M → ℂ) i‖ ^ 2)
        * ‖∑ j ∈ T, x j * (starRingEnd ℂ) ((wvec M : DB M → ℂ) j)‖ ^ 2 := by
  classical
  have hmem : ∀ i ∈ S, i ∉ T := fun i hi => Finset.disjoint_left.mp hST hi
  have hterm : ∀ i ∈ S, (qr M x : H M) i
      = (∑ j ∈ T, x j * (starRingEnd ℂ) ((wvec M : DB M → ℂ) j))
        * ((wvec M : DB M → ℂ) i) := by
    intro i hi
    rw [qr_apply_apply hM]
    have hT : ∑ j, x j * (starRingEnd ℂ) ((wvec M : DB M → ℂ) j)
        = ∑ j ∈ T, x j * (starRingEnd ℂ) ((wvec M : DB M → ℂ) j) := by
      rw [← Finset.sum_subset (Finset.subset_univ T)]
      intro j _ hj
      rw [hx j hj, zero_mul]
    rw [hT, hx i (hmem i hi), sub_zero]
  rw [Finset.sum_congr rfl (fun i hi => by rw [hterm i hi, norm_mul, mul_pow])]
  rw [← Finset.mul_sum]
  exact mul_comm _ _

/-- **The block operator bound.** The squared norm of the block between disjoint
level sets is at most `‖w|_S‖² ‖w|_T‖² ‖x‖²`. -/
theorem block_le {M : ℕ} (hM : 0 < M) (S T : Finset (DB M)) (hST : Disjoint S T)
    (P : DB M → Prop) [DecidablePred P] (hP : ∀ i, P i ↔ i ∈ T) (x : H M) :
    ∑ i ∈ S, ‖(qr M (cproj P x) : H M) i‖ ^ 2
      ≤ (∑ i ∈ S, ‖(wvec M : DB M → ℂ) i‖ ^ 2)
        * (∑ j ∈ T, ‖(wvec M : DB M → ℂ) j‖ ^ 2) * ‖x‖ ^ 2 := by
  classical
  set x' : H M := cproj P x with hx'
  have hxsupp : ∀ i, i ∉ T → x' i = 0 := by
    intro i hi; rw [hx']; simp only [cproj_apply, (hP i).not.mpr hi, if_false]
  have hexact := block_norm_sq hM S T hST x' hxsupp
  have hCS : ‖∑ j ∈ T, x' j * (starRingEnd ℂ) ((wvec M : DB M → ℂ) j)‖ ^ 2
      ≤ (∑ j ∈ T, ‖(wvec M : DB M → ℂ) j‖ ^ 2) * (∑ j ∈ T, ‖x' j‖ ^ 2) := by
    have hnorm : ‖∑ j ∈ T, x' j * (starRingEnd ℂ) ((wvec M : DB M → ℂ) j)‖
        ≤ ∑ j ∈ T, ‖(wvec M : DB M → ℂ) j‖ * ‖x' j‖ := by
      calc ‖∑ j ∈ T, x' j * (starRingEnd ℂ) ((wvec M : DB M → ℂ) j)‖
          ≤ ∑ j ∈ T, ‖x' j * (starRingEnd ℂ) ((wvec M : DB M → ℂ) j)‖ := norm_sum_le _ _
        _ = ∑ j ∈ T, ‖(wvec M : DB M → ℂ) j‖ * ‖x' j‖ := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [norm_mul, RCLike.norm_conj, mul_comm]
    have hsq := Finset.sum_mul_sq_le_sq_mul_sq T
      (fun j => ‖(wvec M : DB M → ℂ) j‖) (fun j => ‖x' j‖)
    have hnn := norm_nonneg (∑ j ∈ T, x' j * (starRingEnd ℂ) ((wvec M : DB M → ℂ) j))
    have hlt : ‖∑ j ∈ T, x' j * (starRingEnd ℂ) ((wvec M : DB M → ℂ) j)‖ ^ 2
        ≤ (∑ j ∈ T, ‖(wvec M : DB M → ℂ) j‖ * ‖x' j‖) ^ 2 :=
      pow_le_pow_left₀ hnn hnorm 2
    exact hlt.trans hsq
  have hxnorm : ∑ j ∈ T, ‖x' j‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    calc ∑ j ∈ T, ‖x' j‖ ^ 2 ≤ ∑ j, ‖x' j‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
            (fun i _ _ => by positivity)
      _ = ‖x'‖ ^ 2 := (EuclideanSpace.norm_sq_eq x').symm
      _ ≤ ‖x‖ ^ 2 := by
          have hle := norm_cproj_le P x
          have h1 := norm_nonneg (cproj P x)
          have h2 := norm_nonneg x
          rw [← hx'] at hle h1
          nlinarith
  have hSA : 0 ≤ ∑ i ∈ S, ‖(wvec M : DB M → ℂ) i‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hTB : 0 ≤ ∑ j ∈ T, ‖(wvec M : DB M → ℂ) j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ∑ i ∈ S, ‖(qr M (cproj P x) : H M) i‖ ^ 2
      = (∑ i ∈ S, ‖(wvec M : DB M → ℂ) i‖ ^ 2)
          * ‖∑ j ∈ T, x' j * (starRingEnd ℂ) ((wvec M : DB M → ℂ) j)‖ ^ 2 := hexact
    _ ≤ (∑ i ∈ S, ‖(wvec M : DB M → ℂ) i‖ ^ 2)
          * ((∑ j ∈ T, ‖(wvec M : DB M → ℂ) j‖ ^ 2) * (∑ j ∈ T, ‖x' j‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hCS hSA
    _ ≤ (∑ i ∈ S, ‖(wvec M : DB M → ℂ) i‖ ^ 2)
          * ((∑ j ∈ T, ‖(wvec M : DB M → ℂ) j‖ ^ 2) * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxnorm hTB) hSA
    _ = (∑ i ∈ S, ‖(wvec M : DB M → ℂ) i‖ ^ 2)
          * (∑ j ∈ T, ‖(wvec M : DB M → ℂ) j‖ ^ 2) * ‖x‖ ^ 2 := by ring

/-! ## The `Chg` bound: squared block norm `≤ 2|Chg|/M` -/

/-- **CFHL21 Lemma 1's changed-set consequence for the concrete unitary.** If the
level function is constant off `Chg`, then between two distinct levels `i < j` the
squared block norm is at most `2|Chg|/M`. -/
theorem block_chg_sq {M : ℕ} (hM : 0 < M) (κ : DB M → ℕ) (i j : ℕ) (hij : i < j)
    (Chg : Finset (DB M)) (hstable : ∀ r, r ∉ Chg → κ r = κ none) (x : H M) :
    ∑ u ∈ Finset.univ.filter (fun r => j ≤ κ r),
        ‖(qr M (cproj (fun r => κ r = i) x) : H M) u‖ ^ 2
      ≤ 2 * (Chg.card : ℝ) / (M : ℝ) * ‖x‖ ^ 2 := by
  classical
  set A := Finset.univ.filter (fun r => j ≤ κ r) with hA
  set B := Finset.univ.filter (fun r => κ r = i) with hB
  have hAB : Disjoint A B := by
    refine Finset.disjoint_left.mpr fun r ha hb => ?_
    have ha' : j ≤ κ r := (Finset.mem_filter.mp ha).2
    have hb' : κ r = i := (Finset.mem_filter.mp hb).2
    omega
  have hbnd := block_le hM A B hAB (fun r => κ r = i) (fun r => by rw [hB]; simp) x
  have hcard : ∀ S : Finset (DB M), S ⊆ Chg → (S.card : ℝ) ≤ (Chg.card : ℝ) :=
    fun S hS => by exact_mod_cast Finset.card_le_card hS
  have hW : (∑ u ∈ A, ‖(wvec M : DB M → ℂ) u‖ ^ 2)
      * (∑ r ∈ B, ‖(wvec M : DB M → ℂ) r‖ ^ 2)
      ≤ 2 * ((Chg.card : ℝ) / (M : ℝ)) := by
    by_cases hnone : none ∈ A
    · have hBn : none ∉ B := fun hb => Finset.disjoint_left.mp hAB hnone hb
      have hBsub : B ⊆ Chg := by
        intro r hr
        by_contra hn
        have hr' : κ r = i := (Finset.mem_filter.mp hr).2
        have hge : j ≤ κ none := (Finset.mem_filter.mp hnone).2
        have heq := hstable r hn
        omega
      have hwB : ∑ r ∈ B, ‖(wvec M : DB M → ℂ) r‖ ^ 2
          = (B.card : ℝ) * (1 / (M:ℝ)) :=
        weight_of_no_bot M hM B (fun r hr he => hBn (he ▸ hr))
      have hwA : ∑ u ∈ A, ‖(wvec M : DB M → ℂ) u‖ ^ 2 ≤ 2 := weight_le_two M hM A
      have hBc : (B.card : ℝ) ≤ (Chg.card : ℝ) := hcard B hBsub
      have hMpos : (0:ℝ) < M := by exact_mod_cast hM
      calc (∑ u ∈ A, _) * (∑ r ∈ B, _) ≤ 2 * ((B.card : ℝ) * (1 / (M:ℝ))) := by
            rw [hwB]; exact mul_le_mul hwA le_rfl (by positivity) (by norm_num)
        _ ≤ 2 * ((Chg.card : ℝ) * (1 / (M:ℝ))) := by
            have := mul_le_mul_of_nonneg_right hBc (by positivity : (0:ℝ) ≤ 1 / (M:ℝ))
            nlinarith
        _ = 2 * ((Chg.card : ℝ) / (M : ℝ)) := by ring
    · have hAsub : A ⊆ Chg := by
        intro r hr
        by_contra hn
        have hr' : j ≤ κ r := (Finset.mem_filter.mp hr).2
        have heq := hstable r hn
        exact hnone (Finset.mem_filter.mpr ⟨Finset.mem_univ none, by omega⟩)
      have hwA : ∑ u ∈ A, ‖(wvec M : DB M → ℂ) u‖ ^ 2
          = (A.card : ℝ) * (1 / (M:ℝ)) :=
        weight_of_no_bot M hM A (fun r hr he => hnone (he ▸ hr))
      have hwB : ∑ r ∈ B, ‖(wvec M : DB M → ℂ) r‖ ^ 2 ≤ 2 := weight_le_two M hM B
      have hAc : (A.card : ℝ) ≤ (Chg.card : ℝ) := hcard A hAsub
      have hMpos : (0:ℝ) < M := by exact_mod_cast hM
      calc (∑ u ∈ A, _) * (∑ r ∈ B, _) ≤ ((A.card : ℝ) * (1 / (M:ℝ))) * 2 := by
            rw [hwA]; exact mul_le_mul le_rfl hwB (by positivity) (by positivity)
        _ ≤ ((Chg.card : ℝ) * (1 / (M:ℝ))) * 2 := by
            have := mul_le_mul_of_nonneg_right hAc (by positivity : (0:ℝ) ≤ 1 / (M:ℝ))
            nlinarith
        _ = 2 * ((Chg.card : ℝ) / (M : ℝ)) := by ring
  calc ∑ u ∈ A, ‖(qr M (cproj (fun r => κ r = i) x) : H M) u‖ ^ 2
      ≤ (∑ u ∈ A, ‖(wvec M : DB M → ℂ) u‖ ^ 2)
          * (∑ r ∈ B, ‖(wvec M : DB M → ℂ) r‖ ^ 2) * ‖x‖ ^ 2 := hbnd
    _ ≤ (2 * ((Chg.card : ℝ) / (M : ℝ))) * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hW (by positivity)
    _ = 2 * (Chg.card : ℝ) / (M : ℝ) * ‖x‖ ^ 2 := by ring

/-! ## The CFHL21 entry magnitudes, and `EntryBounds` inhabited -/

/-- `qop` applied to a basis vector `|r⟩`: the coefficient is `conj w r`, so the
component at `u` is `conj (w r) * w u - δ_{ur}`. -/
theorem qop_single_apply {M : ℕ} (hM : 0 < M) (r u : DB M) :
    (qop M (EuclideanSpace.single r (1:ℂ)) : H M) u
      = (starRingEnd ℂ) ((wvec M : DB M → ℂ) r) * ((wvec M : DB M → ℂ) u)
        - (if u = r then 1 else 0) := by
  rw [qop_apply_apply hM]
  have hsum : ∀ j : DB M, (EuclideanSpace.single r (1:ℂ) : H M) j
      * (starRingEnd ℂ) ((wvec M : DB M → ℂ) j)
      = if j = r then (starRingEnd ℂ) ((wvec M : DB M → ℂ) j) else 0 := by
    intro j
    rw [PiLp.single_apply]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun j _ => hsum j), Finset.sum_ite_eq' Finset.univ]
  rw [if_pos (Finset.mem_univ r), PiLp.single_apply]



/-- The entries of `qop` in the `EntryBounds` sense: squared magnitudes. -/
theorem entry_none_none {M : ℕ} (hM : 0 < M) :
    ‖(qop M (EuclideanSpace.single none (1:ℂ)) : H M) none‖ ^ 2 = 0 := by
  rw [qop_single_apply hM, if_pos rfl, wvec_none]
  simp

/-- `⊥ → r` has squared entry `1/M`. -/
theorem entry_none_some {M : ℕ} (hM : 0 < M) (r : Fin M) :
    ‖(qop M (EuclideanSpace.single (some r) (1:ℂ)) : H M) none‖ ^ 2 = 1 / (M:ℝ) := by
  rw [qop_single_apply hM, if_neg (Ne.symm (Option.some_ne_none r)), sub_zero,
    wvec_none, wvec_some]
  have hq : (starRingEnd ℂ) (-((Real.sqrt M : ℂ))⁻¹) = -((Real.sqrt M : ℂ))⁻¹ := by
    rw [map_neg, map_inv₀, Complex.conj_ofReal]
  rw [hq, norm_mul, norm_one, mul_one]
  exact norm_sqrt_inv_sq hM

/-- `u → ⊥` has squared entry `1/M`. -/
theorem entry_some_none {M : ℕ} (hM : 0 < M) (u : Fin M) :
    ‖(qop M (EuclideanSpace.single none (1:ℂ)) : H M) (some u)‖ ^ 2 = 1 / (M:ℝ) := by
  rw [qop_single_apply hM, if_neg (Option.some_ne_none u), sub_zero,
    wvec_none, wvec_some]
  have h1 : (starRingEnd ℂ) (1:ℂ) = 1 := by simp
  rw [h1, one_mul, norm_neg]
  exact norm_sqrt_inv_sq_pos hM

/-- Off the diagonal of `Y × Y` the squared entry is `1/M² ≤ 9/M²`. -/
theorem entry_some_some_le {M : ℕ} (hM : 0 < M) (u r : Fin M) (hne : u ≠ r) :
    ‖(qop M (EuclideanSpace.single (some r) (1:ℂ)) : H M) (some u)‖ ^ 2
      ≤ 9 / ((M:ℝ) * M) := by
  rw [qop_single_apply hM, if_neg (fun h => hne (Option.some.inj h)), sub_zero,
    wvec_some, wvec_some]
  have hq : (starRingEnd ℂ) (-((Real.sqrt M : ℂ))⁻¹) = -((Real.sqrt M : ℂ))⁻¹ := by
    rw [map_neg, map_inv₀, Complex.conj_ofReal]
  rw [hq, norm_mul]
  have hMpos : (0:ℝ) < M := by exact_mod_cast hM
  have hp : ‖((Real.sqrt M : ℂ))⁻¹‖ ^ 2 = 1 / (M:ℝ) := norm_sqrt_inv_sq_pos hM
  simp only [norm_neg]
  rw [show ‖((Real.sqrt M : ℂ))⁻¹‖ * ‖((Real.sqrt M : ℂ))⁻¹‖
      = ‖((Real.sqrt M : ℂ))⁻¹‖ ^ 2 from by ring, hp]
  have hsq : (1 / (M:ℝ)) ^ 2 = 1 / ((M:ℝ) * M) := by
    rw [div_pow, one_pow, sq]
  rw [hsq]
  have h9 : (1:ℝ) ≤ 9 := by norm_num
  exact div_le_div_of_nonneg_right h9 (by positivity)

/-- The squared-entry function of `qop`, as an `EntryBounds` value. This proves
the `EntryBounds` interface of `Qrom.Transition` is **inhabited by an actual
complex linear isometry**, answering `Qrom.Audit.old_entry_model_not_unitary`. -/
noncomputable def qopEntries (M : ℕ) (hM : 0 < M) : EntryBounds M where
  entry u r := ‖(qop M (EuclideanSpace.single r (1:ℂ)) : H M) u‖ ^ 2
  nonneg _ _ := sq_nonneg _
  bot_bot := entry_none_none hM
  bot_r r := entry_none_some hM r
  u_bot u := entry_some_none hM u
  off_diag u r hne := entry_some_some_le hM u r hne

end Qrom

/-! ## Axiom guards -/

/-- info: 'Qrom.qopEntries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Qrom.qopEntries
/-- info: 'Qrom.entry_some_some_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Qrom.entry_some_some_le
/-- info: 'Qrom.qop_single_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Qrom.qop_single_apply
