import Mathlib
import Qrom.Reflection
import Qrom.Main

/-!
# Qrom.ConcreteInstance — a checked `PotentialEvolution` for the one-point model

`Qrom.Main.qrom_bound` is conditional on a `PotentialEvolution G`. This file
builds one, so that `qrom_binary_bound` can be applied without any remaining
opaque parameter except `G` and `Replacement`.

## The instance

* Space: `H M = EuclideanSpace ℂ (DB M)`, the database register at one oracle
  point (a real normed space via `restrictScalars`).
* Step: `qr M`, the actual reflection of `Qrom.Reflection` — an isometry, so
  `‖qr M‖ = 1`.
* Level function `lev : DB M → ℕ`, with a changed set `Chg` such that `lev` is
  constant off `Chg` (this is CFHL21's stability hypothesis, now a hypothesis
  about a named object rather than an entry of an entry bound).
* `G i j = sqrt (2 |Chg| / M)` for `i < j` and `0` otherwise. The block estimate
  comes from `Qrom.Reflection.block_chg_sq` plus the exact block identity, so it
  is a theorem about `qr M`, not an assumption.
* Initial state `ψ 0 = |⊥⟩` (the all-undefined database at point `x`), so the
  level-`0` mass is `1` and all higher masses vanish, matching `Ahat G 0 j`.

## Honest scope — read this before quoting the conclusion

This is a **one-point, one-query-operator** model. It is *not* the paper's
family:

* the step is the same reflection at every query, not
  `Σ_{x,ŷ} |x,ŷ⟩⟨x,ŷ| ⊗ cO_{xŷ}` lifted over `q` oracle points;
* `κ` is an arbitrary supplied level function, not the collision/inversion
  potential of the transcript;
* `Replacement` (CFHL21 Cor 4.2) remains a cited interface;
* the measured-event inclusion is *proved here* for this model
  (`hmeasured` is instantiated by `le_refl`), which is the one premise the
  skeleton previously assumed.
-/

set_option maxHeartbeats 1600000

namespace Qrom

open scoped BigOperators
open Finset

instance (M : ℕ) : Nonempty (H M) := ⟨0⟩

/-- The real-linear projection, unfolded: this is `cproj`. -/
theorem cprojR_eq {M : ℕ} (P : DB M → Prop) [DecidablePred P] (x : H M) :
    cprojR P x = cproj P x := rfl

theorem cproj_sum_apply {M : ℕ} (P : ℕ → DB M → Prop) [∀ i, DecidablePred (P i)]
    (s : Finset ℕ) (x : H M) (u : DB M) :
    ((∑ i ∈ s, cproj (P i) x : H M) : DB M → ℂ) u
      = ∑ i ∈ s, (if P i u then x u else 0) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s _ ih =>
    simp only [Finset.sum_cons, ih, PiLp.add_apply, cproj_apply]

/-- **Spectral decomposition of the state by level.** Every state is the sum of
its level-`≥j` part and its level-`=i` parts for `i < j`. This is the
`decompose` field of `PotentialEvolution`, proved for the coordinate
projections. -/
theorem level_decompose {M : ℕ} (lev : DB M → ℕ) (j : ℕ) (x : H M) :
    x = cproj (fun i => j ≤ lev i) x
      + ∑ i ∈ Finset.range j, cproj (fun r => lev r = i) x := by
  ext u
  rw [PiLp.add_apply, cproj_sum_apply]
  simp only [cproj_apply]
  by_cases h : j ≤ lev u
  · rw [if_pos h]
    have hzero : ∀ i ∈ Finset.range j, (if lev u = i then x u else 0) = 0 := by
      intro i hi
      rw [if_neg]
      intro he
      have := Finset.mem_range.mp hi
      omega
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, add_zero]
  · rw [if_neg h, zero_add]
    have hlt : lev u < j := by omega
    rw [Finset.sum_eq_single (lev u)]
    · simp
    · intro b _ hb; rw [if_neg (Ne.symm hb)]
    · exact fun h => absurd (Finset.mem_range.mpr hlt) h

/-- Squared norm of a level projection is the mass it keeps. -/
theorem norm_sq_level {M : ℕ} (P : DB M → Prop) [DecidablePred P] (x : H M) :
    ‖cproj P x‖ ^ 2 = ∑ u ∈ Finset.univ.filter P, ‖x u‖ ^ 2 := by
  rw [norm_sq_cproj]
  rw [Finset.sum_filter]

/-- **The block estimate for the concrete operator.** Since `lev` is constant off
`Chg`, the block of `qr M` from level `=i` to level `≥j` (`i < j`) has squared
norm at most `2 |Chg| / M`. -/
theorem block_sq {M : ℕ} (hM : 0 < M) (lev : DB M → ℕ) (j i : ℕ) (hij : i < j)
    (Chg : Finset (DB M)) (hstable : ∀ r, r ∉ Chg → lev r = lev none) (x : H M) :
    ‖cprojR (fun r => j ≤ lev r) (qr M (cprojR (fun r => lev r = i) x))‖ ^ 2
      ≤ (2 * (Chg.card : ℝ) / (M : ℝ)) * ‖x‖ ^ 2 := by
  have hEq : (∑ u ∈ Finset.univ.filter (fun r => j ≤ lev r),
        ‖(qr M (cprojR (fun r => lev r = i) x) : H M) u‖ ^ 2)
      = ‖cprojR (fun r => j ≤ lev r)
          (qr M (cprojR (fun r => lev r = i) x))‖ ^ 2 :=
    (norm_sq_level _ _).symm
  rw [← hEq]
  exact block_chg_sq hM lev i j hij Chg hstable x

/-- The block operator norm bound, from the squared estimate. -/
theorem block_norm {M : ℕ} (hM : 0 < M) (lev : DB M → ℕ) (j i : ℕ) (hij : i < j)
    (Chg : Finset (DB M)) (hstable : ∀ r, r ∉ Chg → lev r = lev none) :
    ‖cprojR (fun r => j ≤ lev r) ∘L qr M ∘L cprojR (fun r => lev r = i)‖
      ≤ Real.sqrt (2 * (Chg.card : ℝ) / (M : ℝ)) := by
  have hc : (0:ℝ) ≤ 2 * (Chg.card : ℝ) / (M : ℝ) := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  have hsq := block_sq hM lev j i hij Chg hstable x
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hroot : ‖cprojR (fun r => j ≤ lev r) (qr M (cprojR (fun r => lev r = i) x))‖
      ≤ Real.sqrt (2 * (Chg.card : ℝ) / (M : ℝ)) * ‖x‖ := by
    have h1 := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_mul hc, Real.sqrt_sq hx] at h1
    rwa [Real.sqrt_sq (norm_nonneg _)] at h1
  simpa only [ContinuousLinearMap.comp_apply] using hroot

/-! ## The initial state and the instance -/

/-- The all-undefined database state at one point. -/
noncomputable def initVec (M : ℕ) : H M :=
  WithLp.equiv 2 (DB M → ℂ) |>.symm (fun i => if i = none then 1 else 0)

theorem initVec_norm {M : ℕ} (P : DB M → Prop) [DecidablePred P] :
    ‖cproj P (initVec M)‖ ^ 2 = if P none then 1 else 0 := by
  rw [norm_sq_cproj, Fintype.sum_option]
  have h0 : ‖(initVec M : DB M → ℂ) none‖ ^ 2 = 1 := by
    rw [show (initVec M : DB M → ℂ) none = 1 from rfl]
    norm_num
  have h1 : ∀ r : Fin M, ‖(initVec M : DB M → ℂ) (some r)‖ ^ 2 = 0 := by
    intro r; simp [initVec]
  have hsum : (∑ i, if P (some i) then ‖(initVec M : DB M → ℂ) (some i)‖ ^ 2 else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [h1 i]
    split_ifs <;> rfl
  rw [hsum, add_zero]
  by_cases h : P none
  · rw [if_pos h, if_pos h, h0]
  · rw [if_neg h, if_neg h]

/-- **A concrete `PotentialEvolution`.** The parameters are a level function with
a stability set `Chg`, and `G` built from `Chg`. Every field is discharged. -/
noncomputable def concreteEvolution (M : ℕ) (hM : 0 < M) (lev : DB M → ℕ)
    (hlev0 : lev none = 0)
    (Chg : Finset (DB M)) (hstable : ∀ r, r ∉ Chg → lev r = lev none) :
    PotentialEvolution (H M) (fun i j => if i < j
      then Real.sqrt (2 * (Chg.card : ℝ) / (M : ℝ)) else 0) where
  tail j := cprojR (fun r => j ≤ lev r)
  exactLevel i := cprojR (fun r => lev r = i)
  tail_contract j := cprojR_contract _
  exact_idem i := cprojR_idem _
  decompose j ψ := level_decompose lev j ψ
  exact_le_tail i ψ :=
    norm_cproj_mono (fun r hr => hr ▸ Nat.le_refl i) ψ
  step _ := qr M
  step_contract _ := qr_contract M
  ψ s := (qr M)^[s] (initVec M)
  evolves s := by
    show (qr M)^[s+1] (initVec M) = qr M ((qr M)^[s] (initVec M))
    rw [Function.iterate_succ_apply']
  init j := by
    show ‖cprojR (fun r => j ≤ lev r) (initVec M)‖ ≤ Ahat _ 0 j
    have hnorm : ‖cprojR (fun r => j ≤ lev r) (initVec M)‖ ^ 2
        = if j ≤ lev none then 1 else 0 := initVec_norm _
    have hle1 : ‖cprojR (fun r => j ≤ lev r) (initVec M)‖ ≤ 1 := by
      split_ifs at hnorm with hj <;>
        nlinarith [norm_nonneg (cprojR (fun r => j ≤ lev r) (initVec M))]
    rw [Ahat, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.choose_self, Nat.cast_one, one_mul]
    simp only [W]
    by_cases hj : j = 0
    · subst hj; exact hle1
    · rw [if_neg hj]
      have hjn : ¬ j ≤ lev none := by omega
      rw [if_neg hjn] at hnorm
      nlinarith [norm_nonneg (cprojR (fun r => j ≤ lev r) (initVec M))]
  block s j i hij := by
    show ‖cprojR (fun r => j ≤ lev r) ∘L qr M ∘L cprojR (fun r => lev r = i)‖
      ≤ (if i < j then Real.sqrt (2 * (Chg.card : ℝ) / (M : ℝ)) else 0)
    rw [if_pos hij]
    exact block_norm hM lev j i hij Chg hstable

/-- **The concrete end-to-end bound.** For this one-point model, the measured bad
probability is bounded by `(t·√(2|Chg|/M) + √slack)²` whenever the cited
replacement inequality holds. The measured-event inclusion is `le_refl`: the
event *is* the projection mass here, not an assumption. -/
theorem concrete_qrom_bound (M : ℕ) (hM : 0 < M) (lev : DB M → ℕ)
    (hlev0 : lev none = 0)
    (Chg : Finset (DB M)) (hstable : ∀ r, r ∉ Chg → lev r = lev none)
    (t : ℕ) (p slack : ℝ) (hp : 0 ≤ p)
    (hreplace : Replacement p
      ((fun S => ‖S.tail 1 (S.ψ t)‖ ^ 2)
        (concreteEvolution M hM lev hlev0 Chg hstable)) slack) :
    p ≤ ((t : ℝ) * Real.sqrt (2 * (Chg.card : ℝ) / (M : ℝ)) + Real.sqrt slack) ^ 2 := by
  let G : ℕ → ℕ → ℝ := fun i j => if i < j
    then Real.sqrt (2 * (Chg.card : ℝ) / (M : ℝ)) else 0
  have hG : ∀ i j, 0 ≤ G i j := by
    intro i j
    show 0 ≤ if i < j then Real.sqrt (2 * (Chg.card : ℝ) / (M : ℝ)) else 0
    split_ifs <;> positivity
  have hmeas : ((fun S => ‖S.tail 1 (S.ψ t)‖ ^ 2)
      (concreteEvolution M hM lev hlev0 Chg hstable)) ≤
      ‖(concreteEvolution M hM lev hlev0 Chg hstable).tail 1
        ((concreteEvolution M hM lev hlev0 Chg hstable).ψ t)‖ ^ 2 := le_rfl
  have hpos : (0:ℝ) ≤ ((fun S => ‖S.tail 1 (S.ψ t)‖ ^ 2)
      (concreteEvolution M hM lev hlev0 Chg hstable)) := by
    show (0:ℝ) ≤ ‖_‖ ^ 2
    positivity
  have := qrom_binary_bound G hG (concreteEvolution M hM lev hlev0 Chg hstable) t p
    ((fun S => ‖S.tail 1 (S.ψ t)‖ ^ 2)
      (concreteEvolution M hM lev hlev0 Chg hstable)) slack hp hpos hmeas hreplace
  simpa only [G, if_pos (show (0:ℕ) < 1 by norm_num)] using this

end Qrom

/-! ## Axiom guards -/

/-- info: 'Qrom.qr_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Qrom.qr_contract
/-- info: 'Qrom.qop_apply_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Qrom.qop_apply_apply
/-- info: 'Qrom.block_chg_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Qrom.block_chg_sq
/-- info: 'Qrom.level_decompose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Qrom.level_decompose
/-- info: 'Qrom.block_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Qrom.block_norm
/-- info: 'Qrom.concreteEvolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Qrom.concreteEvolution
/-- info: 'Qrom.concrete_qrom_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Qrom.concrete_qrom_bound
