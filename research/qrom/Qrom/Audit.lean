import Qrom.Main
import Qrom.Transcript

namespace Qrom

/-- The actual replacement inequality does not imply the withdrawn additive
probability premise. All three constants are in [0,1]. -/
theorem replacement_not_additive :
    Replacement (9/16 : ℝ) (1/4) (1/16) ∧ ¬ ((9/16 : ℝ) ≤ 1/4 + 1/16) := by
  norm_num [Replacement, Real.sqrt_div]

/-- A path bound is an amplitude bound: for one query and one transition,
Ahat = g, not g² or sqrt g. -/
theorem one_query_amplitude (g : ℝ) :
    Ahat (fun _ _ => g) 1 1 = g := by
  simp [Ahat, W, Finset.sum_range_succ]

/-- No full unitary can satisfy the old all-entry bound when M > 10.
Its finite row would have squared norm at most 10/M. -/
theorem old_entry_model_not_unitary (M : ℕ) (hM : 10 < M)
    (a : Fin M → ℝ) (h : ∀ r, a r ≤ 9 / ((M : ℝ) * M)) :
    ¬ ((1 : ℝ) / M + ∑ r, a r = 1) := by
  have hpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hten : (10 : ℝ) < M := by exact_mod_cast hM
  have hs : ∑ r, a r ≤ (M : ℝ) * (9 / ((M : ℝ) * M)) := by
    calc ∑ r, a r ≤ ∑ _r : Fin M, 9 / ((M : ℝ) * M) := Finset.sum_le_sum fun r _ => h r
      _ = _ := by simp
  have heq : (1 : ℝ) / M + (M : ℝ) * (9 / ((M : ℝ) * M)) = 10 / M := by
    field_simp; ring
  have hlt : (10 : ℝ) / M < 1 := (div_lt_one hpos).2 hten
  intro hu
  linarith

/-- info: 'Qrom.qrom_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qrom_bound
/-- info: 'Qrom.complex_block_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms complex_block_finite
#print axioms fact_a
#print axioms Transcript.first_flip_extract
#print axioms replacement_not_additive
#print axioms old_entry_model_not_unitary
#print axioms qrom_binary_bound
#print axioms consequence_chg
end Qrom
