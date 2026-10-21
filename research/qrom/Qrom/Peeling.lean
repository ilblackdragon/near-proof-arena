import Qrom.FactA

/-!
# Correct probability accounting for the proposed peeling reduction

This proves only the scalar implication. The simulation, extractor, family
potential and NV faithfulness are premises still to be instantiated. `delta`
is an event-probability error for an approximate simulator/extractor; exact
simulation sets it to zero.
-/
namespace Qrom.Peeling

theorem bound (p pD pB bad delta slack : ℝ) (hp : 0 ≤ p)
    (hrepl : Qrom.Replacement p pD slack)
    (hextract : pD ≤ pB + bad + delta) :
    p ≤ (Real.sqrt (pB + bad + delta) + Real.sqrt slack)^2 := by
  have hm := Real.sqrt_le_sqrt hextract
  have hr : Qrom.Replacement p (pB + bad + delta) slack := by
    unfold Qrom.Replacement at *
    linarith
  exact Qrom.fact_a _ _ _ hp hr

/-- The former Lemma P omitted the cross term involving `bad` and `slack`.
All probabilities in this example lie in [0,1]. -/
theorem old_peeling_bound_fails :
    Qrom.Replacement (1/4 : ℝ) (1/16) (1/16) ∧
    (1/16 : ℝ) ≤ 0 + 1/16 ∧
    ¬ ((1/4 : ℝ) ≤ (Real.sqrt 0 + Real.sqrt (1/16))^2 + 1/16) := by
  norm_num [Qrom.Replacement, Real.sqrt_div]

/-- A literal scan of all occupied slots at each query has a quadratic total.
This is not a lower bound for every compressed-oracle encoding. -/
theorem scan_work (q : ℕ) :
    2 * (∑ i ∈ Finset.range q, (i + 1)) = q * (q + 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ]
    nlinarith

end Qrom.Peeling
#print axioms Qrom.Peeling.bound
#print axioms Qrom.Peeling.old_peeling_bound_fails
#print axioms Qrom.Peeling.scan_work
