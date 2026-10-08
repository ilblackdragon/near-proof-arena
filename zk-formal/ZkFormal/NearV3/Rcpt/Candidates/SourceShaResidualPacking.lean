import ZkFormal.NearV3.Rcpt.Candidates.PartitionCapacity

namespace ZkFormal.NearV3.Rcpt.Candidates

/-- Three possibly different residual capacities can hold all whole messages
when total demand leaves two maximum-message gaps. Large jobs may be allocated
first; this theorem then fills their unused space with small source jobs. -/
theorem splitBudget_three_residual (xs : List Nat) (c0 c1 c2 M : Nat)
    (hm : ∀ x∈xs,x≤M) (ht : xs.sum+2*M≤c0+c1+c2) :
    (splitBudget c0 xs).1.sum≤c0 ∧
    (splitBudget c1 (splitBudget c0 xs).2).1.sum≤c1 ∧
    (splitBudget c1 (splitBudget c0 xs).2).2.sum≤c2 := by
  refine ⟨splitBudget_prefix_le _ _,splitBudget_prefix_le _ _,?_⟩
  have h0 := splitBudget_reconstruct c0 xs
  have h1 := splitBudget_reconstruct c1 (splitBudget c0 xs).2
  have hs0 := congrArg List.sum h0
  have hs1 := congrArg List.sum h1
  simp only [List.sum_append] at hs0 hs1
  cases hrest1 : (splitBudget c1 (splitBudget c0 xs).2).2 with
  | nil => simp
  | cons b rest =>
    have hb : b∈(splitBudget c0 xs).2 := by rw [←h1,hrest1]; simp
    have hb' : b∈xs := by rw [←h0]; exact List.mem_append_right _ hb
    have hbM := hm b hb'
    have hstop1 := splitBudget_stop c1 (splitBudget c0 xs).2 hrest1
    cases hrest0 : (splitBudget c0 xs).2 with
    | nil => simp [hrest0] at hb
    | cons a tail =>
      have ha : a∈xs := by rw [←h0,hrest0]; simp
      have haM := hm a ha
      have hstop0 := splitBudget_stop c0 xs hrest0
      rw [hrest0] at hs0 hs1 hrest1 hstop1
      rw [hrest1] at hs1
      simp only [List.sum_cons] at hs0 hs1 ⊢
      omega

/-- Source hashes require at most35 rows each, so packing around previously
placed large jobs costs at most70 rows of aggregate slack, not two huge jobs. -/
theorem source_residual_three (weights : List Nat) (u0 u1 u2 : Nat)
    (hm : ∀ x∈weights,x≤35)
    (hu0 : u0≤2^22) (hu1 : u1≤2^22) (hu2 : u2≤2^22)
    (ht : weights.sum+u0+u1+u2+70≤3*2^22) :
    (splitBudget (2^22-u0) weights).1.sum+u0≤2^22 ∧
    (splitBudget (2^22-u1) (splitBudget (2^22-u0) weights).2).1.sum+u1≤2^22 ∧
    (splitBudget (2^22-u1) (splitBudget (2^22-u0) weights).2).2.sum+u2≤2^22 := by
  obtain ⟨h0,h1,h2⟩ := splitBudget_three_residual weights (2^22-u0) (2^22-u1) (2^22-u2)
    35 hm (by omega)
  omega

/-- Historical scalar totals omitted the separately proved scheduler batch.
These are arithmetic diagnostics, not a native full-family budget theorem. -/
theorem historical_capacity_diagnostics :
    12674664-3*2^22=91752 ∧
    12674664+1663260=14337924 ∧
    14337924-3*2^22=1755012 ∧
    8896703+2498545+1243407+1663260=14301915 ∧
    14301915-3*2^22=1719003 := by decide

end ZkFormal.NearV3.Rcpt.Candidates
