import ZkFormal.NearV3.Rcpt.Candidates.DedupListCounter

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra SrcpV3
open SrcpProof (uFirst isOne)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL

/-- Every root row is followed by a complete 32-row leaf unit. -/
theorem root_leaf_unit {r : Nat} (hr : r < tr.height tt) (ht : tr.cell tt r rt = 1) (hd : tr.cell tt r dup = 0) :
    r + 1 + 32 ≤ tr.height tt ∧ IsU tr tt (r + 1) 32 ∧
    tr.cell tt (r + 1) lf = 1 ∧
    (tr.cell tt (r + 1) q).toNat = (tr.cell tt r q).toNat + 1 ∧
    ∀ x ∈ listConst, tr.cell tt (r + 1) x = tr.cell tt r x := by
  have hn := computed_root_not_last hL hr ht hd
  have hf := computed_after_root hL hn ht hd
  have hcarry := computed_list_carry hL hn ht hd
  have huFirst : uFirst tr tt (r + 1) = true := by simp [uFirst, isOne, hf.2.2.1]
  obtain ⟨ℓ, hH, hu⟩ := seg_from (segFacts hL) (r + 1) hn huFirst
  have hnrt : tr.cell tt (r + 1) rt = 0 := by
    have hz := disjoint hL hn
    rw [hf.1] at hz; grind
  have h32 : ℓ = 32 := by
    rcases (segShape hL hu hH hnrt).1 with h | h
    · exact h.2
    · rw [hf.2.1] at h; exact False.elim (by simpa using h.1)
  subst ℓ
  exact ⟨hH, hu, hf.2.1, root_q_succ hL hn ht hd, hcarry⟩

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
