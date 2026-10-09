import ZkFormal.NearV3.Candidates.ProcessRepairReceiptMemoryOrder
import ZkFormal.Near.Link.RunChain
namespace ZkFormal.NearV3.Candidates.ProcessRepairMemoryLanes
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Link
variable {pub:List Fp} {rs:RcptVs} {as:List AcctV}
  (h:ProcessRepairReceiptMemoryOrder.Context pub rs as)
open ProcessRepairReceiptMemoryOrder (mem_read)
include h
theorem slot_acct : ∀ r (hr : r < rs.length), ∃ a ∈ as, a.k = rs[r].kslot := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
    intro hr
    rcases lastW_cases (ksl rs) rs[r].kslot r with e | ⟨r0, -, -, e⟩
    · obtain ⟨a, ha, hk, -⟩ := (mem_read h hr (i := 0) (by decide)).1 e
      exact ⟨a, ha, hk⟩
    · obtain ⟨hr0, hlt, hk, -⟩ := (mem_read h hr (i := 0) (by decide)).2 r0 e
      obtain ⟨a, ha, hk'⟩ := ih r0 hlt hr0
      exact ⟨a, ha, hk' ▸ hk ▸ rfl⟩

/-- Lanes of a receipt's read: locked and storage are the slot's pre-state lanes. -/
theorem lanes (initial:∀a∈as,Bytes8 a.pre)
    (after:∀r,(hr:r<rs.length)→Bytes8 rs[r].aft) : ∀ r (hr : r < rs.length), ∀ a ∈ as, a.k = rs[r].kslot → ∀ i, i < 16 →
    rs[r].lk.getD i 0 = a.pre.getD (16 + i) 0 ∧
    rs[r].st.getD i 0 = (if i < 8 then a.pre.getD (64 + i) 0 else 0) ∧
    rs[r].bef.getD i 0 < 256 := by
  have hnd := h.unique
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
    intro hr a ha hk i hi
    rcases lastW_cases (ksl rs) rs[r].kslot r with e | ⟨r0, -, -, e⟩
    · obtain ⟨b, hb, hbk, he⟩ := (mem_read h hr hi).1 e
      have : b = a := by
        have := (acctOf_eq hnd hb).symm.trans ((hbk.trans hk.symm) ▸ acctOf_eq hnd ha)
        simpa using this
      subst this
      have hpre := initial b hb
      simp only [rdMsg, awMsg, acctLane, List.cons_append, List.nil_append, List.cons.injEq] at he
      refine ⟨he.2.2.2.2.1, he.2.2.2.2.2.1, ?_⟩
      rw [he.2.2.2.1]; exact getD_lt_of_bytes8 hpre _
    · obtain ⟨hr0, hlt, hk0, he⟩ := (mem_read h hr hi).2 r0 e
      have w0 := after r0 hr0
      obtain ⟨i1, i2, -⟩ := ih r0 hlt hr0 a ha (hk.trans hk0.symm) i hi
      simp only [rdMsg, wrMsg, List.cons.injEq] at he
      refine ⟨he.2.2.2.2.1.trans i1, he.2.2.2.2.2.1.trans i2, ?_⟩
      rw [he.2.2.2.1]; exact getD_lt_of_bytes8 w0 _

end ZkFormal.NearV3.Candidates.ProcessRepairMemoryLanes
