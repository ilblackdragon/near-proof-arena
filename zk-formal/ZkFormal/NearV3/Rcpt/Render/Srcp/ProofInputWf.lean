import ZkFormal.NearV3.Rcpt.Render.Srcp.ProofInputFacts

namespace ZkFormal.NearV3.Render.SrcpGen
open NearSpec ZkFormal.Near ZkFormal.Algebra

/-- Encoding facts to discharge from successful decoding, A2/distinct ids, and the original
source row budget. These describe the actual proof entries, not an abstract AIR witness. -/
structure ProofInputsOk (xs : List ProofInput) : Prop where
  nonempty : xs ≠ []
  root : ∀ x ∈ xs, x.root.length = 32
  sibling : ∀ x ∈ xs, ∀ s ∈ x.entry.proof.path, s.1.length = 32
  length : ∀ x ∈ xs, (u64 x.entry.proof.toShard ++ encodeReceipts x.entry.receipts).length < P
  duplicate : ∀ x ∈ xs, x.dup = true → (u64 x.entry.proof.toShard ++ encodeReceipts x.entry.receipts).length = 12
  rows : srcpRows (blocksOfProofs xs) ≤ 2 ^ SrcpV3.maxLog

private theorem length_le_rows (bs : List SrcpB) : bs.length ≤ srcpRows bs := by
  induction bs with
  | nil => simp [srcpRows]
  | cons B bs ih => simp only [srcpRows, List.map_cons, List.sum_cons, List.length_cons] at *; omega

private theorem byte_canon (b : UInt8) : b.toNat < P :=
  Nat.lt_trans (UInt8.toNat_lt b) (by decide)

/-- Concrete decoded proofs compile to the full source-table semantic invariant. -/
theorem blocksOfProofs_wf {xs : List ProofInput} (h : ProofInputsOk xs) :
    SrcpWf (blocksOfProofs xs) := by
  have hcount := length_le_rows (blocksOfProofs xs)
  have hrows := h.rows
  simp only [blocksOfProofs_length, SrcpV3.maxLog] at hcount hrows
  have hsmall : xs.length < P := by unfold P; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.rows⟩
  · intro he
    have hl := congrArg List.length he
    simp only [blocksOfProofs_length, List.length_nil] at hl
    exact h.nonempty (List.length_eq_zero_iff.mp hl)
  · intro i hi
    rw [blocksOfProofs_get xs i hi]
    rfl
  · intro hi
    rw [blocksOfProofs_get xs 0 hi]
    simp [blockOfProof, proofWeight]
  · intro i hi
    have hi' : i < (blocksOfProofs xs).length := by omega
    rw [blocksOfProofs_get xs (i + 1) hi, blocksOfProofs_get xs i hi']
    simp only [blockOfProof, SrcpB.lastQ, proofItems_length]
    rw [proofWeight_next xs i (by simpa using hi')]
    omega
  · intro B hB i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hB
    revert hi
    rw [blocksOfProofs_get xs j hj]
    intro hi
    exact blockOfProof_items _ _ _ _ _ i hi
  · intro B hB
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hB
    rw [blocksOfProofs_get xs j hj]
    exact blockOfProof_root _ _ _ _ _
  · intro B hB hd
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hB
    rw [blocksOfProofs_get xs j hj] at hd ⊢
    exact h.duplicate _ (List.getElem_mem (by simpa using hj)) hd
  · intro B hB
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hB
    rw [blocksOfProofs_get xs j hj]
    have hm := List.getElem_mem (show j < xs.length by simpa using hj)
    refine ⟨?_, ?_, ?_⟩
    · simpa [blockOfProof] using h.root _ hm
    · simp [blockOfProof, ArenaCore.sha256_length]
    · exact proofItems_lengths _ _ _ _ (ArenaCore.sha256_length _) (h.sibling _ hm)
  · intro B hB
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hB
    rw [blocksOfProofs_get xs j hj]
    have hj' : j < xs.length := by simpa using hj
    have hm := List.getElem_mem hj'
    refine ⟨Nat.lt_trans hj' hsmall, h.length _ hm, ?_, ?_⟩
    · intro x hx
      simp only [blockOfProof, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩ <;> exact byte_canon b
    · exact proofItems_canon _ _ _ _

end ZkFormal.NearV3.Render.SrcpGen
