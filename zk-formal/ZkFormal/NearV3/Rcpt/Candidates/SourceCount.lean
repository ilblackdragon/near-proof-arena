import ZkFormal.NearV3.Rcpt.Candidates.SourceDictionary
import NearSpecV3.ChunkValidationV0a

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3

/-- Every computational representative has a key requested by the public occurrences. -/
theorem selectedSources_keys_subset (keys : List Bytes) (entries : List ProofEntry) :
    ∀ e ∈ selectedSources keys entries, e.key ∈ keys := by
  induction entries with
  | nil => simp [selectedSources]
  | cons e rest ih =>
    unfold selectedSources
    split
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.contains_iff_mem.mp hc.1
      · exact ih x hx
    · exact ih

/-- Deduplication does not require keys themselves to be distinct. -/
theorem selectedSources_count (keys : List Bytes) (entries : List ProofEntry) :
    (selectedSources keys entries).length ≤ keys.length := by
  have hh := List.Nodup.length_le_of_subset (selectedSources_keys_nodup keys entries)
    (show ((selectedSources keys entries).map ProofEntry.key) ⊆ keys from by
      intro key hk
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
      exact selectedSources_keys_subset keys entries e he)
  simpa using hh

/-- The actual B2-to-B1 source block slice has at most 31 blocks. -/
theorem sourceBlock_count (blks : List Blk) (b2i stop : Nat)
    (hb : blks.length ≤ 32) (hs : stop + 1 = blks.length) :
    ((blks.drop b2i).take (stop - b2i)).length ≤ 31 := by
  simp only [List.length_take, List.length_drop]
  omega

private theorem flatMap_count {α β : Type} (xs : List α) (f : α → List β) (n : Nat)
    (hf : ∀ x ∈ xs, (f x).length ≤ n) : (xs.flatMap f).length ≤ xs.length * n := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    have h1 := hf a (by simp)
    have h2 := ih (fun x hx => hf x (by simp [hx]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The spec's selected source proof occurrences have the established 31×64 envelope. -/
theorem usedProofs_count (k : WalkD0) (w : StateWitness)
    (hb : k.sourceBlks.length ≤ 31)
    (hs : ∀ b ∈ k.sourceBlks, b.slots.length ≤ 64) : (usedProofs k w).length ≤ 1984 := by
  unfold usedProofs
  have hh := flatMap_count k.sourceBlks
    (fun S => S.slots.filterMap fun (s, ci) =>
      if s.heightIncluded == S.hdr.height then lookupLast (chunkHash s.inner ci.encodedMerkleRoot) w.entries
      else none) 64 (by
        intro b hmem
        exact Nat.le_trans (List.length_filterMap_le _ _) (hs b hmem))
  exact Nat.le_trans hh (by omega)

end ZkFormal.NearV3.Rcpt.Candidates
