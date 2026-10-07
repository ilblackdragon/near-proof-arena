import ZkFormal.NearV3.Assembly.StoreNormal

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

private theorem slotStored_of_values {s : Store} (v : Slot)
    (h : ∀ b ∈ slotVal v, Found s b) : SlotStored s v := by
  cases v with
  | ref => trivial
  | val b => exact h b (by simp [slotVal])

private theorem optSlotStored_of_values {s : Store} (v : Option Slot)
    (h : ∀ b ∈ optSlotVal v, Found s b) : OptSlotStored s v := by
  cases v with
  | none => trivial
  | some v => exact slotStored_of_values v h

mutual
theorem stored_of_occ_found (s : Store) : ∀ t : PTrie,
    (∀ o ∈ occs t, Found s (nodeEnc o) ∧ ∀ b ∈ ownVals o, Found s b) → Stored s t
  | .hash _, _ => trivial
  | .leaf k v m, h => by
    have hh := h (.leaf k v m) (by simp [occs])
    exact ⟨hh.1, slotStored_of_values v hh.2⟩
  | .ext k c m, h => by
    have hh := h (.ext k c m) (by simp [occs])
    exact ⟨hh.1, stored_of_occ_found s c (fun o ho => h o (by simp [occs, ho]))⟩
  | .branch v cs m, h => by
    have hh := h (.branch v cs m) (by simp [occs])
    exact ⟨hh.1, optSlotStored_of_values v hh.2,
      kidsStored_of_occ_found s cs (fun o ho => h o (by simp [occs, ho]))⟩
theorem kidsStored_of_occ_found (s : Store) : ∀ cs : Kids,
    (∀ o ∈ kOccs cs, Found s (nodeEnc o) ∧ ∀ b ∈ ownVals o, Found s b) → KidsStored s cs
  | .nil, _ => trivial
  | .none cs, h => kidsStored_of_occ_found s cs h
  | .some c cs, h =>
    ⟨stored_of_occ_found s c (fun o ho => h o (by simp [kOccs, ho])),
      kidsStored_of_occ_found s cs (fun o ho => h o (by simp [kOccs, ho]))⟩
end

/-- Every regenerated node/value remains available under native first-wins lookup. -/
theorem normalStore_stored {s : Store} {t : PTrie} (ht : Stored s t) :
    Stored (mkStore (normalStore t)) t := by
  apply stored_of_occ_found
  intro o ho
  have hf := normalStore_hashFunctional ht
  constructor
  · apply found_of_mem hf
    simp only [normalStore, List.mem_eraseDups, List.mem_append, List.mem_map]
    exact Or.inl ⟨o, ho, rfl⟩
  · intro b hb
    apply found_of_mem hf
    simp only [normalStore, List.mem_eraseDups, List.mem_append]
    exact Or.inr (ownVals_sub ho hb)

/-- Replay preserves all requested determinate reads and the authenticated root. -/
theorem partialTrie_normalStore_reads (ws : List Bytes) (root : Bytes)
    (keys : List (List Nat)) (hr : root.length = 32)
    (hk : ∀ k ∈ keys, (partialTrie ws root keys).find k ≠ none) :
    (partialTrie (normalStore (partialTrie ws root keys)) root keys).refinedBy
      (partialTrie ws root keys) ∧
    (partialTrie (normalStore (partialTrie ws root keys)) root keys).hashOf = root ∧
    ∀ k ∈ keys, (partialTrie (normalStore (partialTrie ws root keys)) root keys).find k =
      (partialTrie ws root keys).find k := by
  have hb := built_spec ws trieFuel root keys hr
  have hs := buildFor_spec (mkStore (normalStore (partialTrie ws root keys))) trieFuel
    (partialTrie ws root keys) keys hb.2.1 (normalStore_stored hb.2.2.1) hk
  have hroot : (partialTrie ws root keys).hashOf = root := hb.1
  rw [hroot] at hs
  refine ⟨hs.1, ?_, fun k h => hs.2 k h (hb.2.2.2 k)⟩
  exact (PTrie.hashOf_refinedBy _ _ hs.1).trans hb.1

end ZkFormal.NearV3.Assembly
