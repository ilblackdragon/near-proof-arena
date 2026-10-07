import ZkFormal.NearV3.Assembly.ValueCapacity
import ZkFormal.NearV3.Qv.Bounds

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

private theorem slot_found {s : Store} {slot : Slot} {bytes : Bytes}
    (hs : SlotStored s slot) (hf : slot.get.map some = some (some bytes)) : Found s bytes := by
  cases slot with
  | ref => cases hf
  | val b => cases hf; exact hs

mutual
/-- Native successful value reads retain their actual authenticated store preimage. -/
theorem stored_find_found (s : Store) : ∀ t key bytes,
    Stored s t → t.find key = some (some bytes) → Found s bytes
  | .hash _, _, _, _, hf => by cases hf
  | .leaf k slot _, key, bytes, hs, hf => by
    simp only [PTrie.find] at hf
    split at hf
    · exact slot_found hs.2 hf
    · cases hf
  | .ext k c _, key, bytes, hs, hf => by
    simp only [PTrie.find] at hf
    split at hf
    · exact stored_find_found s c _ bytes hs.2 hf
    · cases hf
  | .branch v cs _, [], bytes, hs, hf => by
    cases v with
    | none => cases hf
    | some slot => exact slot_found hs.2.1 hf
  | .branch v cs _, n :: key, bytes, hs, hf =>
    kidsStored_find_found s cs n key bytes hs.2.2 hf
theorem kidsStored_find_found (s : Store) : ∀ cs n key bytes,
    KidsStored s cs → Kids.find cs n key = some (some bytes) → Found s bytes
  | .nil, _, _, _, _, hf => by cases hf
  | .none _, 0, _, _, _, hf => by cases hf
  | .some c _, 0, key, bytes, hs, hf => stored_find_found s c key bytes hs.1 hf
  | .none cs, n+1, key, bytes, hs, hf => kidsStored_find_found s cs n key bytes hs hf
  | .some _ cs, n+1, key, bytes, hs, hf => kidsStored_find_found s cs n key bytes hs.2 hf
end

theorem partialTrie_find_mem {ws : List Bytes} {root : Bytes} {keys : List (List Nat)}
    {key : List Nat} {bytes : Bytes} (hr : root.length = 32)
    (h : (partialTrie ws root keys).find key = some (some bytes)) : bytes ∈ ws :=
  (storeGet_some (stored_find_found (mkStore ws) _ key bytes
    (built_spec ws trieFuel root keys hr).2.2.1 h)).2

theorem partialTrie_find_size {ws : List Bytes} {root : Bytes} {keys : List (List Nat)}
    {key : List Nat} {bytes : Bytes} (hr : root.length = 32)
    (h : (partialTrie ws root keys).find key = some (some bytes)) :
    bytes.length ≤ (ws.map List.length).sum := by
  have hm := partialTrie_find_mem hr h
  exact Link3.le_sum_mem (List.mem_map.mpr ⟨bytes, hm, rfl⟩)

/-- Parsed buffered queue indices are bounded by bytes authenticated in the native store. -/
theorem bufferedShards_store_bound {ws : List Bytes} {root : Bytes} {keys : List (List Nat)}
    {v : Option Bytes} {shards : List Nat} {budget : Nat} (hr : root.length = 32)
    (hf : (partialTrie ws root keys).find keyBufferedIdx = some v)
    (hp : bufferedShards v = .ok shards) (hb : (ws.map List.length).sum ≤ budget) :
    shards.length ≤ budget / 24 := by
  have hv := (Qv.bufferedShards_iff v shards).mp hp
  cases v with
  | none => simp only [Qv.BufferedValue] at hv; subst shards; simp
  | some bytes =>
    have hsize := partialTrie_find_size hr hf
    have hc := Qv.bufferedValue_count_bound hv (Nat.le_trans hsize hb)
    omega

theorem foldl_add_sum : ∀ (xs : List Nat) (acc : Nat),
    xs.foldl (· + ·) acc = acc + xs.sum
  | [], acc => by simp
  | x :: xs, acc => by
    simp only [List.foldl_cons, List.sum_cons]
    rw [foldl_add_sum xs (acc+x)]
    omega

end ZkFormal.NearV3.Assembly
