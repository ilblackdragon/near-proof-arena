import ZkFormal.NearV3.Assembly.StoreNormal

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

/-- Position in the original serialized store, not a compact NodeS3 index.
Byte equality deliberately avoids assuming injective hashes. -/
def originalBlobId (ws : List Bytes) (b : Bytes) : Option Nat :=
  ws.findIdx? (· == b)

theorem originalBlobId_get {ws : List Bytes} {b : Bytes} {i : Nat}
    (h : originalBlobId ws b = some i) : ws[i]? = some b := by
  obtain ⟨hi,hb,_⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact List.getElem?_eq_some_iff.mpr ⟨hi, by simpa using hb⟩

theorem originalBlobId_exists {ws : List Bytes} {b : Bytes} (hb : b ∈ ws) :
    ∃ i, originalBlobId ws b = some i := by
  exact ⟨_,List.findIdx?_eq_some_of_exists ⟨b,hb,by simp⟩⟩

theorem originalBlobId_unique {ws : List Bytes} {a b : Bytes} {i : Nat}
    (ha : originalBlobId ws a = some i) (hb : originalBlobId ws b = some i) : a=b := by
  have := (originalBlobId_get ha).symm.trans (originalBlobId_get hb)
  exact Option.some.inj this

/-- Every normalized byte has an authenticated original position. -/
theorem normalStore_original_id {ws : List Bytes} {t : PTrie}
    (ht : Stored (mkStore ws) t) {b : Bytes} (hb : b ∈ normalStore t) :
    ∃ i, originalBlobId ws b = some i ∧ ws[i]? = some b ∧
      storeGet (mkStore ws) (sha256 b) = some b := by
  have hf := normalStore_found ht b hb
  obtain ⟨i,hi⟩ := originalBlobId_exists (storeGet_some hf).2
  exact ⟨i,hi,originalBlobId_get hi,hf⟩

/-- Occurrence-to-original mapping retains the first-wins digest lookup,
including the case of distinct bytes with colliding hashes. -/
theorem occurrence_original_id {ws : List Bytes} {t o : PTrie}
    (ht : Stored (mkStore ws) t) (ho : o ∈ occs t) :
    ∃ i, originalBlobId ws (nodeEnc o) = some i ∧ ws[i]? = some (nodeEnc o) ∧
      storeGet (mkStore ws) o.hashOf = some (nodeEnc o) := by
  have hn := occs_isNode t o ho
  have hf := stored_found (occs_stored _ _ ht _ ho) hn
  obtain ⟨i,hi⟩ := originalBlobId_exists (storeGet_some hf).2
  refine ⟨i,hi,originalBlobId_get hi,?_⟩
  rwa [hashOf_eq_enc o hn]

/-- Equal digests among actually stored occurrences imply equal bytes because
both are first-match winners; this does not assume cryptographic injectivity. -/
theorem occurrence_original_id_same_hash {ws : List Bytes} {t a b : PTrie}
    (ht : Stored (mkStore ws) t) (ha : a ∈ occs t) (hb : b ∈ occs t)
    (he : a.hashOf=b.hashOf) :
    nodeEnc a=nodeEnc b ∧ originalBlobId ws (nodeEnc a)=originalBlobId ws (nodeEnc b) := by
  obtain ⟨_,_,_,hfa⟩ := occurrence_original_id ht ha
  obtain ⟨_,_,_,hfb⟩ := occurrence_original_id ht hb
  rw [he] at hfa
  have hbytes := Option.some.inj (hfa.symm.trans hfb)
  exact ⟨hbytes,congrArg (originalBlobId ws) hbytes⟩

/-- Native accepted input construction supplies Stored; no extra ownership
premise is needed for the occurrence-to-original byte lookup. -/
theorem partialTrie_occurrence_original_id (ws : List Bytes) (root : Bytes)
    (keys : List (List Nat)) (hr : root.length=32) {o : PTrie}
    (ho : o ∈ occs (partialTrie ws root keys)) :
    ∃ i, originalBlobId ws (nodeEnc o)=some i ∧ ws[i]?=some (nodeEnc o) ∧
      storeGet (mkStore ws) o.hashOf=some (nodeEnc o) := by
  exact occurrence_original_id (built_spec ws trieFuel root keys hr).2.2.1 ho

end ZkFormal.NearV3.Assembly
