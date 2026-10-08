import ZkFormal.NearV3.Candidates.HonestStoreRepresentatives
namespace ZkFormal.NearV3.Candidates.NativeStoreRepresentatives
open NearSpec NearSpecV3 ZkFormal.NearV3.Assembly HonestStoreRepresentatives

/-- The actual native serialization footprint of the revealed trees, including
both node records and values. Original transition indices remain attached. -/
def occurrences (ts : List PTrie) : List Key :=
  ts.zipIdx.flatMap fun p=>(normalStore p.1).map fun bytes=>(p.2,bytes)

def originals (ts : List PTrie) (store : Nat → List Bytes) : List Key :=
  ts.zipIdx.flatMap fun p=>(store p.2).map fun bytes=>(p.2,bytes)

/-- Coverage follows from actual successful native store lookup; equality of
hashes alone is not used to identify two serialized byte records. -/
theorem coverage (ts : List PTrie) (store : Nat → List Bytes)
    (hs : ∀p∈ts.zipIdx,Stored (mkStore (store p.2)) p.1) :
    occurrences ts⊆originals ts store := by
  intro key hk
  obtain ⟨p,hp,hm⟩ := List.mem_flatMap.mp hk
  obtain ⟨bytes,hb,rfl⟩ := List.mem_map.mp hm
  have hf := normalStore_found (hs p hp) bytes hb
  have hmem := (storeGet_some hf).2
  exact List.mem_flatMap.mpr ⟨p,hp,List.mem_map.mpr ⟨bytes,hmem,rfl⟩⟩

theorem charge_paid (ts : List PTrie) (store : Nat → List Bytes)
    (hs : ∀p∈ts.zipIdx,Stored (mkStore (store p.2)) p.1) :
    charge (representatives (occurrences ts))≤charge (originals ts store) :=
  charge_le _ _ (coverage ts store hs)

/-- The resulting payload-plus-header bound is the exact charge used by the
count-extended SIZE table; repeated occurrences add no extra native charge. -/
theorem payload_and_headers_paid (ts : List PTrie) (store : Nat → List Bytes)
    (hs : ∀p∈ts.zipIdx,Stored (mkStore (store p.2)) p.1) :
    ((representatives (occurrences ts)).map fun key=>key.2.length).sum+
      4*(representatives (occurrences ts)).length≤
    ((originals ts store).map fun key=>key.2.length).sum+4*(originals ts store).length := by
  have h := charge_paid ts store hs
  simpa only [charge_split] using h

/-- Every honest representative can be bound to an actual original serialized
store position, retaining the transition tag through the whole lookup. -/
theorem original_position (ts : List PTrie) (store : Nat → List Bytes)
    (hs : ∀p∈ts.zipIdx,Stored (mkStore (store p.2)) p.1)
    (key : Key) (hk : key∈representatives (occurrences ts)) :
    ∃ i,originalBlobId (store key.1) key.2=some i ∧ (store key.1)[i]?=some key.2 := by
  have hm := coverage ts store hs ((covers _ _).mp hk)
  obtain ⟨p,hp,hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨bytes,hb,rfl⟩ := List.mem_map.mp hm
  obtain ⟨i,hi⟩ := originalBlobId_exists hb
  exact ⟨i,hi,originalBlobId_get hi⟩
end ZkFormal.NearV3.Candidates.NativeStoreRepresentatives
