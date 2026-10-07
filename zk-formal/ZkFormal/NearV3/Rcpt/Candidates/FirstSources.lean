import ZkFormal.NearV3.Rcpt.Candidates.OrderedSources
import ZkFormal.NearV3.Rcpt.Candidates.SourceRepetition

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3

/-- Exactly the actual prepared indices whose existing public duplicate flag is false. -/
def firstSourceIndices (sources : List SrcList) : List Nat :=
  (List.range sources.length).filter (fun j => !Public.sourceDup sources j)

theorem firstSourceIndices_lt (sources : List SrcList) {j : Nat}
    (hj : j ∈ firstSourceIndices sources) : j < sources.length :=
  List.mem_range.mp (List.mem_filter.mp hj).1

/-- Existing duplicate flags ensure that retained occurrence keys never repeat. -/
theorem firstSourceIndices_keys_nodup (sources : List SrcList) :
    ((firstSourceIndices sources).map fun j => (sources.getD j ⟨[],0,[]⟩).key).Nodup := by
  have ho : (firstSourceIndices sources).Pairwise (· < ·) :=
    List.pairwise_lt_range.filter _
  apply List.pairwise_map.mpr
  apply ho.imp_of_mem
  intro i j hi hj hij he
  have hil := firstSourceIndices_lt sources hi
  have hjl := firstSourceIndices_lt sources hj
  have hip : i < (sources.take j).length := by simp only [List.length_take]; omega
  have him : sources[i] ∈ sources.take j := by
    have hh := List.getElem_mem hip
    simpa only [List.getElem_take] using hh
  have hik : sources[i].key = (sources.getD j ⟨[],0,[]⟩).key := by
    rw [← List.getElem_eq_getD (h := hil) ⟨[],0,[]⟩] at he
    exact he
  have hd : Public.sourceDup sources j = true :=
    List.any_eq_true.mpr ⟨sources[i], him, by simpa using hik⟩
  have hn := (List.mem_filter.mp hj).2
  simp only [hd, Bool.not_true, Bool.false_eq_true] at hn

def firstSourceEntries (sources : List SrcList) (entryAt : Nat → ProofEntry) : List ProofEntry :=
  (firstSourceIndices sources).map entryAt

theorem firstSourceEntries_keys_nodup (sources : List SrcList) (entries : List ProofEntry)
    (entryAt : Nat → ProofEntry)
    (hl : ∀ j, j < sources.length → lookupLast (sources.getD j ⟨[],0,[]⟩).key entries = some (entryAt j)) :
    ((firstSourceEntries sources entryAt).map ProofEntry.key).Nodup := by
  have he : (firstSourceEntries sources entryAt).map ProofEntry.key =
      (firstSourceIndices sources).map (fun j => (sources.getD j ⟨[],0,[]⟩).key) := by
    simp only [firstSourceEntries, List.map_map]
    apply List.map_congr_left
    intro j hj
    exact lookupLast_key (hl j (firstSourceIndices_lt sources hj))
  rw [he]
  exact firstSourceIndices_keys_nodup sources

/-- The renderer can select first occurrences using the actual public duplicate bit;
its computed paths still obey the raw 8 MiB budget with no depth assumption. -/
theorem firstSourceEntries_raw_budget {raw : Bytes} {w : StateWitness}
    (hw : decodeStateWitness raw = .ok w) (hb : lenT raw ≤ witnessBytes)
    (sources : List SrcList) (entryAt : Nat → ProofEntry)
    (hl : ∀ j, j < sources.length → lookupLast (sources.getD j ⟨[],0,[]⟩).key w.entries = some (entryAt j)) :
    pathCount (firstSourceEntries sources entryAt) ≤ distinctPathItems := by
  apply raw_computed_path_budget hw hb _ (firstSourceEntries_keys_nodup sources w.entries entryAt hl)
  intro e he
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
  have hh := hl j (firstSourceIndices_lt sources hj)
  rw [lookupLast_key hh]
  exact hh

end ZkFormal.NearV3.Rcpt.Candidates
