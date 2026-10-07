import ZkFormal.Near.Extract.Segments
import ZkFormal.NearV3.Rcpt.Candidates.FirstSources
import ZkFormal.NearV3.Rcpt.Candidates.PreparedMetadata

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 ZkFormal.Near

/-- Every occurrence is covered by a first occurrence of its key, selected by
the same executable duplicate bit used in public source records. -/
theorem first_source_cover (sources : List SrcList) {j : Nat} (hj : j<sources.length) :
    ∃ i, i≤j ∧ i<sources.length ∧ Public.sourceDup sources i=false ∧
      (sources.getD i ⟨[],0,[]⟩).key=(sources.getD j ⟨[],0,[]⟩).key := by
  let key := (sources.getD j ⟨[],0,[]⟩).key
  obtain ⟨i, hi, hmin⟩ := exists_least (p := fun i => i<sources.length ∧
    (sources.getD i ⟨[],0,[]⟩).key=key) ⟨j, hj, rfl⟩
  have hij : i≤j := by
    apply Classical.byContradiction
    intro hn
    exact hmin j (by omega) ⟨hj, rfl⟩
  refine ⟨i, hij, hi.1, ?_, hi.2⟩
  cases hd : Public.sourceDup sources i
  · rfl
  · unfold Public.sourceDup at hd
    obtain ⟨s, hs, he⟩ := List.any_eq_true.mp hd
    have he : s.key=(sources.getD i ⟨[],0,[]⟩).key := by simpa using he
    obtain ⟨k, hk, hks⟩ := List.mem_iff_getElem.mp hs
    have hki : k<i := by simp only [List.length_take] at hk; omega
    have hklen : k<sources.length := by omega
    have hks' : sources[k]=s := by simpa only [List.getElem_take] using hks
    have hg : (sources.getD k ⟨[],0,[]⟩).key=key := by
      rw [← List.getElem_eq_getD (h := hklen) ⟨[],0,[]⟩, hks', he]
      exact hi.2
    exact False.elim (hmin k hki ⟨hklen, hg⟩)

/-- The executable native metadata check authenticates both root and from-shard
for reuse of one selected proof at every occurrence of the same key. -/
theorem sourceMetadataConsistent_iff (sources : List SrcList) :
    sourceMetadataConsistent sources=true ↔
      ∀ s∈sources, ∀ t∈sources, s.key=t.key → s.fromShard=t.fromShard ∧ s.root=t.root := by
  simp only [sourceMetadataConsistent, List.all_eq_true]
  constructor
  · intro h s hs t ht he
    simpa [he] using h s hs t ht
  · intro h s hs t ht
    by_cases he : s.key=t.key
    · obtain ⟨hf, hr⟩ := h s hs t ht he
      simp [he, hf, hr]
    · simp [he]

/-- Verification only at first occurrences suffices for every selected dictionary
entry, provided the concrete native metadata check passed. -/
theorem sources_authenticated_of_first (sources : List SrcList) (entries : List ProofEntry)
    (own : Nat) (hmeta : sourceMetadataConsistent sources=true)
    (hv : ∀ i, i<sources.length → Public.sourceDup sources i=false →
      PreparedSourceAuthenticated entries own (sources.getD i ⟨[],0,[]⟩)) :
    ∀ s∈sources, PreparedSourceAuthenticated entries own s := by
  intro s hs
  obtain ⟨j, hj, hjs⟩ := List.mem_iff_getElem.mp hs
  obtain ⟨i, _, hi, hd, hk⟩ := first_source_cover sources hj
  have hg : sources.getD j ⟨[],0,[]⟩=s := by
    rw [← List.getElem_eq_getD (h := hj) ⟨[],0,[]⟩, hjs]
  rw [hg] at hk
  have him : sources.getD i ⟨[],0,[]⟩∈sources := by
    rw [← List.getElem_eq_getD (h := hi) ⟨[],0,[]⟩]; exact List.getElem_mem hi
  have hm := (sourceMetadataConsistent_iff sources).mp hmeta _ him s hs hk
  obtain ⟨e, he, hf, ht, hr⟩ := hv i hi hd
  exact ⟨e, by simpa only [hk] using he, hf.trans hm.1, ht, by simpa only [hm.2] using hr⟩

end ZkFormal.NearV3.Rcpt.Candidates
