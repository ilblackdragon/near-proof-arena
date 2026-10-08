import ZkFormal.NearV3.Rcpt.Candidates.NativeDictionary

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near NearSpec NearSpecV3 Assembly

theorem distinctKeys_eq_map_of_nodup {entries : List ProofEntry}
    (hn : (entries.map ProofEntry.key).Nodup) : distinctKeys entries=entries.map ProofEntry.key := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨he,hn⟩ := List.nodup_cons.mp hn
    simp only [distinctKeys,ih hn]
    simpa using he

/-- The executable dictionary has unique keys when its explicitly unused filler
keys are unique. This does not require native source occurrences to be distinct. -/
theorem nativeDictionary_keys_nodup (sources : List SrcList) (own : Nat)
    (rs : RcptV3Vs) (bs : List SrcpB) (fillers : List ProofEntry)
    (hf : ∀ f∈fillers,∀ s∈sources,f.key≠s.key)
    (hfn : (fillers.map ProofEntry.key).Nodup) :
    (((nativeDictionary sources own rs bs fillers).map DictionaryEntryV3.entry).map ProofEntry.key).Nodup := by
  rw [nativeDictionary_entries,List.map_append,List.nodup_append]
  refine ⟨firstNativeEntries_keys sources own rs bs,hfn,?_⟩
  intro key hk other hfk heq
  subst other
  obtain ⟨entry,he,rfl⟩ := List.mem_map.mp hk
  obtain ⟨f,hfmem,hfe⟩ := List.mem_map.mp hfk
  obtain ⟨e,hem,rfl⟩ := List.mem_map.mp he
  obtain ⟨i,him,rfl⟩ := List.mem_map.mp hem
  have hi := firstSourceIndices_lt sources him
  apply hf f hfmem (sources.getD i ⟨[],0,[]⟩)
  · rw [getD_eq_getElem' sources ⟨[],0,[]⟩ hi]
    exact List.getElem_mem hi
  · exact hfe

/-- Exact unchanged validator cardinality: each repeated occurrence needs an unused
filler key. Existence and byte cost of such fillers remain separate obligations. -/
theorem nativeDictionary_distinct_count (sources : List SrcList) (own : Nat)
    (rs : RcptV3Vs) (bs : List SrcpB) (fillers : List ProofEntry)
    (hf : ∀ f∈fillers,∀ s∈sources,f.key≠s.key)
    (hfn : (fillers.map ProofEntry.key).Nodup) :
    (distinctKeys ((nativeDictionary sources own rs bs fillers).map DictionaryEntryV3.entry)).length=
      (firstSourceIndices sources).length+fillers.length := by
  rw [distinctKeys_eq_map_of_nodup (nativeDictionary_keys_nodup sources own rs bs fillers hf hfn)]
  simp [nativeDictionary,firstNativeSources]

/-- The exact number of unused distinct filler keys discharges the frozen
occurrence-count guard without narrowing the native source domain. -/
theorem nativeDictionary_occurrence_count (sources : List SrcList) (own : Nat)
    (rs : RcptV3Vs) (bs : List SrcpB) (fillers : List ProofEntry)
    (hf : ∀ f∈fillers,∀ s∈sources,f.key≠s.key)
    (hfn : (fillers.map ProofEntry.key).Nodup)
    (hc : fillers.length=sources.length-(firstSourceIndices sources).length) :
    (distinctKeys ((nativeDictionary sources own rs bs fillers).map DictionaryEntryV3.entry)).length=
      sources.length := by
  rw [nativeDictionary_distinct_count sources own rs bs fillers hf hfn,hc]
  have hh : (firstSourceIndices sources).length≤sources.length := by
    simpa only [firstSourceIndices,List.length_range] using List.length_filter_le (fun j => !Public.sourceDup sources j) (List.range sources.length)
  omega

end ZkFormal.NearV3.Rcpt.Candidates
