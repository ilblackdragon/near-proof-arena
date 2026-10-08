import ZkFormal.NearV3.Rcpt.Candidates.NativeDictionaryRouting

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near NearSpec NearSpecV3 Assembly

/-- Concrete first-key lookup agrees with the exact occurrence list. All repeated
occurrences are empty, so lookup reuse preserves order and multiplicity. -/
theorem nativeDictionary_occurrence (sources : List SrcList) (own : Nat)
    (rs : RcptV3Vs) (bs : List SrcpB) (fillers : List ProofEntry)
    (hf : ∀ f∈fillers,∀ s∈sources,f.key≠s.key)
    (he : ∀ i,i<sources.length → sourceRepeated sources i=true → (rs.getD i default).rs=[])
    {j : Nat} (hj : j<sources.length) :
    (sourceEntry ((nativeDictionary sources own rs bs fillers).map DictionaryEntryV3.entry)
      (sources.getD j ⟨[],0,[]⟩)).receipts=
      (rs.getD j default).rs.map (fun r => r.toRcptV.toReceipt) := by
  have hlookup (i : Nat) (hi : i<sources.length) (hd : Public.sourceDup sources i=false) :
      lookupLast (sources.getD i ⟨[],0,[]⟩).key
        ((nativeDictionary sources own rs bs fillers).map DictionaryEntryV3.entry)=
        some (nativeEntryAt sources own rs bs i).entry := by
    rw [nativeDictionary_entries,lookupLast_fresh_append]
    · exact firstNativeEntries_lookup sources own rs bs hi hd
    · intro f hfm
      exact hf f hfm _ (by
        rw [←List.getElem_eq_getD (h:=hi) ⟨[],0,[]⟩]
        exact List.getElem_mem hi)
  cases hd : Public.sourceDup sources j with
  | false =>
    simp only [sourceEntry,hlookup j hj hd,Option.getD_some]
    rfl
  | true =>
    obtain ⟨i,_,hi,hdi,hkey⟩ := first_source_cover sources hj
    have hrepj := sourceDup_repeated sources hj hd
    have hrepi : sourceRepeated sources i=true := by
      simpa only [sourceRepeated,hkey] using hrepj
    have hl := hlookup i hi hdi
    rw [hkey] at hl
    simp only [sourceEntry,hl,Option.getD_some,nativeEntryAt,DedupProof.nativeSourceEntry,
      SourceEntryV3.entry,he i hi hrepi,he j hj hrepj,List.map_nil]

/-- Whole ordered flattening, with no permutation or discarded duplicate
occurrences: only repeated empty lists are identified. -/
theorem nativeDictionary_ordered_receipts (sources : List SrcList) (own : Nat)
    (rs : RcptV3Vs) (bs : List SrcpB) (fillers : List ProofEntry)
    (hf : ∀ f∈fillers,∀ s∈sources,f.key≠s.key)
    (he : ∀ i,i<sources.length → sourceRepeated sources i=true → (rs.getD i default).rs=[])
    (hlen : sources.length=rs.length) (L : Layout) (target : Nat)
    (hr : ∀ x∈flatR rs,L.shardOf x.toRcptV.toReceipt.receiverId=target) :
    sources.flatMap (sourceReceipts
      ((nativeDictionary sources own rs bs fillers).map DictionaryEntryV3.entry) target L)=
      rs.flatMap (fun l => l.rs.map (fun r => r.toRcptV.toReceipt)) := by
  have hm : sources.map (sourceReceipts
      ((nativeDictionary sources own rs bs fillers).map DictionaryEntryV3.entry) target L)=
      rs.map (fun l => l.rs.map (fun r => r.toRcptV.toReceipt)) := by
    apply List.ext_getElem
    · simpa only [List.length_map] using hlen
    · intro j hj hj'
      have hjs : j<sources.length := by simpa only [List.length_map] using hj
      have hjr : j<rs.length := by omega
      simp only [List.getElem_map,sourceReceipts]
      have ho := nativeDictionary_occurrence sources own rs bs fillers hf he hjs
      rw [getD_eq_getElem' sources _ hjs,getD_eq_getElem' rs _ hjr] at ho
      rw [ho]
      apply List.filter_eq_self.mpr
      intro r hrm
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hrm
      have hv := hr x (List.mem_flatMap.mpr ⟨rs[j],List.getElem_mem hjr,hx⟩)
      simpa only [hv,beq_self_eq_true]
  exact congrArg List.flatten hm

end ZkFormal.NearV3.Rcpt.Candidates
