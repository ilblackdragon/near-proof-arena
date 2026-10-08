import ZkFormal.NearV3.Rcpt.Candidates.DedupNativeEntry
import ZkFormal.NearV3.Rcpt.Candidates.FirstSources
import ZkFormal.NearV3.Rcpt.Candidates.SourceCoverage

namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Near NearSpec NearSpecV3 Assembly

/-- A unique-key dictionary returns exactly any member selected by its own key. -/
theorem lookupLast_unique_member {entries : List ProofEntry}
    (hn : (entries.map ProofEntry.key).Nodup) {e : ProofEntry} (he : e∈entries) :
    lookupLast e.key entries=some e := by
  induction entries with
  | nil => simp at he
  | cons a rest ih =>
    obtain ⟨ha,hn⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp he with rfl|he
    · have hz : lookupLast e.key rest=none := by
        cases hh : lookupLast e.key rest with
        | none => rfl
        | some f =>
          have hm := lookupLast_mem hh
          have hk := lookupLast_key hh
          exact False.elim (ha (List.mem_map.mpr ⟨f,hm,hk⟩))
      simp [lookupLast,hz]
    · have hh := ih hn he
      simp [lookupLast,hh]

/-- Concrete source entry at its shared public/source/receipt index. -/
def nativeEntryAt (sources : List SrcList) (own : Nat) (rs : RcptV3Vs) (bs : List SrcpB)
    (i : Nat) : SourceEntryV3 :=
  let s := sources.getD i ⟨[],0,[]⟩
  DedupProof.nativeSourceEntry s.key s.fromShard own (rs.getD i default) (bs.getD i default)

/-- Only first occurrences perform source proof computation. This dictionary
contains authenticated representatives; optional unused fillers are separate. -/
def firstNativeSources (sources : List SrcList) (own : Nat) (rs : RcptV3Vs) (bs : List SrcpB) : List SourceEntryV3 :=
  (firstSourceIndices sources).map (nativeEntryAt sources own rs bs)

def firstNativeEntries (sources : List SrcList) (own : Nat) (rs : RcptV3Vs) (bs : List SrcpB) : List ProofEntry :=
  (firstNativeSources sources own rs bs).map SourceEntryV3.entry

theorem firstNativeEntries_keys (sources : List SrcList) (own : Nat) (rs : RcptV3Vs) (bs : List SrcpB) :
    ((firstNativeEntries sources own rs bs).map ProofEntry.key).Nodup := by
  simpa only [firstNativeEntries,firstNativeSources,List.map_map,Function.comp_def,nativeEntryAt,
    DedupProof.nativeSourceEntry,SourceEntryV3.entry] using firstSourceIndices_keys_nodup sources

theorem firstNativeSources_mem (sources : List SrcList) (own : Nat) (rs : RcptV3Vs) (bs : List SrcpB)
    {i : Nat} (hi : i<sources.length) (hd : Public.sourceDup sources i=false) :
    nativeEntryAt sources own rs bs i∈firstNativeSources sources own rs bs := by
  apply List.mem_map.mpr
  refine ⟨i,?_,rfl⟩
  simp [firstSourceIndices,hi,hd]

/-- Actual last-wins lookup selects each computed representative; no lookup premise. -/
theorem firstNativeEntries_lookup (sources : List SrcList) (own : Nat) (rs : RcptV3Vs) (bs : List SrcpB)
    {i : Nat} (hi : i<sources.length) (hd : Public.sourceDup sources i=false) :
    lookupLast (sources.getD i ⟨[],0,[]⟩).key (firstNativeEntries sources own rs bs)=
      some (nativeEntryAt sources own rs bs i).entry := by
  exact lookupLast_unique_member (firstNativeEntries_keys sources own rs bs)
    (List.mem_map.mpr ⟨_,firstNativeSources_mem sources own rs bs hi hd,rfl⟩)

/-- First-occurrence verification and concrete native metadata checks authenticate
every prepared descriptor, including repeated keys, in the generated dictionary. -/
theorem firstNativeEntries_authenticated (sources : List SrcList) (own : Nat) (rs : RcptV3Vs) (bs : List SrcpB)
    (hm : sourceMetadataConsistent sources=true)
    (hv : ∀ i,i<sources.length → Public.sourceDup sources i=false →
      verifyReceiptProof (sources.getD i ⟨[],0,[]⟩).root (nativeEntryAt sources own rs bs i).entry=true) :
    ∀ s∈sources,PreparedSourceAuthenticated (firstNativeEntries sources own rs bs) own s := by
  apply sources_authenticated_of_first _ _ _ hm
  intro i hi hd
  exact ⟨_,firstNativeEntries_lookup sources own rs bs hi hd,rfl,rfl,hv i hi hd⟩

/-- Appending unused dictionary keys does not change any selected last-wins lookup. -/
theorem lookupLast_fresh_append (key : Bytes) (entries fillers : List ProofEntry)
    (hf : ∀ f∈fillers,f.key≠key) :
    lookupLast key (entries++fillers)=lookupLast key entries := by
  have hz : lookupLast key fillers=none := by
    induction fillers with
    | nil => rfl
    | cons f fs ih =>
      have hfn := hf f (by simp)
      have htail := ih (by intro x hx; exact hf x (by simp [hx]))
      simp [lookupLast,htail,hfn]
  induction entries with
  | nil => exact hz
  | cons e es ih => simp only [List.cons_append,lookupLast,ih]

/-- Computational representatives and explicitly unused original/fresh filler entries.
The cardinality and encoded-byte cost of fillers are separate assembly obligations. -/
def nativeDictionary (sources : List SrcList) (own : Nat) (rs : RcptV3Vs) (bs : List SrcpB)
    (fillers : List ProofEntry) : List DictionaryEntryV3 :=
  (firstNativeSources sources own rs bs).map Sum.inl++fillers.map Sum.inr

theorem nativeDictionary_entries (sources : List SrcList) (own : Nat) (rs : RcptV3Vs) (bs : List SrcpB)
    (fillers : List ProofEntry) :
    (nativeDictionary sources own rs bs fillers).map DictionaryEntryV3.entry=
      firstNativeEntries sources own rs bs++fillers := by
  simp only [nativeDictionary,List.map_append,List.map_map,Function.comp_def,
    DictionaryEntryV3.entry,firstNativeEntries]
  rw [List.map_id']

/-- Every prepared source selects a left-branch authenticated entry, including
repeated keys, while unused filler entries cannot override the selected proof. -/
theorem nativeDictionary_selected (sources : List SrcList) (own : Nat) (rs : RcptV3Vs) (bs : List SrcpB)
    (fillers : List ProofEntry) (hf : ∀ f∈fillers,∀ s∈sources,f.key≠s.key)
    (hm : sourceMetadataConsistent sources=true)
    (hv : ∀ i,i<sources.length → Public.sourceDup sources i=false →
      verifyReceiptProof (sources.getD i ⟨[],0,[]⟩).root (nativeEntryAt sources own rs bs i).entry=true)
    {s : SrcList} (hs : s∈sources) :
    ∃ e : SourceEntryV3,Sum.inl e∈nativeDictionary sources own rs bs fillers ∧
      lookupLast s.key ((nativeDictionary sources own rs bs fillers).map DictionaryEntryV3.entry)=some e.entry ∧
      e.fromShard=s.fromShard ∧ e.toShard=own ∧ verifyReceiptProof s.root e.entry=true := by
  obtain ⟨entry,he,hfrom,hto,hverify⟩ := firstNativeEntries_authenticated sources own rs bs hm hv s hs
  have hem := lookupLast_mem he
  obtain ⟨e,heMember,heEq⟩ : ∃ e∈firstNativeSources sources own rs bs,e.entry=entry := List.mem_map.mp hem
  rw [←heEq] at he hfrom hto hverify
  refine ⟨e,?_,?_,hfrom,hto,hverify⟩
  · exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨e,heMember,rfl⟩))
  · rw [nativeDictionary_entries,lookupLast_fresh_append s.key _ fillers (by intro f hfm; exact hf f hfm s hs)]
    exact he

end ZkFormal.NearV3.Rcpt.Candidates
