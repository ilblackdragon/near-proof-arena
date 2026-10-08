import ZkFormal.NearV3.Rcpt.Candidates.NativeFillers
import ZkFormal.NearV3.Rcpt.Candidates.SourceSizeEncoding
import ZkFormal.NearV3.Assembly.WitnessSize

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Assembly

private theorem computed_cost (entries : List ProofEntry)
    (hk : ∀ e∈entries,e.key.length=32)
    (hp : ∀ e∈entries,∀ s∈e.proof.path,s.1.length=32) :
    (entries.map (fun e => (V3.encodeEntry e).length)).sum=
      (entries.map entrySizeCharge).sum+44*entries.length := by
  induction entries with
  | nil => simp
  | cons e es ih =>
    have he := encoded_entry_charge e (hp e (by simp))
    have ht := ih (fun x hx => hk x (by simp [hx])) (fun x hx => hp x (by simp [hx]))
    have hh := hk e (by simp)
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

/-- Exact source dictionary encoding budget, including the outer vector length.
Each skipped occurrence already pays twelve bytes in SRC SIZE; its filler needs
only the same 44-byte overhead as a computed occurrence. This theorem does not
assume an uncharged global witness margin. -/
theorem nativeDictionary_encoded_size (sources : List SrcList) (hn : sources.length≤1984)
    (own : Nat) (rs : RcptV3Vs) (bs : List SrcpB)
    (hk : ∀ e∈firstNativeEntries sources own rs bs,e.key.length=32)
    (hp : ∀ e∈firstNativeEntries sources own rs bs,∀ s∈e.proof.path,s.1.length=32) :
    (encList V3.encodeEntry
      ((nativeDictionary sources own rs bs (nativeFillers sources)).map DictionaryEntryV3.entry)).length=
      ((firstNativeEntries sources own rs bs).map entrySizeCharge).sum+
      12*(sources.length-(firstSourceIndices sources).length)+44*sources.length+4 := by
  rw [nativeDictionary_entries]
  simp only [encList,List.length_append,u32_len]
  rw [concatAll_size]
  simp only [List.map_append,List.sum_append]
  rw [computed_cost _ hk hp,nativeFillers_encoded_cost sources hn]
  have hl : (firstNativeEntries sources own rs bs).length=(firstSourceIndices sources).length := by
    simp [firstNativeEntries,firstNativeSources]
  have hh : (firstSourceIndices sources).length≤sources.length := by
    simpa only [firstSourceIndices,List.length_range] using
      List.length_filter_le (fun j => !Public.sourceDup sources j) (List.range sources.length)
  rw [hl]
  omega

end ZkFormal.NearV3.Rcpt.Candidates
