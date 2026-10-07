import ZkFormal.NearV3.Rcpt.Link.WitnessSources

/-! Semantic candidate for deduplicated proof computation. The encoded witness dictionary
and its cardinality are preserved separately; this selects only computational representatives. -/
namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3

/-- Select the last occurrence of every used key, retaining original dictionary order. -/
def selectedSources (keys : List Bytes) : List ProofEntry → List ProofEntry
  | [] => []
  | e :: rest =>
    if keys.contains e.key && (lookupLast e.key rest).isNone then
      e :: selectedSources keys rest
    else selectedSources keys rest

/-- Selection cannot increase the total encoded path budget. -/
theorem selectedSources_sublist (keys : List Bytes) (entries : List ProofEntry) :
    List.Sublist (selectedSources keys entries) entries := by
  induction entries with
  | nil => exact List.Sublist.refl _
  | cons e rest ih =>
    unfold selectedSources
    split
    · exact List.Sublist.cons_cons e ih
    · exact List.Sublist.cons e ih

/-- Every used-key last-wins lookup is preserved exactly by computational deduplication. -/
theorem selectedSources_lookup (keys : List Bytes) (entries : List ProofEntry) (key : Bytes)
    (hk : key ∈ keys) : lookupLast key (selectedSources keys entries) = lookupLast key entries := by
  induction entries with
  | nil => rfl
  | cons e rest ih =>
    cases hr : lookupLast key rest with
    | some a =>
      simp only [selectedSources]
      split
      · simp only [lookupLast, ih, hr]
      · simpa only [lookupLast, hr] using ih
    | none =>
      by_cases he : e.key = key
      · have hc : keys.contains e.key = true := by simpa [he] using List.contains_iff_mem.mpr hk
        simp [selectedSources, hc, he, hr, lookupLast, ih, hk]
      · simp only [selectedSources]
        split
        · simp [lookupLast, ih, hr, he]
        · simp [lookupLast, ih, hr, he]

/-- A missing last-wins lookup means no encoded entry has that key. -/
theorem lookupLast_none_keys {key : Bytes} {entries : List ProofEntry}
    (h : lookupLast key entries = none) : ∀ e ∈ entries, e.key ≠ key := by
  induction entries with
  | nil => simp
  | cons a rest ih =>
    simp only [lookupLast] at h
    split at h
    · cases h
    · rename_i hr
      split at h
      · cases h
      · rename_i ha
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · simpa using ha
        · exact ih hr e he

/-- Computational representatives have distinct keys even when the encoded dictionary does not. -/
theorem selectedSources_keys_nodup (keys : List Bytes) (entries : List ProofEntry) :
    ((selectedSources keys entries).map ProofEntry.key).Nodup := by
  induction entries with
  | nil => simp [selectedSources]
  | cons e rest ih =>
    unfold selectedSources
    split
    · rename_i hc
      have hn : lookupLast e.key rest = none := by
        have hh : (lookupLast e.key rest).isNone = true := by simp only [Bool.and_eq_true] at hc; exact hc.2
        exact Option.isNone_iff_eq_none.mp hh
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro hm
      obtain ⟨e', he', heq⟩ := List.mem_map.mp hm
      have hem := (selectedSources_sublist keys rest).subset he'
      exact lookupLast_none_keys hn e' hem heq
    · exact ih

end ZkFormal.NearV3.Rcpt.Candidates
