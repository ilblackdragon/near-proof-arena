import ZkFormal.NearV3.Rcpt.Candidates.RawWitnessBudget
import ZkFormal.NearV3.Rcpt.Candidates.SourceCount

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3

/-- Compute selected proofs once, in first-source-key order. Encoded dictionary order,
including unused filler entries, remains untouched. -/
def orderedSources (keys : List Bytes) (entries : List ProofEntry) : List ProofEntry :=
  keys.eraseDups.filterMap (fun key => lookupLast key entries)

private theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] (xs : List α) :
    xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons a rest =>
    rw [List.eraseDups_cons, List.nodup_cons]
    constructor
    · simp
    · exact eraseDups_nodup (rest.filter fun b => !b == a)
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem lookupLast_key {key : Bytes} {entries : List ProofEntry} {e : ProofEntry}
    (h : lookupLast key entries = some e) : e.key = key := by
  induction entries with
  | nil => cases h
  | cons a rest ih =>
    simp only [lookupLast] at h
    split at h
    · rename_i f hf
      cases h
      exact ih hf
    · split at h
      · rename_i he
        cases h
        simpa using he
      · cases h

private theorem selected_mem_lookup (keys : List Bytes) (entries : List ProofEntry)
    (e : ProofEntry) (he : e ∈ selectedSources keys entries) : lookupLast e.key entries = some e := by
  induction entries with
  | nil => simp [selectedSources] at he
  | cons a rest ih =>
    unfold selectedSources at he
    split at he
    · rename_i hc
      rcases List.mem_cons.mp he with rfl | he
      · have hn : lookupLast e.key rest = none := by
          have hh : (lookupLast e.key rest).isNone = true := by
            simp only [Bool.and_eq_true] at hc; exact hc.2
          exact Option.isNone_iff_eq_none.mp hh
        simp [lookupLast, hn]
      · have ht := ih he
        simp [lookupLast, ht]
    · have ht := ih he
      simp [lookupLast, ht]

theorem orderedSources_keys_nodup (keys : List Bytes) (entries : List ProofEntry) :
    ((orderedSources keys entries).map ProofEntry.key).Nodup := by
  have hn := eraseDups_nodup keys
  unfold orderedSources
  rw [List.map_filterMap]
  apply hn.filterMap
  intro a b hab e he f hf
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp he
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hf
  simpa only [lookupLast_key hp, lookupLast_key hq] using hab

/-- The source-order computation is exactly a permutation of the already budgeted
last-wins dictionary selection. Thus ordering cannot multiply path work. -/
theorem orderedSources_perm (keys : List Bytes) (entries : List ProofEntry) :
    (orderedSources keys entries).Perm (selectedSources keys entries) := by
  have hn1 : (orderedSources keys entries).Nodup :=
    List.Pairwise.of_map ProofEntry.key (fun a b hne he => hne (congrArg ProofEntry.key he))
      (orderedSources_keys_nodup keys entries)
  have hn2 : (selectedSources keys entries).Nodup :=
    List.Pairwise.of_map ProofEntry.key (fun a b hne he => hne (congrArg ProofEntry.key he))
      (selectedSources_keys_nodup keys entries)
  apply (List.perm_ext_iff_of_nodup hn1 hn2).mpr
  intro e
  constructor
  · intro he
    obtain ⟨key, hk, hl⟩ := List.mem_filterMap.mp he
    have hk' := List.mem_eraseDups.mp hk
    have hs : lookupLast key (selectedSources keys entries) = some e := by
      rw [selectedSources_lookup keys entries key hk']; exact hl
    exact lookupLast_mem hs
  · intro he
    apply List.mem_filterMap.mpr
    have hk : e.key ∈ keys := selectedSources_keys_subset keys entries e he
    exact ⟨e.key, List.mem_eraseDups.mpr hk, selected_mem_lookup keys entries e he⟩

theorem orderedSources_pathCount (keys : List Bytes) (entries : List ProofEntry) :
    pathCount (orderedSources keys entries) = pathCount (selectedSources keys entries) :=
  ((orderedSources_perm keys entries).map (fun (e : ProofEntry) => e.proof.path.length)).sum_nat

/-- Actual raw decoding bounds first-occurrence-ordered proof computation. -/
theorem raw_ordered_path_budget {raw : Bytes} {w : StateWitness}
    (hw : decodeStateWitness raw = .ok w) (hb : lenT raw ≤ witnessBytes) (keys : List Bytes) :
    pathCount (orderedSources keys w.entries) ≤ distinctPathItems := by
  rw [orderedSources_pathCount]
  exact raw_selected_path_budget hw hb keys

/-- Any distinct-key ordering of actual selected entries is exactly its dictionary
selection; useful for binding concrete source-row generators to the raw budget. -/
theorem computed_perm_selected (computed entries : List ProofEntry)
    (hn : (computed.map ProofEntry.key).Nodup)
    (hl : ∀ e ∈ computed, lookupLast e.key entries = some e) :
    computed.Perm (selectedSources (computed.map ProofEntry.key) entries) := by
  have hn1 : computed.Nodup := List.Pairwise.of_map ProofEntry.key
    (fun a b hne he => hne (congrArg ProofEntry.key he)) hn
  have hn2 : (selectedSources (computed.map ProofEntry.key) entries).Nodup :=
    List.Pairwise.of_map ProofEntry.key (fun a b hne he => hne (congrArg ProofEntry.key he))
      (selectedSources_keys_nodup _ entries)
  apply (List.perm_ext_iff_of_nodup hn1 hn2).mpr
  intro e
  constructor
  · intro he
    apply lookupLast_mem (key := e.key)
    rw [selectedSources_lookup _ _ _ (List.mem_map.mpr ⟨e, he, rfl⟩)]
    exact hl e he
  · intro he
    obtain ⟨f, hf, hk⟩ := List.mem_map.mp (selectedSources_keys_subset _ entries e he)
    have hs := selected_mem_lookup _ entries e he
    have ht := hl f hf
    rw [hk] at ht
    have hef := Option.some.inj (ht.symm.trans hs)
    exact hef ▸ hf

theorem raw_computed_path_budget {raw : Bytes} {w : StateWitness}
    (hw : decodeStateWitness raw = .ok w) (hb : lenT raw ≤ witnessBytes)
    (computed : List ProofEntry) (hn : (computed.map ProofEntry.key).Nodup)
    (hl : ∀ e ∈ computed, lookupLast e.key w.entries = some e) :
    pathCount computed ≤ distinctPathItems := by
  have hp := ((computed_perm_selected computed w.entries hn hl).map
    (fun (e : ProofEntry) => e.proof.path.length)).sum_nat
  change pathCount computed = pathCount (selectedSources (computed.map ProofEntry.key) w.entries) at hp
  rw [hp]
  exact raw_selected_path_budget hw hb _

end ZkFormal.NearV3.Rcpt.Candidates
