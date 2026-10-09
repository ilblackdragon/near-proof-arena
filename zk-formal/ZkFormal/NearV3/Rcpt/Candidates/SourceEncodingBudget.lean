import ZkFormal.NearV3.Rcpt.Candidates.SourceDictionary
import ZkFormal.NearV3.Rcpt.Candidates.SourceBudget

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3

/-- Number of actual encoded path items, without occurrence replay. -/
def pathCount (entries : List ProofEntry) : Nat :=
  (entries.map fun e => e.proof.path.length).sum

theorem encoded_path_length (path : List (Bytes × Nat))
    (h : ∀ s ∈ path, s.1.length = 32) :
    (concatAll (path.map ZkFormal.V3.encodePathItem)).length = 33 * path.length := by
  induction path with
  | nil => simp [concatAll]
  | cons s rest ih =>
    have hs := h s (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, concatAll, List.length_append, List.length_cons]
    rw [ht]
    simp only [ZkFormal.V3.encodePathItem, List.length_append, u8, leN, List.length_cons, List.length_nil, hs]
    omega

/-- Every selected item is charged 33 bytes in the canonical witness-entry encoding. -/
theorem encoded_entry_path_le (e : ProofEntry)
    (h : ∀ s ∈ e.proof.path, s.1.length = 32) :
    33 * e.proof.path.length ≤ (ZkFormal.V3.encodeEntry e).length := by
  have hp := encoded_path_length e.proof.path h
  simp only [ZkFormal.V3.encodeEntry, encList, List.length_append]
  omega

theorem encoded_entries_paths_le (entries : List ProofEntry)
    (h : ∀ e ∈ entries, ∀ s ∈ e.proof.path, s.1.length = 32) :
    33 * pathCount entries ≤ (concatAll (entries.map ZkFormal.V3.encodeEntry)).length := by
  induction entries with
  | nil => simp [pathCount, concatAll]
  | cons e rest ih =>
    have hh := encoded_entry_path_le e (h e (by simp))
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [pathCount, List.map_cons, List.sum_cons, concatAll, List.length_append] at *
    omega

private theorem weighted_sublist {α : Type} (f : α → Nat) {xs ys : List α}
    (h : List.Sublist xs ys) : (xs.map f).sum ≤ (ys.map f).sum := by
  induction h with
  | slnil => simp
  | cons a h ih => simp only [List.map_cons, List.sum_cons]; omega
  | cons_cons a h ih => simp only [List.map_cons, List.sum_cons]; omega

/-- Deduplicating last-wins computations never repeats any encoded path item. -/
theorem selected_pathCount_le (keys : List Bytes) (entries : List ProofEntry) :
    pathCount (selectedSources keys entries) ≤ pathCount entries :=
  weighted_sublist _ (selectedSources_sublist keys entries)

/-- The unique-proof envelope follows from canonical encoded dictionary coverage.
The separate inverse-decoder/coverage bridge to the raw 8 MiB witness remains explicit. -/
theorem selected_path_budget (keys : List Bytes) (entries : List ProofEntry)
    (hshape : ∀ e ∈ entries, ∀ s ∈ e.proof.path, s.1.length = 32)
    (hbytes : (concatAll (entries.map ZkFormal.V3.encodeEntry)).length ≤ witnessBytes) :
    pathCount (selectedSources keys entries) ≤ distinctPathItems := by
  have h1 := encoded_entries_paths_le entries hshape
  have h2 := selected_pathCount_le keys entries
  apply encoded_paths_bound
  omega

end ZkFormal.NearV3.Rcpt.Candidates
