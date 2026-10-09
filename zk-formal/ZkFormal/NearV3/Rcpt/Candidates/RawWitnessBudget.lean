import ZkFormal.NearV3.Rcpt.Candidates.WireConsumption
import ZkFormal.NearV3.Rcpt.Candidates.PathConsumption
import ZkFormal.NearV3.Rcpt.Link.CheckSources

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Sched

/-- Charge every decoded dictionary path item directly to the raw witness byte stream. -/
theorem decodeStateWitness_path_bytes {raw : Bytes} {w : StateWitness}
    (h : decodeStateWitness raw = .ok w) : 33 * pathCount w.entries ≤ raw.length := by
  unfold decodeStateWitness at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    have hc := pEntries_cost (by assumption)
    have hu := pUInt_le
    have hh := pHash_le
    have hhead := pChunkHeader_le
    have htr := pTransition_le
    unfold NonIncreasing at hu hh hhead htr
    simp only [pU8, pU32, readU8, readU32] at *
    grind only

private theorem lenAcc_eq (bs : Bytes) (n : Nat) : lenAcc bs n = bs.length + n := by
  induction bs generalizing n with
  | nil => simp [lenAcc]
  | cons b rest ih => simp only [lenAcc, List.length_cons, ih]; omega

theorem lenT_eq_length (bs : Bytes) : lenT bs = bs.length := by
  simpa [lenT] using lenAcc_eq bs 0

/-- All uniquely selected source path items fit the raw 8 MiB witness budget, even
when the encoded dictionary contains duplicate keys and unused filler entries. -/
theorem raw_selected_path_budget {raw : Bytes} {w : StateWitness}
    (hw : decodeStateWitness raw = .ok w) (hb : lenT raw ≤ witnessBytes) (keys : List Bytes) :
    pathCount (selectedSources keys w.entries) ≤ distinctPathItems := by
  have hp := decodeStateWitness_path_bytes hw
  have hs := selected_pathCount_le keys w.entries
  rw [lenT_eq_length] at hb
  apply encoded_paths_bound
  omega

/-- Successful unchanged D0a validation supplies the raw bound needed by deduplication. -/
theorem relD0a_selected_path_budget {B : Nat} {cb wb : Bytes} (h : RelD0a B cb wb) :
    ∃ raw codes w,
      decodeWitnessFile wb = .ok (raw, codes) ∧ decodeStateWitness raw = .ok w ∧
      ∀ keys, pathCount (selectedSources keys w.entries) ≤ distinctPathItems := by
  obtain ⟨raw, codes, w, hf, hw, hb, _⟩ := relD0a_source_paths h
  exact ⟨raw, codes, w, hf, hw, fun keys => raw_selected_path_budget hw hb keys⟩

end ZkFormal.NearV3.Rcpt.Candidates
