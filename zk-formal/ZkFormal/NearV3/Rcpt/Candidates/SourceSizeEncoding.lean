import ZkFormal.NearV3.Rcpt.Candidates.SourceEncodingBudget
import ZkFormal.NearV3.Assembly.CodecSize
import ZkFormal.NearV3.Rcpt.Candidates.OrderedSources
import ZkFormal.NearV3.Rcpt.Link.WitnessSources

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3

/-- The source SIZE charge for one computed dictionary entry. -/
def entrySizeCharge (e : ProofEntry) : Nat :=
  (u64 e.proof.toShard ++ encList Receipt.encode e.receipts).length +
    33 * e.proof.path.length

/-- Encoded dictionary overhead pays at least one empty repeated-source header
per dictionary entry, without imposing any extra receipt or path bound. -/
theorem encoded_entry_charge (e : ProofEntry)
    (h : ∀ s ∈ e.proof.path, s.1.length = 32) :
    (ZkFormal.V3.encodeEntry e).length = entrySizeCharge e + e.key.length + 12 := by
  have hp := encoded_path_length e.proof.path h
  simp only [ZkFormal.V3.encodeEntry, entrySizeCharge, encList, List.length_append]
  simp only [u64, u32, leN, List.length_cons, List.length_nil] at *
  omega

theorem encoded_entries_charge (entries : List ProofEntry)
    (h : ∀ e ∈ entries, ∀ s ∈ e.proof.path, s.1.length = 32) :
    (entries.map entrySizeCharge).sum + 12 * entries.length ≤
      (concatAll (entries.map ZkFormal.V3.encodeEntry)).length := by
  induction entries with
  | nil => simp [concatAll]
  | cons e es ih =>
    have he := encoded_entry_charge e (h e (by simp))
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, concatAll, List.length_append]
    omega

private theorem weighted_sublist {α : Type} (f : α → Nat) {xs ys : List α}
    (h : List.Sublist xs ys) : (xs.map f).sum ≤ (ys.map f).sum := by
  induction h with
  | slnil => simp
  | cons a h ih => simp only [List.map_cons, List.sum_cons]; omega
  | cons_cons a h ih => simp only [List.map_cons, List.sum_cons]; omega

/-- Unique last-wins source computations and one twelve-byte header per encoded
entry fit the actual raw witness, even when its encoding is not canonical. -/
theorem raw_computed_size_charge {raw : Bytes} {w : StateWitness}
    (hw : decodeStateWitness raw = .ok w) (computed : List ProofEntry)
    (hn : (computed.map ProofEntry.key).Nodup)
    (hl : ∀ e ∈ computed, lookupLast e.key w.entries = some e) :
    (computed.map entrySizeCharge).sum + 12 * w.entries.length ≤ raw.length := by
  have hp := ((computed_perm_selected computed w.entries hn hl).map entrySizeCharge).sum_nat
  have hs := weighted_sublist entrySizeCharge
    (selectedSources_sublist (computed.map ProofEntry.key) w.entries)
  have he := encoded_entries_charge w.entries
    (fun e he step hstep => (decodeStateWitness_path_shape hw e he step hstep).1)
  have hb := Assembly.decodeStateWitness_encodeSW_size hw
  have ht : (concatAll (w.entries.map ZkFormal.V3.encodeEntry)).length ≤
      (ZkFormal.V3.encodeSW w).length := by
    simp only [ZkFormal.V3.encodeSW, encList, List.length_append]
    omega
  omega

end ZkFormal.NearV3.Rcpt.Candidates
