import ZkFormal.NearV3.Rcpt.Candidates.NativeSetExists

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec

mutual
theorem native_set_input_value : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (t' : PTrie),
    t.set key v = some t' → ∃ old,t.find key = some (some old)
  | .hash _, _, _, _, h => by simp [PTrie.set] at h
  | .leaf k s m, key, v, t', h => by
    simp only [PTrie.set] at h
    split at h
    · rename_i e
      have e' : k = key := by simpa using e
      subst e'
      cases hs : s.get <;> simp [hs] at h; subst h; simp [PTrie.find, hs]
    · simp at h
  | .ext k c m, key, v, t', h => by
    simp only [PTrie.set] at h
    split at h
    · rename_i hp
      cases hs : c.set (key.drop k.length) v <;> simp [hs] at h; subst h
      simp [PTrie.find, hp, native_set_input_value c _ v _ hs]
    · simp at h
  | .branch bv cs m, [], v, t', h => by
    simp only [PTrie.set] at h
    split at h <;> simp at h; subst h; simp [PTrie.find, Slot.get]
  | .branch bv cs m, n :: rest, v, t', h => by
    simp only [PTrie.set] at h
    cases hs : Kids.set cs n rest v <;> simp [hs] at h; subst h
    simp only [PTrie.find]; exact native_kids_set_input_value cs n rest v _ hs
theorem native_kids_set_input_value : ∀ (cs : Kids) (n : Nat) (key : List Nat) (v : Bytes) (cs' : Kids),
    Kids.set cs n key v = some cs' → ∃ old,Kids.find cs n key = some (some old)
  | .nil, _, _, _, _, h => by simp [Kids.set] at h
  | .none _, 0, _, _, _, h => by simp [Kids.set] at h
  | .some c r, 0, key, v, cs', h => by
    simp only [Kids.set] at h
    cases hs : c.set key v <;> simp [hs] at h; subst h
    simp only [Kids.find]; exact native_set_input_value c key v _ hs
  | .none r, i + 1, key, v, cs', h => by
    simp only [Kids.set] at h
    cases hs : Kids.set r i key v <;> simp [hs] at h; subst h
    simp only [Kids.find]; exact native_kids_set_input_value r i key v _ hs
  | .some c r, i + 1, key, v, cs', h => by
    simp only [Kids.set] at h
    cases hs : Kids.set r i key v <;> simp [hs] at h; subst h
    simp only [Kids.find]; exact native_kids_set_input_value r i key v _ hs
end

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
