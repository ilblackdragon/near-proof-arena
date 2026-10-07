import ZkFormal.NearV3.Assembly.ReceiptShape

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpec.TransferV1 NearSpecV3 ReexecV3D0

mutual
theorem set_input_known : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (t' : PTrie),
    t.set key v = some t' → t.find key ≠ none
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
      simp [PTrie.find, hp, set_input_known c _ v _ hs]
    · simp at h
  | .branch bv cs m, [], v, t', h => by
    simp only [PTrie.set] at h
    split at h <;> simp at h; subst h; simp [PTrie.find, Slot.get]
  | .branch bv cs m, n :: rest, v, t', h => by
    simp only [PTrie.set] at h
    cases hs : Kids.set cs n rest v <;> simp [hs] at h; subst h
    simp only [PTrie.find]; exact kids_set_input_known cs n rest v _ hs
theorem kids_set_input_known : ∀ (cs : Kids) (n : Nat) (key : List Nat) (v : Bytes) (cs' : Kids),
    Kids.set cs n key v = some cs' → Kids.find cs n key ≠ none
  | .nil, _, _, _, _, h => by simp [Kids.set] at h
  | .none _, 0, _, _, _, h => by simp [Kids.set] at h
  | .some c r, 0, key, v, cs', h => by
    simp only [Kids.set] at h
    cases hs : c.set key v <;> simp [hs] at h; subst h
    simp only [Kids.find]; exact set_input_known c key v _ hs
  | .none r, i + 1, key, v, cs', h => by
    simp only [Kids.set] at h
    cases hs : Kids.set r i key v <;> simp [hs] at h; subst h
    simp only [Kids.find]; exact kids_set_input_known r i key v _ hs
  | .some c r, i + 1, key, v, cs', h => by
    simp only [Kids.set] at h
    cases hs : Kids.set r i key v <;> simp [hs] at h; subst h
    simp only [Kids.find]; exact kids_set_input_known r i key v _ hs
end

theorem applyReceipt_write_known {ctx : Ctx} {st out : Acc} {r : Receipt}
    (h : applyReceipt ctx st r = some out) :
    st.trie.find (accountKeyPath r.receiverId) ≠ none := by
  obtain ⟨bytes,hs⟩ := Qv.applyReceipt_set h
  exact set_input_known _ _ bytes _ hs

theorem applySystemReceipt_write_known {st out : Acc} {r : Receipt}
    (h : applySystemReceipt st r = .ok out) :
    st.trie.find (accountKeyPath r.receiverId) ≠ none := by
  obtain ⟨bytes,hs⟩ := Qv.applySystemReceipt_set h
  exact set_input_known _ _ bytes _ hs

end ZkFormal.NearV3.Assembly
