import ZkFormal.NearV3.Assembly.TrieShape
import ZkFormal.NearV3.Spec.TrieOps

namespace ZkFormal.NearV3.Assembly
open NearSpec

mutual
theorem shape_set : ∀ (t : PTrie) (key : List Nat) (v : Bytes) (t' : PTrie),
    TrieShape t → t.set key v = some t' → TrieShape t'
  | .hash _, _, _, _, ht, h => by simp [PTrie.set] at h
  | .leaf k s m, key, v, t', ht, h => by
    simp only [PTrie.set] at h
    split at h
    · rename_i e
      have e' : k = key := by simpa using e
      subst e'
      cases hs : s.get <;> simp [hs] at h; subst h; exact ht
    · simp at h
  | .ext k c m, key, v, t', ht, h => by
    simp only [PTrie.set] at h
    split at h
    · rename_i hp
      cases hs : c.set (key.drop k.length) v <;> simp [hs] at h; subst h
      exact ⟨ht.1, shape_set c _ v _ ht.2 hs⟩
    · simp at h
  | .branch bv cs m, [], v, t', ht, h => by
    simp only [PTrie.set] at h
    split at h <;> simp at h; subst h; exact ht
  | .branch bv cs m, n :: rest, v, t', ht, h => by
    simp only [PTrie.set] at h
    cases hs : Kids.set cs n rest v <;> simp [hs] at h; subst h
    exact shape_kids_set cs n rest v _ ht hs
theorem shape_kids_set : ∀ (cs : Kids) (n : Nat) (key : List Nat) (v : Bytes) (cs' : Kids),
    KidsShape cs → Kids.set cs n key v = some cs' → KidsShape cs'
  | .nil, _, _, _, _, ht, h => by simp [Kids.set] at h
  | .none _, 0, _, _, _, ht, h => by simp [Kids.set] at h
  | .some c r, 0, key, v, cs', ht, h => by
    simp only [Kids.set] at h
    cases hs : c.set key v <;> simp [hs] at h; subst h
    exact ⟨shape_set c key v _ ht.1 hs, ht.2⟩
  | .none r, i + 1, key, v, cs', ht, h => by
    simp only [Kids.set] at h
    cases hs : Kids.set r i key v <;> simp [hs] at h; subst h
    simpa only [KidsShape] using shape_kids_set r i key v _ ht hs
  | .some c r, i + 1, key, v, cs', ht, h => by
    simp only [Kids.set] at h
    cases hs : Kids.set r i key v <;> simp [hs] at h; subst h
    exact ⟨ht.1, shape_kids_set r i key v _ ht.2 hs⟩
end

theorem set_known {pre post : PTrie} {key query : List Nat} {value : Bytes}
    (hu : pre.set key value = some post) (hq : pre.find query ≠ none) :
    post.find query ≠ none := by
  by_cases he : query=key
  · subst query
    rw [ZkFormal.NearV3.PTrie.find_set_self _ _ _ _ hu]
    simp
  · rw [ZkFormal.NearV3.PTrie.find_set_ne _ _ _ _ _ hu he]
    exact hq

end ZkFormal.NearV3.Assembly
