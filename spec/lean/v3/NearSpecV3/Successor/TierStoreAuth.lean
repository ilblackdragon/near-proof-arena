import NearSpecV3.Successor.TierRefine
import NearSpecV3.Logged.TrieHash

/-!
# W12 / O7 — the witness store is content-addressed

Every whole-state shell builds the code store as `mkHStore merged` (`RuntimeCore.lean`), a binary
search tree keyed by `sha256 value`. Every value it returns hashes to the key it was looked up by
(`hGet_mkHStore_auth`), so the code sources the recorder engine passes to `resolveCodeBytes` are
`CodeSources.authentic` (`codeSources_authentic`), and on them the complete-code policy *is* the
cold one (`complete_eq_cold`, `complete_eq_cold_mkHStore`). This is the premise O7 needs at chunk
level.
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2

/-- Every node's value hashes to its key. -/
def _root_.NearSpecV3.D2.HStore.Auth : HStore → Prop
  | .tip => True
  | .node k v l r => sha256 v = k ∧ l.Auth ∧ r.Auth

theorem _root_.NearSpecV3.D2.HStore.Auth.insert {t : HStore} (ht : t.Auth) (v : Bytes) :
    (t.insert (sha256 v) v).Auth := by
  induction t with
  | tip => exact ⟨rfl, trivial, trivial⟩
  | node k' v' l r ihl ihr =>
    obtain ⟨hk, hl, hr⟩ := ht
    unfold HStore.insert
    split
    · exact ⟨hk, ihl hl, hr⟩
    · exact ⟨hk, hl, ihr hr⟩
    · rename_i h0 h2
      exact ⟨(Logged.cmpBytes_eq _ _ h0 h2).symm ▸ rfl, hl, hr⟩

theorem _root_.NearSpecV3.D2.HStore.Auth.get {t : HStore} (ht : t.Auth) (k v : Bytes) (h : t.get? k = some v) :
    sha256 v = k := by
  induction t with
  | tip => cases h
  | node k' v' l r ihl ihr =>
    obtain ⟨hk, hl, hr⟩ := ht
    unfold HStore.get? at h
    split at h
    · exact ihl hl h
    · exact ihr hr h
    · rename_i h0 h2
      cases h
      rw [hk, Logged.cmpBytes_eq _ _ h0 h2]

theorem mkHStore_auth (values : List Bytes) : (mkHStore values).Auth := by
  unfold mkHStore
  suffices ∀ (t : HStore), t.Auth → (values.foldl (fun m v => m.insert (sha256 v) v) t).Auth from
    this .tip trivial
  induction values with
  | nil => intro t ht; exact ht
  | cons v vs ih => intro t ht; exact ih _ (ht.insert v)

/-- **The witness store is content-addressed.** -/
theorem hGet_mkHStore_auth (values : List Bytes) (h v : Bytes) (hv : hGet (mkHStore values) h = some v) :
    sha256 v = h :=
  (mkHStore_auth values).get h v hv

/-- Code sources over a `mkHStore` store are authentic. -/
theorem codeSources_authentic (values : List Bytes) (current committed attempted : List Bytes)
    (hash : Bytes) :
    CodeSources.authentic { witness := hGet (mkHStore values), current, committed, attempted } hash :=
  fun code hc => hGet_mkHStore_auth values hash code hc

/-- On a `mkHStore` store the complete-code policy is the cold one. -/
theorem complete_eq_cold_mkHStore (values current committed attempted : List Bytes)
    (pre : PrestateCode) (hash : Bytes) (timely : Bool) :
    resolveCodeBytes .complete { witness := hGet (mkHStore values), current, committed, attempted }
        pre hash timely =
      resolveCodeBytes .coldPartial { witness := hGet (mkHStore values), current, committed, attempted }
        pre hash timely :=
  complete_eq_cold _ pre hash timely (codeSources_authentic values current committed attempted hash)

#print axioms hGet_mkHStore_auth
#print axioms complete_eq_cold_mkHStore

end NearSpecV3.Successor
