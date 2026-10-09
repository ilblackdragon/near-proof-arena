import ZkFormal.NearV3.Assembly.Witness
import ZkFormal.NearV3.Assembly.StoreNormal

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

/-- Encoder normalization preserves the exact native trie for every key set. -/
theorem ExtV3.store_partialTrie (x : ExtV3) (tau : Nat) (root : Bytes)
    (keys : List (List Nat)) :
    partialTrie (x.store tau) root keys = partialTrie (x.rawStore tau) root keys :=
  partialTrie_eraseDups _ _ _

theorem ExtV3.store_cost (x : ExtV3) (tau : Nat) :
    storeCost (x.store tau) ≤ storeCost (x.rawStore tau) := storeCost_eraseDups _

/-- The occurrence-view constructor's exact raw-store identity supplies a
nonexpanding encoded-store bound, including shared nodes and node/value overlap. -/
theorem ExtV3.store_cost_from_tree (x : ExtV3) (tau : Nat) (ws : List Bytes)
    (t : PTrie) (hv : x.rawStore tau = (occs t).map nodeEnc ++ valsOf t)
    (ht : Stored (mkStore ws) t) : storeCost (x.store tau) ≤ storeCost ws := by
  simpa only [ExtV3.store, hv, normalStore] using normalStore_cost ht

end ZkFormal.NearV3.Assembly
