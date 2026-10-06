import NearSpecV3.ChunkValidationV0a

/-!
# A7 (`w.unfolded`): kernel-checked examples of shared subtrees

A store holding one leaf and one branch whose two slots both point to that leaf: the store
has 3 entries, but `partialTrie` reveals the leaf once per path copy, and `unfoldedBytesT`
counts both copies (node and value). This is the mechanism by which an adversarial
producer can push `unfoldBytes` far above `|base_state|` (spec/near-chunk-validation-v0a.md
§2.4 liveness note).
-/

namespace ZkFormal.V3.A7Examples

open NearSpec NearSpecV3

def v : Bytes := [7, 7, 7]
def lf : PTrie := .leaf [2, 3] (.val v) 100
def br : PTrie := .branch none (.some lf (.some lf .nil)) 300

/-- Both copies of the shared leaf count (node bytes and value bytes). -/
theorem unfolded_shared :
    unfoldedBytesT br = (nodeEnc br).length + 2 * ((nodeEnc lf).length + v.length) := by
  decide +kernel

/-- The same through the relation's builder: a 3-entry store, two read keys through the two
slots; the built trie has the same unfolded size as `br`, which exceeds the store's total
bytes. -/
theorem built_shared :
    unfoldedBytesT (partialTrie [nodeEnc lf, v, nodeEnc br] br.hashOf [[0, 2, 3], [1, 2, 3]]) =
      unfoldedBytesT br ∧
    unfoldedBytesT br > ([nodeEnc lf, v, nodeEnc br].map List.length).sum := by
  decide +kernel

end ZkFormal.V3.A7Examples
