import ZkFormal.Near.Spec.Good

/-!
# ZkFormal.Near.Spec.Prune — records of a witness (`extOf`)

`extOf c w` prunes the witness trie to the nodes on the paths of the touched
keys (the receivers' account keys), numbers the revealed nodes (root `0`,
every node once), marks the receivers' value slots `touched` (their bytes go
to `vals0`), turns every other revealed value into a `ref`, and records each
receipt's slot.  Hashes are unchanged and `revealedOf ≤ revealedBytes`.

SKELETON: placeholder body until sub-lane L6-spec-complete lands.
-/

namespace ZkFormal.Near

open NearSpec NearSpec.TransferV1

/-- Records of a witness (pruned to the touched paths). -/
def extOf (_c : Claim) (w : Witness) : Ext :=
  { ns := [], vals0 := fun _ => [], rs := w.receipts, slot := fun _ => 0 }

end ZkFormal.Near
