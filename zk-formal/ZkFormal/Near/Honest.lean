import ZkFormal.Near.Spec.Good
import ZkFormal.Near.Air

/-!
# ZkFormal.Near.Honest — `extOf` (witness → records) and `render` (records → trace)

* `extOf c w` prunes the witness trie to the nodes on the touched paths and
  numbers them (root `0`); slots are the node ids of the receivers' values.
* `render c e` is the honest trace of every table (the SHA table through L5's
  generator on the messages the NEAR tables emit).

SKELETON: both bodies are placeholders until sub-lanes L6a (pruning) and L6e
(trace generation) land; the statements in `Near.Statements` are about these
names and do not change when the bodies do.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

/-- Records of a witness (pruned to the touched paths). -/
def extOf (_c : Claim) (w : Witness) : Ext :=
  { ns := [], vals0 := fun _ => [], rs := w.receipts, slot := fun _ => 0 }

/-- The honest trace of records. -/
def render (_c : Claim) (_e : Ext) : Trace Fp := ⟨fun _ => 1, fun _ _ _ => 0⟩

/-- **The honest trace** of a claim and witness. -/
def honestTrace (c : WfClaim) (w : Witness) : Trace Fp := render c.1 (extOf c.1 w)

end ZkFormal.Near
