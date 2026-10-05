import ZkFormal.Near.Spec.Prune
import ZkFormal.Near.Air

/-!
# ZkFormal.Near.Honest — `extOf` (witness → records) and `render` (records → trace)

* `extOf c w` (`Near.Spec.Prune`) prunes the witness trie to the touched paths;
* `render c e` is the honest trace of every table (the SHA table through L5's
  generator on the messages the NEAR tables emit).

SKELETON: both bodies are placeholders until sub-lanes L6a (pruning) and L6e
(trace generation) land; the statements in `Near.Statements` are about these
names and do not change when the bodies do.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

/-- The honest trace of records. -/
def render (_c : Claim) (_e : Ext) : Trace Fp := ⟨fun _ => 1, fun _ _ _ => 0⟩

/-- **The honest trace** of a claim and witness. -/
def honestTrace (c : WfClaim) (w : Witness) : Trace Fp := render c.1 (extOf c.1 w)

end ZkFormal.Near
