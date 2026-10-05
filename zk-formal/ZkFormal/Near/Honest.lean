import ZkFormal.Near.Spec.Prune
import ZkFormal.Near.Air
import ZkFormal.Near.Render.Trace

/-!
# ZkFormal.Near.Honest — `extOf` (witness → records) and `render` (records → trace)

* `extOf c w` (`Near.Spec.Prune`) prunes the witness trie to the touched paths;
* `render c e` is the honest trace of every table (the SHA table through L5's
  generator on the messages the NEAR tables emit).

`render` is `Near.Render.render` (L6e); `extOf` is a placeholder until
sub-lane L6a (pruning) lands.  The statements in `Near.Statements` are about
these names and do not change when the bodies do.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

/-- The honest trace of records (`Render.render`, lane L6e). -/
def render (c : Claim) (e : Ext) : Trace Fp := Render.render c e

/-- **The honest trace** of a claim and witness. -/
def honestTrace (c : WfClaim) (w : Witness) : Trace Fp := render c.1 (extOf c.1 w)

end ZkFormal.Near
