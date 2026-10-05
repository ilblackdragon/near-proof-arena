import ZkFormal.Near.Render.Proof.NodeBool
import ZkFormal.Near.Render.Proof.NodeTrans2
import ZkFormal.Near.Render.Proof.NodeLinks4

/-!
# ZkFormal.Near.Render.Proof.NodeLocal — `NodeLocalStmt`

The honest node table is locally legal: its height is in `[2, 2^22]`
(`node_log`), its multiplicity bits are boolean (`node_bits`), and every
constraint vanishes on every row (`constr_of` and one `GroupOk` per
constraint group: `cBool_ok`, `cRows_ok`, `cTrans_ok`, `cFields_ok`,
`cBytes_ok`, `cWindows_ok`, `cLinks_ok`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

namespace NodeRow

theorem constraints_ok {c : Claim} {e : Ext} (hg : Good c e) (hs : Small e) : GroupOk c e Node.constraints := by
  unfold Node.constraints
  exact groupOk_append _ _ (groupOk_append _ _ (groupOk_append _ _ (groupOk_append _ _ (groupOk_append _ _
    (groupOk_append _ _ (cBool_ok c e) (cRows_ok hg hs)) (cTrans_ok hg hs)) (cFields_ok hg hs))
    (cBytes_ok hg hs)) (cWindows_ok hg hs)) (cLinks_ok hg hs)

end NodeRow

/-- **`NodeLocalStmt`**: the honest node table is locally legal. -/
theorem nodeLocal : NodeLocalStmt := by
  intro c e hg hs
  exact ⟨(NodeLoc.node_log hg hs).1, (NodeLoc.node_log hg hs).2,
    NodeRow.constr_of (NodeRow.constraints_ok hg hs), NodeLoc.node_bits hg⟩

end ZkFormal.Near.Render
