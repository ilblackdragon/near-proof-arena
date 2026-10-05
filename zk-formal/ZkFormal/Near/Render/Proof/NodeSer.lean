import ZkFormal.Near.Render.Proof.NodeViewFacts
import ZkFormal.Near.Render.Proof.BusBytes

/-!
# ZkFormal.Near.Render.Proof.NodeSer — `NodeSerStmt` (under `KeyBound`)

The honest node views serialize as `mkInfo`'s `pre`/`post` (`view_pre`,
`view_post`).  This needs every revealed key to have fewer than 510 nibbles
(`KeyBound`, R-L6e-2): the view writes the hex-prefix length as one byte.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near NodeInfo

/-- **`NodeSerStmt`** with the extra hypothesis `KeyBound e`. -/
theorem nodeSer' : ∀ (c : WfClaim) (e : Ext), Good c.1 e → KeyBound e → ∀ n, n < e.ns.length →
    (nodeViewOf (mkInfo c.1 e) (edgeUses (bundle c.1 e).walks) n).v.ser false = (mkInfo c.1 e).pre.getD n [] ∧
    (nodeViewOf (mkInfo c.1 e) (edgeUses (bundle c.1 e).walks) n).v.ser true = (mkInfo c.1 e).post.getD n [] := by
  intro c e hg hk n hn
  simp only [nodeViewOf, info_nodeAt hn]
  exact ⟨view_pre hg hn (hk _ (List.getElem_mem hn)), view_post hg hn (hk _ (List.getElem_mem hn))⟩

theorem nodeSer_of (h : ∀ (c : Claim) (e : Ext), Good c e → Small e → KeyBound e) : NodeSerStmt :=
  fun c e hg hs => nodeSer' c e hg (h c.1 e hg hs)

/-- **`NodeSerStmt`.** -/
theorem nodeSer_ok : NodeSerStmt := nodeSer_of fun _ _ _ hs => hs.keys

end ZkFormal.Near.Render
