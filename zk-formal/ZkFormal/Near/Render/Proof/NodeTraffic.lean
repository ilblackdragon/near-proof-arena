import ZkFormal.Near.Render.Proof.NodeTraffic7

/-!
# ZkFormal.Near.Render.Proof.NodeTraffic — `NodeTrafficStmt`

The node table of `render` has exactly the honest node views' traffic:
BYTES, VSLOT, PARENT receives (`NodeTraffic2`), DIGEST, PARENT sends
(`NodeTraffic4`), EDGE (`NodeTraffic5–7`), nothing else.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false

namespace NodeTr
open NodeCells NodeGen NodeInfo

section
variable {c : WfClaim} {e : Ext} (hg : Good c.1 e) (hs : Small e)
include hg hs

theorem tEdge (s : Bool) : ((List.range e.ns.length).flatMap fun n => (nodeRecs (mkInfo c.1 e) n).flatMap fun r =>
      RT (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e))) (publicOf c) r B_EDGE s).Perm
      ((if s then nodeSends (nodeViewsOf (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e)))) B_EDGE
        else nodeRecvs (nodeViewsOf (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e)))) (publicOf c) B_EDGE).map
          Msg.toFp) := by
  have hrow : ∀ n, n < e.ns.length → ((nodeRecs (mkInfo c.1 e) n).flatMap fun r =>
      RT (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e))) (publicOf c) r B_EDGE s) =
      (((nodeRecs (mkInfo c.1 e) n).flatMap (ge (mkInfo c.1 e))).map fun ed =>
        ed ++ [if s then 0 else (edgeUses (walksOf (mkInfo c.1 e))).getD ed 0]).map Msg.toFp := by
    intro n _
    simp only [RT_edge_sem, List.map_flatMap]
  rw [flatMap_congr' fun n hn => hrow n (List.mem_range.1 hn)]
  cases s with
  | true =>
    simp only [if_true, nodeSends, B_BYTES, B_PARENT, B_EDGE, Nat.reduceEqDiff, if_false, zipViews, info_N,
      List.flatMap_map, ↓reduceIte]
    rw [List.map_flatMap]
    apply perm_flatMap_congr; intro n hn
    exact ((node_edges hg hs _ (List.mem_range.1 hn)).map _).map _
  | false =>
    simp only [Bool.false_eq_true, if_false, nodeRecvs, B_DIGEST, B_PARENT, B_VSLOT, B_EDGE, Nat.reduceEqDiff,
      zipViews, info_N, List.flatMap_map, ↓reduceIte]
    rw [List.map_flatMap]
    apply perm_flatMap_congr; intro n hn
    simp only [Function.comp_apply, nodeViewOf]
    have hz := BusEdge.zip_map_self (fun ed => (edgeUses (walksOf (mkInfo c.1 e))).getD ed 0) (fun a b => a ++ [b])
      (edgesOf n (nodeViewOf (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e))) n))
    exact (((node_edges hg hs (edgeUses (walksOf (mkInfo c.1 e))) (List.mem_range.1 hn)).map _).map _).trans
      (List.Perm.of_eq (by rw [← hz]; rfl))

end

end NodeTr

open NodeTr NodeCells in
/-- **`NodeTrafficStmt`.** -/
theorem nodeTraffic_ok : NodeTrafficStmt := by
  intro c e hg hs
  have htf : htf c.1 e T_NODE = nodeTraffic (nodeViewsOf (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e))))
      (publicOf c) := rfl
  rw [htf]
  apply traffic_of
  · intro b
    rw [rows_decomp hg]
    by_cases h0 : b = B_BYTES
    · subst h0; exact tBytes hg hs
    by_cases h2 : b = B_PARENT
    · subst h2; exact tParentS hg hs
    by_cases h4 : b = B_EDGE
    · subst h4; exact tEdge hg hs true
    rw [flatMap_nil' fun n _ => flatMap_nil' fun r _ => RT_other _ _ _ _ b true (by simp [h0]) (by simp)
      h2 (by simp) h4]
    simp [nodeTraffic, nodeSends, h0, h2, h4]
  · intro b
    rw [rows_decomp hg]
    by_cases h1 : b = B_DIGEST
    · subst h1; exact tDigest hg hs
    by_cases h2 : b = B_PARENT
    · subst h2; exact tParentR hg hs
    by_cases h3 : b = B_VSLOT
    · subst h3; exact tVslot hg hs
    by_cases h4 : b = B_EDGE
    · subst h4; exact tEdge hg hs false
    rw [flatMap_nil' fun n _ => flatMap_nil' fun r _ => RT_other _ _ _ _ b false (by simp) (by simp [h1])
      h2 (by simp [h3]) h4]
    simp [nodeTraffic, nodeRecvs, h1, h2, h3, h4]

end ZkFormal.Near.Render
