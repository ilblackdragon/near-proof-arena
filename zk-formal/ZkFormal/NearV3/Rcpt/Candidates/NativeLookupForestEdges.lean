import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupEdgeCoverage

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

/-- A tree's selected provider segment embeds into the unchanged whole forest. -/
theorem indexed_forest_tree_edges (before after : List PTrie) (tree : PTrie)
    (tau nid vid : Nat) (e : Msg)
    (he : e∈indexedNodeEdges (nid+forestLookupNid before)
      (seedNodesT (tau+before.length) 0 (nid+forestLookupNid before)
        (vid+forestLookupVid before) tree)) :
    e∈indexedNodeEdges nid (forestNodes tau nid vid (before++tree::after)) := by
  induction before generalizing tau nid vid with
  | nil=>
    simp only [List.nil_append,forestNodes,indexedNodeEdges_append,seedNodesT_length]
    apply List.mem_append_left
    simpa [forestLookupNid,forestLookupVid,forestBytes] using he
  | cons t before ih=>
    simp only [List.cons_append,forestNodes,indexedNodeEdges_append,seedNodesT_length]
    apply List.mem_append_right
    apply ih (tau+1) (nid+tsize t) (vid+(valsOf t).length)
    simpa [forestLookupNid,forestLookupVid,forestBytes,List.flatMap_cons,
      List.length_append,tsize,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he

/-- Honest arbitrary-key EDGE coverage in the actual global store, preserving
transition occurrence, order, and compact IDs. No local-Wf/provider assumptions. -/
theorem native_forest_edge_coverage (before after : List PTrie) (tree : PTrie)
    (key : List Nat) (steps : List WStep3)
    (h : nativeLookupSteps (forestLookupNid before) (forestLookupVid before) tree key=some steps) :
    ∀s∈steps,s.mode≤1→s.e∈nodeEdgeKeys (forestStoreViews (before++tree::after)).nodes := by
  intro s hs hm
  rw [←indexedNodeEdges_zero]
  apply indexed_forest_tree_edges before after tree 0 0 0
  simpa only [Nat.zero_add] using nativeLookup_edge_coverage before.length 0
    (forestLookupNid before) (forestLookupVid before) tree key steps h s hs hm

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
