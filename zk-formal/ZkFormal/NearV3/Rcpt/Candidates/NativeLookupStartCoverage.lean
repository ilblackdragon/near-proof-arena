import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupForestBitmaps

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

/-- START targets the resolved root of the same transition occurrence. -/
theorem native_start_provider (before after : List (PTrie×PTrie)) (tree post : PTrie)
    (tau nid : Nat) :
    [0,tau+before.length,SYM_START,viewTarget (nid+forestLookupNid (before.map Prod.fst)) tree,0,EK_DOWN]∈
      headEdgeKeys (forestWalkHeads tau nid (before++(tree,post)::after)) := by
  induction before generalizing tau nid with
  | nil=>simp [forestWalkHeads,headEdgeKeys,headEdgeKey,forestLookupNid]
  | cons pair before ih=>
    apply List.mem_cons_of_mem
    simpa [headEdgeKeys,forestLookupNid,List.flatMap_cons,List.length_append,tsize,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (tau+1) (nid+tsize pair.1)

/-- The complete wrapped lookup is covered by the actual HEAD and node EDGE
providers of the same pre/post forest. -/
theorem native_forest_walk_edges (before after : List (PTrie×PTrie)) (tree post : PTrie)
    (wid : Nat) (key : List Nat) (steps : List WStep3)
    (h : nativeLookupSteps (forestLookupNid (before.map Prod.fst))
      (forestLookupVid (before.map Prod.fst)) tree key=some steps) :
    ∀s∈(nativeLookupWalk wid before.length (forestLookupNid (before.map Prod.fst)) tree steps).steps,
      s.mode≤1→s.e∈headEdgeKeys (forestWalkHeads 0 0 (before++(tree,post)::after))++
        nodeEdgeKeys (forestStoreViews ((before++(tree,post)::after).map Prod.fst)).nodes := by
  intro s hs hm
  rcases List.mem_cons.mp hs with rfl|hs
  · apply List.mem_append_left
    simpa only [Nat.zero_add,lookupEdge] using native_start_provider before after tree post 0 0
  · apply List.mem_append_right
    simpa only [List.map_append,List.map_cons] using native_forest_edge_coverage
      (before.map Prod.fst) (after.map Prod.fst) tree key steps h s hs hm

theorem native_forest_walk_bitmaps (before after : List (PTrie×PTrie)) (tree post : PTrie)
    (wid : Nat) (key : List Nat) (steps : List WStep3)
    (h : nativeLookupSteps (forestLookupNid (before.map Prod.fst))
      (forestLookupVid (before.map Prod.fst)) tree key=some steps) :
    ∀s∈(nativeLookupWalk wid before.length (forestLookupNid (before.map Prod.fst)) tree steps).steps,
      s.mode=2→[s.e.getD 0 0,s.bm,s.hv]∈
        nodeBitmapKeys (forestStoreViews ((before++(tree,post)::after).map Prod.fst)).nodes := by
  intro s hs hm
  rcases List.mem_cons.mp hs with rfl|hs
  · change 0=2 at hm;omega
  · simpa only [List.map_append,List.map_cons] using native_forest_bitmap_coverage
      (before.map Prod.fst) (after.map Prod.fst) tree key steps h s hs hm

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
