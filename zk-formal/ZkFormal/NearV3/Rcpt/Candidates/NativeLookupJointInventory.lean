import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupQueryList
import ZkFormal.NearV3.Rcpt.Candidates.UpsRequestInventory

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen UpsRows Assembly

/-- Ranking the joined inventory carries all earlier query requests into UPS.
This is a request inventory identity, not Walk-table validity of UPS padding. -/
theorem rankWalks_append (a b : List WalkR) (p : List WStep3) :
    rankWalks p (a++b)=rankWalks p a++rankWalks (p++a.flatMap (·.steps)) b := by
  induction a generalizing p with
  | nil=>simp [rankWalks]
  | cons w a ih=>simp [rankWalks,ih,List.append_assoc]

theorem native_query_ups_coverage (pairs : List (PTrie×PTrie)) (qs : List NativeLookupQuery)
    (ws : List WalkR) (insts : List Render.UpsInst) (hq : nativeQueryWalks pairs qs=some ws)
    (hu : ∀I∈insts,∃run,InstOk I ∧ DispatchNativeWalkProviders pairs run I ∧ I.ci=run.terminal.ix) :
    (∀e∈walkEdgeKeys (ws++upsWalkInventory insts),e∈headEdgeKeys (forestWalkHeads 0 0 pairs)++
      nodeEdgeKeys (forestStoreViews (pairs.map Prod.fst)).nodes) ∧
    (∀e∈walkBmapKeys (ws++upsWalkInventory insts),e∈nodeBitmapKeys (forestStoreViews (pairs.map Prod.fst)).nodes) := by
  have hqc:=nativeQueryWalks_coverage pairs qs ws hq
  have hue:=ups_edge_inventory_coverage pairs insts (by
    intro I hI
    obtain ⟨run,ho,hp,hi⟩:=hu I hI
    exact ⟨run,ho,dispatchProviders_forget hp,hi⟩)
  have hub:=ups_bitmap_inventory_coverage pairs insts hu
  constructor
  · intro e he
    simp only [walkEdgeKeys,List.flatMap_append,List.filterMap_append,List.mem_append] at he
    exact he.elim (hqc.1 e) (hue e)
  · intro e he
    simp only [walkBmapKeys,List.flatMap_append,List.filterMap_append,List.mem_append] at he
    exact he.elim (hqc.2 e) (hub e)

theorem native_query_ups_edge_balance (pairs : List (PTrie×PTrie)) (qs : List NativeLookupQuery)
    (ws : List WalkR) (insts : List Render.UpsInst) (hq : nativeQueryWalks pairs qs=some ws)
    (hu : ∀I∈insts,∃run,InstOk I ∧ DispatchNativeWalkProviders pairs run I ∧ I.ci=run.terminal.ix)
    (hh : ((forestWalkHeads 0 0 pairs).map HeadE.tau).Nodup)
    (hn : ∀s∈(forestStoreViews (pairs.map Prod.fst)).nodes,s.v.wf)
    (q : UseRequests) (he : q.edges=walkEdgeKeys (ws++upsWalkInventory insts)) :
    let hs:=forestWalkHeads 0 0 pairs
    let ns:=(forestStoreViews (pairs.map Prod.fst)).nodes
    (headSends (assignHeadUses q.edges hs) B_EDGE++nodeSends3 (assignList q 0 ns) B_EDGE++
      walkSends3 (rankWalks [] (ws++upsWalkInventory insts)) B_EDGE).Perm
    (headRecvs (assignHeadUses q.edges hs) B_EDGE++nodeRecvs3 (assignList q 0 ns) B_EDGE++
      walkRecvs3 (rankWalks [] (ws++upsWalkInventory insts)) B_EDGE) :=
  concrete_head_node_edge_balance _ _ _ q he hh hn (native_query_ups_coverage pairs qs ws insts hq hu).1

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
