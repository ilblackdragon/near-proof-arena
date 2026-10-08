import ZkFormal.NearV3.Rcpt.Candidates.NativeReplayHeadKeys
import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupJointInventory

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen UpsRows Assembly

/-- Query paths read the original state. UPS paths read the receipt-replayed
state. Both inventories are supplied by the same original occurrence IDs. -/
theorem native_rebased_query_ups_coverage
    (rs : List ReplayTree) (original rebased : List (PTrie×PTrie))
    (ha : original.map Prod.fst=rs.map ReplayTree.pre)
    (hb : rebased.map Prod.fst=rs.map ReplayTree.post) (hv : ∀r∈rs,r.Valid)
    (qs : List NativeLookupQuery) (ws : List WalkR) (insts : List Render.UpsInst)
    (hq : nativeQueryWalks original qs=some ws)
    (hu : ∀I∈insts,∃run,InstOk I ∧ DispatchNativeWalkProviders rebased run I ∧ I.ci=run.terminal.ix) :
    (∀e∈walkEdgeKeys (ws++upsWalkInventory insts),
      e∈headEdgeKeys (forestWalkHeads 0 0 original)++
        nodeEdgeKeys (forestStoreViews (original.map Prod.fst)).nodes) ∧
    (∀e∈walkBmapKeys (ws++upsWalkInventory insts),
      e∈nodeBitmapKeys (forestStoreViews (original.map Prod.fst)).nodes) := by
  have hheads:=replay_actual_head_keys rs original rebased ha hb hv
  have hnodes:=replay_provider_keys rs 0 0 0 hv
  have he : nodeEdgeKeys (forestStoreViews (original.map Prod.fst)).nodes=
      nodeEdgeKeys (forestStoreViews (rebased.map Prod.fst)).nodes := by
    simpa only [forestStoreViews,ha,hb] using hnodes.1
  have hbmap : nodeBitmapKeys (forestStoreViews (original.map Prod.fst)).nodes=
      nodeBitmapKeys (forestStoreViews (rebased.map Prod.fst)).nodes := by
    simpa only [forestStoreViews,ha,hb] using hnodes.2
  have hqc:=nativeQueryWalks_coverage original qs ws hq
  have hue:=ups_edge_inventory_coverage rebased insts (by
    intro I hI
    obtain ⟨run,ho,hp,hi⟩:=hu I hI
    exact ⟨run,ho,dispatchProviders_forget hp,hi⟩)
  have hub:=ups_bitmap_inventory_coverage rebased insts hu
  rw [←hheads,←he] at hue
  rw [←hbmap] at hub
  constructor
  · intro e h
    simp only [walkEdgeKeys,List.flatMap_append,List.filterMap_append,List.mem_append] at h
    exact h.elim (hqc.1 e) (hue e)
  · intro e h
    simp only [walkBmapKeys,List.flatMap_append,List.filterMap_append,List.mem_append] at h
    exact h.elim (hqc.2 e) (hub e)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
