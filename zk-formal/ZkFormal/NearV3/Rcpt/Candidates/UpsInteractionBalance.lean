import ZkFormal.NearV3.Rcpt.Candidates.UpsInteractionAggregate
import ZkFormal.NearV3.Rcpt.Candidates.HeadNodeBalance

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Algebra Render.UpsGen UpsRows

theorem rankUpsList_arity : ∀(Is : List Render.UpsInst)(p : List WStep3),
    (∀I∈Is,∀t<4,(step I t).mode≤1→(step I t).e.length=6) →
    ∀I∈rankUpsList p Is,∀t<4,(step I t).mode≤1→(step I t).e.length=6
  | [],_,_,_,h=>by simp [rankUpsList] at h
  | I::Is,p,h,J,hJ=>by
    simp only [rankUpsList,List.mem_cons] at hJ
    rcases hJ with rfl|hJ
    · simpa using h I (by simp)
    · exact rankUpsList_arity Is _ (fun J hJ=>h J (by simp [hJ])) J hJ

theorem actual_ranked_edges (Is : List Render.UpsInst) (ho : ∀I∈Is,InstOk I)
    (hl : ∀I∈Is,∀t<4,(step I t).mode≤1→(step I t).e.length=6) (sd : Bool) :
    upsWalkMessages (physicalRankedUps Is) B_EDGE sd=
      (completeCounterMessages (walkEdgeKeys (upsWalkInventory Is)) sd).map reduceMessage := by
  rw [physicalRankedUps,synced_list_edges _ (rankUpsList_arity Is [] hl)]
  congr 1
  simpa only [ups_inventory_flat] using rankUpsList_edge_traffic Is ho sd

theorem actual_ranked_bitmaps (Is : List Render.UpsInst) (ho : ∀I∈Is,InstOk I) (sd : Bool) :
    upsWalkMessages (physicalRankedUps Is) B_BMAP sd=
      (completeCounterMessages (walkBmapKeys (upsWalkInventory Is)) sd).map reduceMessage := by
  rw [physicalRankedUps,synced_list_bitmaps]
  congr 1
  simpa only [ups_inventory_flat] using rankUpsList_bitmap_traffic Is ho sd

theorem actual_ups_edge_balance (Is : List Render.UpsInst) (ho : ∀I∈Is,InstOk I)
    (hl : ∀I∈Is,∀t<4,(step I t).mode≤1→(step I t).e.length=6)
    (providers : List Msg) (hn : providers.Nodup)
    (hc : ∀e∈walkEdgeKeys (upsWalkInventory Is),e∈providers) :
    ((providers.map (·++[0])).map reduceMessage++upsWalkMessages (physicalRankedUps Is) B_EDGE true).Perm
    ((providers.map (fun e=>e++[(walkEdgeKeys (upsWalkInventory Is)).count e])).map reduceMessage++
      upsWalkMessages (physicalRankedUps Is) B_EDGE false) := by
  rw [actual_ranked_edges Is ho hl true,actual_ranked_edges Is ho hl false]
  simpa only [List.map_append,completeCounterMessages,ite_true,Bool.false_eq_true,ite_false]
    using (Near.Render.BusEdge.chain_perm providers hn (walkEdgeKeys (upsWalkInventory Is)) hc).map reduceMessage

theorem actual_ups_bitmap_balance (Is : List Render.UpsInst) (ho : ∀I∈Is,InstOk I)
    (providers : List Msg) (hn : providers.Nodup)
    (hc : ∀e∈walkBmapKeys (upsWalkInventory Is),e∈providers) :
    ((providers.map (·++[0])).map reduceMessage++upsWalkMessages (physicalRankedUps Is) B_BMAP true).Perm
    ((providers.map (fun e=>e++[(walkBmapKeys (upsWalkInventory Is)).count e])).map reduceMessage++
      upsWalkMessages (physicalRankedUps Is) B_BMAP false) := by
  rw [actual_ranked_bitmaps Is ho true,actual_ranked_bitmaps Is ho false]
  simpa only [List.map_append,completeCounterMessages,ite_true,Bool.false_eq_true,ite_false]
    using (Near.Render.BusEdge.chain_perm providers hn (walkBmapKeys (upsWalkInventory Is)) hc).map reduceMessage

theorem concrete_actual_ups_edge_balance (Is : List Render.UpsInst)
    (ho : ∀I∈Is,InstOk I) (hs : List HeadE) (ss : List NodeS3)
    (q : UseRequests) (hq : q.edges=walkEdgeKeys (upsWalkInventory Is))
    (hh : (hs.map HeadE.tau).Nodup) (hw : ∀s∈ss,s.v.wf)
    (hc : ∀e∈walkEdgeKeys (upsWalkInventory Is),e∈headEdgeKeys hs++nodeEdgeKeys ss) :
    ((headSends (assignHeadUses q.edges hs) B_EDGE++nodeSends3 (assignList q 0 ss) B_EDGE).map reduceMessage++
      upsWalkMessages (physicalRankedUps Is) B_EDGE true).Perm
    ((headRecvs (assignHeadUses q.edges hs) B_EDGE++nodeRecvs3 (assignList q 0 ss) B_EDGE).map reduceMessage++
      upsWalkMessages (physicalRankedUps Is) B_EDGE false) := by
  have hl : ∀I∈Is,∀t<4,(step I t).mode≤1→(step I t).e.length=6 := by
    intro I hI t ht hm
    apply provider_edge_arity hs ss _
    apply hc
    unfold walkEdgeKeys
    rw [List.filterMap_flatMap]
    apply List.mem_flatMap.mpr
    refine ⟨{w:=I.tau,tau:=I.tau,steps:=fourSteps I},?_,?_⟩
    · exact List.mem_map.mpr ⟨I,hI,rfl⟩
    · apply List.mem_filterMap.mpr
      refine ⟨step I t,?_,?_⟩
      · exact List.mem_ofFn.mpr ⟨⟨t,ht⟩,rfl⟩
      · simp [hm]
  rw [(assigned_head_edges q.edges hs).1,(assigned_head_edges q.edges hs).2,
    assigned_node_edges_send,assigned_node_edges_recv,hq]
  simpa only [List.map_append] using actual_ups_edge_balance Is ho hl
    (headEdgeKeys hs++nodeEdgeKeys ss) (head_node_keys_distinct hs ss hh hw) hc

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
