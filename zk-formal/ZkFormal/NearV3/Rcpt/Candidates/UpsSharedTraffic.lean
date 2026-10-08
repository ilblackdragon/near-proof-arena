import ZkFormal.NearV3.Rcpt.Candidates.UpsCounterCanonical

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near Render.UpsGen

/-- The bitmap interaction reads the same physical counter as EDGE. -/
def sharedBitmapTraffic (ss : List WStep3) (sd : Bool) : List Msg :=
  ss.filterMap (fun st=>if st.mode=2 then
    some [st.e.getD 0 0,st.bm,st.hv,st.u+(if sd then 1 else 0)] else none)

theorem sync_edge_traffic (ss : List WStep3) (sd : Bool) :
    edgeTraffic (ss.map syncStep) sd=edgeTraffic ss sd := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    by_cases h : s.mode≤1
    · have hn : s.mode≠2 := by omega
      simpa [edgeTraffic,syncStep,h,hn] using ih
    · simpa [edgeTraffic,syncStep,h] using ih

theorem sync_bitmap_traffic (ss : List WStep3) (sd : Bool) :
    sharedBitmapTraffic (ss.map syncStep) sd=bitmapTraffic ss sd := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    by_cases h : s.mode=2 <;> simpa [sharedBitmapTraffic,bitmapTraffic,syncStep,h] using ih

theorem syncUps_fourSteps (I : Render.UpsInst) :
    fourSteps (syncUps I)=(fourSteps I).map syncStep := by
  apply List.ext_getElem
  · simp [fourSteps]
  · intro i hi hj
    simp only [fourSteps,List.getElem_ofFn,List.getElem_map,Fin.getElem_fin]
    change step (syncUps I) i=syncStep (step I i)
    simp only [step,syncUps,List.getD_eq_getElem?_getD,List.getElem?_map]
    cases I.walk[i]? <;> rfl

theorem physicalRankedUps_flatten (Is : List Render.UpsInst) :
    (physicalRankedUps Is).flatMap fourSteps=
      ((rankUpsList [] Is).flatMap fourSteps).map syncStep := by
  simp only [physicalRankedUps,List.flatMap_map,syncUps_fourSteps,List.map_flatMap]

theorem physical_edge_traffic (Is : List Render.UpsInst)
    (h : ∀I∈Is,InstOk I) (sd : Bool) :
    edgeTraffic ((physicalRankedUps Is).flatMap fourSteps) sd=
      completeCounterMessages (walkEdgeKeys (upsWalkInventory Is)) sd := by
  rw [physicalRankedUps_flatten,sync_edge_traffic]
  simpa only [ups_inventory_flat] using rankUpsList_edge_traffic Is h sd

theorem physical_bitmap_traffic (Is : List Render.UpsInst)
    (h : ∀I∈Is,InstOk I) (sd : Bool) :
    sharedBitmapTraffic ((physicalRankedUps Is).flatMap fourSteps) sd=
      completeCounterMessages (walkBmapKeys (upsWalkInventory Is)) sd := by
  rw [physicalRankedUps_flatten,sync_bitmap_traffic]
  simpa only [ups_inventory_flat] using rankUpsList_bitmap_traffic Is h sd

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
