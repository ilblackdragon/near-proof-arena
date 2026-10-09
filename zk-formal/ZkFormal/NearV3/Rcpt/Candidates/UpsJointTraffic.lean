import ZkFormal.NearV3.Rcpt.Candidates.UpsPhysicalPrefix

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen UpsRows

theorem joint_actual_edges (ws : List WalkR) (Is : List UpsInst) (ho : ∀I∈Is,InstOk I)
    (hl : ∀I∈Is,∀t<4,(step I t).mode≤1→(step I t).e.length=6) (sd : Bool) :
    ((if sd then walkSends3 (rankWalks [] ws) B_EDGE else walkRecvs3 (rankWalks [] ws) B_EDGE).map reduceMessage++
      upsWalkMessages (physicalPrefixUps (ws.flatMap (·.steps)) Is) B_EDGE sd)=
    (completeCounterMessages (walkEdgeKeys (ws++upsWalkInventory Is)) sd).map reduceMessage := by
  rw [ranked_walk_edges,actual_prefix_edges _ Is ho hl sd,←List.map_append]
  change (completeCounterMessages (walkEdgeKeys ws) sd++
    counterMessages (walkEdgeKeys ws) (walkEdgeKeys (upsWalkInventory Is)) sd).map reduceMessage=_
  rw [counterMessages_append]
  simp only [walkEdgeKeys,List.flatMap_append,List.filterMap_append]

theorem joint_actual_bitmaps (ws : List WalkR) (Is : List UpsInst) (ho : ∀I∈Is,InstOk I) (sd : Bool) :
    ((if sd then walkSends3 (rankWalks [] ws) B_BMAP else walkRecvs3 (rankWalks [] ws) B_BMAP).map reduceMessage++
      upsWalkMessages (physicalPrefixUps (ws.flatMap (·.steps)) Is) B_BMAP sd)=
    (completeCounterMessages (walkBmapKeys (ws++upsWalkInventory Is)) sd).map reduceMessage := by
  rw [ranked_walk_bmaps,actual_prefix_bitmaps _ Is ho sd,←List.map_append]
  change (completeCounterMessages (walkBmapKeys ws) sd++
    counterMessages (walkBmapKeys ws) (walkBmapKeys (upsWalkInventory Is)) sd).map reduceMessage=_
  rw [counterMessages_append]
  simp only [walkBmapKeys,List.flatMap_append,List.filterMap_append]

/-- Actual UPS interaction counts include prior native query consumption. -/
theorem joint_physical_edge_count (ws : List WalkR) (Is : List UpsInst) (ho : ∀I∈Is,InstOk I)
    (hl : ∀I∈Is,∀t<4,(step I t).mode≤1→(step I t).e.length=6)
    (hs : UpsShape (physicalPrefixUps (ws.flatMap (·.steps)) Is)) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hL : TableLocal UpsV3.table tr t pub)
    (hlog : tr.log t=logOf (R (physicalPrefixUps (ws.flatMap (·.steps)) Is)+1))
    (hcell : ∀r x,r<tr.height t→x<200→tr.cell t r x=((cell (physicalPrefixUps (ws.flatMap (·.steps)) Is) r x:Int):Fp))
    (sd : Bool) (m : List Fp) :
    ((if sd then walkSends3 (rankWalks [] ws) B_EDGE else walkRecvs3 (rankWalks [] ws) B_EDGE).map Msg.toFp).count m+
      tableBusCount UpsV3.interactions tr t pub B_EDGE sd m=
    ((completeCounterMessages (walkEdgeKeys (ws++upsWalkInventory Is)) sd).map Msg.toFp).count m := by
  rw [physical_walk_bus_count _ hs tr t pub hL hlog hcell B_EDGE (Or.inl rfl) sd m]
  have hh:=congrArg (fun xs=>(xs.map Msg.toFp).count m) (joint_actual_edges ws Is ho hl sd)
  simpa only [List.map_append,List.count_append,reduceMessages_toFp] using hh

theorem joint_physical_bitmap_count (ws : List WalkR) (Is : List UpsInst) (ho : ∀I∈Is,InstOk I)
    (hs : UpsShape (physicalPrefixUps (ws.flatMap (·.steps)) Is)) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hL : TableLocal UpsV3.table tr t pub)
    (hlog : tr.log t=logOf (R (physicalPrefixUps (ws.flatMap (·.steps)) Is)+1))
    (hcell : ∀r x,r<tr.height t→x<200→tr.cell t r x=((cell (physicalPrefixUps (ws.flatMap (·.steps)) Is) r x:Int):Fp))
    (sd : Bool) (m : List Fp) :
    ((if sd then walkSends3 (rankWalks [] ws) B_BMAP else walkRecvs3 (rankWalks [] ws) B_BMAP).map Msg.toFp).count m+
      tableBusCount UpsV3.interactions tr t pub B_BMAP sd m=
    ((completeCounterMessages (walkBmapKeys (ws++upsWalkInventory Is)) sd).map Msg.toFp).count m := by
  rw [physical_walk_bus_count _ hs tr t pub hL hlog hcell B_BMAP (Or.inr rfl) sd m]
  have hh:=congrArg (fun xs=>(xs.map Msg.toFp).count m) (joint_actual_bitmaps ws Is ho sd)
  simpa only [List.map_append,List.count_append,reduceMessages_toFp] using hh

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
