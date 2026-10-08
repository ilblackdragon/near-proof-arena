import ZkFormal.NearV3.Rcpt.Candidates.CompactWalkRanks
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen Render.UpsRelay UpsRows

/-- Actual UPS interaction counts include prior native query consumption. -/
theorem joint_compact_edge_count (ws : List WalkR) (Is : List UpsInst) (ho : ∀I∈Is,InstOk I)
    (hl : ∀I∈Is,∀t<4,(step I t).mode≤1→(step I t).e.length=6)
    (hR : compactR (physicalPrefixUps (ws.flatMap (·.steps)) Is)≤2^22)
    (t : Nat) (pub : List Fp)
    (hL : TableLocal compactTable (Candidates.CompactHeight.trace (physicalPrefixUps (ws.flatMap (·.steps)) Is)) t pub)
    (rank : Nat→Nat)
    (sd : Bool) (m : List Fp) :
    ((if sd then walkSends3 (rankWalks [] ws) B_EDGE else walkRecvs3 (rankWalks [] ws) B_EDGE).map Msg.toFp).count m+
      tableBusCount compactTable.interactions (patchWindowCounters
        (Candidates.CompactHeight.trace (physicalPrefixUps (ws.flatMap (·.steps)) Is)) t rank) t pub B_EDGE sd m=
    ((completeCounterMessages (walkEdgeKeys (ws++upsWalkInventory Is)) sd).map Msg.toFp).count m := by
  rw [Candidates.WindowPatchOtherTraffic.count hL rank B_EDGE (by decide),
    compact_physical_walk_count _ hR t pub B_EDGE (Or.inl rfl) sd m]
  have hh:=congrArg (fun xs=>(xs.map Msg.toFp).count m) (joint_actual_edges ws Is ho hl sd)
  simpa only [List.map_append,List.count_append,reduceMessages_toFp] using hh

theorem joint_compact_bitmap_count (ws : List WalkR) (Is : List UpsInst) (ho : ∀I∈Is,InstOk I)
    (hR : compactR (physicalPrefixUps (ws.flatMap (·.steps)) Is)≤2^22)
    (t : Nat) (pub : List Fp)
    (hL : TableLocal compactTable (Candidates.CompactHeight.trace (physicalPrefixUps (ws.flatMap (·.steps)) Is)) t pub)
    (rank : Nat→Nat)
    (sd : Bool) (m : List Fp) :
    ((if sd then walkSends3 (rankWalks [] ws) B_BMAP else walkRecvs3 (rankWalks [] ws) B_BMAP).map Msg.toFp).count m+
      tableBusCount compactTable.interactions (patchWindowCounters
        (Candidates.CompactHeight.trace (physicalPrefixUps (ws.flatMap (·.steps)) Is)) t rank) t pub B_BMAP sd m=
    ((completeCounterMessages (walkBmapKeys (ws++upsWalkInventory Is)) sd).map Msg.toFp).count m := by
  rw [Candidates.WindowPatchOtherTraffic.count hL rank B_BMAP (by decide),
    compact_physical_walk_count _ hR t pub B_BMAP (Or.inr rfl) sd m]
  have hh:=congrArg (fun xs=>(xs.map Msg.toFp).count m) (joint_actual_bitmaps ws Is ho sd)
  simpa only [List.map_append,List.count_append,reduceMessages_toFp] using hh

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
