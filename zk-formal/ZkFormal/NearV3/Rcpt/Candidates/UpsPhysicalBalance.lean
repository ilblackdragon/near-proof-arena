import ZkFormal.NearV3.Rcpt.Candidates.UpsPhysicalSegments

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen UpsRows

theorem reduceMessage_toFp (m : Near.Msg) : Msg.toFp (reduceMessage m)=Msg.toFp m := by
  simp only [Msg.toFp,reduceMessage,List.map_map,Function.comp_def,Fp.ofNat_toNat]

theorem reduceMessages_toFp (ms : List Near.Msg) :
    (ms.map reduceMessage).map Msg.toFp=ms.map Msg.toFp := by
  simp only [List.map_map,Function.comp_def,reduceMessage_toFp]

theorem ranked_physical_edge_count (Is : List UpsInst) (ho : ∀I∈Is,InstOk I)
    (hl : ∀I∈Is,∀t<4,(step I t).mode≤1→(step I t).e.length=6)
    (hs : UpsShape (physicalRankedUps Is)) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hL : TableLocal UpsV3.table tr t pub)
    (hlog : tr.log t=logOf (R (physicalRankedUps Is)+1))
    (hcell : ∀r x,r<tr.height t→x<200→tr.cell t r x=((cell (physicalRankedUps Is) r x:Int):Fp))
    (sd : Bool) (m : List Fp) :
    tableBusCount UpsV3.interactions tr t pub B_EDGE sd m=
      ((completeCounterMessages (walkEdgeKeys (upsWalkInventory Is)) sd).map Msg.toFp).count m := by
  rw [physical_walk_bus_count _ hs tr t pub hL hlog hcell B_EDGE (Or.inl rfl) sd m,
    actual_ranked_edges Is ho hl sd,reduceMessages_toFp]

theorem ranked_physical_bitmap_count (Is : List UpsInst) (ho : ∀I∈Is,InstOk I)
    (hs : UpsShape (physicalRankedUps Is)) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hL : TableLocal UpsV3.table tr t pub)
    (hlog : tr.log t=logOf (R (physicalRankedUps Is)+1))
    (hcell : ∀r x,r<tr.height t→x<200→tr.cell t r x=((cell (physicalRankedUps Is) r x:Int):Fp))
    (sd : Bool) (m : List Fp) :
    tableBusCount UpsV3.interactions tr t pub B_BMAP sd m=
      ((completeCounterMessages (walkBmapKeys (upsWalkInventory Is)) sd).map Msg.toFp).count m := by
  rw [physical_walk_bus_count _ hs tr t pub hL hlog hcell B_BMAP (Or.inr rfl) sd m,
    actual_ranked_bitmaps Is ho sd,reduceMessages_toFp]

theorem physical_edge_provider_balance (Is : List UpsInst) (ho : ∀I∈Is,InstOk I)
    (hl : ∀I∈Is,∀t<4,(step I t).mode≤1→(step I t).e.length=6)
    (hs : UpsShape (physicalRankedUps Is)) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hL : TableLocal UpsV3.table tr t pub)
    (hlog : tr.log t=logOf (R (physicalRankedUps Is)+1))
    (hcell : ∀r x,r<tr.height t→x<200→tr.cell t r x=((cell (physicalRankedUps Is) r x:Int):Fp))
    (providers : List Near.Msg) (hn : providers.Nodup)
    (hc : ∀e∈walkEdgeKeys (upsWalkInventory Is),e∈providers) (m : List Fp) :
    ((providers.map (·++[0])).map Msg.toFp).count m+
      tableBusCount UpsV3.interactions tr t pub B_EDGE true m=
    ((providers.map (fun e=>e++[(walkEdgeKeys (upsWalkInventory Is)).count e])).map Msg.toFp).count m+
      tableBusCount UpsV3.interactions tr t pub B_EDGE false m := by
  rw [ranked_physical_edge_count Is ho hl hs tr t pub hL hlog hcell true m,
    ranked_physical_edge_count Is ho hl hs tr t pub hL hlog hcell false m]
  have hp:=(Near.Render.BusEdge.chain_perm providers hn (walkEdgeKeys (upsWalkInventory Is)) hc).map Msg.toFp
  simpa only [List.map_append,List.count_append,completeCounterMessages,ite_true,Bool.false_eq_true,ite_false]
    using hp.count_eq m

theorem physical_bitmap_provider_balance (Is : List UpsInst) (ho : ∀I∈Is,InstOk I)
    (hs : UpsShape (physicalRankedUps Is)) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hL : TableLocal UpsV3.table tr t pub)
    (hlog : tr.log t=logOf (R (physicalRankedUps Is)+1))
    (hcell : ∀r x,r<tr.height t→x<200→tr.cell t r x=((cell (physicalRankedUps Is) r x:Int):Fp))
    (providers : List Near.Msg) (hn : providers.Nodup)
    (hc : ∀e∈walkBmapKeys (upsWalkInventory Is),e∈providers) (m : List Fp) :
    ((providers.map (·++[0])).map Msg.toFp).count m+
      tableBusCount UpsV3.interactions tr t pub B_BMAP true m=
    ((providers.map (fun e=>e++[(walkBmapKeys (upsWalkInventory Is)).count e])).map Msg.toFp).count m+
      tableBusCount UpsV3.interactions tr t pub B_BMAP false m := by
  rw [ranked_physical_bitmap_count Is ho hs tr t pub hL hlog hcell true m,
    ranked_physical_bitmap_count Is ho hs tr t pub hL hlog hcell false m]
  have hp:=(Near.Render.BusEdge.chain_perm providers hn (walkBmapKeys (upsWalkInventory Is)) hc).map Msg.toFp
  simpa only [List.map_append,List.count_append,completeCounterMessages,ite_true,Bool.false_eq_true,ite_false]
    using hp.count_eq m

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
