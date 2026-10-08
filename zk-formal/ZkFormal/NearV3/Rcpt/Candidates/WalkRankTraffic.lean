import ZkFormal.NearV3.Rcpt.Candidates.WalkCounterMessages

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near

private theorem select_map {α β : Type} (xs : List α) (p : α→Bool) (f : α→β) :
    xs.filterMap (fun x=>if p x then some (f x) else none)=(xs.filter p).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [hp,ih]

theorem edgeTraffic_flatten (ws : List WalkR) (sd : Bool) :
    edgeTraffic (ws.flatMap (·.steps)) sd=(if sd then walkSends3 ws B_EDGE else walkRecvs3 ws B_EDGE) := by
  have he : edgeTraffic (ws.flatMap (·.steps)) sd=ws.flatMap (fun w=>
      (w.steps.filter (fun st=>st.mode≤1)).map (fun st=>st.e++[st.u+(if sd then 1 else 0)])) := by
    unfold edgeTraffic
    rw [List.filterMap_flatMap]
    apply congrArg (List.flatMap · ws)
    funext w
    simpa using select_map w.steps (fun st=>decide (st.mode≤1)) (fun st=>st.e++[st.u+(if sd then 1 else 0)])
  cases sd <;> simpa [walkSends3,walkRecvs3,WStep3.edgeMsg] using he

theorem bitmapTraffic_flatten (ws : List WalkR) (sd : Bool) :
    bitmapTraffic (ws.flatMap (·.steps)) sd=(if sd then walkSends3 ws B_BMAP else walkRecvs3 ws B_BMAP) := by
  have he : bitmapTraffic (ws.flatMap (·.steps)) sd=ws.flatMap (fun w=>
      (w.steps.filter (fun st=>st.mode=2)).map (fun st=>[st.e.getD 0 0,st.bm,st.hv,st.ub+(if sd then 1 else 0)])) := by
    unfold bitmapTraffic
    rw [List.filterMap_flatMap]
    apply congrArg (List.flatMap · ws)
    funext w
    simpa using select_map w.steps (fun st=>decide (st.mode=2)) (fun st=>[st.e.getD 0 0,st.bm,st.hv,st.ub+(if sd then 1 else 0)])
  cases sd <;> simpa [walkSends3,walkRecvs3,WStep3.bmapMsg,B_BMAP,B_EDGE] using he

theorem ranked_walk_edges (ws : List WalkR) (sd : Bool) :
    (if sd then walkSends3 (rankWalks [] ws) B_EDGE else walkRecvs3 (rankWalks [] ws) B_EDGE)=
    completeCounterMessages (walkEdgeKeys ws) sd := by
  rw [←edgeTraffic_flatten,rankWalks_flatten,ranked_edge_traffic]
  change counterMessages [] (walkEdgeKeys ws) sd=_
  exact counterMessages_empty _ _

theorem ranked_walk_bmaps (ws : List WalkR) (sd : Bool) :
    (if sd then walkSends3 (rankWalks [] ws) B_BMAP else walkRecvs3 (rankWalks [] ws) B_BMAP)=
    completeCounterMessages (walkBmapKeys ws) sd := by
  rw [←bitmapTraffic_flatten,rankWalks_flatten,ranked_bitmap_traffic]
  change counterMessages [] (walkBmapKeys ws) sd=_
  exact counterMessages_empty _ _

theorem ranked_walk_edge_balance (ws : List WalkR) (providers : List Msg)
    (hn : providers.Nodup) (hc : ∀e∈walkEdgeKeys ws,e∈providers) :
    (providers.map (·++[0])++walkSends3 (rankWalks [] ws) B_EDGE).Perm
      (providers.map (fun e=>e++[(walkEdgeKeys ws).count e])++walkRecvs3 (rankWalks [] ws) B_EDGE) := by
  have hs:=ranked_walk_edges ws true
  have hr:=ranked_walk_edges ws false
  simp only [completeCounterMessages,ite_true,Bool.false_eq_true,ite_false] at hs hr
  rw [hs,hr]
  exact Near.Render.BusEdge.chain_perm providers hn (walkEdgeKeys ws) hc

theorem ranked_walk_bmap_balance (ws : List WalkR) (providers : List Msg)
    (hn : providers.Nodup) (hc : ∀e∈walkBmapKeys ws,e∈providers) :
    (providers.map (·++[0])++walkSends3 (rankWalks [] ws) B_BMAP).Perm
      (providers.map (fun e=>e++[(walkBmapKeys ws).count e])++walkRecvs3 (rankWalks [] ws) B_BMAP) := by
  have hs:=ranked_walk_bmaps ws true
  have hr:=ranked_walk_bmaps ws false
  simp only [completeCounterMessages,ite_true,Bool.false_eq_true,ite_false] at hs hr
  rw [hs,hr]
  exact Near.Render.BusEdge.chain_perm providers hn (walkBmapKeys ws) hc

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
