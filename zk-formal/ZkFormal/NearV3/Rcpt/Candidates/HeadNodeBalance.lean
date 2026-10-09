import ZkFormal.NearV3.Rcpt.Candidates.HeadNodeDistinct

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Algebra

def assignHeadUses (keys : List Msg) (hs : List HeadE) : List HeadE :=
  hs.map (fun h=>{h with mE:=keys.count (headEdgeKey h)})

theorem assignHeadUses_wf (keys : List Msg) (hs : List HeadE) (h : HeadWf hs)
    (hb : keys.length<P) : HeadWf (assignHeadUses keys hs) := by
  constructor
  · intro hd hm;obtain ⟨o,ho,rfl⟩:=List.mem_map.mp hm;exact h.len o ho
  · intro hd hm;obtain ⟨o,ho,rfl⟩:=List.mem_map.mp hm
    have hc:=h.canon o ho
    exact ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,
      Nat.lt_of_le_of_lt List.count_le_length hb,hc.2.2.2.2.2⟩

theorem assigned_head_edges (keys : List Msg) (hs : List HeadE) :
    headSends (assignHeadUses keys hs) B_EDGE=(headEdgeKeys hs).map (·++[0]) ∧
    headRecvs (assignHeadUses keys hs) B_EDGE=(headEdgeKeys hs).map (fun e=>e++[keys.count e]) := by
  simp [headSends,headRecvs,assignHeadUses,headEdgeKeys,headEdgeKey,startEdgeMsg,
    List.map_map,B_EDGE,B_MIDROOT,B_PARENT,B_DIGEST,B_ROOT]

theorem assigned_node_edges_send (q : UseRequests) (ss : List NodeS3) :
    nodeSends3 (assignList q 0 ss) B_EDGE=(nodeEdgeKeys ss).map (·++[0]) := by
  simp only [nodeSends3,show B_EDGE≠B_BYTES by decide,show B_EDGE≠B_PARENT by decide,
    show B_EDGE≠B_VPARENT by decide,ite_false,ite_true]
  rw [assignList_length,List.range_eq_range',assignList_zip,List.flatMap_map]
  unfold nodeEdgeKeys
  rw [List.range_eq_range',List.map_flatMap]
  rfl

theorem assigned_node_edges_recv (q : UseRequests) (ss : List NodeS3) :
    nodeRecvs3 (assignList q 0 ss) B_EDGE=(nodeEdgeKeys ss).map (fun e=>e++[q.edges.count e]) := by
  rw [assigned_edges]
  simp only [nodeEdgeKeys,List.map_flatMap]

theorem concrete_head_node_edge_balance (ws : List WalkR) (hs : List HeadE) (ss : List NodeS3)
    (q : UseRequests) (hq : q.edges=walkEdgeKeys ws)
    (hh : (hs.map HeadE.tau).Nodup) (hw : ∀s∈ss,s.v.wf)
    (hc : ∀e∈walkEdgeKeys ws,e∈headEdgeKeys hs++nodeEdgeKeys ss) :
    (headSends (assignHeadUses q.edges hs) B_EDGE++nodeSends3 (assignList q 0 ss) B_EDGE++
      walkSends3 (rankWalks [] ws) B_EDGE).Perm
    (headRecvs (assignHeadUses q.edges hs) B_EDGE++nodeRecvs3 (assignList q 0 ss) B_EDGE++
      walkRecvs3 (rankWalks [] ws) B_EDGE) := by
  rw [(assigned_head_edges q.edges hs).1,(assigned_head_edges q.edges hs).2,
    assigned_node_edges_send,assigned_node_edges_recv]
  rw [hq]
  simpa only [List.map_append] using ranked_walk_edge_balance ws
    (headEdgeKeys hs++nodeEdgeKeys ss) (head_node_keys_distinct hs ss hh hw) hc

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
