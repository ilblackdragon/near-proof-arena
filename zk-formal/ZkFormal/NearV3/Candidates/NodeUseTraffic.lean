import ZkFormal.NearV3.Candidates.NodeUseLocal
import ZkFormal.NearV3.Candidates.TrieCountTraffic
import ZkFormal.NearV3.Rcpt.Candidates.HeadNodeBalance
namespace ZkFormal.NearV3.Candidates.NodeUseTraffic
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

/-- Exact non-SIZE traffic of the physical count-extended node table after
assigning every provider count from the request multiset. -/
theorem non_size (q : UseRequests) (vs : List NodeS3) (hn : NodeOk vs)
    (he : q.edges.length<Algebra.P) (hb : q.bmaps.length<Algebra.P) (hu : q.windows.length<Algebra.P)
    (t : Nat) (pub : List Fp) (b : Nat) (msg : List Fp) (hbus : b≠B_SIZE) :
    tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 vs) pub) t pub b true msg=
      ((nodeSends3 (assignList q 0 vs) b).map Msg.toFp).count msg ∧
    tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 vs) pub) t pub b false msg=
      ((nodeRecvs3 (assignList q 0 vs) b).map Msg.toFp).count msg := by
  rw [TrieCountTraffic.node_non_size _ _ _ _ _ _ hbus,TrieCountTraffic.node_non_size _ _ _ _ _ _ hbus]
  exact (TrieHeight.node_complete _ (NodeUseLocal.node_ok q vs hn he hb hu) t pub).2.1 b msg

theorem edge (q : UseRequests) (vs : List NodeS3) (hn : NodeOk vs)
    (he : q.edges.length<Algebra.P) (hb : q.bmaps.length<Algebra.P) (hu : q.windows.length<Algebra.P)
    (t : Nat) (pub : List Fp) (msg : List Fp) :
    tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 vs) pub) t pub B_EDGE true msg=
      (((nodeEdgeKeys vs).map (·++[0])).map Msg.toFp).count msg ∧
    tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 vs) pub) t pub B_EDGE false msg=
      (((nodeEdgeKeys vs).map (fun e=>e++[q.edges.count e])).map Msg.toFp).count msg := by
  have h:=non_size q vs hn he hb hu t pub B_EDGE msg (by decide)
  rwa [assigned_node_edges_send,assigned_node_edges_recv] at h

theorem bitmap (q : UseRequests) (vs : List NodeS3) (hn : NodeOk vs)
    (he : q.edges.length<Algebra.P) (hb : q.bmaps.length<Algebra.P) (hu : q.windows.length<Algebra.P)
    (t : Nat) (pub : List Fp) (msg : List Fp) :
    tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 vs) pub) t pub B_BMAP false msg=
      (((vs.zip (List.range vs.length)).flatMap fun (s,n)=>
        match s.v.bmap with | none=>[] | some (bm,hv)=>[[n,bm,hv,q.bmaps.count [n,bm,hv]]]).map Msg.toFp).count msg := by
  have h:=(non_size q vs hn he hb hu t pub B_BMAP msg (by decide)).2
  rwa [assigned_bmaps] at h

theorem windows (q : UseRequests) (vs : List NodeS3) (hn : NodeOk vs)
    (he : q.edges.length<Algebra.P) (hb : q.bmaps.length<Algebra.P) (hu : q.windows.length<Algebra.P)
    (t : Nat) (pub : List Fp) (msg : List Fp) :
    tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 vs) pub) t pub B_UPB false msg=
      (((vs.zip (List.range vs.length)).flatMap fun (s,n)=>
        (List.range (s.v.ser false).length).map fun p=>windowKey n p s++[q.windows.count (windowKey n p s)]).map Msg.toFp).count msg := by
  have h:=(non_size q vs hn he hb hu t pub B_UPB msg (by decide)).2
  rwa [assigned_windows] at h
/-- Field-level EDGE conservation for the rendered head, usage-counted node
and ranked walk tables. Inventory conservation is transferred with multiplicity. -/
theorem edge_balance (q : UseRequests) (vs : List NodeS3) (hn : NodeOk vs)
    (he : q.edges.length<Algebra.P) (hb : q.bmaps.length<Algebra.P) (hu : q.windows.length<Algebra.P)
    (hs : List HeadE) (ws : List WalkR) (hq : q.edges=walkEdgeKeys ws)
    (hh : (hs.map HeadE.tau).Nodup)
    (hc : ∀e∈walkEdgeKeys ws,e∈headEdgeKeys hs++nodeEdgeKeys vs)
    (trh trw : Trace Fp) (th tn tw : Nat) (pub : List Fp)
    (hhead : TableTraffic HeadV3.interactions trh th pub (headTraffic (assignHeadUses q.edges hs)))
    (hwalk : TableTraffic WalkV3.interactions trw tw pub (walkTraffic3 (rankWalks [] ws)))
    (msg : List Fp) :
    tableBusCount HeadV3.interactions trh th pub B_EDGE true msg+
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 vs) pub) tn pub B_EDGE true msg+
      tableBusCount WalkV3.interactions trw tw pub B_EDGE true msg=
    tableBusCount HeadV3.interactions trh th pub B_EDGE false msg+
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 vs) pub) tn pub B_EDGE false msg+
      tableBusCount WalkV3.interactions trw tw pub B_EDGE false msg := by
  have hperm:=concrete_head_node_edge_balance ws hs vs q hq hh hn.wf.wf hc
  have hcount:=((hperm.map Msg.toFp).count_eq msg)
  simp only [List.map_append,List.count_append] at hcount
  rw [(hhead B_EDGE msg).1,(hhead B_EDGE msg).2,(hwalk B_EDGE msg).1,(hwalk B_EDGE msg).2,
    (non_size q vs hn he hb hu tn pub B_EDGE msg (by decide)).1,
    (non_size q vs hn he hb hu tn pub B_EDGE msg (by decide)).2]
  exact hcount

end ZkFormal.NearV3.Candidates.NodeUseTraffic
