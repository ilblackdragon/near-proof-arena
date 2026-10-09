import ZkFormal.NearV3.Rcpt.Candidates.UpsJointTraffic
import ZkFormal.NearV3.Candidates.NodeUseTraffic

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen UpsRows
open ZkFormal.NearV3.Candidates

/-- Four physical tables share one request counter sequence. The window request
inventory remains arbitrary and is retained in the same node assignment. -/
theorem shared_physical_edge_balance (ws : List WalkR) (Is : List UpsInst)
    (ho : ∀I∈Is,InstOk I) (hl : ∀I∈Is,∀t<4,(step I t).mode≤1→(step I t).e.length=6)
    (hs : List HeadE) (vs : List NodeS3) (hn : NodeOk vs) (q : UseRequests)
    (he : q.edges=walkEdgeKeys (ws++upsWalkInventory Is))
    (hqe : q.edges.length<Algebra.P) (hqb : q.bmaps.length<Algebra.P) (hqu : q.windows.length<Algebra.P)
    (hh : (hs.map HeadE.tau).Nodup)
    (hc : ∀e∈walkEdgeKeys (ws++upsWalkInventory Is),e∈headEdgeKeys hs++nodeEdgeKeys vs)
    (trh trw tru : Trace Fp) (th tn tw tu : Nat) (pub : List Fp)
    (hhead : TableTraffic HeadV3.interactions trh th pub (headTraffic (assignHeadUses q.edges hs)))
    (hwalk : TableTraffic WalkV3.interactions trw tw pub (walkTraffic3 (rankWalks [] ws)))
    (huShape : UpsShape (physicalPrefixUps (ws.flatMap (·.steps)) Is))
    (huLocal : TableLocal UpsV3.table tru tu pub)
    (huLog : tru.log tu=logOf (R (physicalPrefixUps (ws.flatMap (·.steps)) Is)+1))
    (huCell : ∀r x,r<tru.height tu→x<200→
      tru.cell tu r x=((cell (physicalPrefixUps (ws.flatMap (·.steps)) Is) r x:Int):Fp))
    (msg : List Fp) :
    tableBusCount HeadV3.interactions trh th pub B_EDGE true msg+
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 vs) pub) tn pub B_EDGE true msg+
      tableBusCount WalkV3.interactions trw tw pub B_EDGE true msg+
      tableBusCount UpsV3.interactions tru tu pub B_EDGE true msg=
    tableBusCount HeadV3.interactions trh th pub B_EDGE false msg+
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 vs) pub) tn pub B_EDGE false msg+
      tableBusCount WalkV3.interactions trw tw pub B_EDGE false msg+
      tableBusCount UpsV3.interactions tru tu pub B_EDGE false msg := by
  have hnode:=NodeUseTraffic.edge q vs hn hqe hqb hqu tn pub msg
  rw [(hhead B_EDGE msg).1,(hhead B_EDGE msg).2,hnode.1,hnode.2,
    (hwalk B_EDGE msg).1,(hwalk B_EDGE msg).2]
  simp only [headTraffic,walkTraffic3]
  rw [(assigned_head_edges q.edges hs).1,(assigned_head_edges q.edges hs).2]
  have hsend:=joint_physical_edge_count ws Is ho hl huShape tru tu pub huLocal huLog huCell true msg
  have hrecv:=joint_physical_edge_count ws Is ho hl huShape tru tu pub huLocal huLog huCell false msg
  simp only [ite_true,Bool.false_eq_true,ite_false] at hsend hrecv
  have hperm:=(Near.Render.BusEdge.chain_perm (headEdgeKeys hs++nodeEdgeKeys vs)
    (head_node_keys_distinct hs vs hh hn.wf.wf) (walkEdgeKeys (ws++upsWalkInventory Is)) hc).map Msg.toFp
  have hcoun:=hperm.count_eq msg
  simp only [List.map_append,List.count_append] at hcoun
  change _+((completeCounterMessages (walkEdgeKeys (ws++upsWalkInventory Is)) true).map Msg.toFp).count msg=
    _+((completeCounterMessages (walkEdgeKeys (ws++upsWalkInventory Is)) false).map Msg.toFp).count msg at hcoun
  rw [he]
  simp only [Nat.add_assoc]
  rw [hsend,hrecv]
  simpa only [Nat.add_assoc] using hcoun

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
