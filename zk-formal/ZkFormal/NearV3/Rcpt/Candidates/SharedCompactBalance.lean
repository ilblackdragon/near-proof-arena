import ZkFormal.NearV3.Rcpt.Candidates.CompactJointTraffic
import ZkFormal.NearV3.Rcpt.Candidates.SharedPhysicalBitmapBalance
import ZkFormal.NearV3.Rcpt.Candidates.SharedPhysicalEdgeBalance

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen Render.UpsRelay UpsRows
open ZkFormal.NearV3.Candidates

/-- Four physical tables share one request counter sequence. The window request
inventory remains arbitrary and is retained in the same node assignment. -/
theorem shared_compact_edge_balance (ws : List WalkR) (Is : List UpsInst)
    (ho : ∀I∈Is,InstOk I) (hl : ∀I∈Is,∀t<4,(step I t).mode≤1→(step I t).e.length=6)
    (hs : List HeadE) (vs : List NodeS3) (hn : NodeOk vs) (q : UseRequests)
    (he : q.edges=walkEdgeKeys (ws++upsWalkInventory Is))
    (hqe : q.edges.length<Algebra.P) (hqb : q.bmaps.length<Algebra.P) (hqu : q.windows.length<Algebra.P)
    (hh : (hs.map HeadE.tau).Nodup)
    (hc : ∀e∈walkEdgeKeys (ws++upsWalkInventory Is),e∈headEdgeKeys hs++nodeEdgeKeys vs)
    (trh trw : Trace Fp) (th tn tw tu : Nat) (pub : List Fp)
    (hhead : TableTraffic HeadV3.interactions trh th pub (headTraffic (assignHeadUses q.edges hs)))
    (hwalk : TableTraffic WalkV3.interactions trw tw pub (walkTraffic3 (rankWalks [] ws)))
    (hR : compactR (physicalPrefixUps (ws.flatMap (·.steps)) Is)≤2^22)
    (huLocal : TableLocal compactTable (CompactHeight.trace (physicalPrefixUps (ws.flatMap (·.steps)) Is)) tu pub)
    (rank : Nat→Nat)
    (msg : List Fp) :
    tableBusCount HeadV3.interactions trh th pub B_EDGE true msg+
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 vs) pub) tn pub B_EDGE true msg+
      tableBusCount WalkV3.interactions trw tw pub B_EDGE true msg+
      tableBusCount compactTable.interactions (patchWindowCounters
        (CompactHeight.trace (physicalPrefixUps (ws.flatMap (·.steps)) Is)) tu rank) tu pub B_EDGE true msg=
    tableBusCount HeadV3.interactions trh th pub B_EDGE false msg+
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 vs) pub) tn pub B_EDGE false msg+
      tableBusCount WalkV3.interactions trw tw pub B_EDGE false msg+
      tableBusCount compactTable.interactions (patchWindowCounters
        (CompactHeight.trace (physicalPrefixUps (ws.flatMap (·.steps)) Is)) tu rank) tu pub B_EDGE false msg := by
  have hnode:=NodeUseTraffic.edge q vs hn hqe hqb hqu tn pub msg
  rw [(hhead B_EDGE msg).1,(hhead B_EDGE msg).2,hnode.1,hnode.2,
    (hwalk B_EDGE msg).1,(hwalk B_EDGE msg).2]
  simp only [headTraffic,walkTraffic3]
  rw [(assigned_head_edges q.edges hs).1,(assigned_head_edges q.edges hs).2]
  have hsend:=joint_compact_edge_count ws Is ho hl hR tu pub huLocal rank true msg
  have hrecv:=joint_compact_edge_count ws Is ho hl hR tu pub huLocal rank false msg
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


/-- Exact bitmap counter conservation across node, query walk, and UPS tables. -/
theorem shared_compact_bitmap_balance (ws : List WalkR) (Is : List UpsInst)
    (ho : ∀I∈Is,InstOk I)
    (vs : List NodeS3) (hn : NodeOk vs) (q : UseRequests)
    (he : q.bmaps=walkBmapKeys (ws++upsWalkInventory Is))
    (hqe : q.edges.length<Algebra.P) (hqb : q.bmaps.length<Algebra.P) (hqu : q.windows.length<Algebra.P)
    (hc : ∀e∈walkBmapKeys (ws++upsWalkInventory Is),e∈nodeBitmapKeys vs)
    (trw : Trace Fp) (tn tw tu : Nat) (pub : List Fp)
    (hwalk : TableTraffic WalkV3.interactions trw tw pub (walkTraffic3 (rankWalks [] ws)))
    (hR : compactR (physicalPrefixUps (ws.flatMap (·.steps)) Is)≤2^22)
    (huLocal : TableLocal compactTable (CompactHeight.trace (physicalPrefixUps (ws.flatMap (·.steps)) Is)) tu pub)
    (rank : Nat→Nat)
    (msg : List Fp) :
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 vs) pub) tn pub B_BMAP true msg+
      tableBusCount WalkV3.interactions trw tw pub B_BMAP true msg+
      tableBusCount compactTable.interactions (patchWindowCounters
        (CompactHeight.trace (physicalPrefixUps (ws.flatMap (·.steps)) Is)) tu rank) tu pub B_BMAP true msg=
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 vs) pub) tn pub B_BMAP false msg+
      tableBusCount WalkV3.interactions trw tw pub B_BMAP false msg+
      tableBusCount compactTable.interactions (patchWindowCounters
        (CompactHeight.trace (physicalPrefixUps (ws.flatMap (·.steps)) Is)) tu rank) tu pub B_BMAP false msg := by
  have hnode:=NodeUseTraffic.non_size q vs hn hqe hqb hqu tn pub B_BMAP msg (by decide)
  rw [hnode.1,hnode.2,(hwalk B_BMAP msg).1,(hwalk B_BMAP msg).2]
  simp only [walkTraffic3]
  rw [assigned_bitmap_send,assigned_bitmap_recv]
  have hsend:=joint_compact_bitmap_count ws Is ho hR tu pub huLocal rank true msg
  have hrecv:=joint_compact_bitmap_count ws Is ho hR tu pub huLocal rank false msg
  simp only [ite_true,Bool.false_eq_true,ite_false] at hsend hrecv
  have hperm:=(Near.Render.BusEdge.chain_perm (nodeBitmapKeys vs)
    (nodeBitmapKeys_distinct vs) (walkBmapKeys (ws++upsWalkInventory Is)) hc).map Msg.toFp
  have hcoun:=hperm.count_eq msg
  simp only [List.map_append,List.count_append] at hcoun
  change _+((completeCounterMessages (walkBmapKeys (ws++upsWalkInventory Is)) true).map Msg.toFp).count msg=
    _+((completeCounterMessages (walkBmapKeys (ws++upsWalkInventory Is)) false).map Msg.toFp).count msg at hcoun
  rw [he]
  simp only [Nat.add_assoc]
  rw [hsend,hrecv]
  exact hcoun


end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
