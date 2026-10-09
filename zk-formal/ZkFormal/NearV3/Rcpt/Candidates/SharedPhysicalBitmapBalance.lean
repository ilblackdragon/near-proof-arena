import ZkFormal.NearV3.Rcpt.Candidates.NodeBitmapMessages

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen UpsRows
open ZkFormal.NearV3.Candidates

/-- Exact bitmap counter conservation across node, query walk, and UPS tables. -/
theorem shared_physical_bitmap_balance (ws : List WalkR) (Is : List UpsInst)
    (ho : ∀I∈Is,InstOk I)
    (vs : List NodeS3) (hn : NodeOk vs) (q : UseRequests)
    (he : q.bmaps=walkBmapKeys (ws++upsWalkInventory Is))
    (hqe : q.edges.length<Algebra.P) (hqb : q.bmaps.length<Algebra.P) (hqu : q.windows.length<Algebra.P)
    (hc : ∀e∈walkBmapKeys (ws++upsWalkInventory Is),e∈nodeBitmapKeys vs)
    (trw tru : Trace Fp) (tn tw tu : Nat) (pub : List Fp)
    (hwalk : TableTraffic WalkV3.interactions trw tw pub (walkTraffic3 (rankWalks [] ws)))
    (huShape : UpsShape (physicalPrefixUps (ws.flatMap (·.steps)) Is))
    (huLocal : TableLocal UpsV3.table tru tu pub)
    (huLog : tru.log tu=logOf (R (physicalPrefixUps (ws.flatMap (·.steps)) Is)+1))
    (huCell : ∀r x,r<tru.height tu→x<200→
      tru.cell tu r x=((cell (physicalPrefixUps (ws.flatMap (·.steps)) Is) r x:Int):Fp))
    (msg : List Fp) :
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 vs) pub) tn pub B_BMAP true msg+
      tableBusCount WalkV3.interactions trw tw pub B_BMAP true msg+
      tableBusCount UpsV3.interactions tru tu pub B_BMAP true msg=
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 vs) pub) tn pub B_BMAP false msg+
      tableBusCount WalkV3.interactions trw tw pub B_BMAP false msg+
      tableBusCount UpsV3.interactions tru tu pub B_BMAP false msg := by
  have hnode:=NodeUseTraffic.non_size q vs hn hqe hqb hqu tn pub B_BMAP msg (by decide)
  rw [hnode.1,hnode.2,(hwalk B_BMAP msg).1,(hwalk B_BMAP msg).2]
  simp only [walkTraffic3]
  rw [assigned_bitmap_send,assigned_bitmap_recv]
  have hsend:=joint_physical_bitmap_count ws Is ho huShape tru tu pub huLocal huLog huCell true msg
  have hrecv:=joint_physical_bitmap_count ws Is ho huShape tru tu pub huLocal huLog huCell false msg
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
