import ZkFormal.NearV3.Candidates.PostNodeLocal
import ZkFormal.NearV3.Rcpt.Candidates.NodePostProviders
import ZkFormal.NearV3.Rcpt.Candidates.SharedPhysicalBitmapBalance

namespace ZkFormal.NearV3.Candidates.PostSharedTraffic
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen UpsRows Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

theorem edge_balance (u : Inputs) (ws : List WalkR) (Is : List UpsInst)
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
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 (records u vs)) pub) tn pub B_EDGE true msg+
      tableBusCount WalkV3.interactions trw tw pub B_EDGE true msg+
      tableBusCount UpsV3.interactions tru tu pub B_EDGE true msg=
    tableBusCount HeadV3.interactions trh th pub B_EDGE false msg+
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 (records u vs)) pub) tn pub B_EDGE false msg+
      tableBusCount WalkV3.interactions trw tw pub B_EDGE false msg+
      tableBusCount UpsV3.interactions tru tu pub B_EDGE false msg := by
  exact shared_physical_edge_balance ws Is ho hl hs (records u vs) (PostNodeLocal.node_ok u vs hn) q he hqe hqb hqu hh
    (by simpa only [records_edge_keys] using hc) trh trw tru th tn tw tu pub hhead hwalk huShape huLocal huLog huCell msg

theorem bitmap_balance (u : Inputs) (ws : List WalkR) (Is : List UpsInst)
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
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 (records u vs)) pub) tn pub B_BMAP true msg+
      tableBusCount WalkV3.interactions trw tw pub B_BMAP true msg+
      tableBusCount UpsV3.interactions tru tu pub B_BMAP true msg=
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 (records u vs)) pub) tn pub B_BMAP false msg+
      tableBusCount WalkV3.interactions trw tw pub B_BMAP false msg+
      tableBusCount UpsV3.interactions tru tu pub B_BMAP false msg := by
  exact shared_physical_bitmap_balance ws Is ho (records u vs) (PostNodeLocal.node_ok u vs hn) q he hqe hqb hqu
    (by simpa only [records_bitmap_keys] using hc) trw tru tn tw tu pub hwalk huShape huLocal huLog huCell msg

end ZkFormal.NearV3.Candidates.PostSharedTraffic
