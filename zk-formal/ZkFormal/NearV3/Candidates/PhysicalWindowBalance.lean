import ZkFormal.NearV3.Candidates.PhysicalWindowRequests
import ZkFormal.NearV3.Rcpt.Candidates.NodeWindowDistinct

namespace ZkFormal.NearV3.Candidates.PhysicalWindowBalance
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

theorem assigned_send (q : UseRequests) (vs : List NodeS3) :
    nodeSends3 (assignList q 0 vs) B_UPB=(nodeWindowKeys vs).map (·++[0]) := by
  simp only [nodeSends3,show B_UPB≠B_BYTES by decide,show B_UPB≠B_PARENT by decide,
    show B_UPB≠B_VPARENT by decide,show B_UPB≠B_EDGE by decide,show B_UPB≠B_BMAP by decide,
    show B_UPB≠B_DIGS by decide,show B_UPB≠B_ENT by decide,show B_UPB≠B_SIZE by decide,ite_false,ite_true]
  rw [assignList_length,List.range_eq_range',assignList_zip,List.flatMap_map]
  simp [nodeWindowKeys,List.range_eq_range',List.map_flatMap,List.map_map,assignUses,windowKey,upbOf,Function.comp_def]

theorem assigned_recv (q : UseRequests) (vs : List NodeS3) :
    nodeRecvs3 (assignList q 0 vs) B_UPB=
      (nodeWindowKeys vs).map (fun e=>e++[q.windows.count e]) := by
  rw [assigned_windows]
  simp [nodeWindowKeys,List.map_flatMap,List.map_map,Function.comp_def]

/-- Full physical UPB conservation between native node providers and ranked
compact reads. Provider keys are provably unique; only actual reader ownership
remains explicit, and window counter capacity follows from compact height. -/
theorem balance (tr : Trace Fp) (tu tn : Nat) (pub : List Fp)
    (hl : TableLocal Render.UpsRelay.compactTable tr tu pub)
    (q : UseRequests) (vs : List NodeS3) (hn : Render.NodeOk vs)
    (he : q.edges.length<P) (hb : q.bmaps.length<P)
    (hq : q.windows=PhysicalWindowRequests.keys tr tu)
    (hc : ∀r∈physicalWindowRows tr tu,physicalWindowKey tr tu r∈nodeWindowKeys vs)
    (msg : List Fp) :
    tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 vs) pub) tn pub B_UPB true msg+
      tableBusCount Render.UpsRelay.compactTable.interactions
        (patchWindowCounters tr tu (physicalWindowRank tr tu)) tu pub B_UPB true msg=
    tableBusCount Render.UpsRelay.compactTable.interactions
        (patchWindowCounters tr tu (physicalWindowRank tr tu)) tu pub B_UPB false msg+
      tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node (assignList q 0 vs) pub) tn pub B_UPB false msg := by
  have hu : q.windows.length<P := by rw [hq];exact PhysicalWindowRequests.field_bound hl
  have ht:=NodeUseTraffic.non_size q vs hn he hb hu tn pub B_UPB msg (by decide)
  rw [ht.1,ht.2,assigned_send,assigned_recv]
  simp only [hq,PhysicalWindowRequests.count]
  exact window_counter_field_balance tr tu pub (nodeWindowKeys vs) (nodeWindowKeys_distinct vs) hc msg

/-- Construct both physical tables from the actual read inventory. The node
terminal counters and UPS prefix counters are chosen here, not supplied as
independent witnesses. Other request families retain their original multisets. -/
theorem concrete (tr : Trace Fp) (tu tn : Nat) (pub : List Fp)
    (hl : TableLocal Render.UpsRelay.compactTable tr tu pub)
    (edges bmaps : List Msg) (vs : List NodeS3) (hn : Render.NodeOk vs)
    (he : edges.length<P) (hb : bmaps.length<P)
    (hc : ∀r∈physicalWindowRows tr tu,physicalWindowKey tr tu r∈nodeWindowKeys vs) :
    let q : UseRequests:=⟨edges,bmaps,PhysicalWindowRequests.keys tr tu⟩
    let node:=TrieCountHeight.node (assignList q 0 vs) pub
    let ups:=patchWindowCounters tr tu (physicalWindowRank tr tu)
    node.log tn=22 ∧ TableLocal SizeCount.nodeTable node tn pub ∧
    TableLocal Render.UpsRelay.compactTable ups tu pub ∧
    ∀msg,tableBusCount SizeCount.nodeTable.interactions node tn pub B_UPB true msg+
      tableBusCount Render.UpsRelay.compactTable.interactions ups tu pub B_UPB true msg=
      tableBusCount Render.UpsRelay.compactTable.interactions ups tu pub B_UPB false msg+
      tableBusCount SizeCount.nodeTable.interactions node tn pub B_UPB false msg := by
  refine ⟨rfl,NodeUseLocal.complete _ vs hn he hb (PhysicalWindowRequests.field_bound hl) tn pub,
    patchWindowCounters_local hl _,?_⟩
  intro msg
  exact balance tr tu tn pub hl _ vs hn he hb rfl hc msg

end ZkFormal.NearV3.Candidates.PhysicalWindowBalance
