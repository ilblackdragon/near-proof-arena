import ZkFormal.NearV3.Assembly.RoutingFrameLocal
import ZkFormal.NearV3.Rcpt.Link.BoundaryValidity

namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

theorem normalized_endpoint_positive {cb : Bytes} {k : WalkD0}
    (hk : walkD0 cb=.ok k) {q : Nat} (hq : q<(boundedIntervals k.L k.H.shardId).length) :
    ∀b∈((boundedIntervals k.L k.H.shardId).getD q (none,none)).2.getD [],0<b.toNat := by
  have hv := walkD0_boundaries hk
  have hb : ∀b∈(boundedLayout k.L).boundaries,AccountId.valid b=true := by
    intro b h
    exact hv b (List.mem_of_mem_take h)
  have hm : (boundedIntervals k.L k.H.shardId).getD q (none,none)∈
      ownIntervals (boundedLayout k.L) k.H.shardId := by
    change (boundedIntervals k.L k.H.shardId).getD q (none,none)∈boundedIntervals k.L k.H.shardId
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hq,Option.getD_some] using
      List.getElem_mem hq
  have he := ownIntervals_endpoints _ _ hb hm
  have hp := (RcptLink.boundaryNats_valid he.2).1
  intro b h
  apply (hp b.toNat ?_).1
  exact List.mem_map.mpr ⟨b,h,rfl⟩

/-- Actual decoded native receipts choose a normalized public interval, and every
receiver-byte/end-marker arithmetic frame satisfies the unchanged cRoute list.
This is a routing-group constructor, not a full receipt TableLocal theorem. -/
theorem applied_receipt_route_frames {cb bs : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    {w : StateWitness} (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k)
    (hw : decodeStateWitness bs=.ok w) {r : Receipt} (hr : r∈appliedReceipts k w)
    (pub : List Fp) :
    ∃q,selectInterval k.L k.H.shardId r.receiverId=some q ∧ q<128 ∧
      ∀pos,pos≤r.receiverId.length →
        routeKey (boundedPrep p k.L k.H.shardId).bnds q pos∈
          Public.boundaryRecords (boundedPrep p k.L k.H.shardId) ∧
        ∀e∈cRoute,e.eval (frameTrace (frameOf r.receiverId
          ((boundedIntervals k.L k.H.shardId).getD q (none,none)) pos)) 0 0 pub=0 := by
  obtain ⟨q,hq,hlt,hiv,hkeys⟩ := applied_receipt_selection hp hk hw hr
  refine ⟨q,hq,hlt,?_⟩
  intro pos hpos
  refine ⟨hkeys pos hpos,frame_route_constraints _ ?_ pub⟩
  exact frameOf_ordered _ _ _ hpos hiv
    (normalized_endpoint_positive hk (selectInterval_valid _ _ _ hq).1)

end ZkFormal.NearV3.Assembly.RoutingBoundedLayout
