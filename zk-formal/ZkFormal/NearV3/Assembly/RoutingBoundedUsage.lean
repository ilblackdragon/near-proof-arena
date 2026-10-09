import ZkFormal.NearV3.Assembly.RoutingBoundedRender
import ZkFormal.NearV3.Rcpt.Link.BndRequests

namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Algebra ZkFormal.Air

def requestKeys (ls : RcptV3Vs) : List Msg := (RcptLink.boundaryRequests ls).map Prod.fst

/-- Provider usage counts come from the actual receipt routing requests. Their
field range follows from the existing receipt row budget, not an extra cap. -/
theorem normalized_render_from_receipts {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k)
    {pub : List Fp} {ls : RcptV3Vs} (hv : RcptV3Wf pub ls)
    (hn : (flatR ls).length≤2^22) :
    let bounds := (boundedPrep p k.L k.H.shardId).bnds
    let es := boundaryEntries bounds (requestKeys ls)
    BndWf es ∧
    es.map BndE.rec4=Public.boundaryRecords (boundedPrep p k.L k.H.shardId) ∧
    TableLocal BndV3.table (boundaryTrace bounds (requestKeys ls)) 0 pub ∧
    TableTraffic BndV3.interactions (boundaryTrace bounds (requestKeys ls)) 0 pub (bndTraffic es) := by
  apply normalized_render hp hk
  simpa only [requestKeys,List.length_map] using RcptLink.boundaryRequests_bound hv hn

end ZkFormal.NearV3.Assembly.RoutingBoundedLayout
