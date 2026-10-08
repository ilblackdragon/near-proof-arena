import ZkFormal.NearV3.Rcpt.Link.BndAuthenticated
import ZkFormal.NearV3.Rcpt.Link.BoundaryValidity
import ZkFormal.NearV3.Rcpt.Candidates.PreparedRoutingIntervals

namespace ZkFormal.NearV3.RcptLink
open ZkFormal.Near ZkFormal.Algebra NearSpec NearSpecV3 RcptV3Proof

/-- Authenticated requests from the complete receipt view imply native routing
under actual successful preparation. Endpoint validity is derived from decoding. -/
theorem prepared_native_routing {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hprep : prepD0 cb hint=.ok p) (hwalk : walkD0 cb=.ok k)
    {pub : List Fp} {ls : RcptV3Vs} (hv : RcptV3Wf pub ls)
    (es : List BndE) (he : BndWf es)
    (hb : ∀ m,cnt (es.map BndE.rec4) m=cnt (Public.boundaryRecords p) m)
    (hp : ∀ r∈boundaryRequests ls,∃ e∈es,e.rec4=r.1)
    {x : RcptE} (hx : x∈flatR ls) :
    k.L.shardOf x.toRcptV.toReceipt.receiverId=k.H.shardId := by
  have hr := (view_route_bounds hv hx).1
  have hn : 0<x.rlk.length := by have := hr.len.1; omega
  have hfirst := List.getElem_mem hn
  have ha := boundary_requests_authenticated p hv es he hb hp hx hfirst
  have hi : p.bnds.getD x.q (none,none)∈p.bnds := by
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ha.1,Option.getD_some] using List.getElem_mem ha.1
  have hintervals := Assembly.prepD0_routing_intervals hprep hwalk
  have him : p.bnds.getD x.q (none,none)∈ownIntervals k.L k.H.shardId := by
    rw [←hintervals]; exact hi
  have hs := Assembly.ownIntervals_endpoints k.L k.H.shardId
    (Assembly.walkD0_boundaries hwalk) him
  have hlo := boundaryNats_valid hs.1
  have hhi := boundaryNats_valid hs.2
  apply route_native_of_interval hr k.L k.H.shardId _ him hlo.1 hhi.1 hlo.2 hhi.2
  intro e hem
  exact (boundary_requests_authenticated p hv es he hb hp hx hem).2

/-- Candidate receipt AIR, exact BND counter/public balance, and native prep
close routing for every receipt in the SAME complete physical view. -/
theorem candidate_native_routing {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hprep : prepD0 cb hint=.ok p) (hwalk : walkD0 cb=.ok k)
    {tr : ZkFormal.Air.Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal Assembly.RoutingQCandidate.candidateTable tr tt pub)
    {bs : List ListBlock} {e : Nat} (hc : ListChain tr tt 0 bs e)
    (hrange : ReceiptPublicRanges pub) (es : List BndE) (he : BndWf es)
    (hpublic : ∀ m,cnt (es.map BndE.rec4) m=cnt (Public.boundaryRecords p) m)
    (hb : ((es.map (fun e => e.rec4++[0])++
        (boundaryRequests (bs.map (ListBlock.view tr tt))).map (fun r => r.1++[r.2+1])).map Msg.toFp).Perm
      ((es.map (fun e => e.rec4++[e.U])++
        (boundaryRequests (bs.map (ListBlock.view tr tt))).map (fun r => r.1++[r.2])).map Msg.toFp)) :
    ∀ x∈flatR (bs.map (ListBlock.view tr tt)),
      k.L.shardOf x.toRcptV.toReceipt.receiverId=k.H.shardId := by
  have hv := hc.view_wf (Assembly.RoutingQCandidate.local_base h) hrange
  have hp := candidate_boundary_provider h hc hrange es he hb
  intro x hx
  exact prepared_native_routing hprep hwalk hv es he hpublic hp hx

end ZkFormal.NearV3.RcptLink
