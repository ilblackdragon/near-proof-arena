import ZkFormal.NearV3.Rcpt.Link.ListByteIds
import ZkFormal.NearV3.Assembly.RoutingQExtract
import ZkFormal.NearV3.Rcpt.Link.BndRequests

namespace ZkFormal.NearV3.RcptLink
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3Proof

/-- The candidate repair bounds every receipt in the SAME complete physical view. -/
theorem candidate_view_q {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal Assembly.RoutingQCandidate.candidateTable tr tt pub)
    {bs : List ListBlock} {e : Nat} (hc : ListChain tr tt 0 bs e) :
    ∀ x∈flatR (bs.map (ListBlock.view tr tt)),x.q<128 := by
  intro x hx
  obtain ⟨L,hLm,hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hLm
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
  exact Assembly.RoutingQCandidate.extracted_q_lt h ((hc.blocks B hB).layouts y hy)

/-- Corrected local receipt AIR plus actual BND counter balance supplies a real
boundary provider for every physical-view routing request. -/
theorem candidate_boundary_provider {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal Assembly.RoutingQCandidate.candidateTable tr tt pub)
    {bs : List ListBlock} {e : Nat} (hc : ListChain tr tt 0 bs e)
    (hp : ReceiptPublicRanges pub) (es : List BndE) (he : BndWf es)
    (hb : ((es.map (fun e => e.rec4++[0])++
        (boundaryRequests (bs.map (ListBlock.view tr tt))).map (fun r => r.1++[r.2+1])).map Msg.toFp).Perm
      ((es.map (fun e => e.rec4++[e.U])++
        (boundaryRequests (bs.map (ListBlock.view tr tt))).map (fun r => r.1++[r.2])).map Msg.toFp)) :
    ∀ r∈boundaryRequests (bs.map (ListBlock.view tr tt)),∃ e∈es,e.rec4=r.1 := by
  have hl := Assembly.RoutingQCandidate.local_base h
  have hv := hc.view_wf hl hp
  have hn := (physical_view_counts hl hc).2
  exact bnd_lookup_provider es _ he
    (boundaryRequests_canonical hv (candidate_view_q h hc)) (boundaryRequests_bound hv hn) hb

end ZkFormal.NearV3.RcptLink
