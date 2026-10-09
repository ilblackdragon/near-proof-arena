import ZkFormal.NearV3.Rcpt.Link.BndDecode
import ZkFormal.NearV3.Rcpt.Link.BndCandidateView

namespace ZkFormal.NearV3.RcptLink
open ZkFormal.Near ZkFormal.Algebra NearSpec

/-- Exact public BND counts and actual providers identify every requested endpoint
with the prepared interval selected by the receipt's natural index. -/
theorem boundary_requests_authenticated (p : NearSpecV3.Prep)
    {pub : List Fp} {ls : RcptV3Vs} (hv : RcptV3Wf pub ls)
    (es : List BndE) (he : BndWf es)
    (hb : ∀ m,cnt (es.map BndE.rec4) m=cnt (Public.boundaryRecords p) m)
    (hp : ∀ r∈boundaryRequests ls,∃ e∈es,e.rec4=r.1)
    {x : RcptE} (hx : x∈flatR ls) {pos lo hi hn u : Nat}
    (hr : (pos,lo,hi,hn,u)∈x.rlk) :
    x.q<p.bnds.length ∧
    lo=padB (boundaryNats (p.bnds.getD x.q (none,none)).1) pos ∧
    hi=padB (boundaryNats (p.bnds.getD x.q (none,none)).2) pos ∧
    hn=(if (p.bnds.getD x.q (none,none)).2.isNone then 1 else 0) := by
  have hvx := view_route_bounds hv hx
  have hpos : pos∈List.range x.rlk.length := by
    rw [←hvx.1.pos]
    exact List.mem_map.mpr ⟨(pos,lo,hi,hn,u),hr,rfl⟩
  have hpl := List.mem_range.mp hpos
  have hlen := hvx.1.len.2
  have hpos65 : pos<65 := by omega
  have hm : ([65*x.q+pos,lo,hi,hn],u)∈boundaryRequests ls :=
    List.mem_flatMap.mpr ⟨x,hx,List.mem_map.mpr ⟨(pos,lo,hi,hn,u),hr,rfl⟩⟩
  obtain ⟨e,hem,here⟩ := hp _ hm
  obtain ⟨idx,hidx,hrec⟩ := boundary_public_record p es he hb hem
  have hrecord : [65*x.q+pos,lo,hi,hn]=[idx]++(Public.boundaryRow p.bnds idx).map UInt8.toNat :=
    here.symm.trans hrec
  exact boundary_record_decode p hpos65 hidx hrecord

end ZkFormal.NearV3.RcptLink
