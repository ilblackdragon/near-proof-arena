import ZkFormal.NearV3.Rcpt.Extract.BndProof
import ZkFormal.NearV3.Link.Walk3Chain

namespace ZkFormal.NearV3.RcptLink
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Link

/-- Exact BND counter balance supplies an actual boundary provider. The request
bound excludes a provider-free field cycle; repeated requests are counted. -/
theorem bnd_lookup_provider (es : List BndE) (reqs : List (Msg × Nat))
    (he : BndWf es)
    (hr : ∀ r∈reqs,r.1.length=4 ∧ Canon r.1 ∧ r.2<P)
    (hlen : reqs.length<P)
    (hb : ((es.map (fun e => e.rec4++[0])++reqs.map (fun r => r.1++[r.2+1])).map Msg.toFp).Perm
      ((es.map (fun e => e.rec4++[e.U])++reqs.map (fun r => r.1++[r.2])).map Msg.toFp)) :
    ∀ r∈reqs,∃ e∈es,e.rec4=r.1 := by
  intro r hm
  by_cases hex : ∃ e∈es,e.rec4=r.1
  · exact hex
  · exfalso
    apply Walk3.chain_provided
      (es.map (fun e => e.rec4++[0])) (es.map (fun e => e.rec4++[e.U])) reqs r.1
      _ hr hlen (hr r hm).1 (hr r hm).2.1 hm hb
    intro m hmem
    have hc : ∀ e∈es,Canon e.rec4 := by
      intro e hem a ha
      obtain ⟨hx,hl,hh,hn,_⟩ := he.canon e hem
      simp only [BndE.rec4,List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl <;> assumption
    rcases List.mem_append.mp hmem with hmem|hmem
    · obtain ⟨e,hem,rfl⟩ := List.mem_map.mp hmem
      exact ⟨e.rec4,0,rfl,rfl,hc e hem,fun h => hex ⟨e,hem,h⟩⟩
    · obtain ⟨e,hem,rfl⟩ := List.mem_map.mp hmem
      exact ⟨e.rec4,e.U,rfl,rfl,hc e hem,fun h => hex ⟨e,hem,h⟩⟩

/-- Seven actual q bits and the existing position bound suffice for an injective
natural interpretation of the packed boundary key. The q bound must come from a
candidate AIR repair; it is not a fact of the frozen receipt table. -/
theorem bounded_boundary_key {q pos x : Nat} (hq : q<128) (hp : pos<65) (hx : x<8192)
    (he : Fp.ofNat (65*q+pos)=Fp.ofNat x) : q=x/65 ∧ pos=x%65 := by
  have hn : 65*q+pos=x := ZkFormal.Near.Link.ofNat_inj (by unfold P; omega) (by unfold P; omega) he
  omega

end ZkFormal.NearV3.RcptLink
