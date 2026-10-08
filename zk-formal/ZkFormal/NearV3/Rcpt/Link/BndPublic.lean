import ZkFormal.NearV3.Rcpt.Link.BndProvider
import ZkFormal.NearV3.Public.ReceiptIndex

namespace ZkFormal.NearV3.RcptLink
open ZkFormal.Near ZkFormal.Algebra NearSpec Near.Link

/-- Actual public multiplicity forces every prepared boundary record to fit the
physical BND capacity. No native layout-length assumption is introduced. -/
theorem boundary_public_capacity (p : NearSpecV3.Prep) (es : List BndE) (he : BndWf es)
    (hb : ∀ m,cnt (es.map BndE.rec4) m=cnt (Public.boundaryRecords p) m) :
    BND_STRIDE*p.bnds.length≤8192 := by
  have hp : ((es.map BndE.rec4).map Msg.toFp).Perm ((Public.boundaryRecords p).map Msg.toFp) :=
    List.perm_iff_count.mpr hb
  have hl := hp.length_eq
  simp only [Public.boundaryRecords,List.length_map,List.length_range] at hl
  have hh := he.rows
  change es.length≤8192 at hh
  omega

/-- A boundary provider is the exact public indexed record, not merely a
field-equivalent unbounded natural tuple. -/
theorem boundary_public_record (p : NearSpecV3.Prep) (es : List BndE) (he : BndWf es)
    (hb : ∀ m,cnt (es.map BndE.rec4) m=cnt (Public.boundaryRecords p) m)
    {e : BndE} (hem : e∈es) :
    ∃ x,x<BND_STRIDE*p.bnds.length ∧ e.rec4=[x]++(Public.boundaryRow p.bnds x).map UInt8.toNat := by
  have hm : e.rec4.toFp∈(es.map BndE.rec4).map Msg.toFp :=
    List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨e,hem,rfl⟩,rfl⟩
  have hc := List.count_pos_iff.mpr hm
  change 0<cnt (es.map BndE.rec4) e.rec4.toFp at hc
  rw [hb] at hc
  obtain ⟨msg,hmsg,hfield⟩ := List.mem_map.mp (List.count_pos_iff.mp hc)
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hmsg
  have hxl := List.mem_range.mp hx
  have hcap := boundary_public_capacity p es he hb
  have hcanon : Canon ([x]++(Public.boundaryRow p.bnds x).map UInt8.toNat) := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · obtain rfl := List.mem_singleton.mp ha
      unfold P
      omega
    · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      have hh := b.toNat_lt
      unfold P
      omega
  have hecanon : Canon e.rec4 := by
    obtain ⟨hx,hl,hh,hn,_⟩ := he.canon e hem
    intro a ha
    simp only [BndE.rec4,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl <;> assumption
  exact ⟨x,hxl,(toFp_inj hcanon hecanon hfield).symm⟩

end ZkFormal.NearV3.RcptLink
