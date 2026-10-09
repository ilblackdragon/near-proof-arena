import ZkFormal.NearV3.Rcpt.Link.ListByteIds

namespace ZkFormal.NearV3.RcptLink
open ZkFormal.Near ZkFormal.Algebra NearSpec Near.Link

theorem receipt_enc_values {x : RcptE} {r tok tok' : Nat} {gp : List Nat}
    (w : x.Wf r gp tok tok') : RawOrByte x.toRcptV x.enc := by
  obtain ⟨hp,hv,hs,_⟩ := w.ids
  have hp := (valid_length hp).2
  have hv := (valid_length hv).2
  have hs := (valid_length hs).2
  simp only [toBytes_length] at hp hv hs
  unfold RcptV.enc
  rob

/-- Every natural RC payload limb is canonical, including header and inline lengths. -/
theorem list_encoding_canonical {pub : List Fp} {ls : RcptV3Vs} (h : RcptV3Wf pub ls)
    {L : ListV3} (hL : L∈ls) : ∀ v∈listEncoding pub L,v<P := by
  intro v hv
  simp only [listEncoding,hdrBytes,List.mem_append] at hv
  rcases hv with (hv|hv)|hv
  · simp only [pubBytes,List.mem_map] at hv
    obtain ⟨i,_,rfl⟩ := hv
    exact Fp.toNat_lt _
  · have hh := h.canon.1 L hL
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl|rfl|rfl
    · exact hh.1
    · exact hh.2
    · decide
    · decide
  · obtain ⟨x,hx,hv⟩ := List.mem_flatMap.mp hv
    have hmem : x∈flatR ls := List.mem_flatMap.mpr ⟨L,hL,hx⟩
    obtain ⟨toks,_,_,hw,_⟩ := h.toks
    obtain ⟨r,hr,he⟩ := List.mem_iff_getElem.mp hmem
    have hw := hw r hr
    rw [he] at hw
    rcases receipt_enc_values hw v hv with hv|hv
    · exact h.canon.2 x hmem v (by simp [RcptE.raw3,hv])
    · unfold P; omega

/-- RC payload length is the same natural endpoint sent over RCL. -/
theorem list_encoding_length (pub : List Fp) (L : ListV3) :
    (listEncoding pub L).length=lOffs L.rs L.rs.length := by
  rw [list_offset_flat,List.take_length]
  simp only [listEncoding,List.length_append,list_header_length]

end ZkFormal.NearV3.RcptLink
