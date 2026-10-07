import ZkFormal.NearV3.Rcpt.Link.ListByteIsolation

namespace ZkFormal.NearV3.RcptLink
open ZkFormal.Near ZkFormal.Algebra NearSpec Near.Link

/-- A receipt's global natural index lies inside the actual flattened lists. -/
theorem located_index_bound (ls : RcptV3Vs) {j : Nat} (hj : j<ls.length) :
    baseR ls j+ls[j].rs.length≤(flatR ls).length := by
  induction ls generalizing j with
  | nil => simp at hj
  | cons L ls ih =>
    cases j with
    | zero => simp only [baseR,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add,flatR,List.flatMap_cons,List.length_append,List.getElem_cons_zero]; omega
    | succ j =>
      have hh := ih (by simpa using hj)
      simp only [baseR,List.take_succ_cons,List.map_cons,List.sum_cons,flatR,List.flatMap_cons,List.length_append,List.getElem_cons_succ] at *
      omega

/-- All receipt byte-stream IDs are canonical under the physical table's coarse row bound. -/
theorem receipt_byte_id_canonical {pub : List Fp} {xs : List RcptE} {j r off a : Nat} {x : RcptE} {m : Msg}
    (hj : j<2^22) (hr : r<2^22) (hm : m∈rSends pub xs j r off x B_BYTES) (ha : m.head?=some a) : a<P := by
  simp only [rSends,ite_true,List.mem_append] at hm
  rcases hm with (((hm|hm)|hm)|hm)|hm
  · rw [emitAt_head_eq hm ha]; unfold msgId K_RC P; omega
  · split at hm
    · rw [emitAt_head_eq hm ha]; decide
    · simp at hm
  · rw [emitAt_head_eq hm ha]; unfold msgId K_PEO P; omega
  · rw [emitAt_head_eq hm ha]; unfold msgId K_LEAF P; omega
  · split at hm
    · rw [emitAt_head_eq hm ha]; unfold msgId K_RID P; omega
    · simp at hm

/-- Every byte sender ID in the receipt semantic traffic is canonical, before
selecting a particular RC stream. -/
theorem receipt_bytes_ids {pub : List Fp} {ls : RcptV3Vs}
    (hl : ls.length≤2^22) (hr : (flatR ls).length≤2^22)
    {m : Msg} (hm : m∈rcptSends3 pub ls B_BYTES) {a : Nat} (ha : m.head?=some a) : a<P := by
  simp only [rcptSends3,ite_true,show B_BYTES≠B_RCL by decide,ite_false,List.append_nil] at hm
  obtain ⟨j,hj,hm⟩ := List.mem_flatMap.mp hm
  have hj := List.mem_range.mp hj
  rcases List.mem_append.mp hm with hm|hm
  · rw [emitAt_head_eq hm ha]; unfold msgId K_RC P; omega
  · obtain ⟨⟨r,off,x⟩,hpos,hm⟩ := List.mem_flatMap.mp hm
    simp only [located,getD_eq_getElem' ls default hj,List.mem_map,List.mem_range] at hpos
    obtain ⟨k,hk,hpos⟩ := hpos
    cases hpos
    have hbound := located_index_bound ls hj
    exact receipt_byte_id_canonical (by omega) (by omega) hm ha

/-- Coarse list and receipt counts follow from physical rows, not from a new
native-domain restriction. -/
theorem physical_view_counts {tr : Air.Trace Fp} {pub : List Fp} {tt e : Nat}
    {bs : List RcptV3Proof.ListBlock} (hT : TableLocal RcptV3.table tr tt pub)
    (hc : RcptV3Proof.ListChain tr tt 0 bs e) :
    (bs.map (RcptV3Proof.ListBlock.view tr tt)).length≤2^22 ∧
    (flatR (bs.map (RcptV3Proof.ListBlock.view tr tt))).length≤2^22 := by
  have hlist := hc.length_le_rows
  have hreceipts := RcptV3Proof.receipt_counts_le_rows bs
  have hrows := hc.rows
  have hpad := hc.end_padding.1
  have hheight := RcptV3Proof.height_le hT
  simp only [List.length_map,RcptV3Proof.flat_views_length]
  omega

/-- Equality of field IDs cannot alias a different list or a different receipt stream. -/
theorem list_bytes_field_isolate {pub : List Fp} {ls : RcptV3Vs}
    (hl : ls.length≤2^22) (hr : (flatR ls).length≤2^22)
    {i : Nat} (hi : i<ls.length) {m : Msg} (hm : m∈rcptSends3 pub ls B_BYTES)
    {a : Nat} (ha : m.head?=some a) (he : Fp.ofNat a=Fp.ofNat (msgId K_RC i)) :
    ∃ k,k<(listEncoding pub ls[i]).length ∧ m=[msgId K_RC i,k,(listEncoding pub ls[i]).getD k 0] := by
  have hc := receipt_bytes_ids hl hr hm ha
  have hid : msgId K_RC i<P := by unfold msgId K_RC P; omega
  have heq := Near.Link.ofNat_inj hc hid he
  subst a
  obtain ⟨_,hh⟩ := list_bytes_isolate hm ha
  exact hh

end ZkFormal.NearV3.RcptLink
