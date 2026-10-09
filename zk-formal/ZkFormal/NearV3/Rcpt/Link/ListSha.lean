import ZkFormal.NearV3.Rcpt.Link.ListEncodingBounds

namespace ZkFormal.NearV3.RcptLink
open ZkFormal.Near ZkFormal.Algebra NearSpec Near.Link

/-- The closed SHA contract authenticates one complete RC list. Other table
senders must have canonical IDs outside the RC kind; receipt-stream isolation is proved. -/
theorem list_sha_digest {pub : List Fp} {ls : RcptV3Vs} (h : RcptV3Wf pub ls)
    (hl : ls.length≤2^22) (hr : (flatR ls).length≤2^22)
    {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR) (others : List Msg)
    (hbytes : ∀ m,shaR B_BYTES m=cnt (rcptSends3 pub ls B_BYTES++others) m)
    (hother : ∀ m∈others,∀ a,m.head?=some a → a<P ∧ a%16≠K_RC)
    {i : Nat} (hi : i<ls.length) (hlen : (listEncoding pub ls[i]).length<P)
    {d : List Nat} (hd : ∀ v∈d,v<P)
    (hrecv : 0<shaS B_DIGEST (digMsg (msgId K_RC i) (listEncoding pub ls[i]).length d).toFp) :
    Bytes8 (listEncoding pub ls[i]) ∧ d=(sha256 (toBytes (listEncoding pub ls[i]))).map UInt8.toNat := by
  have hid : msgId K_RC i<P := by unfold msgId K_RC P; omega
  apply sha_core hsha _ hbytes hid (list_encoding_canonical h (List.getElem_mem hi)) hlen hd _ hrecv
  intro m hm a ha he
  rcases List.mem_append.mp hm with hm|hm
  · exact list_bytes_field_isolate hl hr hi hm ha he
  · have hh := hother m hm a ha
    have heq := Near.Link.ofNat_inj hh.1 hid he
    have hk : msgId K_RC i%16=K_RC := by simp [msgId,K_RC,Nat.add_mod]
    exact False.elim (hh.2 (heq ▸ hk))

/-- SHA-range-checked header bytes turn the field-valued list count into its
ordinary natural count; no extra public or native receipt-count restriction. -/
theorem list_byte_count {pub : List Fp} {ls : RcptV3Vs} (h : RcptV3Wf pub ls)
    (hr : (flatR ls).length≤2^22) {i : Nat} (hi : i<ls.length)
    (hb : Bytes8 (listEncoding pub ls[i])) :
    ls[i].n0<256 ∧ ls[i].n1<256 ∧ ls[i].rs.length=ls[i].n0+256*ls[i].n1 := by
  have h0 : ls[i].n0<256 := hb _ (by simp [listEncoding,hdrBytes])
  have h1 : ls[i].n1<256 := hb _ (by simp [listEncoding,hdrBytes])
  refine ⟨h0,h1,?_⟩
  have hbound := located_index_bound ls hi
  have hh := h.nj ls[i] (List.getElem_mem hi)
  exact (Near.Link.ofNat_inj (by unfold P; omega) (by unfold P; omega) hh).symm

/-- An RC leaf digest is the actual native receipt-proof preimage hash. -/
theorem list_sha_native {pub : List Fp} {ls : RcptV3Vs} (h : RcptV3Wf pub ls)
    (hl : ls.length≤2^22) (hr : (flatR ls).length≤2^22)
    {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR) (others : List Msg)
    (hbytes : ∀ m,shaR B_BYTES m=cnt (rcptSends3 pub ls B_BYTES++others) m)
    (hother : ∀ m∈others,∀ a,m.head?=some a → a<P ∧ a%16≠K_RC)
    {i : Nat} (hi : i<ls.length) (hlen : (listEncoding pub ls[i]).length<P)
    {d : List Nat} (hd : ∀ v∈d,v<P)
    (hrecv : 0<shaS B_DIGEST (digMsg (msgId K_RC i) (listEncoding pub ls[i]).length d).toFp)
    {own : Nat} (hown : toBytes (pubBytes pub PH_OWN 8)=u64 own) :
    toBytes d=sha256 (u64 own++encodeReceipts (ls[i].rs.map (fun x => x.toRcptV.toReceipt))) := by
  obtain ⟨hb,he⟩ := list_sha_digest h hl hr hsha others hbytes hother hi hlen hd hrecv
  obtain ⟨h0,h1,hn⟩ := list_byte_count h hr hi hb
  rw [he,Near.Link.toBytes_map_toNat']
  unfold listEncoding
  rw [list_toBytes_encoding h (List.getElem_mem hi) hown h0 h1 hn]

end ZkFormal.NearV3.RcptLink
