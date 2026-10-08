import ZkFormal.NearV3.Rcpt.Link.ListSha

namespace ZkFormal.NearV3.RcptLink
open ZkFormal.Near ZkFormal.Algebra NearSpec Near.Link

/-- SHA byte coverage identifies the exact native encoded preimage length. -/
theorem list_sha_native_size {pub : List Fp} {ls : RcptV3Vs} (h : RcptV3Wf pub ls)
    (hl : ls.length≤2^22) (hr : (flatR ls).length≤2^22)
    {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR) (others : List Msg)
    (hbytes : ∀ m,shaR B_BYTES m=cnt (rcptSends3 pub ls B_BYTES++others) m)
    (hother : ∀ m∈others,∀ a,m.head?=some a → a<P ∧ a%16≠K_RC)
    {i : Nat} (hi : i<ls.length) (hlen : (listEncoding pub ls[i]).length<P)
    {d : List Nat} (hd : ∀ v∈d,v<P)
    (hrecv : 0<shaS B_DIGEST (digMsg (msgId K_RC i) (listEncoding pub ls[i]).length d).toFp)
    {own : Nat} (hown : toBytes (pubBytes pub PH_OWN 8)=u64 own) :
    (u64 own++encodeReceipts (ls[i].rs.map (fun x => x.toRcptV.toReceipt))).length=
      (listEncoding pub ls[i]).length := by
  obtain ⟨hb,_⟩ := list_sha_digest h hl hr hsha others hbytes hother hi hlen hd hrecv
  obtain ⟨h0,h1,hn⟩ := list_byte_count h hr hi hb
  have he := list_toBytes_encoding h (List.getElem_mem hi) hown h0 h1 hn
  have hh := congrArg List.length he
  simpa only [listEncoding,toBytes,List.length_map] using hh.symm

end ZkFormal.NearV3.RcptLink
