import ZkFormal.NearV3.Rcpt.Link.NativeListEncoding

namespace ZkFormal.NearV3.RcptLink
open ZkFormal.Near ZkFormal.Algebra NearSpec NearSpecV3

/-- Native owner-shard bytes occupy their frozen position in the actual header. -/
theorem header_owner (p : Prep) (overhead : Nat) {k : Nat} (hk : k<8) :
    (Public.headerBytes p overhead).getD (PH_OWN+k) 0=(u64 p.hdr.own).getD k 0 := by
  simp only [Public.headerBytes,PrepHdr.encode,List.append_assoc]
  rw [show PH_OWN+k=(borshBytes prepTag).length+(8+k) by
    rw [Public.prep_tag_prefix_length]; unfold PH_OWN; omega]
  rw [Public.getD_right]
  rw [show 8+k=(u32 p.hdr.K).length+(4+k) by simp [u32,leN_length]; omega]
  rw [Public.getD_right]
  rw [show 4+k=(u32 p.hdr.n).length+k by simp [u32,leN_length]]
  rw [Public.getD_right]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simpa [u64,leN_length] using hk)]

/-- Exact byte windows survive actual field packing without a natural-value bound. -/
theorem public_bytes_native (pub : List Fp) (off : Nat) (bs : Bytes)
    (hr : ∀ k,k<bs.length → pub.getD (off+k) 0=Public.byteF (bs.getD k 0)) :
    toBytes (pubBytes pub off bs.length)=bs := by
  have hm : pubBytes pub off bs.length=bs.map UInt8.toNat := by
    apply List.ext_getElem (by simp [pubBytes])
    intro k hk hk'
    have hkB : k<bs.length := by simpa [pubBytes] using hk
    simp only [pubBytes,List.getElem_map,List.getElem_range,pubNat]
    rw [hr k hkB]
    change ZkFormal.V2.PubVal.val (Public.byteF (bs.getD k 0))=_
    rw [Public.byteF_val]
    simp only [List.getD,List.getElem?_eq_getElem hkB,Option.getD_some]
  rw [hm]
  exact Near.Link.toBytes_map_toNat' bs

/-- The receipt view's owner bytes are exactly the prepared native shard u64. -/
theorem prepared_owner (p : Prep) (overhead : Nat) (hr : Public.RootsSized p) :
    toBytes (pubBytes (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) PH_OWN 8)=u64 p.hdr.own := by
  have hlen : (u64 p.hdr.own).length=8 := by simp [u64,leN_length]
  rw [←hlen]
  apply public_bytes_native
  intro k hk
  rw [Public.pub_getD,Public.prepared_header p overhead hr (by unfold PH_OWN; omega),header_owner p overhead (by omega)]

end ZkFormal.NearV3.RcptLink
