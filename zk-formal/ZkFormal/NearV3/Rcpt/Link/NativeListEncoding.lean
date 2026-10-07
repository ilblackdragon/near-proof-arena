import ZkFormal.NearV3.Rcpt.Link.NativeEncoding

namespace ZkFormal.NearV3.RcptLink
open ZkFormal.Near ZkFormal.Algebra NearSpec Near.Link

/-- The four emitted count bytes encode the ordinary natural list length. -/
theorem list_count_encoding {a b n : Nat} (ha : a<256) (hb : b<256) (hn : n=a+256*b) :
    toBytes [a,b,0,0]=u32 n := by
  have he : leN' [a,b,0,0]=a+256*b := by
    simp only [leN',List.map_cons,List.map_nil,leNat,UInt8.toNat_ofNat',Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb]
    omega
  rw [←hn] at he
  rw [u32,←he]
  exact (leN_leN' (by rfl : [a,b,0,0].length=4)).symm

/-- A V3 receipt list serializes exactly the source proof's native preimage.
Byte-range and exact count premises are discharged by SHA and physical list facts. -/
theorem list_toBytes_encoding {pub : List Fp} {ls : RcptV3Vs} (h : RcptV3Wf pub ls)
    {L : ListV3} (hL : L∈ls) {own : Nat}
    (hown : toBytes (pubBytes pub PH_OWN 8)=u64 own)
    (h0 : L.n0<256) (h1 : L.n1<256) (hn : L.rs.length=L.n0+256*L.n1) :
    toBytes (hdrBytes pub L++L.rs.flatMap (fun x => x.enc))=
      u64 own++encodeReceipts (L.rs.map (fun x => x.toRcptV.toReceipt)) := by
  rw [toBytes_append,hdrBytes,toBytes_append,hown,list_count_encoding h0 h1 hn,
    view_receipts_encoding h hL]
  simp only [encodeReceipts,List.length_map,List.append_assoc]

/-- Physical header counting supplies exact native length independently of any
semantic dictionary assertion. -/
theorem physical_list_toBytes_encoding {tr : Air.Trace Fp} {pub : List Fp} {tt e : Nat}
    {bs : List RcptV3Proof.ListBlock}
    (hT : TableLocal RcptV3.table tr tt pub) (hc : RcptV3Proof.ListChain tr tt 0 bs e)
    (hp : RcptV3Proof.ReceiptPublicRanges pub) {B : RcptV3Proof.ListBlock} (hB : B∈bs)
    {own : Nat} (hown : toBytes (pubBytes pub PH_OWN 8)=u64 own)
    (h0 : (B.view tr tt).n0<256) (h1 : (B.view tr tt).n1<256) :
    toBytes (hdrBytes pub (B.view tr tt)++(B.view tr tt).rs.flatMap (fun x => x.enc))=
      u64 own++encodeReceipts ((B.view tr tt).rs.map (fun x => x.toRcptV.toReceipt)) :=
  list_toBytes_encoding (hc.view_wf hT hp) (List.mem_map.mpr ⟨B,hB,rfl⟩) hown h0 h1
    ((hc.blocks B hB).view_count hT h0 h1)

end ZkFormal.NearV3.RcptLink
