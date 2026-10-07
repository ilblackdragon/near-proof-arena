import ZkFormal.NearV3.Rcpt.Extract.V.ViewProof
import ZkFormal.Near.Link.EncLemmas

namespace ZkFormal.NearV3.RcptLink
open ZkFormal.Near ZkFormal.Algebra NearSpec Near.Link

/-- V3 permits system receipts; encoding only needs the actual shared byte layout
and identifier/length facts, not the V1 non-system receipt premise. -/
theorem receipt_toBytes_enc {x : RcptE} {r tok tok' : Nat} {gp : List Nat}
    (w : x.Wf r gp tok tok') : toBytes x.enc=x.toRcptV.toReceipt.encode := by
  obtain ⟨hp,hv,hs,_⟩ := w.ids
  have hp := (valid_length hp).2
  have hv := (valid_length hv).2
  have hs := (valid_length hs).2
  simp only [toBytes_length] at hp hv hs
  obtain ⟨_,_,hkt,hgp,hdep,_⟩ := w.lens
  have hkt8 : x.kt<256 := by omega
  simp only [RcptV.enc,toBytes_append,RcptV.toReceipt,Receipt.encode,PublicKey.encode]
  rw [toBytes_borshN (by omega),toBytes_borshN (by omega),toBytes_borshN (by omega),tailN_eq]
  simp only [u128]
  rw [leN_leN' (w:=16) hgp,leN_leN' (w:=16) hdep]
  have ht : u8 x.kt=toBytes [x.kt] := by
    simp only [u8,leN,toBytes,List.map_cons,List.map_nil,Nat.mod_eq_of_lt hkt8]
  rw [ht]
  simp only [List.append_assoc]
  rfl

/-- Every receipt in a full extracted V3 view carries the native encoding equality. -/
theorem view_receipt_encoding {pub : List Fp} {ls : RcptV3Vs} (h : RcptV3Wf pub ls)
    {x : RcptE} (hx : x∈flatR ls) : toBytes x.enc=x.toRcptV.toReceipt.encode := by
  obtain ⟨toks,_,_,hw,_⟩ := h.toks
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
  have hh := receipt_toBytes_enc (hw i hi)
  simpa only [he] using hh

/-- Native receipt-list payload bytes are the concatenation already emitted by
V3 receipt fields; this statement makes no V1 slice assumption. -/
theorem view_receipts_encoding {pub : List Fp} {ls : RcptV3Vs} (h : RcptV3Wf pub ls)
    {L : ListV3} (hL : L∈ls) :
    toBytes (L.rs.flatMap (fun x => x.enc))=
      concatAll ((L.rs.map (fun x => x.toRcptV.toReceipt)).map Receipt.encode) := by
  rw [toBytes_flatMap,List.map_map]
  congr 1
  apply List.map_congr_left
  intro x hx
  exact view_receipt_encoding h (List.mem_flatMap.mpr ⟨L,hL,hx⟩)

end ZkFormal.NearV3.RcptLink
