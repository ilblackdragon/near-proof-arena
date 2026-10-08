import ZkFormal.NearV3.Rcpt.Candidates.NativeSourceSize

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 ZkFormal.Near

/-- Native receipt encoding is nonempty even before any receipt wellformedness
assumption; it includes the fixed receipt/action tags. -/
theorem receipt_encoding_positive (r : Receipt) : 0<r.encode.length := by
  simp only [Receipt.encode,List.length_append,List.length_cons,List.length_nil]
  omega

/-- The twelve-byte shard/list header cannot hide a native receipt. -/
theorem receipt_preimage_empty {own : Nat} {rs : List Receipt}
    (h : (u64 own++encodeReceipts rs).length=12) : rs=[] := by
  cases rs with
  | nil => rfl
  | cons r rs =>
    have hp := receipt_encoding_positive r
    simp only [encodeReceipts,List.map_cons,concatAll,List.length_append,
      u64,u32,leN,List.length_cons,List.length_nil] at h
    omega

/-- Exact native SIZE authentication plus the repeated-source twelve-byte charge
forces the extracted receipt view itself to be empty. -/
theorem receipt_view_empty {own : Nat} {L : ListV3}
    (h : (u64 own++encodeReceipts (L.rs.map (fun x => x.toRcptV.toReceipt))).length=12) :
    L.rs=[] := by
  have hh := receipt_preimage_empty h
  exact List.map_eq_nil_iff.mp hh

end ZkFormal.NearV3.Rcpt.Candidates
