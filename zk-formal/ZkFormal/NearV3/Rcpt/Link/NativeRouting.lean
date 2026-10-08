import ZkFormal.NearV3.Rcpt.Link.OwnIntervals
import ZkFormal.NearV3.Rcpt.Link.Lex
import ZkFormal.NearV3.Rcpt.Link.NativeEncoding

namespace ZkFormal.NearV3.RcptLink
open ZkFormal.Near NearSpec NearSpecV3

/-- Byte projection used by actual public boundary records, with zero-padding
for absent endpoints. -/
def boundaryNats (endpoint : Option Bytes) : List Nat := (endpoint.getD []).map UInt8.toNat

/-- Authenticated position-wise lookups in one ACTUAL native ownership interval
turn the extracted routing constraints into native receipt routing. Corrected
interval-index binding is a separate premise here, not inferred from packed keys. -/
theorem route_native_of_interval {x : RcptE} (hx : RouteOk x)
    (L : Layout) (own : Nat) (iv : Option Bytes × Option Bytes)
    (hiv : iv∈ownIntervals L own)
    (hlo : ∀ y∈boundaryNats iv.1,0<y ∧ y<256)
    (hhi : ∀ y∈boundaryNats iv.2,0<y ∧ y<256)
    (hll : (boundaryNats iv.1).length≤64) (hhl : (boundaryNats iv.2).length≤64)
    (hlookup : ∀ e∈x.rlk,e.2.1=padB (boundaryNats iv.1) e.1 ∧
      e.2.2.1=padB (boundaryNats iv.2) e.1 ∧ e.2.2.2.1=(if iv.2.isNone then 1 else 0)) :
    L.shardOf x.toRcptV.toReceipt.receiverId=own := by
  have hs := hx.sem (boundaryNats iv.1) (boundaryNats iv.2)
    (if iv.2.isNone then 1 else 0) hlo hhi hll hhl (by split <;> omega) hlookup
  change L.shardOf (toBytes x.v)=own
  apply ownIntervals_sound L own (toBytes x.v) hiv
  rcases iv with ⟨lo,hi⟩
  cases lo <;> cases hi <;>
    simp_all [Function.comp_def,boundaryNats,Option.getD_none,Option.getD_some,Option.isNone_none,
      Option.isNone_some,ite_true,Bool.false_eq_true,ite_false,inInterval,
      toBytes,List.map_map,UInt8.ofNat_toNat,List.map_id',Bool.and_eq_true,
      Nat.zero_ne_one,or_false,false_or,Bool.not_eq_true']

end ZkFormal.NearV3.RcptLink
