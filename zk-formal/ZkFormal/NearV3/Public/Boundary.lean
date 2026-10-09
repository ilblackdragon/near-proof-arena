import ZkFormal.NearV3.Public.Records
import ZkFormal.NearV3.Rcpt.Ids

/-! Routing boundary records at positions 0 through 64, including end sentinels. -/
namespace ZkFormal.NearV3.Public
open ZkFormal.V2 ZkFormal.Algebra

abbrev Interval := Option ByteString × Option ByteString

def boundaryRow (bounds : List Interval) (x : Nat) : ByteString :=
  let b := bounds.getD (x / BND_STRIDE) (none,none)
  let k := x % BND_STRIDE
  [(b.1.getD []).getD k 0, (b.2.getD []).getD k 0, if b.2.isNone then 1 else 0]

def boundaryPayload (bounds : List Interval) : Payload :=
  (List.range (BND_STRIDE*bounds.length)).map (boundaryRow bounds)

def boundaryPlan : PubSeg :=
  { bus := B_BNDP, send := true, width := 3, countAt := 0, start := 0, indexBase := some 0 }

theorem boundaryPayload_length (bounds : List Interval) :
    (boundaryPayload bounds).length = BND_STRIDE*bounds.length := by simp [boundaryPayload]

theorem boundaryPayload_width (bounds : List Interval) :
    ∀ row ∈ boundaryPayload bounds, row.length = boundaryPlan.width := by
  intro row hr
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hr
  rfl

theorem boundaryPayload_getD (bounds : List Interval) {x : Nat}
    (hx : x < BND_STRIDE*bounds.length) :
    (boundaryPayload bounds).getD x [] = boundaryRow bounds x := by
  rw [← List.getElem_eq_getD (h := (show x < (boundaryPayload bounds).length by
    rw [boundaryPayload_length]; exact hx)) []]
  simp only [boundaryPayload,List.getElem_map,List.getElem_range]

theorem boundary_record (bounds : List Interval) {x : Nat} (hx : x < BND_STRIDE*bounds.length) :
    recordValues boundaryPlan x ((boundaryPayload bounds).getD x []) =
      [Fp.ofNat x] ++ (boundaryRow bounds x).map byteF := by
  rw [boundaryPayload_getD bounds hx]
  simp only [recordValues,boundaryPlan,Nat.zero_add,List.map_nil,List.nil_append]
  rfl

theorem descriptor_boundary_record (header : ByteString) (blocks : List Payload)
    (bounds : List Interval) {i x : Nat} (hi : i < blocks.length)
    (hb : blocks.getD i [] = boundaryPayload bounds) (hx : x < BND_STRIDE*bounds.length)
    (ho : payloadOffset (dataStart header blocks) blocks i < 256^4) :
    (descriptor boundaryPlan header.length i).record (ZkFormal.Udr.pubOf Fp (encode header blocks)) x =
      [Fp.ofNat x] ++ (boundaryRow bounds x).map byteF := by
  rw [descriptor_record boundaryPlan header blocks hi
    (by rw [hb,boundaryPayload_length]; exact hx)
    (by rw [hb]; exact boundaryPayload_width bounds) ho,hb]
  exact boundary_record bounds hx

end ZkFormal.NearV3.Public
