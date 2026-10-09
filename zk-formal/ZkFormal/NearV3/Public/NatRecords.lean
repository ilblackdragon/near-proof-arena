import ZkFormal.NearV3.Public.Records

/-! Byte serialization preserves natural-valued scheduler messages when every
component is a byte. Non-byte generated indices use indexed segments instead. -/
namespace ZkFormal.NearV3.Public
open ZkFormal.V2 ZkFormal.Algebra

def natPayload (records : List (List Nat)) : Payload := records.map (·.map UInt8.ofNat)

theorem byteF_ofNat (n : Nat) (hn : n < 256) : byteF (UInt8.ofNat n) = Fp.ofNat n := by
  unfold byteF
  rw [UInt8.toNat_ofNat',Nat.mod_eq_of_lt hn]

theorem natRow_field (row : List Nat) (hb : ∀ n ∈ row, n < 256) :
    (row.map UInt8.ofNat).map byteF = row.map Fp.ofNat := by
  rw [List.map_map]
  apply List.map_congr_left
  intro n hn
  exact byteF_ofNat n (hb n hn)

theorem natPayload_width (records : List (List Nat)) (width : Nat)
    (hw : ∀ row ∈ records, row.length = width) :
    ∀ row ∈ natPayload records, row.length = width := by
  intro row hr
  change row ∈ records.map (·.map UInt8.ofNat) at hr
  obtain ⟨r,hs,he⟩ := List.mem_map.mp hr
  rw [← he,List.length_map]
  exact hw r hs

theorem natPayload_getD (records : List (List Nat)) {j : Nat} (hj : j < records.length) :
    (natPayload records).getD j [] = (records.getD j []).map UInt8.ofNat := by
  rw [← List.getElem_eq_getD (h := (show j < (natPayload records).length by
    simpa [natPayload] using hj)) [],← List.getElem_eq_getD (h := hj) []]
  simp only [natPayload,List.getElem_map]

theorem nat_record (plan : PubSeg) (records : List (List Nat))
    (hp : plan.msgPrefix = []) (hidx : plan.indexBase = none)
    (hb : ∀ row ∈ records, ∀ n ∈ row, n < 256) {j : Nat} (hj : j < records.length) :
    recordValues plan j ((natPayload records).getD j []) = (records.getD j []).map Fp.ofNat := by
  rw [natPayload_getD records hj]
  simp only [recordValues,hp,hidx,List.map_nil,List.nil_append]
  apply natRow_field
  apply hb
  rw [← List.getElem_eq_getD (h := hj) []]
  exact List.getElem_mem hj

theorem descriptor_nat_record (plan : PubSeg) (header : ByteString) (blocks : List Payload)
    (records : List (List Nat)) {i j : Nat} (hi : i < blocks.length)
    (hp : plan.msgPrefix = []) (hidx : plan.indexBase = none)
    (hb : blocks.getD i [] = natPayload records) (hj : j < records.length)
    (hw : ∀ row ∈ records, row.length = plan.width)
    (hbytes : ∀ row ∈ records, ∀ n ∈ row, n < 256)
    (ho : payloadOffset (dataStart header blocks) blocks i < 256^4) :
    (descriptor plan header.length i).record (ZkFormal.Udr.pubOf Fp (encode header blocks)) j =
      (records.getD j []).map Fp.ofNat := by
  rw [descriptor_record plan header blocks hi
    (by rw [hb]; simpa [natPayload] using hj)
    (by rw [hb]; exact natPayload_width records plan.width hw) ho,hb]
  exact nat_record plan records hp hidx hbytes hj

end ZkFormal.NearV3.Public
