import ZkFormal.NearV3.Public.PreparedFit

/-! Static header reads of the concrete encoded statement. Witness overhead
range is explicit: serializing u32 alone must never certify its natural value. -/
namespace ZkFormal.NearV3.Public
open ZkFormal.V2 ZkFormal.Algebra NearSpecV3

theorem encode_header (header : ByteString) (blocks : List Payload) {j : Nat}
    (hj : j < header.length) : (encode header blocks).getD j 0 = header.getD j 0 := by
  unfold encode
  rw [List.append_assoc]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hj]

theorem prepared_header (p : Prep) (witnessOverhead : Nat) (hr : RootsSized p) {j : Nat}
    (hj : j < 202) :
    (preparedBytes p witnessOverhead).getD j 0 = (headerBytes p witnessOverhead).getD j 0 := by
  apply encode_header
  rw [headerBytes_length p witnessOverhead hr]
  exact hj

theorem prepared_body_size_le (p : Prep) (witnessOverhead : Nat) (hr : RootsSized p) :
    p.body.length ≤ (preparedBytes p witnessOverhead).length := by
  have hb := data_block_bound (preparedBlocks p) (i := 2) (by rw [preparedBlocks_length]; decide)
  change (dataBytes ((preparedBlocks p).take 2)).length + (payloadBytes (bodyPayload p.body)).length ≤ _ at hb
  rw [payload_length _ 1 (bodyPayload_width p.body),bodyPayload_length,Nat.mul_one] at hb
  have he := encode_length (headerBytes p witnessOverhead) (preparedBlocks p)
  rw [prepared_dataStart p witnessOverhead hr] at he
  change (preparedBytes p witnessOverhead).length = _ at he
  omega

theorem prepared_body_count (p : Prep) (witnessOverhead : Nat) (hr : RootsSized p)
    (hlen : (preparedBytes p witnessOverhead).length < 256^4) :
    V2.leNat ((List.range 4).map (fun k => PubVal.val
      ((ZkFormal.Udr.pubOf Fp (preparedBytes p witnessOverhead)).getD (PH_BLEN+k) 0))) =
      p.body.length := by
  apply read4_u32 _ _ (by have := prepared_body_size_le p witnessOverhead hr; omega)
  intro k hk
  rw [pub_getD,prepared_header p witnessOverhead hr (by unfold PH_BLEN; omega),
    header_body_length p witnessOverhead hr hk]

theorem prepared_overhead_count (p : Prep) (witnessOverhead : Nat) (hr : RootsSized p)
    (ho : witnessOverhead < 256^4) :
    V2.leNat ((List.range 4).map (fun k => PubVal.val
      ((ZkFormal.Udr.pubOf Fp (preparedBytes p witnessOverhead)).getD (SizeV3.PH_WOVH+k) 0))) =
      witnessOverhead := by
  apply read4_u32 _ _ ho
  intro k hk
  rw [pub_getD,prepared_header p witnessOverhead hr (by unfold SizeV3.PH_WOVH; omega),
    header_witness_overhead p witnessOverhead hr k]

end ZkFormal.NearV3.Public
