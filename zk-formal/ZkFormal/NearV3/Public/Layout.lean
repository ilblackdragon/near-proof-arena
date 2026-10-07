import ZkFormal.NearV3.Public.Payload

/-! Bind segment count, start and payload bytes to the packed statement encoder. -/
namespace ZkFormal.NearV3.Public
open ZkFormal.V2 ZkFormal.Algebra

/-- A static segment descriptor reads its count and offset from its metadata slot. -/
def descriptor (plan : PubSeg) (headerLength i : Nat) : PubSeg :=
  { plan with countAt := headerLength+8*i, start := 0, startAt := some (headerLength+8*i+4) }

def dataStart (header : ByteString) (blocks : List Payload) : Nat := header.length+8*blocks.length

theorem encode_count (header : ByteString) (blocks : List Payload) {i k : Nat}
    (hi : i < blocks.length) (hk : k < 4) :
    (encode header blocks).getD (header.length+8*i+k) 0 =
      (NearSpec.u32 (blocks.getD i []).length).getD k 0 := by
  unfold encode
  rw [Nat.add_assoc,getD_middle _ _ _ (by rw [metadata_length]; omega)]
  exact metadata_count _ _ hi hk

theorem encode_offset (header : ByteString) (blocks : List Payload) {i k : Nat}
    (hi : i < blocks.length) (hk : k < 4) :
    (encode header blocks).getD (header.length+8*i+4+k) 0 =
      (NearSpec.u32 (payloadOffset (dataStart header blocks) blocks i)).getD k 0 := by
  unfold encode
  rw [show header.length+8*i+4+k = header.length+(8*i+4+k) by omega,
    getD_middle _ _ _ (by rw [metadata_length]; omega)]
  exact metadata_offset _ _ hi hk

theorem encode_payload (header : ByteString) (blocks : List Payload) {i c : Nat}
    (hi : i < blocks.length) (hc : c < (payloadBytes (blocks.getD i [])).length) :
    (encode header blocks).getD (payloadOffset (dataStart header blocks) blocks i+c) 0 =
      (payloadBytes (blocks.getD i [])).getD c 0 := by
  unfold encode
  have he : payloadOffset (dataStart header blocks) blocks i+c =
      (header ++ metadata (header.length+8*blocks.length) blocks).length+
        ((dataBytes (blocks.take i)).length+c) := by
    simp [payloadOffset,dataStart,metadata_length,Nat.add_assoc]
  rw [he,getD_right]
  exact data_getD blocks hi hc

theorem descriptor_count (plan : PubSeg) (header : ByteString) (blocks : List Payload)
    {i : Nat} (hi : i < blocks.length) (hn : (blocks.getD i []).length < 256^4) :
    (descriptor plan header.length i).count (ZkFormal.Udr.pubOf Fp (encode header blocks)) =
      (blocks.getD i []).length := by
  apply count_of_u32 _ _ _ hn
  intro k hk
  rw [pub_getD]
  exact congrArg byteF (encode_count header blocks hi hk)

theorem descriptor_offset (plan : PubSeg) (header : ByteString) (blocks : List Payload)
    {i : Nat} (hi : i < blocks.length)
    (ho : payloadOffset (dataStart header blocks) blocks i < 256^4) :
    (descriptor plan header.length i).startOffset (ZkFormal.Udr.pubOf Fp (encode header blocks)) =
      payloadOffset (dataStart header blocks) blocks i := by
  apply offset_of_u32 _ _ _ _ rfl ho
  intro k hk
  rw [pub_getD]
  exact congrArg byteF (encode_offset header blocks hi hk)

end ZkFormal.NearV3.Public
