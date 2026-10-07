import ZkFormal.NearV3.Public.Fits

/-! All u32 count and offset bounds follow from the encoded statement bound
when payload widths are positive. -/
namespace ZkFormal.NearV3.Public
open ZkFormal.V2 ZkFormal.Algebra

theorem descriptor_u32_bounds (plan : PubSeg) (header : ByteString) (blocks : List Payload)
    {i : Nat} (hi : i < blocks.length) (hp : 0 < plan.width)
    (hw : ∀ row ∈ blocks.getD i [], row.length = plan.width)
    (hlen : (encode header blocks).length < 256^4) :
    (blocks.getD i []).length < 256^4 ∧
      payloadOffset (dataStart header blocks) blocks i < 256^4 := by
  have hb := data_block_bound blocks hi
  rw [payload_length _ _ hw] at hb
  have hm : (blocks.getD i []).length ≤ (blocks.getD i []).length * plan.width := by
    have := Nat.mul_le_mul_left (blocks.getD i []).length hp
    simpa using this
  rw [encode_length] at hlen
  unfold payloadOffset
  constructor <;> omega

theorem descriptor_fits_of_bound (plan : PubSeg) (header : ByteString) (blocks : List Payload)
    {i maxPub : Nat} (hi : i < blocks.length) (hp : 0 < plan.width)
    (hw : ∀ row ∈ blocks.getD i [], row.length = plan.width)
    (hm : (encode header blocks).length ≤ maxPub) (hmax : maxPub < 256^4) :
    (descriptor plan header.length i).fits maxPub
      (ZkFormal.Udr.pubOf Fp (encode header blocks)) = true := by
  obtain ⟨hn,ho⟩ := descriptor_u32_bounds plan header blocks hi hp hw (by omega)
  exact descriptor_fits plan header blocks hi hn hw ho hm

end ZkFormal.NearV3.Public
