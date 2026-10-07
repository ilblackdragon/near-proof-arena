import ZkFormal.NearV3.Public.Layout

/-! Packed segments stay within the actual statement, including empty payloads. -/
namespace ZkFormal.NearV3.Public
open ZkFormal.V2 ZkFormal.Algebra

theorem data_block_bound (blocks : List Payload) {i : Nat} (hi : i < blocks.length) :
    (dataBytes (blocks.take i)).length + (payloadBytes (blocks.getD i [])).length ≤
      (dataBytes blocks).length := by
  induction blocks generalizing i with
  | nil => simp at hi
  | cons rs rest ih =>
    cases i with
    | zero => simp [dataBytes]
    | succ i =>
      have h := ih (show i < rest.length by simpa using hi)
      simpa only [List.take_succ_cons,dataBytes,List.flatMap_cons,List.length_append,
        List.getD_cons_succ,Nat.add_assoc] using Nat.add_le_add_left h (payloadBytes rs).length

theorem encode_length (header : ByteString) (blocks : List Payload) :
    (encode header blocks).length = dataStart header blocks + (dataBytes blocks).length := by
  simp [encode,dataStart,metadata_length,Nat.add_assoc]

theorem descriptor_fits (plan : PubSeg) (header : ByteString) (blocks : List Payload)
    {i maxPub : Nat} (hi : i < blocks.length)
    (hn : (blocks.getD i []).length < 256^4)
    (hw : ∀ row ∈ blocks.getD i [], row.length = plan.width)
    (ho : payloadOffset (dataStart header blocks) blocks i < 256^4)
    (hm : (encode header blocks).length ≤ maxPub) :
    (descriptor plan header.length i).fits maxPub
      (ZkFormal.Udr.pubOf Fp (encode header blocks)) = true := by
  have hb := data_block_bound blocks hi
  rw [payload_length _ _ hw] at hb
  have he := encode_length header blocks
  unfold PubSeg.fits
  rw [descriptor_offset plan header blocks hi ho,descriptor_count plan header blocks hi hn]
  simp only [descriptor,ZkFormal.Udr.pubOf,List.length_map,Bool.and_eq_true,decide_eq_true_eq]
  simp only [payloadOffset] at *
  constructor
  · omega
  · exact decide_eq_true (by omega)

end ZkFormal.NearV3.Public
