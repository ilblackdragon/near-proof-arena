import ZkFormal.NearV3.Public.Records
import ZkFormal.NearV3.Rcpt.Ids

/-! Public refund-body records: the first eight bytes are handled by the body codec. -/
namespace ZkFormal.NearV3.Public
open ZkFormal.V2 ZkFormal.Algebra

def bodyPayload (body : ByteString) : Payload := (body.drop 8).map (fun b => [b])

def bodyPlan : PubSeg :=
  { bus := 0, send := false, width := 1, countAt := 0, start := 0,
    msgPrefix := [2], indexBase := some 8 }

theorem bodyPayload_length (body : ByteString) :
    (bodyPayload body).length = body.length - 8 := by simp [bodyPayload]

theorem bodyPayload_width (body : ByteString) :
    ∀ row ∈ bodyPayload body, row.length = bodyPlan.width := by
  intro row hr
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hr
  rfl

theorem bodyPayload_record (body : ByteString) {j : Nat} (hj : j < body.length-8) :
    recordValues bodyPlan j ((bodyPayload body).getD j []) =
      [Fp.ofNat 2, Fp.ofNat (8+j), byteF (body.getD (8+j) 0)] := by
  have hdrop : j < (body.drop 8).length := by simpa using hj
  have hmap : j < (bodyPayload body).length := by simpa [bodyPayload] using hdrop
  rw [← List.getElem_eq_getD (h := hmap) []]
  simp only [bodyPayload,List.getElem_map,List.getElem_drop]
  rw [← List.getElem_eq_getD (h := (show 8+j < body.length by omega)) 0]
  rfl

theorem descriptor_body_record (header : ByteString) (blocks : List Payload) (body : ByteString)
    {i j : Nat} (hi : i < blocks.length) (hb : blocks.getD i [] = bodyPayload body)
    (hj : j < body.length-8)
    (ho : payloadOffset (dataStart header blocks) blocks i < 256^4) :
    (descriptor bodyPlan header.length i).record (ZkFormal.Udr.pubOf Fp (encode header blocks)) j =
      [Fp.ofNat 2, Fp.ofNat (8+j), byteF (body.getD (8+j) 0)] := by
  rw [descriptor_record bodyPlan header blocks hi
    (by rw [hb,bodyPayload_length]; exact hj)
    (by rw [hb]; exact bodyPayload_width body) ho,hb]
  exact bodyPayload_record body hj

end ZkFormal.NearV3.Public
