import ZkFormal.NearV3.Public.Layout

/-! Exact public bus records of the packed statement, including generated indices. -/
namespace ZkFormal.NearV3.Public
open ZkFormal.V2 ZkFormal.Algebra

def recordValues (plan : PubSeg) (j : Nat) (row : ByteString) : List Fp :=
  plan.msgPrefix.map (fun n => @Nat.cast Fp Lean.Grind.Semiring.natCast n) ++
    (match plan.indexBase with | none => [] | some off => [@Nat.cast Fp Lean.Grind.Semiring.natCast (off+j)]) ++
    row.map byteF

theorem descriptor_record (plan : PubSeg) (header : ByteString) (blocks : List Payload)
    {i j : Nat} (hi : i < blocks.length) (hj : j < (blocks.getD i []).length)
    (hw : ∀ row ∈ blocks.getD i [], row.length = plan.width)
    (ho : payloadOffset (dataStart header blocks) blocks i < 256^4) :
    (descriptor plan header.length i).record (ZkFormal.Udr.pubOf Fp (encode header blocks)) j =
      recordValues plan j ((blocks.getD i []).getD j []) := by
  have hr : ((blocks.getD i []).getD j []).length = plan.width := by
    apply hw
    rw [← List.getElem_eq_getD (h := hj) []]
    exact List.getElem_mem hj
  simp only [PubSeg.record,recordValues]
  change _ ++ _ ++ (List.range plan.width).map _ = _ ++ _ ++ _
  congr 1
  apply List.ext_getElem (by simpa only [List.length_map,List.length_range] using hr.symm)
  intro c hc hc'
  have hc0 : c < plan.width := by simpa using hc
  simp only [List.getElem_map,List.getElem_range]
  change (ZkFormal.Udr.pubOf Fp (encode header blocks)).getD
    ((descriptor plan header.length i).startOffset (ZkFormal.Udr.pubOf Fp (encode header blocks)) + j*plan.width+c) 0 = _
  rw [descriptor_offset plan header blocks hi ho,pub_getD]
  rw [Nat.add_assoc,encode_payload header blocks hi (by
    rw [payload_length _ _ hw]
    have := Nat.mul_le_mul_right plan.width (show j+1 ≤ (blocks.getD i []).length by omega)
    simp only [Nat.add_mul,Nat.one_mul] at this
    omega),payload_getD _ _ hw hj hc0]
  rw [← List.getElem_eq_getD (h := (show c < ((blocks.getD i []).getD j []).length by omega)) 0]

theorem descriptor_msgs (plan : PubSeg) (header : ByteString) (blocks : List Payload)
    {i : Nat} (hi : i < blocks.length)
    (hn : (blocks.getD i []).length < 256^4)
    (hw : ∀ row ∈ blocks.getD i [], row.length = plan.width)
    (ho : payloadOffset (dataStart header blocks) blocks i < 256^4) :
    (descriptor plan header.length i).msgs (ZkFormal.Udr.pubOf Fp (encode header blocks)) =
      (List.range (blocks.getD i []).length).map
        (fun j => recordValues plan j ((blocks.getD i []).getD j [])) := by
  unfold PubSeg.msgs
  rw [descriptor_count plan header blocks hi hn]
  apply List.map_congr_left
  intro j hj
  exact descriptor_record plan header blocks hi (List.mem_range.mp hj) hw ho

end ZkFormal.NearV3.Public
