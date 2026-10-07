import ZkFormal.NearV3.Qv.Reads

/-! Queue parser sizes follow from their actual encodings. No separate queue
size restriction is introduced into the accepted relation. -/
namespace ZkFormal.NearV3.Qv
open NearSpec NearSpecV3

@[simp] theorem bufferEntryBytes_length (e : BufferEntry) :
    (bufferEntryBytes e).length = 24 := by
  simp [bufferEntryBytes,u64,leN]

theorem bufferEntries_length (es : List BufferEntry) :
    (concatAll (es.map bufferEntryBytes)).length = 24 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [concatAll,ih,Nat.mul_add,Nat.add_comm]

@[simp] theorem bufferedBytes_length (es : List BufferEntry) :
    (bufferedBytes es).length = 4 + 24 * es.length := by
  simp [bufferedBytes,encList,bufferEntries_length,u32,leN]; omega

theorem bufferedValue_length {bs : Bytes} {shards : List Nat}
    (h : BufferedValue (some bs) shards) :
    bs.length = 4 + 24 * shards.length := by
  obtain ⟨es,rfl,_,_,_,rfl⟩ := h
  simp

theorem bufferedValue_count_bound {bs : Bytes} {shards : List Nat} {budget : Nat}
    (h : BufferedValue (some bs) shards) (hb : bs.length ≤ budget) :
    4 + 24 * shards.length ≤ budget := by
  rwa [bufferedValue_length h] at hb

/-- A byte budget below 2^24 makes the u32 vector count a three-byte number.
The premise is explicit, to be discharged from the authenticated value budget. -/
theorem bufferedValue_count_u24 {bs : Bytes} {shards : List Nat}
    (h : BufferedValue (some bs) shards) (hb : bs.length < 256^3) :
    shards.length < 256^3 := by
  have := bufferedValue_length h
  omega

end ZkFormal.NearV3.Qv
