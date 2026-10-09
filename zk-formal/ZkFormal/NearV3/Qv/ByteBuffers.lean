import ZkFormal.NearV3.Qv.Bounds

/-! Byte-level buffered queue witnesses avoid embedding u64 shard/index values
in the proof field. Equal index byte strings express queue emptiness exactly. -/
namespace ZkFormal.NearV3.Qv
open NearSpec NearSpecV3

structure ByteBuffer where
  shard : Bytes
  index : Bytes

def ByteBuffer.Sized (e : ByteBuffer) : Prop := e.shard.length=8 ∧ e.index.length=8
def ByteBuffer.entry (e : ByteBuffer) : BufferEntry :=
  (leNat e.shard,leNat e.index,leNat e.index)
def ByteBuffer.bytes (e : ByteBuffer) : Bytes := e.shard ++ e.index ++ e.index

theorem ByteBuffer.entry_sized (e : ByteBuffer) (h : e.Sized) : BufferEntrySized e.entry := by
  have hs := ZkFormal.Near.Sound.leNat_lt e.shard
  have hi := ZkFormal.Near.Sound.leNat_lt e.index
  rw [h.1] at hs
  rw [h.2] at hi
  exact ⟨hs,hi,hi⟩

theorem ByteBuffer.entry_bytes (e : ByteBuffer) (h : e.Sized) :
    bufferEntryBytes e.entry = e.bytes := by
  have hs := ZkFormal.Near.Sound.leN_leNat e.shard
  have hi := ZkFormal.Near.Sound.leN_leNat e.index
  rw [h.1] at hs
  rw [h.2] at hi
  simp only [bufferEntryBytes,ByteBuffer.entry,ByteBuffer.bytes,u64,hs,hi]

def byteBufferedBytes (es : List ByteBuffer) : Bytes := encList ByteBuffer.bytes es

theorem byteBufferedBytes_eq (es : List ByteBuffer) (h : ∀ e ∈ es, e.Sized) :
    bufferedBytes (es.map ByteBuffer.entry) = byteBufferedBytes es := by
  unfold bufferedBytes byteBufferedBytes encList
  simp only [List.length_map,List.map_map]
  congr 2
  apply List.map_congr_left
  intro e he
  exact e.entry_bytes (h e he)

theorem byteBuffered_accept (es : List ByteBuffer) (hn : es.length < 256^4)
    (h : ∀ e ∈ es, e.Sized) :
    bufferedShards (some (byteBufferedBytes es)) = .ok (es.map (fun e => leNat e.shard)) := by
  rw [← byteBufferedBytes_eq es h]
  have ha := bufferedShards_encode (es.map ByteBuffer.entry) (by simpa using hn)
    (by intro e he; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp he; exact b.entry_sized (h b hb))
    (by intro e he; obtain ⟨b,_,rfl⟩ := List.mem_map.mp he; rfl)
  simpa [List.map_map,Function.comp_def,ByteBuffer.entry] using ha

def byteBufferOfEntry (e : BufferEntry) : ByteBuffer := ⟨u64 e.1,u64 e.2.1⟩

theorem byteBufferOfEntry_sized (e : BufferEntry) : (byteBufferOfEntry e).Sized := by
  simp [byteBufferOfEntry,ByteBuffer.Sized,u64,leN]

theorem byteBufferOfEntry_bytes (e : BufferEntry) (he : e.2.1=e.2.2) :
    (byteBufferOfEntry e).bytes = bufferEntryBytes e := by
  simp only [byteBufferOfEntry,ByteBuffer.bytes,bufferEntryBytes,he]

theorem byteBuffered_complete {bs : Bytes} {shards : List Nat}
    (h : bufferedShards (some bs) = .ok shards) :
    ∃ es : List ByteBuffer, bs = byteBufferedBytes es ∧ es.length < 256^4 ∧
      (∀ e ∈ es, e.Sized) ∧ shards = es.map (fun e => leNat e.shard) := by
  obtain ⟨es,rfl,hn,hs,he,rfl⟩ := bufferedShards_inv h
  refine ⟨es.map byteBufferOfEntry,?_,by simpa using hn,?_,?_⟩
  · unfold bufferedBytes byteBufferedBytes encList
    simp only [List.length_map,List.map_map]
    congr 2
    apply List.map_congr_left
    intro e hm
    exact (byteBufferOfEntry_bytes e (he e hm)).symm
  · intro e hm
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp hm
    exact byteBufferOfEntry_sized e
  · simp only [List.map_map]
    apply List.map_congr_left
    intro e hm
    simp only [Function.comp_def,byteBufferOfEntry,u64]
    exact (leNat_leN 8 e.1 (hs e hm).1).symm

 theorem byteBuffered_iff (bs : Bytes) (shards : List Nat) :
    bufferedShards (some bs) = .ok shards ↔
    ∃ es : List ByteBuffer, bs = byteBufferedBytes es ∧ es.length < 256^4 ∧
      (∀ e ∈ es, e.Sized) ∧ shards = es.map (fun e => leNat e.shard) := by
  constructor
  · exact byteBuffered_complete
  · rintro ⟨es,rfl,hn,hs,rfl⟩
    exact byteBuffered_accept es hn hs

end ZkFormal.NearV3.Qv
