import ZkFormal.NearV3.Qv.Candidates.ValueGen

/-! Exact natural byte messages of generated parser rows. This is an honest
traffic component; complete field-row and bus-count theorems remain separate. -/
namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec

def byteMessages (rows : List (List Nat)) : List (List Nat) :=
  (rows.filter (fun r => r.getD ValueTable.gb 0 = 1)).map
    (fun r => [r.getD ValueTable.vid 0,r.getD ValueTable.pos 0,r.getD ValueTable.byte 0])

def numberedBytes (vid offset : Nat) (bytes : Bytes) : List (List Nat) :=
  bytes.zipIdx.map fun (b,i) => [vid,offset+i,b.toNat]

theorem byteMessages_append (a b : List (List Nat)) :
    byteMessages (a++b) = byteMessages a ++ byteMessages b := by
  simp [byteMessages]

theorem wordRows_bytes (cfg : Config) (offset phase entry : Nat) (bytes regs : Bytes)
    (hn : cfg.length ≠ 0) :
    byteMessages (wordRows cfg offset phase entry bytes regs) = numberedBytes cfg.vid offset bytes := by
  simp [byteMessages,wordRows,numberedBytes,row,hn,ValueTable.gb,ValueTable.vid,
    ValueTable.pos,ValueTable.byte,List.filter_map,List.map_map,Function.comp_def]
  all_goals rw [List.filter_eq_self.mpr (by intros; rfl)]

theorem rawRows_bytes (vid tau users : Nat) (bytes : Bytes) :
    byteMessages (rawRows vid tau users bytes) = numberedBytes vid 0 bytes := by
  cases bytes with
  | nil => simp [rawRows,byteMessages,row,numberedBytes,ValueTable.gb]
  | cons b bs =>
    simp [rawRows,byteMessages,row,numberedBytes,ValueTable.gb,ValueTable.vid,
      ValueTable.pos,ValueTable.byte,List.filter_map,List.map_map,Function.comp_def]
    all_goals rw [List.filter_eq_self.mpr (by intros; rfl)]

theorem numberedBytes_shift (vid offset start : Nat) (bytes : Bytes) :
    (bytes.zipIdx start).map (fun (b,i) => [vid,offset+i,b.toNat]) =
      numberedBytes vid (offset+start) bytes := by
  rw [show start = start+0 by omega,← List.map_snd_add_zipIdx_eq_zipIdx]
  simp only [List.map_map,Function.comp_def,Prod.map,numberedBytes]
  apply List.map_congr_left
  intro x _
  simp only [id_eq]
  congr 2 <;> omega

theorem numberedBytes_append (vid offset : Nat) (a b : Bytes) :
    numberedBytes vid offset (a++b) =
      numberedBytes vid offset a ++ numberedBytes vid (offset+a.length) b := by
  unfold numberedBytes
  rw [List.zipIdx_append,List.map_append]
  congr 1
  simpa only [Nat.zero_add,numberedBytes] using numberedBytes_shift vid offset a.length b

theorem emptyRows_bytes (vid tau users : Nat) (index : Bytes) (hi : index.length=8) :
    byteMessages (emptyRows vid tau users index) = numberedBytes vid 0 (index++index) := by
  unfold emptyRows
  rw [byteMessages_append,wordRows_bytes _ _ _ _ _ _ (by change 16 ≠ 0; decide),
    wordRows_bytes _ _ _ _ _ _ (by change 16 ≠ 0; decide),numberedBytes_append]
  simp only [hi,Nat.zero_add]

theorem entryRows_bytes (cfg : Config) (e : ByteBuffer) (i : Nat)
    (hn : cfg.length ≠ 0) (he : e.Sized) :
    byteMessages (wordRows cfg (4+24*i) 1 i e.shard e.index ++
      wordRows cfg (12+24*i) 2 i e.index e.index ++
      wordRows cfg (20+24*i) 3 i e.index e.index) =
      numberedBytes cfg.vid (4+24*i) e.bytes := by
  simp only [byteMessages_append,wordRows_bytes _ _ _ _ _ _ hn,
    ByteBuffer.bytes,numberedBytes_append,List.length_append,he.1,he.2]
  rw [show 12+24*i = 4+24*i+8 by omega,
    show 20+24*i = 4+24*i+(8+8) by omega]

theorem bufferEntryRows_bytes (cfg : Config) (es : List ByteBuffer)
    (hn : cfg.length ≠ 0) (hs : ∀ e ∈ es, e.Sized) (start : Nat) :
    byteMessages ((es.zipIdx start).flatMap (fun (e,i) =>
      wordRows cfg (4+24*i) 1 i e.shard e.index ++
      wordRows cfg (12+24*i) 2 i e.index e.index ++
      wordRows cfg (20+24*i) 3 i e.index e.index)) =
      numberedBytes cfg.vid (4+24*start) (concatAll (es.map ByteBuffer.bytes)) := by
  induction es generalizing start with
  | nil => simp [byteMessages,numberedBytes,concatAll]
  | cons e es ih =>
    have he := hs e (by simp)
    have ht : ∀ e ∈ es, e.Sized := fun e hm => hs e (by simp [hm])
    simp only [List.zipIdx_cons,List.flatMap_cons,List.map_cons,concatAll,
      byteMessages_append,entryRows_bytes cfg e start hn he,numberedBytes_append]
    rw [ih ht]
    have hl : e.bytes.length=24 := by simp [ByteBuffer.bytes,he.1,he.2]
    rw [hl]
    congr 2 <;> omega

theorem bufferRows_bytes (vid tau users : Nat) (es : List ByteBuffer)
    (hs : ∀ e ∈ es, e.Sized) :
    byteMessages (bufferRows vid tau users es) = numberedBytes vid 0 (byteBufferedBytes es) := by
  unfold bufferRows
  rw [byteMessages_append,wordRows_bytes _ _ _ _ _ _ (by dsimp; omega),
    bufferEntryRows_bytes _ es (by dsimp; omega) hs]
  unfold byteBufferedBytes NearSpecV3.encList
  rw [numberedBytes_append]
  simp [u32,leN]

end ZkFormal.NearV3.Qv.Candidates.ValueGen
