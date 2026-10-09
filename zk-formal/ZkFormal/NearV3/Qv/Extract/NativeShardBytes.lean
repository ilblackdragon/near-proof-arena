import ZkFormal.NearV3.Qv.Bounds

namespace ZkFormal.NearV3.Qv
open NearSpec NearSpecV3 ReexecV3D0

private theorem prefix_getD (a b : Bytes) (i : Nat) (hi : i<a.length) :
    (a++b).getD i 0=a.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

private theorem suffix_getD (a b : Bytes) (i : Nat) :
    (a++b).getD (a.length+i) 0=b.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (show a.length≤a.length+i by omega),
    Nat.add_sub_cancel_left]

/-- Native entry serialization exposes each shard's eight bytes at offset 24*j. -/
theorem bufferEntries_shard_byte (es : List BufferEntry) (j : Nat) (hj : j<es.length)
    (i : Nat) (hi : i<8) :
    (concatAll (es.map bufferEntryBytes)).getD (24*j+i) 0=(u64 es[j].1).getD i 0 := by
  induction es generalizing j with
  | nil => simp at hj
  | cons e es ih =>
    cases j with
    | zero =>
      simp only [List.map_cons,concatAll,List.getElem_cons_zero,Nat.mul_zero,Nat.zero_add]
      rw [prefix_getD (bufferEntryBytes e) _ i (by rw [bufferEntryBytes_length]; omega)]
      simp only [bufferEntryBytes,List.append_assoc]
      apply prefix_getD
      simpa [u64,leN] using hi
    | succ j =>
      simp only [List.map_cons,concatAll,List.getElem_cons_succ]
      have hpos : 24*(j+1)+i=(bufferEntryBytes e).length+(24*j+i) := by
        rw [bufferEntryBytes_length]; omega
      rw [hpos,suffix_getD]
      exact ih j (by simp only [List.length_cons] at hj; omega)

/-- The native buffered predicate fixes every shard byte in serialized vector order. -/
theorem bufferedValue_shard_byte {bs : Bytes} {shards : List Nat}
    (h : BufferedValue (some bs) shards) (j : Nat) (hj : j<shards.length)
    (i : Nat) (hi : i<8) :
    bs.getD (4+24*j+i) 0=(u64 shards[j]).getD i 0 := by
  obtain ⟨es,rfl,_,_,_,rfl⟩ := h
  have hj' : j<es.length := by simpa only [List.length_map] using hj
  simp only [List.getElem_map]
  have hlen : (u32 es.length).length=4 := by simp [u32,leN]
  change (u32 es.length++concatAll (es.map bufferEntryBytes)).getD (4+24*j+i) 0=_
  have hp : 4+24*j+i=(u32 es.length).length+(24*j+i) := by omega
  rw [hp,suffix_getD]
  exact bufferEntries_shard_byte es j hj' i hi

end ZkFormal.NearV3.Qv
