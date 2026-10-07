import ZkFormal.NearV3.Qv.Candidates.BufferTrace

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec

theorem bufferRowAt_entry (vid tau users : Nat) (es : List ByteBuffer)
    (i j : Nat) (hi : i<es.length) (hj : j<24) :
    bufferRowAt vid tau users es (4+24*i+j) =
      let e := es.getD i ⟨[],[]⟩
      row ⟨vid,tau,users,1,4+24*es.length,es.length⟩ (4+24*i+j)
        ((if j<8 then e.shard.getD j 0 else e.index.getD (j%8) 0).toNat)
        (if j<8 then 1 else if j<16 then 2 else 3) (j%8) i e.index := by
  have h4 : ¬4+24*i+j<4 := by omega
  have hl : 4+24*i+j<4+24*es.length := by omega
  have hd : (4+24*i+j-4)/24=i := by omega
  have hm : (4+24*i+j-4)%24=j := by omega
  simp [bufferRowAt,h4,hl,hd,hm]

theorem bufferRowAt_zero (vid tau users : Nat) (es : List ByteBuffer) :
    bufferRowAt vid tau users es 0 =
      row ⟨vid,tau,users,1,4+24*es.length,es.length⟩ 0
        ((u32 es.length).getD 0 0).toNat 0 0 0 (u32 es.length) := by
  simp [bufferRowAt]

theorem bufferRowAt_after_entry (vid tau users : Nat) (es : List ByteBuffer)
    (i : Nat) (hi : i<es.length) :
    bufferRowAt vid tau users es (4+24*i+23+1) =
      if i+1=es.length then [] else
        let e := es.getD (i+1) ⟨[],[]⟩
        row ⟨vid,tau,users,1,4+24*es.length,es.length⟩ (4+24*i+23+1)
          (e.shard.getD 0 0).toNat 1 0 (i+1) e.index := by
  by_cases he : i+1=es.length
  · have h4 : ¬4+24*i+23+1<4 := by omega
    have hl : ¬4+24*i+23+1<4+24*es.length := by omega
    simp [bufferRowAt,h4,hl,he]
  · have hn : i+1<es.length := by omega
    simpa [he,Nat.mul_add,Nat.mul_one,Nat.add_assoc] using
      bufferRowAt_entry vid tau users es (i+1) 0 hn (by decide)

end ZkFormal.NearV3.Qv.Candidates.ValueGen
