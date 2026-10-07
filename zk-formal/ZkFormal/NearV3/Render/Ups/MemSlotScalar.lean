import ZkFormal.NearV3.Render.Ups.MemNative

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec

theorem slot_memory_scalar (Q : UpsPartI) (frontBytes rest : List Nat) (n : Nat)
    (hb : Q.pb=frontBytes++(u32 n).map UInt8.toNat++rest)
    (ho : Q.soff=frontBytes.length) (hn : n<256^4) : pfx (slb Q) 8=(n:Int) := by
  have hf : slb Q=(fun i => if i<4 then (((u32 n).map UInt8.toNat).getD i 0:Int) else 0) := by
    funext i
    simp only [slb,ho]
    split
    · rw [hb,List.append_assoc,List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      rw [List.getElem?_append_left (by simpa using ‹i<4›)]
      rfl
    · rfl
  rw [hf]
  simp [pfx,UpsRows.toNats_u32,List.getD]
  omega
end ZkFormal.NearV3.Render.UpsGen
