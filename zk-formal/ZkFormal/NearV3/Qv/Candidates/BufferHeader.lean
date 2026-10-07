import ZkFormal.NearV3.Qv.Candidates.BufferTrace
import ZkFormal.NearV3.Spec.U32Bytes

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Near

theorem le256_four (xs : List Nat) (hx : xs.length=4) :
    le256 xs = xs.getD 0 0 + 256*xs.getD 1 0 +
      65536*xs.getD 2 0 + 16777216*xs.getD 3 0 := by
  rw [List.eq_getElem_of_length_eq_four xs hx]
  simp [le256,Nat.mul_add,Nat.add_assoc,←Nat.mul_assoc]

theorem buffer_count_value (n : Nat) (hn : n<16777216) :
    n = ((u32 n).getD 0 0).toNat + 256*((u32 n).getD 1 0).toNat +
      65536*((u32 n).getD 2 0).toNat + 16777216*((u32 n).getD 3 0).toNat := by
  have hv := u32Bytes_value (n:=n) (by omega)
  rw [le256_four _ (u32Bytes_length n)] at hv
  simpa [u32Bytes] using hv.symm

theorem buffer_count_top_zero (n : Nat) (hn : n<16777216) :
    ((u32 n).getD 3 0).toNat = 0 := by
  simpa [u32Bytes] using u32Bytes_top_zero hn

end ZkFormal.NearV3.Qv.Candidates.ValueGen
