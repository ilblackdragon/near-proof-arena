import ZkFormal.NearV3.Qv.Extract.RepairedKeyTraffic

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Native nibble indexing preserves byte order exactly. -/
theorem native_nibble_high (bs : NearSpec.Bytes) (i : Nat) :
    (NearSpec.nibbles bs).getD (2*i) 0=(bs.getD i 0).toNat/16 := by
  induction bs generalizing i with
  | nil => simp [NearSpec.nibbles]
  | cons b bs ih =>
    cases i with
    | zero => simp [NearSpec.nibbles]
    | succ i =>
      have he : 2*(i+1)=2*i+2 := by omega
      simpa [NearSpec.nibbles,he,List.getD_cons_succ] using ih i

theorem native_nibble_low (bs : NearSpec.Bytes) (i : Nat) :
    (NearSpec.nibbles bs).getD (2*i+1) 0=(bs.getD i 0).toNat%16 := by
  induction bs generalizing i with
  | nil => simp [NearSpec.nibbles]
  | cons b bs ih =>
    cases i with
    | zero => simp [NearSpec.nibbles]
    | succ i =>
      have he : 2*(i+1)+1=(2*i+1)+2 := by omega
      simpa [NearSpec.nibbles,he,List.getD_cons_succ] using ih i

theorem native_nibbles_length (bs : NearSpec.Bytes) :
    (NearSpec.nibbles bs).length=2*bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [NearSpec.nibbles,List.length_cons,ih]; omega

theorem native_nibble_bound (bs : NearSpec.Bytes) (j : Nat) :
    (NearSpec.nibbles bs).getD j 0<16 := by
  induction bs generalizing j with
  | nil => simp [NearSpec.nibbles]
  | cons b bs ih =>
    have hb := UInt8.toNat_lt b
    cases j with
    | zero => simp [NearSpec.nibbles]; omega
    | succ j =>
      cases j with
      | zero => simp [NearSpec.nibbles]; omega
      | succ j => simpa [NearSpec.nibbles,List.getD_cons_succ] using ih j

end ZkFormal.NearV3.Qv.Extract
