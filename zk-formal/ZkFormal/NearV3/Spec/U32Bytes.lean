import ZkFormal.NearV3.Spec.Codec
import ZkFormal.Near.Extract.Segments

/-! Full four-byte little-endian lengths for v3 trie serialization. -/
namespace ZkFormal.NearV3
open NearSpec ZkFormal.Near

/-- Natural-number view of the protocol's four-byte length encoding. -/
def u32Bytes (n : Nat) : List Nat := (u32 n).map UInt8.toNat

@[simp] theorem u32Bytes_length (n : Nat) : (u32Bytes n).length = 4 := by
  simp [u32Bytes]

theorem u32Bytes_lt (n x : Nat) (hx : x ∈ u32Bytes n) : x < 256 := by
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
  exact b.toNat_lt

@[simp] theorem u32Bytes_toBytes (n : Nat) :
    (u32Bytes n).map UInt8.ofNat = u32 n := by
  simp [u32Bytes, List.map_map, Function.comp_def]

theorem le256_bytes (bs : Bytes) : le256 (bs.map UInt8.toNat) = leNat bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [le256, leNat, ih]

theorem u32Bytes_value {n : Nat} (hn : n < 4294967296) :
    le256 (u32Bytes n) = n := by
  exact (le256_bytes _).trans (leNat_u32 hn)

theorem leN_le256 (xs : List Nat) (hx : ∀ x ∈ xs, x < 256) :
    (leN xs.length (le256 xs)).map UInt8.toNat = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have h : x < 256 := hx x (by simp)
    have ht : ∀ y ∈ xs, y < 256 := fun y hy => hx y (by simp [hy])
    have hm : (x + 256 * le256 xs) % 256 = x := by omega
    have hd : (x + 256 * le256 xs) / 256 = le256 xs := by omega
    simp only [List.length_cons, le256, leN, hm, hd, List.map_cons]
    rw [toNat_ofNat_lt h, ih ht]

/-- Four byte-range-checked digits are uniquely determined by their integer value. -/
theorem u32Bytes_of_digits (xs : List Nat) (hl : xs.length = 4)
    (hx : ∀ x ∈ xs, x < 256) : u32Bytes (le256 xs) = xs := by
  simpa only [u32Bytes, u32, hl] using leN_le256 xs hx

theorem u32Bytes_small {n : Nat} (hn : n < 256) :
    u32Bytes n = u32r n := by
  have hd : n / 256 = 0 := Nat.div_eq_of_lt hn
  simp [u32Bytes, u32, leN, hd, Nat.mod_eq_of_lt hn, u32r,
    toNat_ofNat_lt hn]

end ZkFormal.NearV3
