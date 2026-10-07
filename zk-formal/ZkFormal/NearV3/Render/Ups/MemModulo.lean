import ZkFormal.NearV3.Render.Ups.MemArith

namespace ZkFormal.NearV3.Render.UpsGen
/-- Every serialized u64 digit depends only on the low64 bits of the exact scalar. -/
theorem low64_digit (x : Int) {i : Nat} (hi : i<8) :
    x/256^i%256=(x%256^8)/256^i%256 := by
  rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 by omega)
    with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [Int.reducePow] <;> omega
end ZkFormal.NearV3.Render.UpsGen
