import ZkFormal.NearV3.Render.Node.Facts

/-! Header bounds derived from the existing total-row budget. No key-length premise. -/
namespace ZkFormal.NearV3.Render.NodeGen3
open ZkFormal.Near NearSpec

private theorem mem_sum_le (xs : List Nat) (n : Nat) (hn : n ∈ xs) : n ≤ xs.sum := by
  induction xs with
  | nil => simp at hn
  | cons x xs ih =>
    simp only [List.mem_cons] at hn
    simp only [List.sum_cons]
    rcases hn with rfl | hn
    · omega
    · have := ih hn; omega

theorem hplen_le_ser (v : NodeV3) : hplenOf v ≤ (v.ser false).length := by
  cases v <;> simp [hplenOf, isLE, keyOf, NodeV3.ser, hpN_len] <;> omega

/-- Existing row cap alone implies the HPL fits in three bytes. -/
theorem hplen_lt24 {vs : List NodeS3} (ok : NodeOk vs) {n : Nat} (hn : n < vs.length) :
    hplenOf (rec vs n).v < 16777216 := by
  have hs := mem_sum_le (vs.map fun s => (s.v.ser false).length)
    ((rec vs n).v.ser false).length (List.mem_map.mpr ⟨rec vs n, rec_mem hn, rfl⟩)
  have hh := hplen_le_ser (rec vs n).v
  have hr := ok.rows
  omega


end ZkFormal.NearV3.Render.NodeGen3
