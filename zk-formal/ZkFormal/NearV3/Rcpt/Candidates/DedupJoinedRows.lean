import ZkFormal.NearV3.Rcpt.Candidates.DedupCellEnv

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

/-- Logical cells omit the duplicated left carry row and clone the final inactive
right row once. The resulting logical height is exactly2H. -/
def joinedCells (H : Nat) (L R : Nat → Nat → Fp) (r : Nat) : Nat → Fp :=
  if r < H-1 then L r else R (min (r-(H-1)) (H-1))

theorem joined_left (H : Nat) (L R : Nat → Nat → Fp) {r : Nat} (hr : r<H-1) :
    joinedCells H L R r = L r := by simp [joinedCells, hr]

theorem joined_right {H : Nat} (hH : 1≤H) (L R : Nat → Nat → Fp)
    {r : Nat} (hr : r<H) : joinedCells H L R (H-1+r) = R r := by
  have hn : ¬H-1+r<H-1 := by omega
  have he : H-1+r-(H-1)=r := by omega
  have hm : min r (H-1)=r := Nat.min_eq_left (by omega)
  simp [joinedCells, hn, he, hm]

theorem joined_clone {H : Nat} (hH : 1≤H) (L R : Nat → Nat → Fp) :
    joinedCells H L R (2*H-1) = R (H-1) := by
  have hn : ¬2*H-1<H-1 := by omega
  have hm : min (2*H-1-(H-1)) (H-1)=H-1 := Nat.min_eq_right (by omega)
  simp [joinedCells, hn, hm]

/-- The overlap equality affects only columns read by the source constraints;
no unauthenticated cells outside the57-field carry tuple are assumed equal. -/
theorem joined_left_successor {H r : Nat} (hH : 2≤H) (hr : r<H-1)
    (L R : Nat → Nat → Fp) (hc : ∀ x, x<57 → L (H-1) x=R 0 x) :
    ∀ x, x<57 → joinedCells H L R (r+1) x=L (r+1) x := by
  intro x hx
  by_cases hn : r+1<H-1
  · rw [joined_left H L R hn]
  · have he : r+1=H-1 := by omega
    rw [he, ← Nat.add_zero (H-1), joined_right (by omega) L R (by omega)]
    exact (hc x hx).symm

end ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
