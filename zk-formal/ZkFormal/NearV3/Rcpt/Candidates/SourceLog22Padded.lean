import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22Join

namespace ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra DedupPartitionTable

theorem four_terminal (s : Nat) (A B C D : Nat → Nat → Fp) :
    fourCells s A B C D (4*s)=D s := by
  change prefixCells s A (prefixCells s B (prefixCells s C D)) (4*s)=D s
  rw [show 4*s=s+(s+(s+s)) by omega,prefix_after,prefix_after,prefix_after]

def paddedCells (s : Nat) (A B C D : Nat → Nat → Fp) (r : Nat) : Nat → Fp :=
  fourCells s A B C D (min r (4*s))

theorem padded_before (s : Nat) (A B C D : Nat → Nat → Fp) {r : Nat} (hr : r≤4*s) :
    paddedCells s A B C D r=fourCells s A B C D r := by
  simp [paddedCells,Nat.min_eq_left hr]

theorem padded_after (s : Nat) (A B C D : Nat → Nat → Fp) {r : Nat} (hr : 4*s≤r) :
    paddedCells s A B C D r=D s := by
  rw [paddedCells,Nat.min_eq_right hr,four_terminal]

/-- Three inactive clones restore the power-of-two logical height after removing
the three duplicated overlap rows. Their equations follow from the actual
inactive endpoint, including the cyclic last-row transition. -/
theorem padded_constraints {H : Nat} (hH : 2≤H)
    (A B C D : Nat → Nat → Fp) (pub : Nat → Fp)
    (hsteps : ∀ r, r<4*(H-1) → SourceRow (fourCells (H-1) A B C D r)
      (fourCells (H-1) A B C D (r+1)) (if r=0 then 1 else 0) 0 1 pub)
    (hfinal : SourceRow (D (H-1)) (D 0) 0 1 0 pub)
    (hinactive : Inactive (D (H-1))) :
    ∀ r, r<4*H → SourceRow (paddedCells (H-1) A B C D r)
      (paddedCells (H-1) A B C D ((r+1)%(4*H))) (if r=0 then 1 else 0)
      (if r+1=4*H then 1 else 0) (if r+1=4*H then 0 else 1) pub := by
  intro r hr
  by_cases hpre : r<4*(H-1)
  · have hn : r+1≠4*H := by omega
    have hm : (r+1)%(4*H)=r+1 := Nat.mod_eq_of_lt (by omega)
    simp only [hn,ite_false,hm]
    rw [padded_before _ A B C D (by omega),padded_before _ A B C D (by omega)]
    exact hsteps r hpre
  · have hz : r≠0 := by omega
    rw [padded_after _ A B C D (by omega)]
    by_cases hlast : r+1=4*H
    · simp only [hz,hlast,ite_false,ite_true,Nat.mod_self]
      intro e he
      rw [inactive_terminal_retarget _ _ (D 0) hinactive 1 1 pub e he]
      exact hfinal e he
    · have hm : (r+1)%(4*H)=r+1 := Nat.mod_eq_of_lt (by omega)
      simp only [hz,hlast,ite_false,hm]
      rw [padded_after _ A B C D (by omega)]
      intro e he
      rw [inactive_self_step _ (D 0) hinactive 1 pub e he]
      exact hfinal e he

end ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
