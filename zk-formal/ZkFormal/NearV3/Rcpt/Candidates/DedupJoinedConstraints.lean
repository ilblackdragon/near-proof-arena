import ZkFormal.NearV3.Rcpt.Candidates.DedupJoinedRows

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

/-- Source equations for explicitly supplied cells and selectors. -/
def SourceRow (C D : Nat → Fp) (fst lst trn : Fp) (pub : Nat → Fp) : Prop :=
  ∀ e ∈ DedupTable.constraints, e.evalWith (cellEnv C D fst lst trn pub) = 0

/-- Local soundness of joining physical source partitions. The logical trace
retains every transition, uses the authenticated overlap, and appends an inactive
clone to restore a power-of-two height. -/
theorem joined_constraints (H : Nat) (hH : 2≤H) (L R : Nat → Nat → Fp)
    (pub : Nat → Fp)
    (hleft : ∀ r, r<H-1 → SourceRow (L r) (L (r+1)) (if r=0 then 1 else 0) 0 1 pub)
    (hright : ∀ r, r<H → SourceRow (R r) (R ((r+1)%H)) 0
      (if r+1=H then 1 else 0) (if r+1=H then 0 else 1) pub)
    (hcarry : ∀ x, x<57 → L (H-1) x=R 0 x)
    (hinactive : Inactive (R (H-1))) :
    ∀ r, r<2*H → SourceRow (joinedCells H L R r)
      (joinedCells H L R ((r+1)%(2*H))) (if r=0 then 1 else 0)
      (if r+1=2*H then 1 else 0) (if r+1=2*H then 0 else 1) pub := by
  intro r hr
  by_cases hl : r<H-1
  · have hn : r+1≠2*H := by omega
    have hm : (r+1)%(2*H)=r+1 := Nat.mod_eq_of_lt (by omega)
    simp only [hn, ite_false, hm]
    intro e he
    rw [cellEnv_congr e (base_constraint_width e he)
      (C' := L r) (D' := L (r+1))
      (fun x _ => congrFun (joined_left H L R hl) x)
      (joined_left_successor hH hl L R hcarry)]
    exact hleft r hl e he
  · have hz : r≠0 := by omega
    have hfinal := hright (H-1) (by omega)
    have hs : H-1+1=H := by omega
    simp only [hs, Nat.mod_self, ite_true] at hfinal
    by_cases hlast : r+1=2*H
    · have he : r=2*H-1 := by omega
      simp only [hz, hlast, ite_false, ite_true, Nat.mod_self]
      rw [he, joined_clone (by omega) L R]
      intro e hem
      rw [inactive_terminal_retarget _ _ (R 0) hinactive 1 1 pub e hem]
      exact hfinal e hem
    · have hm : (r+1)%(2*H)=r+1 := Nat.mod_eq_of_lt (by omega)
      simp only [hz, hlast, ite_false, hm]
      let q := r-(H-1)
      have hq : q<H := by dsimp [q]; omega
      have he : r=H-1+q := by dsimp [q]; omega
      rw [he, joined_right (by omega) L R hq]
      by_cases hqend : q+1=H
      · have hqe : q=H-1 := by omega
        have he' : H-1+q+1=2*H-1 := by omega
        rw [he', joined_clone (by omega) L R, hqe]
        intro e hem
        rw [inactive_self_step _ (R 0) hinactive 1 pub e hem]
        exact hfinal e hem
      · have hqn : q+1<H := by omega
        rw [Nat.add_assoc, joined_right (by omega) L R hqn]
        have hh := hright q hq
        simpa only [hqend, ite_false, Nat.mod_eq_of_lt hqn] using hh

end ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
