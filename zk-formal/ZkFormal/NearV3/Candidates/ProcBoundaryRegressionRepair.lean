import ZkFormal.NearV3.Candidates.ProcBoundaryKeys
import ZkFormal.NearV3.Candidates.ProcEmptyBoundaryRegression
namespace ZkFormal.NearV3.Candidates.ProcBoundaryRegressionRepair
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcEmptyBoundaryRegression

/-- All repaired key constraints pass at the same differing-seed boundary
where the old rotation constraint evaluates to one. -/
theorem repaired_key_boundary (R : Run) :
    ∀e∈ProcBoundaryRepair.cKey,e.eval (concatenated R) 0 15 []=0 := by
  apply ProcBoundaryKeys.key_to_key (empty0 R) (empty1 R) rfl (concatenated R) 0 15 []
  · intro c; rfl
  · intro c
    have hmod : (15+1)%(concatenated R).height 0=16 := by
      change 16%(2^22)=16
      exact Nat.mod_eq_of_lt (by decide)
    rw [hmod]
    rfl
end ZkFormal.NearV3.Candidates.ProcBoundaryRegressionRepair
