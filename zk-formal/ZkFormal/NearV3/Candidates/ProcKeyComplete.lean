import ZkFormal.NearV3.Candidates.ProcNonKey
namespace ZkFormal.NearV3.Candidates.ProcKeyComplete
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcHeightBits

/-- Complete native process key-family constraints at physical log22, including
all headers/entries, the carried tail row, and the cyclic final padding row. -/
theorem key_constraints (R : Run) (t r : Nat) (pub : List Fp)
    (hrows : (procVs R).length+1≤2^22) (hr : r<(trace R).height t) :
    ∀ e ∈ Proc.cKey,e.eval (trace R) t r pub=0 := by
  by_cases h : r<15
  · exact ProcKeyInterior.key_interior R t r pub h
  · by_cases he : r=15
    · subst r
      exact ProcKeyLast.last_native R t pub
    · exact ProcNonKey.native_nonkey R t r pub (by omega) hr hrows
end ZkFormal.NearV3.Candidates.ProcKeyComplete
