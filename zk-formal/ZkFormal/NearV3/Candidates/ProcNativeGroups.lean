import ZkFormal.NearV3.Candidates.ProcBoundaryLocal
namespace ZkFormal.NearV3.Candidates.ProcNativeGroups
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete

theorem groups (R : Run) (hd : ProcData.RunData R) (hrows : (procVs R).length+1≤2^22)
    (t r : Nat) (pub : List Fp) (hr : r<2^22) :
    ∀e∈ProcBoundaryRepair.cKey++Proc.cHdr++Proc.cEnt,
      e.eval (ProcHeightBits.trace R) t r pub=0 := by
  simp only [List.forall_mem_append]
  exact ⟨⟨ProcBoundaryLocal.old_key _ _ _ _ (ProcKeyComplete.key_constraints R t r pub hrows hr),
    ProcComplete.header_all R hd hrows t r pub hr⟩,ProcComplete.entry_all R hd hrows t r pub⟩
end ZkFormal.NearV3.Candidates.ProcNativeGroups
