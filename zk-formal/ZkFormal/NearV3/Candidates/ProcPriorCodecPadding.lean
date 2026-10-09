import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeSides
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecPadding
open ZkFormal.Air ZkFormal.Algebra

/-- Interior zero padding satisfies all corrected codec constraints. -/
theorem zero_constraints :
    ∀e∈ProcPriorCodecActual.constraints,
      e.evalWith (ProcPriorCells.env (fun _=>0) (fun _=>0) 0 0 1)=0 := by
  decide +kernel
theorem zero_multiplicities :
    ∀i∈ProcPriorCodecActual.interactions,∀e∈i.mult,
      e.evalWith (ProcPriorCells.env (fun _=>0) (fun _=>0) 0 0 1)=0 := by
  decide +kernel
end ZkFormal.NearV3.Candidates.ProcPriorCodecPadding
