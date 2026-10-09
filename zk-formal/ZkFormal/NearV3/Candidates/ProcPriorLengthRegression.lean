import ZkFormal.NearV3.Candidates.ProcPriorDecode
namespace ZkFormal.NearV3.Candidates.ProcPriorLengthRegression
open NearSpec NearSpec.Bandwidth

/-- The smallest native state is exactly 37 bytes. -/
theorem initial_length : State.initial.encode.length=37 := by decide +kernel

theorem initial_decodes : State.decode State.initial.encode=some State.initial := by decide +kernel

/-- Pointwise authentication of every parsed byte alone does not exclude an
extra authenticated byte; the original native decoder rejects that input. -/
theorem trailing_rejected : State.decode (State.initial.encode++[0])=none := by decide +kernel

theorem trailing_prefix : (State.initial.encode++[0]).take 37=State.initial.encode := by decide +kernel

end ZkFormal.NearV3.Candidates.ProcPriorLengthRegression
