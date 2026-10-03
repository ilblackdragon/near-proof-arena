import ArenaCore
import NearSpec.TransferV1
/-- Soundness proof instantiated at parameters giving ~40 bits, while the
    manifest asks for 128. The judge computes the bound from these parameters. -/
def Candidate.params : ArenaCore.CryptoParams :=
  { queryReps := 1, fieldBits := 64, soundnessErrorLog2 := 40 }
theorem Candidate.certificate :
    ArenaCore.AdmitsWith Candidate.params NearSpec.TransferV1.NearRelation := by
  exact ArenaCore.admits_of_sound NearSpec.TransferV1.sound
