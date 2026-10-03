import ArenaCore
import NearSpec.TransferV1
def Candidate.params : ArenaCore.CryptoParams :=
  { queryReps := 1, fieldBits := 64, soundnessErrorLog2 := 40 }
theorem Candidate.certificate :
    ArenaCore.AdmitsWith Candidate.params NearSpec.TransferV1.NearRelation := by
  exact ArenaCore.admits_of_sound NearSpec.TransferV1.sound
