import ArenaCore
import NearSpec.TransferV1
theorem Candidate.certificate :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation := by
  exact ArenaCore.admits_of_sound NearSpec.TransferV1.sound
