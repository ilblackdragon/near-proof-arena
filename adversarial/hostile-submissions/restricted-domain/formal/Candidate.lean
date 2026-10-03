import ArenaCore
import NearSpec.TransferV1
theorem Candidate.certificate (h : NearSpec.TransferV1.SingleReceipt) :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation := by
  exact ArenaCore.admits_of_sound (NearSpec.TransferV1.sound_restricted h)
