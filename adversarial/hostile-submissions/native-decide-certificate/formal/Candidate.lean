import ArenaCore
import NearSpec.TransferV1
theorem Candidate.certificate :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation := by
  native_decide
