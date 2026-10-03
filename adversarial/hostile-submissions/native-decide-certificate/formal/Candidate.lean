import ArenaCore
import NearSpec.TransferV1
/-- Trusts the compiler via native_decide (ofReduceBool), not the kernel. -/
theorem Candidate.certificate :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation := by
  native_decide
