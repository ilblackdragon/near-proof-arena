import ArenaCore
import NearSpec.TransferV1
/-- The admission certificate. Its TYPE is dictated by the challenge
    (`FormalSpecRef.relation_decl`); the candidate supplies only the proof term.
    Honest base: a sound soundness proof for the exact required relation. -/
theorem Candidate.certificate :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation := by
  exact ArenaCore.admits_of_sound NearSpec.TransferV1.sound
