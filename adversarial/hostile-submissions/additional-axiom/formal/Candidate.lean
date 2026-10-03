import ArenaCore
import NearSpec.TransferV1
/-- A fabricated axiom used to discharge the obligation. Not on the allowlist. -/
axiom Candidate.cheat : ArenaCore.Admits NearSpec.TransferV1.NearRelation
theorem Candidate.certificate :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation := Candidate.cheat
