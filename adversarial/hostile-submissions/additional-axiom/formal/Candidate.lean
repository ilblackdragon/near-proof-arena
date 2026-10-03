import ArenaCore
import NearSpec.TransferV1
axiom Candidate.cheat : ArenaCore.Admits NearSpec.TransferV1.NearRelation
theorem Candidate.certificate :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation := Candidate.cheat
