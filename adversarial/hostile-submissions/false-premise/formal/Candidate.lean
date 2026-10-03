import ArenaCore
import NearSpec.TransferV1
theorem Candidate.certificate (h : False) :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation :=
  absurd h (by intro x; exact x.elim)
