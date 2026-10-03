import ArenaCore
import NearSpec.TransferV1
/-- Vacuous: assumes `False`. Trivially provable, proves nothing. The required
    certificate type has no such premise. -/
theorem Candidate.certificate (h : False) :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation :=
  absurd h (by intro x; exact x.elim)
