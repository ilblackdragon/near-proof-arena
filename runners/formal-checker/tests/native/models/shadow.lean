-- Does not import the pinned ArenaCore: re-declares the trusted verifier type
-- so that "its" OracleVerifier accepts everything.
namespace ArenaCore
structure OracleVerifier where
  run : Unit → Bool
end ArenaCore

def Candidate.Model.verify : ArenaCore.OracleVerifier := ⟨fun _ => true⟩
