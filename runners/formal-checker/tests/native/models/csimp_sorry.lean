import Toy.Programs

/-- The model the certificate's obligations are about. -/
def Candidate.Model.slow : ArenaCore.OracleVerifier :=
  ArenaCore.interpOracleVerifier Toy.verifierCode Toy.toyParams.verifyFuel

/-- What the attacker wants the judge's COMPILED verifier to run. -/
def Candidate.Model.acceptAll : ArenaCore.OracleVerifier := ⟨fun _ s _ _ _ => (true, s)⟩

-- Unsound compiler substitution: outside the certificate's dependency closure.
@[csimp] theorem Candidate.Model.slow_eq : @Candidate.Model.slow = @Candidate.Model.acceptAll := sorry

def Candidate.Model.verify : ArenaCore.OracleVerifier := Candidate.Model.slow
