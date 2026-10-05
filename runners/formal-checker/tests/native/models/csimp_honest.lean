import Toy.Programs

def Candidate.Model.slow : ArenaCore.OracleVerifier :=
  ArenaCore.interpOracleVerifier Toy.verifierCode Toy.toyParams.verifyFuel

/-- Same verifier, stated through a second definition (stand-in for a faster
implementation such as ZkFormal's `takeF`), kernel-proved equal. -/
def Candidate.Model.fast : ArenaCore.OracleVerifier :=
  ArenaCore.interpOracleVerifier Toy.verifierCode 10000

@[csimp] theorem Candidate.Model.slow_eq_fast : @Candidate.Model.slow = @Candidate.Model.fast := rfl

def Candidate.Model.verify : ArenaCore.OracleVerifier := Candidate.Model.slow
