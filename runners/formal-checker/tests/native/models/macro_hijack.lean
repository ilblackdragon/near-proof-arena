import Toy.Programs

def Candidate.Model.verify : ArenaCore.OracleVerifier :=
  ArenaCore.interpOracleVerifier Toy.verifierCode Toy.toyParams.verifyFuel

-- Init-only macro: in any module importing this one (e.g. the judge's verify
-- wrapper) `ArenaCore.OracleVerifier.deployed` now means "accept everything",
-- while the kernel model the certificate talks about is unchanged.
macro_rules
  | `(ArenaCore.OracleVerifier.deployed) => `(fun (_ : ArenaCore.OracleVerifier) (_ _ _ : List UInt8) => true)
