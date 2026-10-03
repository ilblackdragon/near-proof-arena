import Toy.Programs

-- The manifest names `Candidate.Model.verify`, but the module declares another name.
def Candidate.Model.verifier : ArenaCore.OracleVerifier :=
  ArenaCore.interpOracleVerifier Toy.verifierCode Toy.toyParams.verifyFuel
