import Toy.Programs

/-- The candidate's verifier model (the NPAI toy verifier, as a Lean function). -/
def Candidate.Model.verify : ArenaCore.OracleVerifier :=
  ArenaCore.interpOracleVerifier Toy.verifierCode Toy.toyParams.verifyFuel
