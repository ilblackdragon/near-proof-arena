import Toy.Programs
import Lean

def Candidate.Model.verify : ArenaCore.OracleVerifier :=
  ArenaCore.interpOracleVerifier Toy.verifierCode Toy.toyParams.verifyFuel
