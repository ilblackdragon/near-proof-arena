import Toy.Programs

def Candidate.Model.fuel : Nat := (sorry : Nat) * 0 + 10000

def Candidate.Model.verify : ArenaCore.OracleVerifier :=
  ArenaCore.interpOracleVerifier Toy.verifierCode Candidate.Model.fuel
