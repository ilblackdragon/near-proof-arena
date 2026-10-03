import Toy.Programs

theorem Candidate.Model.t : (10000 : Nat) = 10000 := by native_decide

def Candidate.Model.fuel : Nat := (fun (_ : (10000 : Nat) = 10000) => 10000) Candidate.Model.t

def Candidate.Model.verify : ArenaCore.OracleVerifier :=
  ArenaCore.interpOracleVerifier Toy.verifierCode Candidate.Model.fuel
