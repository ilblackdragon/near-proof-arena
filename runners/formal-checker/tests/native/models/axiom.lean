import Toy.Programs

-- A candidate axiom inside the model (Prop-valued, so the model still compiles).
axiom Candidate.Model.fuelOk : (10000 : Nat) = 10000

def Candidate.Model.fuel : Nat := (fun (_ : (10000 : Nat) = 10000) => 10000) Candidate.Model.fuelOk

def Candidate.Model.verify : ArenaCore.OracleVerifier :=
  ArenaCore.interpOracleVerifier Toy.verifierCode Candidate.Model.fuel
