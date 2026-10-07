import ZkFormal.Size.V3Synth
import ZkFormal.NearV3.Rcpt.Candidates.SourceBudget

/-! Isolated shape-model candidates, not admitted AIR configurations. Two source/SHA
partitions and log27 LDE are model inputs only; no active cap or parameter changes. -/
namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Size ZkFormal.Size.V3 ZkFormal.Stark

def partitionParams (g : Nat) : Params := { ZkFormal.V2.G.pg g with maxLogLde := 27 }

def partitionShapes (g : Nat) : List TShape :=
  let sha := { shapeOf g shaT with maxLog := 23 }
  let src := { (rcptS g)[4]! with maxLog := 23 }
  [sha, sha] ++ trieS g ++ chachaT.map (shapeOf g) ++ schedS g ++
    (rcptS g).set 4 src ++ [src] ++ v1S g

/-- Numerical model only: does not assert well-formedness, security, or admission of a redesigned AIR. -/
def partitionSize (g : Nat) : Nat := sizeOfWeq (partitionParams g) (partitionShapes g)

end ZkFormal.NearV3.Rcpt.Candidates
