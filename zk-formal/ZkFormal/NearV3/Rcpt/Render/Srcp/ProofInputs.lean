import ZkFormal.NearV3.Rcpt.Render.Srcp.FromProofFacts

namespace ZkFormal.NearV3.Render.SrcpGen
open NearSpec ZkFormal.Near

/-- A claim-derived source root and its selected decoded witness proof. -/
structure ProofInput where
  root : Bytes
  dup : Bool
  entry : NearSpecV3.ProofEntry

def proofWeight (xs : List ProofInput) : Nat :=
  (xs.map fun x => 1 + x.entry.proof.path.length).sum

/-- Assign global list and source-message indices while compiling actual proof entries. -/
def blocksOfProofs (xs : List ProofInput) : List SrcpB :=
  List.ofFn fun i : Fin xs.length =>
    let x := xs[i]
    blockOfProof x.root x.dup i.val (1 + proofWeight (xs.take i.val)) x.entry

end ZkFormal.NearV3.Render.SrcpGen
