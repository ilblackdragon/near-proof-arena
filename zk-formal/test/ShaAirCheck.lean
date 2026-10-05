import ZkFormal.Sha.Table
import ZkFormal.Air.Export
open ZkFormal.Air
def shaOnly : Air := ⟨[ZkFormal.Sha.Table.table 0 1], 2, 0⟩
def main : IO Unit := do
  let T := ZkFormal.Sha.Table.table 0 1
  IO.println s!"constraints {T.constraints.length} allConstraints {T.allConstraints.length}"
  IO.println s!"max degree {(T.allConstraints.map Expr.degree).foldr max 0}"
  IO.println s!"wf(maxDeg 4) {shaOnly.wf 4}  multBound {shaOnly.multBound} fpBound {shaOnly.fpBound}"
  let js := shaOnly.exportJson
  IO.println s!"export bytes {js.length}"
  IO.FS.writeFile "/tmp/claude-1002/-data-illia-nearproof/29f86fd5-cfb7-44c7-996e-70d81e3d17a4/scratchpad/sha-air.json" js
