import ZkFormal.NearV3.Rcpt.Tables.Rcpt

/-! Prints the `rcptV3` constraints and interactions (one per line, prefix S-expressions) for
`test/rcptv3_model.py`: `lake env lean --run test/RcptExport.lean > rcpt_air.txt`.
Interaction lines: `I bus send mult msg…` (single-bit multiplicities). -/
open ZkFormal.Air
partial def ser : Expr → String
  | .const v => s!"(k {v})"
  | .col x nx => s!"(c {x} {if nx then 1 else 0})"
  | .pub i => s!"(p {i})"
  | .isFirst => "(F)"
  | .isLast => "(L)"
  | .isTransition => "(T)"
  | .add a b => s!"(+ {ser a} {ser b})"
  | .mul a b => s!"(* {ser a} {ser b})"
  | .neg a => s!"(- {ser a})"
def main : IO Unit := do
  IO.println s!"W {ZkFormal.NearV3.RcptV3.table.width}"
  for e in ZkFormal.NearV3.RcptV3.table.constraints do
    IO.println s!"C {ser e}"
  for i in ZkFormal.NearV3.RcptV3.table.interactions do
    IO.println s!"I {i.bus} {if i.send then 1 else 0} {ser (i.mult.headD (.const 0))} {String.intercalate " " (i.msg.map ser)}"
