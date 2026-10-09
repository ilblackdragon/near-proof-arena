import ZkFormal.NearV3.Tables.Ups

/-! Prints the `upsV3` constraints and interactions (one per line, prefix S-expressions) for
`test/upsv3_model.py`: `lake env lean --run test/UpsExport.lean > ups_air.txt`. -/
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
  for e in ZkFormal.NearV3.UpsV3.table.constraints do
    IO.println s!"C {ser e}"
  for i in ZkFormal.NearV3.UpsV3.table.interactions do
    IO.println s!"I {i.bus} {if i.send then 1 else 0} {ser (i.mult.headD (.const 0))} {String.intercalate " " (i.msg.map ser)}"
