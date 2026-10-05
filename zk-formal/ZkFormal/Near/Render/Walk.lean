import ZkFormal.Near.Render.Common
import ZkFormal.Near.Tables.Walk

/-!
# ZkFormal.Near.Render.Walk — honest rows of the `walk` table

One segment per receipt (batch order): the `START` row, then one row per key
symbol of `nibbles (0 ‖ receiver) ++ [END]`.  The chained edge counter `u` of a
step is the number of earlier steps (in table order) using the same edge.
-/

namespace ZkFormal.Near.Render

open ZkFormal.Near

def walkRowsAll (ws : List (List WStep)) : Array Row := Id.run do
  let mut cnt : Std.HashMap Edge Nat := {}
  let mut rows : Array Row := #[]
  for (w, r) in ws.zip (List.range ws.length) do
    for s in w do
      let u := cnt.getD s.edge 0
      cnt := cnt.insert s.edge (u + 1)
      let mut row := zeroRow WalkTab.width
      row := row.set! WalkTab.act 1
      row := row.set! WalkTab.ws (if s.t.isNone then 1 else 0)
      row := row.set! WalkTab.we (if s.last then 1 else 0)
      row := row.set! WalkTab.r r
      row := row.set! WalkTab.t (s.t.getD 0)
      row := row.set! WalkTab.sym s.sym
      row := row.set! WalkTab.nN (s.edge.getD 0 0)
      row := row.set! WalkTab.nI (s.edge.getD 1 0)
      row := row.set! WalkTab.nN2 (s.edge.getD 3 0)
      row := row.set! WalkTab.nI2 (s.edge.getD 4 0)
      row := row.set! WalkTab.u u
      row := row.set! WalkTab.gK (if s.t.isNone then 0 else 1)
      rows := rows.push row
  return padTo rows (zeroRow WalkTab.width)

end ZkFormal.Near.Render
