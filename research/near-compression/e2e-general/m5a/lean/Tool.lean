import StateM5a.Air

/-! `m5a-tool air D AIR_JSON NAMES_JSON`: export the M5a AIR (depth-`D` working-set tree) and its
column names. -/

open StateM5a

def main (args : List String) : IO UInt32 := do
  match args with
  | ["air", d, out, names] =>
    let D := d.toNat!
    IO.FS.writeFile out (ZkFormal.Air.Air.exportJson (m5aAir D))
    IO.FS.writeFile names (namesJson D)
    let A := m5aAir D
    for (nm, t) in tableNames.zip A.tables do
      IO.println s!"{nm}: width {t.width}, constraints {t.allConstraints.length}, interactions {t.interactions.length}"
    return 0
  | _ =>
    IO.eprintln "usage: m5a-tool air D AIR_JSON NAMES_JSON"
    return 2
