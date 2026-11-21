import M5T1.Dump
import M5T1.Air

/-! `m5t1-tool dump CASE_DIR OUT_JSON`: the Lean run of every incoming receipt of a corpus case
(`M5T1.Dump.dumpCase`): receipt, RS before/after, VM query and answer, outcome, new receipts.

`m5t1-tool air AIR_JSON NAMES_JSON SCHEMA_JSON`: export the M5-T1 AIR (`M5T1.m5t1Air`), its column
names and the byte engine's schema. -/

open M5T1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["dump", dir, out] =>
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    let j ← M5T1.Dump.dumpCase cb.toList wb.toList
    IO.FS.writeFile out j.pretty
    return 0
  | ["air", out, names, sch] =>
    IO.FS.writeFile out (ZkFormal.Air.Air.exportJson m5t1Air)
    IO.FS.writeFile names namesJson
    IO.FS.writeFile sch schemaJson
    for (nm, t) in tableNames.zip m5t1Air.tables do
      let deg := (t.allConstraints.map ZkFormal.Air.Expr.degree).foldl max 0
      IO.println s!"{nm}: width {t.width}, constraints {t.allConstraints.length}, interactions {t.interactions.length}, degree {deg}, wf {ZkFormal.Air.Table.wf m5t1Air 4 t}"
    IO.println s!"schema entries {schema.length}, public values {Rx.NUM_PUB}"
    return 0
  | _ => IO.eprintln "usage: m5t1-tool dump CASE_DIR OUT_JSON | air AIR_JSON NAMES_JSON SCHEMA_JSON"; return 2
