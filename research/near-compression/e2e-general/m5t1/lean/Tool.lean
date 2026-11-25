import M5T1.Dump
import M5T1.Air
import M5T1.Ent
import M5T1.Se

/-! `m5t1-tool dump CASE_DIR OUT_JSON`: the Lean run of every incoming receipt of a corpus case
(`M5T1.Dump.dumpCase`): receipt, RS before/after, VM query and answer, outcome, new receipts.

`m5t1-tool air AIR_JSON NAMES_JSON SCHEMA_JSON`: export the M5-T1 AIR (`M5T1.m5t1Air`), its column
names and the byte engine's schema.

`m5t1-tool air-ent AIR_JSON NAMES_JSON`: export the `rt` enter leaf's AIR (`M5T1.Ent.entAir`).
`m5t1-tool air-se AIR_JSON NAMES_JSON`: export the STATE engine half's leaf AIR (`M5T1.Se.seAir`, F-5). -/

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
    IO.FS.writeFile out (ZkFormal.Air.Air.exportJson exportAir)
    IO.FS.writeFile names namesJson
    IO.FS.writeFile sch schemaJson
    for (nm, t) in tableNames.zip exportAir.tables do
      let deg := (t.allConstraints.map ZkFormal.Air.Expr.degree).foldl max 0
      IO.println s!"{nm}: width {t.width}, constraints {t.allConstraints.length}, interactions {t.interactions.length}, degree {deg}, wf {ZkFormal.Air.Table.wf exportAir 4 t}"
    IO.println s!"schema entries {schema.length}, public values {Rx.NUM_PUB}"
    return 0
  | ["air-ent", out, names] =>
    -- F-6: the exported enter AIR is `entAirB` (`ENT` + every public value a byte on `RNG`)
    IO.FS.writeFile out (ZkFormal.Air.Air.exportJson M5T1.Ent.entAirB)
    IO.FS.writeFile names ("{\"ENT\":[\"z\"],\"RNG\":[" ++
      ",".intercalate (Rng.L.names.map q) ++ "],\"tables\":[\"ENT\",\"RNG\"],\"pub\":[" ++
      ",".intercalate (M5T1.Ent.PL.names.map q) ++ "]}")
    for (nm, t) in M5T1.Ent.tableNamesB.zip M5T1.Ent.entAirB.tables do
      let deg := (t.allConstraints.map ZkFormal.Air.Expr.degree).foldl max 0
      IO.println s!"{nm}: width {t.width}, constraints {t.allConstraints.length}, interactions {t.interactions.length}, degree {deg}, wf {ZkFormal.Air.Table.wf M5T1.Ent.entAirB 4 t}"
    IO.println s!"enter leaf: public values {M5T1.Ent.NUM_PUB}"
    return 0
  | ["air-se", out, names] =>
    IO.FS.writeFile out (ZkFormal.Air.Air.exportJson M5T1.Se.seAir)
    IO.FS.writeFile names ("{\"SE\":[" ++ ",".intercalate (M5T1.Se.L.names.map q) ++ "],\"RNG\":[" ++
      ",".intercalate (Rng.L.names.map q) ++ "],\"tables\":[\"SE\",\"RNG\"],\"pub\":[" ++
      ",".intercalate (M5T1.Se.PL.names.map q) ++ "]}")
    for (nm, t) in M5T1.Se.tableNames.zip M5T1.Se.seAir.tables do
      let deg := (t.allConstraints.map ZkFormal.Air.Expr.degree).foldl max 0
      IO.println s!"{nm}: width {t.width}, constraints {t.allConstraints.length}, interactions {t.interactions.length}, degree {deg}, wf {ZkFormal.Air.Table.wf M5T1.Se.seAir 4 t}"
    IO.println s!"SE leaf: public values {M5T1.Se.NUM_PUB}"
    return 0
  | _ => IO.eprintln "usage: m5t1-tool dump CASE_DIR OUT_JSON | air AIR_JSON NAMES_JSON SCHEMA_JSON"; return 2
