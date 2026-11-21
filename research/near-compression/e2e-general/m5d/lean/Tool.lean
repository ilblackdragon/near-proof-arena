import FinalM5d.Dump
import FinalM5d.Final
import FinalM5d.Init
import FinalM5d.Cls.All
import ZkFormal.Air.Export

/-!
`m5d-tool dump CASE_DIR OUT.json` — the checker's FINAL on a corpus case (`FinalM5d.Dump`).
`m5d-tool air-final AIR_JSON NAMES_JSON` — the FINAL AIR (`FinalM5d.finalAir`) and its column
names and class constants for the trace generator.
-/

open FinalM5d

def q (s : String) : String := "\"" ++ s ++ "\""

def namesJson (tables : List String) (lays : List (String × Layout)) (consts : List (String × String)) :
    String :=
  "{\"tables\":[" ++ ",".intercalate (tables.map q) ++ "]," ++
  "\"cols\":{" ++ ",".intercalate (lays.map fun (t, L) =>
    q t ++ ":[" ++ ",".intercalate (L.names.map q) ++ "]") ++ "}," ++
  "\"consts\":{" ++ ",".intercalate (consts.map fun (k, v) => q k ++ ":" ++ v) ++ "}}"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["dump", dir, outp] =>
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    match Dump.dump dir cb.toList wb.toList with
    | .ok j =>
      IO.FS.writeFile outp j.pretty
      IO.println s!"dump: wrote {outp}"
      return 0
    | .error e => IO.eprintln s!"dump: {e}"; return 1
  | ["air-final", out, names] =>
    IO.FS.writeFile out (ZkFormal.Air.Air.exportJson finalAir)
    IO.FS.writeFile names (namesJson finalNames finalLayouts finalConsts)
    for (n, t) in finalNames.zip finalAir.tables do
      IO.println s!"TABLE {n}: width {t.width}, constraints {t.constraints.length}, interactions {t.interactions.length}"
    return 0
  | ["air-final-cls", ns, d, tt, out, names] =>
    match FinalM5d.Cls.byClass ns.toNat! d.toNat! tt.toNat! with
    | some (A, lays, consts) =>
      IO.FS.writeFile out (ZkFormal.Air.Air.exportJson A)
      IO.FS.writeFile names (namesJson finalNames lays consts)
      for (n, t) in finalNames.zip A.tables do
        IO.println s!"TABLE {n}: width {t.width}, constraints {t.constraints.length}, interactions {t.interactions.length}"
      return 0
    | none => IO.eprintln s!"class ({ns}, {d}, {tt}) not generated (gen_class.py)"; return 2
  | ["air-init", out, names] =>
    IO.FS.writeFile out (ZkFormal.Air.Air.exportJson InitT.initAir)
    IO.FS.writeFile names (namesJson InitT.initNames InitT.initLayouts
      (finalConsts ++ [("ID_CTX", toString InitT.ID_CTX), ("CTX_TAG", toString InitT.CTX_TAG)]))
    for (n, t) in InitT.initNames.zip InitT.initAir.tables do
      IO.println s!"TABLE {n}: width {t.width}, constraints {t.constraints.length}, interactions {t.interactions.length}"
    return 0
  | _ =>
    IO.eprintln "usage: m5d-tool dump CASE_DIR OUT.json | m5d-tool air-final|air-init AIR_JSON NAMES_JSON | m5d-tool air-final-cls NS D T AIR_JSON NAMES_JSON"
    return 2
