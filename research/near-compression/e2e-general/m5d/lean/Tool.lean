import FinalM5d.Dump
import FinalM5d.Final
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

def natList (l : List Nat) : String := "[" ++ ",".intercalate (l.map toString) ++ "]"

def finalConsts : List (String × String) :=
  [("NS", toString NS), ("RSD", toString RSD), ("RST", toString RST), ("CI_OFF", toString CI_OFF),
   ("HBN", toString HBN), ("PRE_LEN", toString PRE_LEN), ("FI_LEN", toString FI_LEN),
   ("FIN_TAG", toString FIN_TAG), ("SHM0", toString SHM0), ("SHL0", toString SHL0),
   ("PID0", toString PID0), ("MID0", toString MID0), ("ID_CLAIM", toString ID_CLAIM),
   ("ID_FIN", toString ID_FIN), ("RCH0", toString RCH0), ("OCH0", toString OCH0),
   ("CH_OUT", toString CH_OUT), ("CH_RC", toString CH_RC), ("TR_OUT", toString TR_OUT),
   ("TR_SH", toString TR_SH), ("TR_RS", toString TR_RS), ("NUM_PUB", toString NUM_PUB),
   ("acc0", natList acc0), ("ivLimbs", natList S384.ivLimbs),
   ("matrix", "[" ++ ",".intercalate (Rs.matrix.map natList) ++ "]"),
   ("streamFixed", "[" ++ ",".intercalate (streamFixed.map fun (a, b) => natList [a, b]) ++ "]")]

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
  | _ =>
    IO.eprintln "usage: m5d-tool dump CASE_DIR OUT.json | m5d-tool air-final AIR_JSON NAMES_JSON"
    return 2
