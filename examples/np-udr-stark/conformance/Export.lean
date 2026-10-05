import Conformance.AirJson
import Conformance.Toys
import Conformance.Sha
import ZkFormal.Near.Air

/-!
`np-lean-export <fib|multi|sha|near>` — print `Air.exportJson` of a Lean toy AIR.
`np-lean-export --roundtrip <air.json>` — parse an `np-air-v1` file, check
that re-exporting gives a JSON-equal value, report byte identity.
-/

open Conformance ZkFormal.Air

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--roundtrip", path] =>
    match parseAirChecked (← IO.FS.readFile path) with
    | .error e => IO.eprintln s!"np-lean-export: {path}: {e}"; return 1
    | .ok (A, same) =>
      IO.println s!"roundtrip ok: {A.tables.length} table(s), json-equal, byte-identical={same}"
      return 0
  | [name] =>
    match (toys ++ [("sha", Conformance.Sha.shaAir), ("near", ZkFormal.Near.nearAir)]).lookup name with
    | some A => IO.println A.exportJson; return 0
    | none => IO.eprintln s!"np-lean-export: unknown AIR {name} (fib|multi|sha|near)"; return 2
  | _ => IO.eprintln "usage: np-lean-export <fib|multi|sha|near> | --roundtrip <air.json>"; return 2
