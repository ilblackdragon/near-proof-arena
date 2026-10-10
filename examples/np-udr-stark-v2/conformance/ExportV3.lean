import ZkFormal.NearV3.Assembly.NearAir
import ZkFormal.V2.Export
import ZkFormal.Stark.Protocol

/-!
`np-lean-export-v3` — prints `nearAirV3.exportJson` (format `np-air-v2`), the
frozen assembled v3 AIR the Rust prover is fed.

`np-lean-export-v3 --layout <g>` — per table, one line
`t width auxCount degree quotCount sendG recvG maxLog` at `auxGroup = g`
(`ZkFormal.Stark.Protocol`), for comparison with `npudr layout`.
-/

open ZkFormal.Air ZkFormal.Stark

def main (args : List String) : IO UInt32 := do
  let AP := ZkFormal.NearV3.Assembly.nearAirV3
  match args with
  | [] => IO.print AP.exportJson; return 0
  | ["--layout", gS] =>
    let some g := gS.toNat? | IO.eprintln "bad g"; return 2
    for (T, t) in AP.tables.zipIdx do
      IO.println s!"{t} {T.width} {T.auxCount g} {T.degree g} {T.quotCount g} {numGroups (T.numSide true) g} {numGroups (T.numSide false) g} {T.maxLog}"
    return 0
  | _ => IO.eprintln "usage: np-lean-export-v3 [--layout g]"; return 2
