import WasmBase.ToolCore
import WasmBase.Census
import WasmBase.Check.TraceDump
import WasmBase.SegAirG
/-!
`wasmbase-tool` — exporter and verifier-side preparation for the direct-Wasm base layer.

* `wasmbase-tool air <nloc> <ngl>`: the AIR `wasmBaseAir nloc ngl` as JSON (the Rust crate interprets it;
  `ngl` is the number of globals).
* `wasmbase-tool airH <nloc> <ngl>`: `wasmBaseHostAir` (the same tables plus HOST, HOSTO, HOSTT).
* `wasmbase-tool prep <file.wasm> <exportName> <g0>`: `prepare` (PV86), `check` of the exported function,
  and a reference execution with the spec's own `step` from the post-`enter` state with
  `gas.g = g0` (after the prologue charge), as JSON.
* `wasmbase-tool eval <nloc> <ngl> <points>`: evaluate every constraint, interaction count and message
  of `wasmBaseAir nloc ngl` at the given points (difftest; selectors are free field values).
* `wasmbase-tool evalH <nloc> <ngl> <points>`: the same for `wasmBaseHostAir`.
* `wasmbase-tool airX <nloc> <ngl>`: `wasmBaseHashAir` (= `wasmBaseHostAir` with `HOSTO`
  extended by the hash-call summary, plus the SHA256 table).
* `wasmbase-tool evalX <nloc> <ngl> <points>`: the same for `wasmBaseHashAir`.
* `wasmbase-tool airR <nloc> <ngl>`: `wasmBaseRegAir` (= `wasmBaseHostAir` plus the REG table).
* `wasmbase-tool evalR <nloc> <ngl> <points>`: the same for `wasmBaseRegAir`.
* `wasmbase-tool airIfR <nloc> <ngl>` / `evalIfR`: `wasmBaseIfRegAir` (E2E M1-a: IF + REG' with the
  `read_register` memory write, `WasmBase/RegMem.lean`).
* `wasmbase-tool airM2 <nloc> <ngl>` / `evalM2`: `wasmBaseM2Air` (E2E M2, `WasmBase/M2Air.lean`).
* `wasmbase-tool airSegMP <nloc> <ngl>`: `wasmBaseSegAirMP` (E2E M4b: `wasmBaseSegAir` with MPATH as a batched
  Merkle multiproof, `WasmBase/SegAirMP.lean`).
* `wasmbase-tool airM2r <nloc> <ngl>` / `evalM2r`: `wasmBaseM2rAir` (M2 + the absent-register header:
  REG-A and RINIT, `WasmBase/M2RegAbsent.lean`).
* `wasmbase-tool airM3 <nloc> <ngl>` / `evalM3` / `prepM3`: `wasmBaseM3Air` (HOST-W tags, MEMG, MSZ,
  GINIT, `WasmBase/M3Air.lean`) and its checker `checkModuleM3`.
* `wasmbase-tool airSegG <nloc> <ngl>`: `wasmBaseSegAirG` (E2E M4c: `wasmBaseSegAirMP` + MEMG, SEGG,
  MEMBG — segments containing `memory.grow`, `WasmBase/SegAirG.lean`); the full-run AIR is `airM3`
  and the prep `prepM3`.
-/

open NearSpecV3.Wasm WasmBase ZkFormal.Algebra

/-- `census <wasm> <export>`: why `checkModuleIfH` rejects the export (E2E M2). -/
def censusCmd (path exportName : String) : IO Unit := do
  let code ← IO.FS.readBinFile path
  match prepare pv86 code with
  | .ok p =>
    let some (_, _, fi) := p.m.exports.find? (fun (n, k, _) => n = exportName && k = 0)
      | throw (IO.userError "export not found")
    let fn := fi - p.m.imports.size
    let ok := (checkModuleIfH pv86 p fn).isSome
    IO.println s!"eligible {ok}"
    for (f, rs) in census pv86 p fn do
      IO.println s!"  fn {f}: {rs.map fun (r, n) => s!"{r}x{n}"}"
    IO.println s!"eligibleM2 {(checkModuleM2 pv86 p fn).isSome}"
    for (f, rs) in censusM2 pv86 p fn do
      if !rs.isEmpty then IO.println s!"  fn {f}: {rs.map fun (r, n) => s!"{r}x{n}"}"
  | _ => IO.println "prepare failed"

def main (args : List String) : IO Unit := do
  match args with
  | ["census", path, e] => censusCmd path e
  | ["holds", a, l, n, path] => HoldsCheck.holdsCmd a l.toNat! n.toNat! path
  | ["holds", a, l, n, path, a2, l2, n2] => HoldsCheck.holdsCmd a l.toNat! n.toNat! path (some (a2, l2.toNat!, n2.toNat!))
  | ["air", l, n] => IO.println (airJson (wasmBaseAir l.toNat! n.toNat!))
  | ["airH", l, n] => IO.println (airJson (wasmBaseHostAir l.toNat! n.toNat!))
  | ["airR", l, n] => IO.println (airJson (wasmBaseRegAir l.toNat! n.toNat!))
  | ["airX", l, n] => IO.println (airJson (Chips.wasmBaseHashAir l.toNat! n.toNat!))
  | ["prep", path, exportName, g0] => prep path exportName g0.toNat!
  | ["prep", path, exportName, g0, inp] => prep path exportName g0.toNat! inp
  | ["prepIf", path, exportName, g0] => prepIf path exportName g0.toNat!
  | ["prepIf", path, exportName, g0, inp] => prepIf path exportName g0.toNat! inp
  | ["prepM2", path, exportName, g0] => prepIf path exportName g0.toNat! "" checkModuleM2
  | ["prepM2", path, exportName, g0, inp] => prepIf path exportName g0.toNat! inp checkModuleM2
  | ["airM2", l, n] => IO.println (airJson (wasmBaseM2Air l.toNat! n.toNat!))
  | ["airSeg", l, n] => IO.println (airJson (wasmBaseSegAir l.toNat! n.toNat!))
  | ["airSegMP", l, n] => IO.println (airJson (wasmBaseSegAirMP l.toNat! n.toNat!))
  | ["airSegG", l, n] => IO.println (airJson (wasmBaseSegAirG l.toNat! n.toNat!))
  | ["evalM2", l, n, path] => evalPoints l.toNat! n.toNat! path 5
  | ["airM2r", l, n] => IO.println (airJson (wasmBaseM2rAir l.toNat! n.toNat!))
  | ["airM3", l, n] => IO.println (airJson (wasmBaseM3Air l.toNat! n.toNat!))
  | ["evalM3", l, n, path] => evalPoints l.toNat! n.toNat! path 7
  | ["prepM3", path, exportName, g0] => prepIf path exportName g0.toNat! "" checkModuleM3
  | ["prepM3", path, exportName, g0, inp] => prepIf path exportName g0.toNat! inp checkModuleM3
  | ["evalM2r", l, n, path] => evalPoints l.toNat! n.toNat! path 6
  | ["airIf", l, n] => IO.println (airJson (wasmBaseIfAir l.toNat! n.toNat!))
  | ["airIfH", l, n] => IO.println (airJson (wasmBaseIfHostAir l.toNat! n.toNat!))
  | ["airIfR", l, n] => IO.println (airJson (wasmBaseIfRegAir l.toNat! n.toNat!))
  | ["eval", l, n, path] => evalPoints l.toNat! n.toNat! path
  | ["evalH", l, n, path] => evalPoints l.toNat! n.toNat! path 1
  | ["evalR", l, n, path] => evalPoints l.toNat! n.toNat! path 2
  | ["evalX", l, n, path] => evalPoints l.toNat! n.toNat! path 3
  | ["evalIfR", l, n, path] => evalPoints l.toNat! n.toNat! path 4
  | _ => IO.eprintln "usage: wasmbase-tool air|airH|airR|airX <nloc> <ngl> | prep <wasm> <exportName> <g0> [inputHex] | eval|evalH|evalR|evalX <nloc> <ngl> <points>"
