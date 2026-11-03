import WasmBase.ToolCore
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
-/

open NearSpecV3.Wasm WasmBase ZkFormal.Algebra

def main (args : List String) : IO Unit := do
  match args with
  | ["air", l, n] => IO.println (airJson (wasmBaseAir l.toNat! n.toNat!))
  | ["airH", l, n] => IO.println (airJson (wasmBaseHostAir l.toNat! n.toNat!))
  | ["airR", l, n] => IO.println (airJson (wasmBaseRegAir l.toNat! n.toNat!))
  | ["airX", l, n] => IO.println (airJson (Chips.wasmBaseHashAir l.toNat! n.toNat!))
  | ["prep", path, exportName, g0] => prep path exportName g0.toNat!
  | ["prep", path, exportName, g0, inp] => prep path exportName g0.toNat! inp
  | ["prepIf", path, exportName, g0] => prepIf path exportName g0.toNat!
  | ["prepIf", path, exportName, g0, inp] => prepIf path exportName g0.toNat! inp
  | ["airIf", l, n] => IO.println (airJson (wasmBaseIfAir l.toNat! n.toNat!))
  | ["airIfH", l, n] => IO.println (airJson (wasmBaseIfHostAir l.toNat! n.toNat!))
  | ["airIfR", l, n] => IO.println (airJson (wasmBaseIfRegAir l.toNat! n.toNat!))
  | ["eval", l, n, path] => evalPoints l.toNat! n.toNat! path
  | ["evalH", l, n, path] => evalPoints l.toNat! n.toNat! path 1
  | ["evalR", l, n, path] => evalPoints l.toNat! n.toNat! path 2
  | ["evalX", l, n, path] => evalPoints l.toNat! n.toNat! path 3
  | ["evalIfR", l, n, path] => evalPoints l.toNat! n.toNat! path 4
  | _ => IO.eprintln "usage: wasmbase-tool air|airH|airR|airX <nloc> <ngl> | prep <wasm> <exportName> <g0> [inputHex] | eval|evalH|evalR|evalX <nloc> <ngl> <points>"
