import Lean
import NearSpecV3.Wasm.Exec
import NearSpecV3.Wasm.Arcs

open NearSpecV3.Wasm

def main (args : List String) : IO UInt32 := do
  let path :: rest := args | IO.eprintln "usage: nearspec-v3-runtime MODULE.wasm [METHOD [INPUT_FILE]]"; return 2
  let code ← IO.FS.readBinFile path
  let method := rest.headD "main"
  let cfg := { floatPv86 with loadingLimits := !rest.contains "--ablate-loading-limits" }
  let input ← match (rest.drop 1).find? (fun s => !s.startsWith "--") with
    | some p => IO.FS.readBinFile p
    | none => pure ByteArray.empty
  let ctx : CallCtx := { prepaidGas := 300000000000000, input := input }
  let fuel := (ctx.prepaidGas / cfg.regularOpCost + 2) * 64 + 1000000
  IO.println (outcome cfg code method ctx fuel true true)
  return 0
