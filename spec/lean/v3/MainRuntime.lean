import Lean
import NearSpecV3.Wasm.Exec

open NearSpecV3.Wasm

def main (args : List String) : IO UInt32 := do
  let path :: rest := args | IO.eprintln "usage: nearspec-v3-runtime MODULE.wasm [METHOD]"; return 2
  let code ← IO.FS.readBinFile path
  let method := rest.headD "main"
  let cfg := { floatPv86 with loadingLimits := !rest.contains "--ablate-loading-limits" }
  let ctx : CallCtx := { prepaidGas := 300000000000000 }
  let fuel := (ctx.prepaidGas / cfg.regularOpCost + 2) * 64 + 1000000
  IO.println (outcome cfg code method ctx fuel true true)
  return 0
