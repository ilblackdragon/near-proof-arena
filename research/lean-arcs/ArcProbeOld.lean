import NearSpecV3.Wasm.Fuel

/-!
# arcprobe-old: the single-step baseline for `arcprobe` (same text, no `Wasm/Arcs` import, so
the compiled `outcome` is `Exec.outcome` over `Exec.run`).
-/

open NearSpecV3.Wasm

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--run", g, file] | ["--run", g, file, _] =>
    let gas := g.toNat?.getD 0
    let method := (args.drop 3).headD "run"
    let code ← IO.FS.readBinFile file
    let ctx : CallCtx := { prepaidGas := gas }
    let t0 ← IO.monoMsNow
    IO.println (outcome pv86 code method ctx (wasmFuel pv86 gas))
    (← IO.getStdout).flush
    let t1 ← IO.monoMsNow
    IO.println s!"ms: {t1 - t0}"
    pure 0
  | _ => IO.eprintln "usage: arcprobe-old --run GAS FILE [METHOD]"; pure 2
