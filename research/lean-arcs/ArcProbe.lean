import NearSpecV3.Wasm.Arcs

/-!
# arcprobe: timing of the committed fast path (`NearSpecV3.Wasm.Arcs`)

* `arcprobe --run GAS FILE [METHOD]` — `outcome pv86 …` at `wasmFuel pv86 GAS`. The source calls
  `Exec.outcome`; because this module imports `Wasm/Arcs`, the `@[csimp]` lemma
  `outcome_eq_fast` makes the compiled call `outcomeFast`. `arcprobe-old` (`ArcProbeOld.lean`,
  same text, no `Arcs` import) is the single-step baseline: identical output lines = A/B parity,
  and the timing difference shows that the csimp replacement is in effect.
* `arcprobe --arcs FILE` — arc-table statistics and prepare+build time.

`GAS` is raw gas (`300000000000000` = 300 Tgas). Each phase is forced by its own `IO` action
before the closing clock read.
-/

open NearSpecV3.Wasm

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--arcs", file] =>
    let code ← IO.FS.readBinFile file
    let t0 ← IO.monoMsNow
    match prepare pv86 code true with
    | .ok p =>
      let arcs := arcsOf p
      let mut n := 0
      let mut fused := 0
      let mut maxLen := 0
      for row in arcs do
        for e in row do
          match e with
          | some a =>
            n := n + 1
            if a.br.isSome then fused := fused + 1
            maxLen := Nat.max maxLen a.core.len
          | none => pure ()
      let t1 ← IO.monoMsNow
      IO.println s!"funcs={p.funcs.size} arcs={n} fused={fused} maxLen={maxLen} prepare+build ms={t1 - t0}"
      pure 0
    | _ => IO.println "prepare failed"; pure 1
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
  | _ => IO.eprintln "usage: arcprobe --run GAS FILE [METHOD] | --arcs FILE"; pure 2
