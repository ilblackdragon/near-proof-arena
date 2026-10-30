import NearSpecV3.Examples.MlDsaVectors

/-! `nearspec-v3-mldsa-check`: `MlDsa65.verify` (the successor's ML-DSA-65 verifier: pure, empty
context) on each stdin line `PK_HEX MSG_HEX SIG_HEX`; prints `true` / `false` per line. Used to
check the `z`-at-the-norm-bound signatures of `tools/d3/mldsa65_bound.py` (workplan item 10). Not a
default target. -/

open NearSpecV3.Examples.MlDsaVectors NearSpecV3.MlDsa65

partial def loop (h : IO.FS.Stream) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  match line.trim.splitOn " " with
  | [pk, msg, sig] =>
    IO.println (if verify (unhex pk).toList (unhex sig).toList (unhex msg).toList then "true" else "false")
  | _ => IO.println "bad-line"
  loop h

def main : IO UInt32 := do
  loop (← IO.getStdin)
  return 0
