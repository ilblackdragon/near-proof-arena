import ReexecNpai.Model

/-! Differential-test oracle: `ReexecNpai.check` (the Lean reference model)
on `claim.bin`/`proof.bin` pairs. Reads lines `CLAIM_PATH PROOF_PATH` from
stdin, prints `1`/`0` per line. -/

partial def loop (h : IO.FS.Stream) (o : IO.FS.Stream) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  match (line.trimAscii.toString.splitOn " ") with
  | [c, p] =>
    let cb ← IO.FS.readBinFile c
    let pb ← IO.FS.readBinFile p
    o.putStrLn (if ReexecNpai.check cb.toList pb.toList then "1" else "0")
    o.flush
  | _ => o.putStrLn "?"
  loop h o

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
