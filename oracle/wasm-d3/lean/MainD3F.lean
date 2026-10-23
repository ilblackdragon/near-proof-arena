import NearSpecV3.ChallengeChunkV3Float

/-!
`nearspec-v3-check-d3f [--proto] CASE_DIR...` — evaluates the L2 float extension
(`NearSpecV3.checkD3F`, or `checkD3ProtoFloat` with `--proto`, which also replaces `gAlpha` with the
protocol gas bound) on `claim.bin` / `witness.bin` (code blobs appended) of each case directory; one
JSON line per case in the format of `nearspec-v3-check-d3`: verdict `accept` | `reject` |
`out_of_domain`.
-/

open NearSpecV3

def esc (s : String) : String := s.replace "\\" "\\\\" |>.replace "\"" "\\\""

def main (args : List String) : IO UInt32 := do
  let (proto, dirs) := match args with
    | "--proto" :: rest => (true, rest)
    | rest => (false, rest)
  for dir in dirs do
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    let r := if proto then checkD3ProtoFloat cb.toList wb.toList else checkD3F cb.toList wb.toList
    let (v, reason) := match r with
      | .ok () => ("accept", "")
      | .error e => (if e.startsWith "out of domain" then "out_of_domain" else "reject", e)
    IO.println s!"\{\"case\": \"{esc dir}\", \"verdict\": \"{v}\", \"reason\": \"{esc reason}\"}"
  return 0
