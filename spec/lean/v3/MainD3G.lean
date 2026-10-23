import NearSpecV3.GenesisD3

/-!
`nearspec-v3-check-d3g CASE_DIR...` — evaluates `NearSpecV3.checkD3G` (the D3 checker with the
`MainTransition::Genesis` branch modelled) on `claim.bin` / `witness.bin` of each case directory;
one JSON line per case in the format of `nearspec-v3-check-d3`: verdict `accept` | `reject` |
`out_of_domain`.
-/

open NearSpecV3

def esc (s : String) : String := s.replace "\\" "\\\\" |>.replace "\"" "\\\""

def main (args : List String) : IO UInt32 := do
  for dir in args do
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    let (v, reason) := match checkD3G cb.toList wb.toList with
      | .ok () => ("accept", "")
      | .error e => (if e.startsWith "out of domain" then "out_of_domain" else "reject", e)
    IO.println s!"\{\"case\": \"{esc dir}\", \"verdict\": \"{v}\", \"reason\": \"{esc reason}\"}"
  return 0
