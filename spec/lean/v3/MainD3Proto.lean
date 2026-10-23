import NearSpecV3.ChallengeChunkV3Gas

/-!
`nearspec-v3-check-d3proto CASE_DIR...` — evaluates `NearSpecV3.RelD3Proto` (the L1 successor:
`checkD2Core` with the protocol's `max_gas_burnt` in place of the proof-capacity `G_α`) on
`claim.bin` / `witness.bin` of each case directory; one JSON line per case in the format of
`nearspec-v3-check-d3`: verdict `accept` | `reject` | `out_of_domain`.

This exists to *exhibit* the L1 widening on real chunk data rather than assert it structurally.
Run the same case through both binaries: a case that `checkD3` refuses as `out of domain (e.g_alpha)`
and that this accepts is the band chunk the lane's log says was missing.
-/

open NearSpecV3

def esc (s : String) : String := s.replace "\\" "\\\\" |>.replace "\"" "\\\""

def main (args : List String) : IO UInt32 := do
  for dir in args do
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    let (v, reason) := match checkD3Proto cb.toList wb.toList with
      | .ok () => ("accept", "")
      | .error e => (if e.startsWith "out of domain" then "out_of_domain" else "reject", e)
    IO.println s!"\{\"case\": \"{esc dir}\", \"verdict\": \"{v}\", \"reason\": \"{esc reason}\"}"
  return 0
