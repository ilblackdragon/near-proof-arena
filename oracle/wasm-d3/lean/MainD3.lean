import NearSpecV3.D3.FunctionCall

/-!
`nearspec-v3-check-d3 CASE_DIR...` — evaluates `NearSpecV3.D3.checkD3` (RuntimeD3: D2 + WASM
FunctionCalls) on `claim.bin` / `witness.bin` (code blobs appended) of each case directory; one JSON
line per case in the format of `nearspec-v3-check-d2`: verdict `accept` | `reject` | `out_of_domain`.
-/

open NearSpecV3

def esc (s : String) : String := s.replace "\\" "\\\\" |>.replace "\"" "\\\""

def main (args : List String) : IO UInt32 := do
  for dir in args do
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    let (v, reason) := match D3.checkD3 cb.toList wb.toList with
      | .ok () => ("accept", "")
      | .error e => (if e.startsWith "out of domain" then "out_of_domain" else "reject", e)
    IO.println s!"\{\"case\": \"{esc dir}\", \"verdict\": \"{v}\", \"reason\": \"{esc reason}\"}"
  return 0
