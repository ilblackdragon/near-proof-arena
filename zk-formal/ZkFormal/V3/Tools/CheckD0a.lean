import NearSpecV3.ChunkValidationV0a

/-!
`nearspec-v3-check-d0a CASE_DIR...` — the compiled amended relation `NearSpecV3.checkD0a`
(`.ok ()` ⇔ `RelD0a`, `relD0a_iff`) on `claim.bin` / `witness.bin` of each case directory;
one JSON line per case: `{"case", "verdict": "accept" | "reject" | "out_of_domain", "reason"}`.
Plain spec code (no candidate fast paths), so it is the reference side of the difftest.
-/

open NearSpecV3

def esc (s : String) : String := s.replace "\\" "\\\\" |>.replace "\"" "\\\""

def main (args : List String) : IO UInt32 := do
  for dir in args do
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    let (v, reason) := match checkD0a cb.toList wb.toList with
      | .ok () => ("accept", "")
      | .error e => (if e.startsWith "out of domain" then "out_of_domain" else "reject", e)
    IO.println s!"\{\"case\": \"{esc dir}\", \"verdict\": \"{v}\", \"reason\": \"{esc reason}\"}"
  return 0
