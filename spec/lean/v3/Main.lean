import NearSpecV3
import NearSpecV3.ChunkValidationV0

/-!
`nearspec-v3-check CASE_DIR...` — evaluates the compiled Lean D0 relation
(`NearSpecV3.checkD0`) on `claim.bin` / `witness.bin` of each case directory and
prints one JSON line per case:
`{"case": dir, "verdict": "accept" | "reject" | "out_of_domain", "reason": ...}`.
`accept` ⇔ `RelD0 claim witness`.
-/

open NearSpecV3

def esc (s : String) : String := s.replace "\\" "\\\\" |>.replace "\"" "\\\""

def classify (r : Except String Unit) : String × String :=
  match r with
  | .ok () => ("accept", "")
  | .error e => (if e.startsWith "out of domain" then "out_of_domain" else "reject", e)

def main (args : List String) : IO UInt32 := do
  for dir in args do
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    let (v, reason) := classify (checkD0 cb.toList wb.toList)
    IO.println s!"\{\"case\": \"{esc dir}\", \"verdict\": \"{v}\", \"reason\": \"{esc reason}\"}"
  return 0
