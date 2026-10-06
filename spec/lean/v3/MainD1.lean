import NearSpecV3
import NearSpecV3.ChunkValidationD1

/-!
`nearspec-v3-check-d1 CASE_DIR...` — evaluates the compiled Lean D1 relation
(`NearSpecV3.checkD1`) on `claim.bin` / `witness.bin` of each case directory and prints one
JSON line per case: `{"case": dir, "verdict": "accept" | "reject" | "out_of_domain", "reason": ...}`.
`accept` ⇔ `RelD1 claim witness`. With `--d0` first, evaluates `checkD0` instead (so one binary
answers both domains on the same corpus).
-/

open NearSpecV3

def esc (s : String) : String := s.replace "\\" "\\\\" |>.replace "\"" "\\\""

def classify (r : Except String Unit) : String × String :=
  match r with
  | .ok () => ("accept", "")
  | .error e => (if e.startsWith "out of domain" then "out_of_domain" else "reject", e)

def main (args : List String) : IO UInt32 := do
  let (d0, dirs) := match args with
    | "--d0" :: rest => (true, rest)
    | _ => (false, args)
  for dir in dirs do
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    let r := if d0 then checkD0 cb.toList wb.toList else checkD1 cb.toList wb.toList
    let (v, reason) := classify r
    IO.println s!"\{\"case\": \"{esc dir}\", \"verdict\": \"{v}\", \"reason\": \"{esc reason}\"}"
  return 0
