import NearSpecV3
import NearSpecV3.ChunkValidationD2

/-!
`nearspec-v3-check-d2 [--d1|--d0] CASE_DIR...` — evaluates the compiled Lean D2 relation
(`NearSpecV3.checkD2`) on `claim.bin` / `witness.bin` of each case directory and prints one
JSON line per case: `{"case": dir, "verdict": "accept" | "reject" | "out_of_domain", "reason": ...}`
(the format of `nearspec-v3-check-d1`). `accept` ⇔ `RelD2 claim witness`. With `--d1` / `--d0`
first, evaluates `checkD1` / `checkD0` instead.
-/

open NearSpecV3

def esc (s : String) : String := s.replace "\\" "\\\\" |>.replace "\"" "\\\""

def classify (r : Except String Unit) : String × String :=
  match r with
  | .ok () => ("accept", "")
  | .error e => (if e.startsWith "out of domain" then "out_of_domain" else "reject", e)

def main (args : List String) : IO UInt32 := do
  let (mode, dirs) := match args with
    | "--d0" :: rest => (0, rest)
    | "--d1" :: rest => (1, rest)
    | _ => (2, args)
  for dir in dirs do
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    let r := if mode == 0 then checkD0 cb.toList wb.toList
      else if mode == 1 then checkD1 cb.toList wb.toList
      else checkD2 cb.toList wb.toList
    let (v, reason) := classify r
    IO.println s!"\{\"case\": \"{esc dir}\", \"verdict\": \"{v}\", \"reason\": \"{esc reason}\"}"
  return 0
