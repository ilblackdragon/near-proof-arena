import NearSpecV3.D3.FunctionCall
import NearSpecV3.Logged.D2Check

/-!
`nearspec-v3-check-logged [--d2|--d2l] CASE_DIR...` — the read-logging checkers (`NearSpecV3.Logged`):
`--d2l` evaluates `checkD2L` on the tagged store (proved equal to `checkD2`), `--d2` the original
`checkD2`; one JSON line per case in the `nearspec-v3-check-d2` format, plus `"reads"` (number of
distinct keys read).
-/

open NearSpecV3 NearSpecV3.D2 NearSpecV3.Logged

def esc (s : String) : String := s.replace "\\" "\\\\" |>.replace "\"" "\\\""

def main (args : List String) : IO UInt32 := do
  let (mode, dirs) := match args with
    | "--d2" :: rest => (0, rest)
    | "--d2l" :: rest => (1, rest)
    | _ => (1, args)
  for dir in dirs do
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    let (r, nreads) : Except String Unit × Nat :=
      if mode == 0 then (checkD2 cb.toList wb.toList, 0)
      else
        let d := storesData wb.toList
        let (r, rs) := SM.runR (storeFn d) (checkD2L cb.toList wb.toList)
        (r, rs.length)
    let (v, reason) := match r with
      | .ok () => ("accept", "")
      | .error e => (if e.startsWith "out of domain" then "out_of_domain" else "reject", e)
    IO.println s!"\{\"case\": \"{esc dir}\", \"verdict\": \"{v}\", \"reason\": \"{esc reason}\", \"reads\": {nreads}}"
  return 0
