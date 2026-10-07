import NearSpecV3.D3.FunctionCall
import NearSpecV3.Logged.API

/-!
`nearspec-v3-check-logged [--d2|--d2l|--d3|--d3l] CASE_DIR...` — the read-logging checkers
(`NearSpecV3.Logged`): `--d2l` / `--d3l` evaluate `checkD2Reads` / `checkD3Reads` (one run: the
verdict, proved equal to `checkD2` / `checkD3`, and the recorded-storage keys read); `--d2` / `--d3`
the original `checkD2` / `checkD3`. One JSON line per case in the `nearspec-v3-check-d2` format, plus
`"reads"` (number of keys read) and `"ms"` (wall time of the check).
-/

open NearSpecV3 NearSpecV3.D2 NearSpecV3.D3 NearSpecV3.Logged

def esc (s : String) : String := s.replace "\\" "\\\\" |>.replace "\"" "\\\""

def main (args : List String) : IO UInt32 := do
  let (mode, dirs) := match args with
    | "--d2" :: rest => (0, rest)
    | "--d2l" :: rest => (1, rest)
    | "--d3" :: rest => (2, rest)
    | "--d3l" :: rest => (3, rest)
    | _ => (1, args)
  for dir in dirs do
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    let t0 ← IO.monoMsNow
    let (r, nreads) : Except String Unit × Nat ←
      match mode with
      | 0 => pure (checkD2 cb.toList wb.toList, 0)
      | 2 => pure (checkD3 cb.toList wb.toList, 0)
      | 3 => let (r, rs) := checkD3Reads cb.toList wb.toList; pure (r, rs.length)
      | _ => let (r, rs) := checkD2Reads cb.toList wb.toList; pure (r, rs.length)
    let t1 ← IO.monoMsNow
    let (v, reason) := match r with
      | .ok () => ("accept", "")
      | .error e => (if e.startsWith "out of domain" then "out_of_domain" else "reject", e)
    IO.println s!"\{\"case\": \"{esc dir}\", \"verdict\": \"{v}\", \"reason\": \"{esc reason}\", \"reads\": {nreads}, \"ms\": {t1 - t0}}"
  return 0
