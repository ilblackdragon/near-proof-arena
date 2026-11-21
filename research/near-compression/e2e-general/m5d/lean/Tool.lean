import FinalM5d.Dump

open FinalM5d

def main (args : List String) : IO UInt32 := do
  match args with
  | ["dump", dir, outp] =>
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    match Dump.dump dir cb.toList wb.toList with
    | .ok j =>
      IO.FS.writeFile outp j.pretty
      IO.println s!"dump: wrote {outp}"
      return 0
    | .error e => IO.eprintln s!"dump: {e}"; return 1
  | _ =>
    IO.eprintln "usage: m5d-tool dump CASE_DIR OUT.json"
    return 2
