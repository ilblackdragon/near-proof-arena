import ReexecNpai.Program

/-! Writes the verifier bytecode image `ReexecNpai.code` (= `encode program`)
to the given path. Run by `build-recipe/build.sh` as
`lean --run Export.lean out/verifier.npai`. -/

def main (args : List String) : IO UInt32 := do
  match args with
  | [out] =>
    IO.FS.writeBinFile out (ByteArray.mk ReexecNpai.code.toArray)
    return 0
  | _ =>
    IO.eprintln "usage: Export OUT"
    return 2
