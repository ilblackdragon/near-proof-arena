import NearSpecV3.Successor.ZstdFrame

/-! `nearspec-v3-zstd-decode <frame> [out] [encCap] [decCap]`: decode a zstd frame with the Lean
decoder. With `encCap`/`decCap` (bytes), it mirrors the relation's two size checks
(`decodeWitnessFileV`): reject if the encoded frame exceeds `encCap`
(`MAX_COMPRESSED_STATE_WITNESS_SIZE`), and apply the `decCap` (`MAX_UNCOMPRESSED...` 64 MiB)
`CountingRead` cut-off during decode. Used by the W02 size-limits differential and boundary tests
against the vendored zstd 1.5.6 (`zref`). -/

open NearSpecV3.Zstd

def main (args : List String) : IO UInt32 := do
  match args with
  | frame :: rest =>
    let bytes ← IO.FS.readBinFile frame
    let outPath? := rest.head?
    let encCap? := (rest.drop 1).head?.bind (·.toNat?)
    let decCap := ((rest.drop 2).head?.bind (·.toNat?)).getD (1 <<< 62)
    match encCap? with
    | some ec =>
      if bytes.size > ec then
        IO.println "ERR invalid: encoded_length exceeds MAX_COMPRESSED_STATE_WITNESS_SIZE"
        return 0
    | none => pure ()
    match decompress bytes 0 bytes.size decCap with
    | .ok out =>
      match outPath? with
      | some outPath => if outPath != "-" then IO.FS.writeBinFile outPath out
      | none => pure ()
      IO.println s!"OK {out.size}"
      pure 0
    | .error e =>
      IO.println s!"ERR {e}"
      pure 0
  | [] => IO.eprintln "usage: nearspec-v3-zstd-decode <frame> [out|-] [encCap] [decCap]"; pure 2
