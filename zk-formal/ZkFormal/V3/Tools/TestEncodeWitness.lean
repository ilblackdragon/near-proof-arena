import ZkFormal.V3.EncodeWitness
import ZkFormal.V3.Fast.RS

/-!
Executable check of `NearSpecV3.EncodeWitness` on real witnesses. Usage:
`nearspec-v3-test-encw DIR...` (each DIR holds `witness.bin`).

For every case: decode (`decodeWitnessFile`, `decodeStateWitness`); when decoding
succeeds evaluate `D0Shape.wf`; when it holds, check
`decodeStateWitness (encodeSW sw)` succeeds and re-encodes to `encodeSW sw`, and that
`decodeWitnessFile (encodeWitnessFile sw) = .ok (encodeSW sw, [])`. Also counts how
often `encodeSW sw` reproduces the original state-witness bytes exactly (it differs
only in `height_included` / the chunk signature, which `StateWitness` does not keep).
Normal form: on each case with `checkD0 claim witness = .ok ()`, take `s' := normW K R s`
(`keysD0 claim witness = .ok (K, R)`), re-encode `w' := encodeWitnessFile s'` and check
`D0Shape.wf s'`, `normalW claim w' = true`, `checkD0 claim w' = .ok ()`, and that `w'` equals
the reference normaliser's output `wrapW c` (`normSW K R sw = .ok c`).
Prints one JSON line of counts; exit code 1 iff a check failed or no case decoded.
-/

open NearSpec NearSpecV3 ZkFormal.V3 ReexecV3D0

def main (args : List String) : IO UInt32 := do
  let mut cases := 0
  let mut missing := 0
  let mut decodeFail := 0
  let mut decoded := 0
  let mut shapeOk := 0
  let mut shapeFail := 0
  let mut rtOk := 0
  let mut rtFail := 0
  let mut fileOk := 0
  let mut fileFail := 0
  let mut sameBytes := 0
  let mut failed : List String := []
  let mut relOk := 0
  let mut nShape := 0
  let mut nNormal := 0
  let mut nCheck := 0
  let mut nSameRef := 0
  let mut nFail := 0
  for dir in args do
    cases := cases + 1
    let path := dir ++ "/witness.bin"
    if !(← System.FilePath.pathExists path) then
      missing := missing + 1; continue
    let wb := (← IO.FS.readBinFile path).toList
    match decodeWitnessFile wb with
    | .error _ => decodeFail := decodeFail + 1
    | .ok (swb, _) =>
      match decodeStateWitness swb with
      | .error _ => decodeFail := decodeFail + 1
      | .ok sw =>
        decoded := decoded + 1
        if !D0Shape.wf sw then
          shapeFail := shapeFail + 1
        else
          shapeOk := shapeOk + 1
          let enc := encodeSW sw
          if enc == swb then sameBytes := sameBytes + 1
          match decodeStateWitness enc with
          | .ok sw' =>
            if encodeSW sw' == enc && D0Shape.wf sw' then rtOk := rtOk + 1
            else rtFail := rtFail + 1; failed := dir :: failed
          | .error _ => rtFail := rtFail + 1; failed := dir :: failed
          match decodeWitnessFile (encodeWitnessFile sw) with
          | .ok (b, codes) =>
            if b == enc && codes.isEmpty then fileOk := fileOk + 1
            else fileFail := fileFail + 1; failed := dir :: failed
          | .error _ => fileFail := fileFail + 1; failed := dir :: failed
        -- normal form (accepted cases only)
        let cpath := dir ++ "/claim.bin"
        if (← System.FilePath.pathExists cpath) then
          let cb := (← IO.FS.readBinFile cpath).toList
          if let .ok () := checkD0 cb wb then
            relOk := relOk + 1
            match (do let (K, R) ← keysD0 cb wb; let c ← normSW K R swb; pure (K, R, c) :
                Except String _) with
            | .ok (K, R, c) =>
              let s' := normW K R sw
              let w' := encodeWitnessFile s'
              let ok1 := D0Shape.wf s'
              let ok2 := normalW cb w'
              let ok3 := match checkD0 cb w' with | .ok () => true | .error _ => false
              let ok4 := w' == wrapW c
              if ok1 then nShape := nShape + 1
              if ok2 then nNormal := nNormal + 1
              if ok3 then nCheck := nCheck + 1
              if ok4 then nSameRef := nSameRef + 1
              if !(ok1 && ok2 && ok3 && ok4) then nFail := nFail + 1; failed := dir :: failed
            | .error _ => nFail := nFail + 1; failed := dir :: failed
  let fl := ", ".intercalate (failed.reverse.take 10 |>.map (fun d => "\"" ++ d ++ "\""))
  IO.println (s!"\{\"cases\": {cases}, \"missing\": {missing}, \"decode_fail\": {decodeFail}, " ++
    s!"\"decoded\": {decoded}, \"d0shape_true\": {shapeOk}, \"d0shape_false\": {shapeFail}, " ++
    s!"\"sw_roundtrip_ok\": {rtOk}, \"sw_roundtrip_fail\": {rtFail}, " ++
    s!"\"file_roundtrip_ok\": {fileOk}, \"file_roundtrip_fail\": {fileFail}, " ++
    s!"\"bytes_equal_original\": {sameBytes}, \"rel_ok\": {relOk}, " ++
    s!"\"normal_d0shape\": {nShape}, \"normal_normalW\": {nNormal}, " ++
    s!"\"normal_checkD0_ok\": {nCheck}, \"normal_eq_reference\": {nSameRef}, " ++
    s!"\"normal_fail\": {nFail}, \"failed\": [{fl}]}")
  return (if rtFail + fileFail + nFail > 0 || decoded == 0 then 1 else 0)
