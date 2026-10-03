import ArenaCore.Interp
import ArenaCoreTests.InterpVectors

/-!
# `arena-interp-ref` — the Lean reference interpreter as an executable

Used to differentially test the Rust interpreter against the Lean
semantics.  NOT part of any certificate or of the TCB of a checked result.

```
arena-interp-ref run --code F --public F --claim F --proof F --fuel N
    prints one JSON line {"outcome": ..., "fuel_used": N, "out0": hex, "out1": hex}
    exit 0 = accept, 1 = reject, 2 = trap / out_of_fuel / decode_error
arena-interp-ref vectors OUT.json
    writes the built-in vector suite with expected results
```
-/

open ArenaCore Interp InterpVectors

def outcomeStr : Outcome → String
  | .accept => "accept"
  | .reject => "reject"
  | .trap => "trap"
  | .outOfFuel => "out_of_fuel"

def jsonStr (s : String) : String := "\"" ++ s ++ "\""

def expectJson : Expect → String
  | .decodeError => "{\"outcome\":\"decode_error\"}"
  | .ran o f a b =>
    "{\"outcome\":" ++ jsonStr (outcomeStr o) ++ ",\"fuel_used\":" ++ toString f ++
      ",\"out0\":" ++ jsonStr a.toHex ++ ",\"out1\":" ++ jsonStr b.toHex ++ "}"

def caseJson (c : Case) : String :=
  "{\"name\":" ++ jsonStr c.name ++ ",\"code\":" ++ jsonStr c.image.toHex ++
    ",\"public\":" ++ jsonStr c.pub.toHex ++ ",\"claim\":" ++ jsonStr c.claim.toHex ++
    ",\"proof\":" ++ jsonStr c.proof.toHex ++ ",\"fuel\":" ++ toString c.fuel ++
    ",\"expect\":" ++ expectJson (expect c) ++ "}"

def readBytes (path : String) : IO Bytes := do
  return (← IO.FS.readBinFile path).toList

partial def getArg (args : List String) (key : String) : Option String :=
  match args with
  | k :: v :: rest => if k == key then some v else getArg (v :: rest) key
  | _ => none

def main (args : List String) : IO UInt32 := do
  match args with
  | "vectors" :: out :: _ =>
    let body := ",\n".intercalate (cases.map caseJson)
    IO.FS.writeFile out ("{\"format\":\"npai-v1-vectors\",\"cases\":[\n" ++ body ++ "\n]}\n")
    IO.println s!"wrote {cases.length} cases to {out}"
    return 0
  | "run" :: rest =>
    let some code := getArg rest "--code" | IO.eprintln "missing --code"; return 2
    let some pubF := getArg rest "--public" | IO.eprintln "missing --public"; return 2
    let some claimF := getArg rest "--claim" | IO.eprintln "missing --claim"; return 2
    let some proofF := getArg rest "--proof" | IO.eprintln "missing --proof"; return 2
    let some fuelS := getArg rest "--fuel" | IO.eprintln "missing --fuel"; return 2
    let some fuel := fuelS.toNat? | IO.eprintln "bad --fuel"; return 2
    let c : Case := { name := "cli", image := ← readBytes code, pub := ← readBytes pubF,
                      claim := ← readBytes claimF, proof := ← readBytes proofF, fuel }
    let e := expect c
    IO.println (expectJson e)
    return match e with
      | .ran .accept .. => 0
      | .ran .reject .. => 1
      | _ => 2
  | _ =>
    IO.eprintln "usage: arena-interp-ref (run --code F --public F --claim F --proof F --fuel N | vectors OUT.json)"
    return 2
