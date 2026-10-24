import NearSpecV3.D3.FunctionCall
import NearSpecV3.ChunkValidationD2Out

/-!
`nearspec-v3-check-d3-out [--d2] CASE_DIR...` — evaluates the chunk transition and prints, per case, the
verdict **and the consensus outputs**.

This is the observable-emitting companion to `nearspec-v3-check-d3`. The plain driver prints only
`{"case", "verdict", "reason"}`, so nothing it produces can be diffed against nearcore's gas/roots/logs.
This driver prints them.

## Output line

```json
{"case": dir, "verdict": "accept"|"reject"|"out_of_domain", "reason": "...",
 "outputs": null | {"stateRoot": "hex", "outcomeRoot": "hex", "gasBurnt": n, "balanceBurnt": n,
                    "outgoingReceiptsRoot": "hex", "proposals": ["hex", ...], "txRoot": "hex",
                    "encodedMerkleRoot": "hex", "encodedLength": n,
                    "congestion": {...}, "bwRequests": [...],
                    "logs": ["hex", ...], "receiptCount": n, "wasmGas": n}}
```

`outputs` is non-null exactly when the case is accepted. On a rejection the signed checker's reason names
the header field that disagreed; the outputs are `null` because the signed checker does not expose its
computed values on a failing path (see `NearSpecV3.ChunkValidationD2Out`'s module docstring, "Does not buy
(1)").

## Why `outputs` is the *endorsed header's* record

`checkD2CoreOut` runs the signed checker and, on acceptance, returns the endorsed header's consensus
fields. The signed checker's comparison block proved those fields equal the values it computed, so on
acceptance the two coincide. Emitting the header's record therefore emits the computed output; the
justification is `NearSpecV3.accepted_observable_agrees`.

## Exit status

`0` always: this is a report driver. The caller decides what a disagreement means; a non-zero exit would
make a shard's failure indistinguishable from a checker crash. -/

open NearSpecV3 NearSpecV3.D2 NearSpecV3.D3

def esc (s : String) : String := s.replace "\\" "\\\\" |>.replace "\"" "\\\""

/-- Lowercase hex, as the Rust oracle and the difftest scripts emit. -/
def hexOf (bs : List UInt8) : String :=
  let d := fun (n : Nat) => if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  String.ofList (bs.flatMap fun b => [d (b.toNat / 16), d (b.toNat % 16)])

/-- `Bytes` is `List UInt8` (`NearSpec.Bytes`), so the helper applies directly. -/
def hexB : NearSpec.Bytes → String := hexOf

def jsonList (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"

def jsonBytesList (xs : List NearSpec.Bytes) : String := jsonList (xs.map fun b => "\"" ++ hexB b ++ "\"")

/-- A `Congestion` as JSON. Field order follows the structure; the difftest compares field by field. -/
def jsonCongestion (c : Congestion) : String :=
  "{" ++ "\"delayedGas\":" ++ toString c.delayedGas ++
  ",\"bufferedGas\":" ++ toString c.bufferedGas ++
  ",\"receiptBytes\":" ++ toString c.receiptBytes ++
  ",\"allowedShard\":" ++ toString c.allowedShard ++ "}"

/-- A `BwRequest` as JSON. -/
def jsonBwRequest (r : BwRequest) : String :=
  "{" ++ "\"toShard\":" ++ toString r.toShard ++
  ",\"bitmap\":\"" ++ hexB r.bitmap ++ "\"}"

/-- The outputs record as one JSON object. -/
def jsonObservable (o : Observable) : String :=
  "{" ++ "\"stateRoot\":\"" ++ hexB o.stateRoot ++ "\"" ++
  ",\"outcomeRoot\":\"" ++ hexB o.outcomeRoot ++ "\"" ++
  ",\"gasBurnt\":" ++ toString o.gasBurnt ++
  ",\"balanceBurnt\":" ++ toString o.balanceBurnt ++
  ",\"outgoingReceiptsRoot\":\"" ++ hexB o.outgoingReceiptsRoot ++ "\"" ++
  ",\"proposals\":" ++ jsonBytesList o.proposals ++
  ",\"txRoot\":\"" ++ hexB o.txRoot ++ "\"" ++
  ",\"encodedMerkleRoot\":\"" ++ hexB o.encodedMerkleRoot ++ "\"" ++
  ",\"encodedLength\":" ++ toString o.encodedLength ++
  ",\"congestion\":" ++ jsonCongestion o.congestion ++
  ",\"bwRequests\":" ++ jsonList (o.bwRequests.map jsonBwRequest) ++
  ",\"logs\":" ++ jsonBytesList o.logs ++
  ",\"receiptCount\":" ++ toString o.receiptCount ++
  ",\"wasmGas\":" ++ toString o.wasmGas ++ "}"

def classify : Except String Observable → String × String × String
  | .ok o => ("accept", "", jsonObservable o)
  | .error e => (if e.startsWith "out of domain" then "out_of_domain" else "reject", e, "null")

def main (args : List String) : IO UInt32 := do
  let (d2, dirs) := match args with
    | "--d2" :: rest => (true, rest)
    | _ => (false, args)
  for dir in dirs do
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    let r : Except String Observable :=
      if d2 then checkD2CoreOut d2Hooks false cb.toList wb.toList
      else checkD2CoreOut (d3Hooks Wasm.pv86) true cb.toList wb.toList (some gAlpha)
    let (v, reason, outs) := classify r
    IO.println s!"\{\"case\": \"{esc dir}\", \"verdict\": \"{v}\", \"reason\": \"{esc reason}\", \"outputs\": {outs}}"
  return 0
