import NearSpecV3.D3.FunctionCall
import NearSpecV3.ChunkValidationD1Out
import NearSpecV3.ChunkValidationD2Out

/-!
`nearspec-v3-check-d3-out [--d1|--d2] CASE_DIR...` — evaluates the chunk transition and prints, per
case, the verdict **and the consensus outputs**.

Modes: no flag runs the signed D3 pipeline (`checkD2CoreOut` with `d3Hooks`); `--d2` runs the signed D2
pipeline (`checkD2CoreOut` with `d2Hooks`); `--d1` runs the signed D1 pipeline (`checkD1CoreOut`). The
JSON shape is identical in all three. In `--d1` the three D2/D3-only fields are honest: `proposals` and
`bwRequests` are `[]` (D1 verifies the header's are empty and computes no list) and `wasmGas` is `0`
(D1 executes no WASM).

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

## Why `outputs` is the *computed* record

Each mode's `check…CoreOut` runs the signed checker and returns the record of values the pipeline
computed and then compared against the endorsed header (`checkD2CoreObs` for D2/D3, `checkD1CoreObs` for
D1). It is not a read-back of the header: the comparison block tests those same computed expressions, so
on acceptance the computed value and the header's value coincide. The justification is
`NearSpecV3.accepted_observable_computed`.

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

/-- Which checker the driver runs. `d3` is the default (the signed D3 pipeline); `d2` and `d1` select
the lower domains so the same JSON shape carries their outputs. -/
inductive Mode where
  | d3
  | d2
  | d1
  deriving DecidableEq, Repr

def main (args : List String) : IO UInt32 := do
  let (mode, dirs) := match args with
    | "--d2" :: rest => (Mode.d2, rest)
    | "--d1" :: rest => (Mode.d1, rest)
    | _ => (Mode.d3, args)
  for dir in dirs do
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    let r : Except String Observable :=
      match mode with
      | .d1 => checkD1CoreOut cb.toList wb.toList
      | .d2 => checkD2CoreOut d2Hooks false cb.toList wb.toList
      | .d3 => checkD2CoreOut (d3Hooks Wasm.pv86) true cb.toList wb.toList (some gAlpha)
    let (v, reason, outs) := classify r
    IO.println s!"\{\"case\": \"{esc dir}\", \"verdict\": \"{v}\", \"reason\": \"{esc reason}\", \"outputs\": {outs}}"
  return 0
