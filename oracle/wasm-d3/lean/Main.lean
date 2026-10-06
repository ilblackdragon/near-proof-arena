import NearSpecV3.Wasm.Exec
import NearSpecV3.Wasm.ChunkStorage
import NearSpecV3.Wasm.DomainD3
import NearSpecV3.Wasm.Segment
/-! `nearspec-v3-wasm`: stdin `<prepaid_gas> <wasm_hex> [<receiver>,…]` per line → one outcome line per case in the
format of the nearcore harness (`oracle/wasm-d3/src/main.rs`). Method name: `main`.
Flag `--instruction-level-metering`: the finite-wasm merging ablation. Flag `--prepared-size`: print
the exact instrumented-module size (compare with the harness `prepare` mode). -/
open NearSpecV3.Wasm

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def unhex (s : String) : Option ByteArray := Id.run do
  let cs := s.toList.toArray
  if cs.size % 2 ≠ 0 then return none
  let mut out := ByteArray.empty
  for i in [0:cs.size / 2] do
    match hexVal cs[2 * i]!, hexVal cs[2 * i + 1]! with
    | some a, some b => out := out.push (UInt8.ofNat (16 * a + b))
    | _, _ => return none
  return some out

/-- The harness's optional 3rd token: a comma list of receivers, or `k=v;…` (`rcv`, `input`,
`results`, `deposit`, `balance`), see `oracle/wasm-d3/src/main.rs` `parse_opts`. -/
def parseCtx (gas : Nat) (tok : Option String) : Option CallCtx := do
  let base : CallCtx := { prepaidGas := gas }
  match tok with
  | none => pure base
  | some t =>
    if !t.contains '=' then pure { base with receivers := (t.splitOn ",").toArray }
    else
      let mut c := base
      for kv in t.splitOn ";" do
        if kv.isEmpty then continue
        match kv.splitOn "=" with
        | [k, v] =>
          match k with
          | "rcv" => c := { c with receivers := ((v.splitOn ",").filter (· ≠ "")).toArray }
          | "input" => c := { c with input := ← unhex v }
          | "results" =>
            let mut rs := #[]
            for r in (v.splitOn ",").filter (· ≠ "") do
              if r.startsWith "S" then rs := rs.push (PRes.ok (← unhex (r.drop 1).toString))
              else if r = "F" then rs := rs.push .failed
              else rs := rs.push .notReady
            c := { c with promiseResults := rs }
          | "deposit" => c := { c with attachedDeposit := ← v.toNat? }
          | "balance" => c := { c with accountBalance := ← v.toNat? }
          | _ => none
        | _ => none
      pure c

/-- `--chunk`: one line per chunk, `C <root> <n> <node>… <k> (<account> <gas> <args|-> <expected…14>)…`
(`oracle/d3-ttn` trace); prints one profile line per call (`TTN.profileLine`). The expected
columns are skipped here (compared by `oracle/d3-ttn/difftest_ttn.py`). The code is the first
argument after `--chunk` (hex file path). -/
def chunkLine (code : ByteArray) (ablate : String) (deltas : Bool) (line : String) : List String := Id.run do
  let toks := (line.splitOn " ").toArray
  if toks.size < 4 || toks[0]! != "C" then return ["unmodeled bad chunk line"]
  let some root := unhex toks[1]! | return ["unmodeled bad root"]
  let some n := toks[2]!.toNat? | return ["unmodeled bad n"]
  let mut nodes := []
  for i in [0:n] do
    match unhex toks[3 + i]! with
    | some b => nodes := b :: nodes
    | none => return ["unmodeled bad node"]
  let some k := toks[3 + n]!.toNat? | return ["unmodeled bad k"]
  let mut calls := []
  for j in [0:k] do
    let b := 4 + n + 17 * j
    let some gas := toks[b + 1]!.toNat? | return ["unmodeled bad gas"]
    let input ← match toks[b + 2]! with
      | "-" => pure ByteArray.empty
      | h => match unhex h with
        | some d => pure d
        | none => return ["unmodeled bad args"]
    calls := { account := toks[b]!, prepaid := gas, input } :: calls
  TTN.replayChunk pv86 code (TTN.mkStore nodes) root calls.reverse
    (fun gas => (gas / pv86.regularOpCost + 2) * 64 + 1000000) ablate deltas

partial def chunkLoop (code : ByteArray) (ablate : String) (deltas : Bool) (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let line := line.trimAscii.toString
  if !line.isEmpty then
    for l in chunkLine code ablate deltas line do stdout.putStrLn l
    stdout.flush
  chunkLoop code ablate deltas stdin stdout

partial def loop (bl sizeMode full cpMode : Bool) (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let line := line.trimAscii.toString
  if line.isEmpty then loop bl sizeMode full cpMode stdin stdout else
  let parts := line.splitOn " "
  match parts with
  | g :: h :: rest =>
    match g.toNat?, unhex h with
    | some gas, some code =>
      match parseCtx gas rest.head? with
      | none => stdout.putStrLn "unmodeled bad options"
      | some ctx =>
        let fuel := (gas / pv86.regularOpCost + 2) * 64 + 1000000
        stdout.putStrLn (if sizeMode then preparedSizeLine pv86 code
          else if cpMode then chargePointsLine pv86 code
          else outcome pv86 code "main" ctx fuel bl full)
    | _, _ => stdout.putStrLn "unmodeled bad input"
  | _ => stdout.putStrLn "unmodeled bad input"
  stdout.flush
  loop bl sizeMode full cpMode stdin stdout

def main (args : List String) : IO Unit := do
  if let some code := (match args with
      | "--chunk" :: path :: _ => some path
      | _ => none) then
    let some c := unhex (← IO.FS.readFile code).trimAscii.toString | throw (IO.userError "bad code hex")
    let ablate := if args.contains "--ablate-cache" then "cache"
      else if args.contains "--ablate-overlay" then "overlay" else ""
    chunkLoop c ablate (args.contains "--deltas") (← IO.getStdin) (← IO.getStdout)
    return
  loop (!args.contains "--instruction-level-metering") (args.contains "--prepared-size")
    (args.contains "--full") (args.contains "--charge-points") (← IO.getStdin) (← IO.getStdout)
