import NearSpecV3.Wasm.Exec
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

partial def loop (bl sizeMode full : Bool) (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let line := line.trimAscii.toString
  if line.isEmpty then loop bl sizeMode full stdin stdout else
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
          else outcome pv86 code "main" ctx fuel bl full)
    | _, _ => stdout.putStrLn "unmodeled bad input"
  | _ => stdout.putStrLn "unmodeled bad input"
  stdout.flush
  loop bl sizeMode full stdin stdout

def main (args : List String) : IO Unit := do
  loop (!args.contains "--instruction-level-metering") (args.contains "--prepared-size")
    (args.contains "--full") (← IO.getStdin) (← IO.getStdout)
