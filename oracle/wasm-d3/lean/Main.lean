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

partial def loop (bl sizeMode : Bool) (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let line := line.trimAscii.toString
  if line.isEmpty then loop bl sizeMode stdin stdout else
  let parts := line.splitOn " "
  match parts with
  | g :: h :: rest =>
    let receivers := match rest with
      | [r] => (r.splitOn ",").toArray
      | _ => #[]
    match g.toNat?, unhex h with
    | some gas, some code =>
      let fuel := (gas / pv86.regularOpCost + 2) * 64 + 1000000
      stdout.putStrLn (if sizeMode then preparedSizeLine pv86 code
        else outcome pv86 code "main" gas fuel bl receivers)
    | _, _ => stdout.putStrLn "unmodeled bad input"
  | _ => stdout.putStrLn "unmodeled bad input"
  stdout.flush
  loop bl sizeMode stdin stdout

def main (args : List String) : IO Unit := do
  loop (!args.contains "--instruction-level-metering") (args.contains "--prepared-size")
    (← IO.getStdin) (← IO.getStdout)
