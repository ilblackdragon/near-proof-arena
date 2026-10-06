import WasmPoC
/-! `wasm-poc`: stdin `<prepaid_gas> <wasm_hex>` per line → one outcome line
per case, in the same format as the nearcore harness (`oracle/wasm-d3`). -/
open WasmPoC

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

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let line := line.trimAscii.toString
  if line.isEmpty then loop stdin stdout else
  match line.splitOn " " with
  | [g, h] =>
    match g.toNat?, unhex h with
    | some gas, some code =>
      -- step budget: far above what gas allows (every loop iteration charges ≥ 1 op)
      let fuel := (gas / regularOpCost + 2) * 64 + 1000000
      stdout.putStrLn (outcome code gas fuel)
    | _, _ => stdout.putStrLn "unmodeled bad input"
  | _ => stdout.putStrLn "unmodeled bad input"
  stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
