import NearSpecV3.Wasm.Float

/-! `nearspec-v3-test-float` — evaluate `NearSpecV3.Wasm.evalFloatOp` on literal bit patterns.

stdin, one case per line: `<op> <a-hex> <b-hex>` (op decimal; a/b the raw 32- or 64-bit patterns,
hex without `0x`). stdout, one line per case:
`<result-hex>` for a value, `trap` for a trapping conversion, `badop` for an opcode this driver
does not evaluate. Used by `oracle/wasm-d3/tests/difftest_float.py`, which compares against pinned
nearcore's own Wasmtime engine; this driver is test scaffolding, not part of the relation. -/

open NearSpecV3.Wasm

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def unhex (s : String) : Option Nat := Id.run do
  let cs := s.toList
  if cs.isEmpty then return none
  let mut acc := 0
  for c in cs do
    match hexDigit c with
    | some d => acc := acc * 16 + d
    | none => return none
  return some acc

def hexOf (n w : Nat) : String := Id.run do
  let digits := "0123456789abcdef".toList.toArray
  let mut s := ""
  for i in [0:w / 4] do
    let sh := w - 4 * (i + 1)
    s := s.push digits[(n / 2 ^ sh) % 16]!
  return s

def runLine (line : String) : String :=
  match line.splitOn " " with
  | [opS, aS, bS] =>
    match opS.toNat?, unhex aS, unhex bS with
    | some op, some a, some b =>
      if !isFloatOpNoImm op then "badop"
      else match evalFloatOp op a b with
        | some r => hexOf r ((floatResultType op).size * 8)
        | none => "trap"
    | _, _, _ => "badline"
  | _ => "badline"

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let mut out := ""
  let mut line ← stdin.getLine
  while line.length > 0 do
    out := out ++ runLine line.trimAscii.toString ++ "\n"
    line ← stdin.getLine
  IO.print out
  return 0
