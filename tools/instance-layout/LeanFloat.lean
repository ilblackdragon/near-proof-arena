import NearSpecV3.Wasm.Float
/-!
UQ-003: evaluate the Lean float kernel (`NearSpecV3/Wasm/Float.lean`) on the call list of
`nan_probe.py` (`<f32|f64>.<op> <bits> [<bits>]` per line) and print `<line> -> <result bits>`,
the same format as `instance-layout-probe call`. Run from `spec/lean/v3`:

    lake env lean --run ../../../tools/instance-layout/LeanFloat.lean CALLS > lean.txt
-/
open NearSpecV3.Wasm NearSpecV3.Wasm.Fmt

def evalCall (name : String) (args : List Nat) : Option Nat :=
  match name.splitOn ".", args with
  | [t, op], [a, b] =>
    let f := if t == "f32" then f32 else f64
    match op with
    | "add" => some (add f a b) | "sub" => some (sub f a b) | "mul" => some (mul f a b)
    | "div" => some (div f a b) | "min" => some (min f a b) | "max" => some (max f a b)
    | "copysign" => some (copysign f a b) | _ => none
  | ["f64", "promote"], [a] => some (promote a)
  | ["f32", "demote"], [a] => some (demote a)
  | [t, op], [a] =>
    let f := if t == "f32" then f32 else f64
    match op with
    | "sqrt" => some (sqrt f a) | "ceil" => some (ceil f a) | "floor" => some (floor f a)
    | "trunc" => some (trunc f a) | "nearest" => some (nearest f a) | "abs" => some (abs f a)
    | "neg" => some (neg f a) | _ => none
  | _, _ => none

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: LeanFloat.lean CALLS"; return 2
  for line in (← IO.FS.lines path) do
    match line.splitOn " " with
    | name :: rest =>
      let some ns := rest.mapM String.toNat? | IO.eprintln s!"bad line {line}"; return 2
      let some r := evalCall name ns | IO.eprintln s!"unknown call {line}"; return 2
      IO.println s!"{line} -> {r}"
    | [] => pure ()
  return 0
