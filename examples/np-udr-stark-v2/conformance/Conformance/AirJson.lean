import Lean.Data.Json
import ZkFormal.Air.Export
import ZkFormal.V2.Export

/-!
# Conformance.AirJson — reading the `np-air-v1` export back into an `Air`

`Air.exportJson` (lane L4, `ZkFormal.Air.Export`) is the normative writer;
this is its inverse, used only by the conformance harness (it is not part of
the verifier model and not part of soundness).

The export lists `Table.allConstraints` = user constraints followed by the
generated multiplicity-bit booleanity constraints.  The reader strips the
trailing `Σ |mult|` constraints and **requires** them to be exactly
`Table.bitConstraints` of the parsed table, so that the `Air` handed to the
verifier re-exports to the same text.  `roundTrip` checks this end to end:
`Json.parse (exportJson (ofJson j)) == j`.
-/

namespace Conformance

open Lean ZkFormal.Air

private def field (j : Json) (k : String) : Except String Json := j.getObjVal? k

private def arr (j : Json) (k : String) : Except String (List Json) := do
  return (← (← field j k).getArr?).toList

private def nat (j : Json) (k : String) : Except String Nat := do (← field j k).getNat?

/-- An expression in prefix form. -/
partial def exprOfJson (j : Json) : Except String Expr := do
  let a := (← j.getArr?).toList
  match a with
  | [] => throw "empty expression"
  | op :: args =>
    match (← op.getStr?), args with
    | "c", [n] => return .const (← n.getNat?)
    | "v", [c, nx] =>
      let nx ← nx.getNat?
      if nx > 1 then throw s!"bad next flag {nx}"
      return .col (← c.getNat?) (nx == 1)
    | "p", [i] => return .pub (← i.getNat?)
    | "first", [] => return .isFirst
    | "last", [] => return .isLast
    | "trans", [] => return .isTransition
    | "+", [x, y] => return .add (← exprOfJson x) (← exprOfJson y)
    | "*", [x, y] => return .mul (← exprOfJson x) (← exprOfJson y)
    | "-", [x] => return .neg (← exprOfJson x)
    | o, _ => throw s!"bad expression operator/arity: {o} {j.compress}"

def interactionOfJson (j : Json) : Except String Interaction := do
  let bus ← nat j "bus"
  let send ← (← field j "send").getBool?
  let mult ← (← arr j "mult").mapM exprOfJson
  let msg ← (← arr j "msg").mapM exprOfJson
  return { bus, mult, msg, send }

def tableOfJson (j : Json) : Except String Table := do
  let width ← nat j "width"
  let maxLog ← nat j "maxLog"
  let interactions ← (← arr j "interactions").mapM interactionOfJson
  let all ← (← arr j "constraints").mapM exprOfJson
  let nb := (interactions.map (·.mult.length)).sum
  if all.length < nb then throw "fewer constraints than multiplicity bits"
  let T : Table := { width, constraints := all.take (all.length - nb), interactions, maxLog }
  if all.drop (all.length - nb) != T.bitConstraints then
    throw "trailing constraints are not the generated bit constraints (Table.bitConstraints)"
  return T

def airOfJson (j : Json) : Except String Air := do
  let fmt ← (← field j "format").getStr?
  if fmt != "np-air-v1" then throw s!"unknown format {fmt}"
  let numBuses ← nat j "numBuses"
  let numPub ← nat j "numPub"
  let tables ← (← arr j "tables").mapM tableOfJson
  return { tables, numBuses, numPub }

/-- Parse `np-air-v1` text. -/
def parseAir (s : String) : Except String Air := do
  airOfJson (← Json.parse s)

/-- Parse, then check that `Air.exportJson` of the result is the same JSON
value as the input (and report whether it is also byte-identical, modulo a
trailing newline). Returns the AIR and the byte-identity flag. -/
def parseAirChecked (s : String) : Except String (Air × Bool) := do
  let j ← Json.parse s
  let A ← airOfJson j
  let s' := A.exportJson
  let j' ← Json.parse s'
  if j' != j then throw "re-export of the parsed AIR is not JSON-equal to the input"
  return (A, s' == s || s' ++ "\n" == s)

/-! ## `np-air-v2` (`ZkFormal.V2.AirP.exportJson`, FORMATS.md §8.1) -/

open ZkFormal.V2 in
private def optNat (j : Json) (k : String) : Except String (Option Nat) := do
  let v ← field j k
  if v.isNull then return none else return some (← v.getNat?)

open ZkFormal.V2 in
def pubSegOfJson (j : Json) : Except String PubSeg := do
  return { bus := ← nat j "bus", send := ← (← field j "send").getBool?, width := ← nat j "width",
           countAt := ← nat j "countAt", start := ← nat j "start",
           msgPrefix := ← (← arr j "prefix").mapM (·.getNat?),
           indexBase := ← optNat j "indexBase", startAt := ← optNat j "startAt" }

open ZkFormal.V2 in
def airPOfJson (j : Json) : Except String AirP := do
  let fmt ← (← field j "format").getStr?
  if fmt != "np-air-v2" then throw s!"unknown format {fmt}"
  let numBuses ← nat j "numBuses"
  let numPub ← nat j "numPub"
  let tables ← (← arr j "tables").mapM tableOfJson
  let pubSegs ← (← arr j "pubSegs").mapM pubSegOfJson
  let maxPub ← nat j "maxPub"
  return { tables, numBuses, numPub, pubSegs, maxPub }

open ZkFormal.V2 in
/-- Parse `np-air-v2`, check `AirP.exportJson` re-exports to the same JSON value,
and report byte identity (as `parseAirChecked`). -/
def parseAirPChecked (s : String) : Except String (AirP × Bool) := do
  let j ← Json.parse s
  let A ← airPOfJson j
  let s' := A.exportJson
  let j' ← Json.parse s'
  if j' != j then throw "re-export of the parsed AirP is not JSON-equal to the input"
  return (A, s' == s || s' ++ "\n" == s)

end Conformance
