import Lean.Data.Json
import NearSpecV3

/-!
Leaf differential tests: every leaf module of NearSpecV3 against vectors that
nearcore's own code produced (`near-arena-oracle-v3 vectors`,
`oracle/fixtures/v3/vectors/*.json`). Usage: `nearspec-v3-leaftest DIR`.
-/

open Lean NearSpecV3

def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

def unhex (s : String) : List UInt8 :=
  let rec go : List Char → List UInt8
    | a :: b :: rest => UInt8.ofNat (hexVal a * 16 + hexVal b) :: go rest
    | _ => []
  go s.toList

def getStr (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
def getNat (j : Json) (k : String) : Nat := (j.getObjValAs? Nat k).toOption.getD 0
def getArr (j : Json) (k : String) : Array Json := (j.getObjValAs? (Array Json) k).toOption.getD #[]

def testChaCha (dir : String) : IO (Nat × Nat) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile (dir ++ "/chacha.json")))
  let mut ok := 0
  let mut bad := 0
  for s in getArr j "streams" do
    let seed := unhex (getStr s "seed")
    let want : Array Nat := (s.getObjValAs? (Array Nat) "u32").toOption.getD #[]
    let mut r := Rng.ofSeed seed
    let mut got : Array Nat := #[]
    for _ in [0:want.size] do
      let (w, r') := r.nextU32
      got := got.push w
      r := r'
    if got == want then ok := ok + 1 else bad := bad + 1
  for s in getArr j "shuffles" do
    let seed := unhex (getStr s "seed")
    let n := getNat s "n"
    let want : List Nat := ((s.getObjValAs? (Array Nat) "perm").toOption.getD #[]).toList
    if shuffleWithSeed (List.range n) seed == some want then ok := ok + 1 else bad := bad + 1
  return (ok, bad)

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "../../../oracle/fixtures/v3/vectors"
  let (ok, bad) ← testChaCha dir
  IO.println s!"chacha: {ok} ok, {bad} bad"
  return (if bad == 0 then 0 else 1)
