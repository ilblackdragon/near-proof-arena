import NearSpecV3.D2.State

/-!
`nearspec-v3-test-trie-d2 FILE` — checks the D2 trie finalize (`PTrie.upsert`, `PTrie.del` with
squash, `Ovl.finalize`) against vectors from an independent canonical-trie builder
(`CASE` / `root` / `node` / `chg key value|-` / `exp` lines; the expected root is the
canonical trie of the updated key→value map, with nearcore's node encoding and memory usage).
-/

open NearSpec NearSpecV3 NearSpecV3.D2

def hexNib (c : Char) : Nat :=
  if c.isDigit then c.toNat - 48 else c.toNat - 87

def unhex (s : String) : Bytes :=
  let cs := s.toList
  let rec go : List Char → Bytes
    | a :: b :: rest => UInt8.ofNat (hexNib a * 16 + hexNib b) :: go rest
    | _ => []
  go cs

def hex (b : Bytes) : String :=
  String.join (b.map fun x => let s := (Nat.toDigits 16 x.toNat).asString; if s.length == 1 then "0" ++ s else s)

structure Case where
  root : Bytes := []
  nodes : List Bytes := []
  chg : List (Bytes × Option Bytes) := []
  exp : Bytes := []

def main (args : List String) : IO UInt32 := do
  let txt ← IO.FS.readFile (args.headD "trievec.txt")
  let mut cases : List Case := []
  let mut cur : Case := {}
  for line in txt.splitOn "\n" do
    match line.splitOn " " with
    | ["CASE"] => if !cur.exp.isEmpty || !cur.nodes.isEmpty then cases := cases ++ [cur]; cur := {}
    | ["root", h] => cur := { cur with root := unhex h }
    | ["node", h] => cur := { cur with nodes := cur.nodes ++ [unhex h] }
    | ["chg", k, v] => cur := { cur with chg := cur.chg ++ [(unhex k, if v == "-" then none else if v == "." then some [] else some (unhex v))] }
    | ["exp", h] => cur := { cur with exp := unhex h }
    | _ => pure ()
  cases := cases ++ [cur]
  let mut bad := 0
  let mut i := 0
  for c in cases do
    let t := revealTrie c.nodes c.root
    let o : Ovl := ⟨t, c.chg, [], 0⟩
    match o.finalize with
    | .ok r => if r != c.exp then bad := bad + 1; IO.println s!"case {i}: got {hex r} want {hex c.exp}"
    | .error e => bad := bad + 1; IO.println s!"case {i}: error {e}"
    i := i + 1
  IO.println s!"{cases.length} cases, {bad} mismatches"
  return (if bad == 0 then 0 else 1)
