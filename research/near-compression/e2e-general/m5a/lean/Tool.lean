import StateM5a.Air
import StateM5a.St
import StateM5a.Tmpl
import StateM5a.StHostIf
import StateM5a.Stc
import NearSpecV3.D2.State
import Lean.Data.Json

/-! `m5a-tool air D AIR_JSON NAMES_JSON`: export the M5a AIR (depth-`D` working-set tree) and its
column names; `m5a-tool airb …` the same for the M5b AIR (`St.m5bAir`: plus the STATE rows).

`m5a-tool apply STATE_JSON`: the spec oracle for a state-access file (`extract_state.py`'s format,
or a synthetic one): reveal the pre-state trie from `nodes_read` (`revealTrie`), apply the
`changes` in the spec's order (`applyChanges ∘ sortKV`, as `Ovl.finalize`) and print the root
(`rootHash`) as hex — the root the trace generator's transcription must reach. -/

open StateM5a NearSpec NearSpecV3.D2

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def unhex (s : String) : Bytes :=
  let rec go : List Char → Bytes
    | a :: b :: rest => UInt8.ofNat (16 * hexVal a + hexVal b) :: go rest
    | _ => []
  go s.toList

def hex (b : Bytes) : String :=
  let d (n : Nat) : Char := "0123456789abcdef".get ⟨n⟩
  String.mk (b.flatMap fun x => [d (x.toNat / 16), d (x.toNat % 16)])

def applyOracle (path : String) : IO UInt32 := do
  let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
  let nodes ← IO.ofExcept (j.getObjValAs? (Array String) "nodes_read")
  let pre ← IO.ofExcept (j.getObjValAs? String "pre_root")
  let chs ← IO.ofExcept (j.getObjValAs? (Array Lean.Json) "changes")
  let mut cs : List (Bytes × Option Bytes) := []
  for c in chs do
    let k ← IO.ofExcept (c.getArrVal? 0 >>= (·.getStr?))
    let v ← IO.ofExcept (c.getArrVal? 1)
    let vb : Option Bytes := match v.getStr? with
      | .ok s => some (unhex s)
      | .error _ => none
    cs := cs ++ [(unhex k, vb)]
  let pr := unhex pre
  let t0 : Option PTrie := if pr == emptyRoot then none else some (revealTrie (nodes.toList.map unhex) pr)
  match applyChanges t0 (sortKV cs) with
  | some t => IO.println (hex (rootHash t)); return 0
  | none => IO.println "FAIL (applyChanges: unrevealed node)"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["air", d, out, names] =>
    let D := d.toNat!
    IO.FS.writeFile out (ZkFormal.Air.Air.exportJson (m5aAir D))
    IO.FS.writeFile names (namesJson D)
    let A := m5aAir D
    for (nm, t) in tableNames.zip A.tables do
      IO.println s!"{nm}: width {t.width}, constraints {t.allConstraints.length}, interactions {t.interactions.length}"
    return 0
  | ["airb", d, out, names] =>
    -- M5b: the M5a tables plus the first STATE rows (`STB`, `STW`)
    let D := d.toNat!
    IO.FS.writeFile out (ZkFormal.Air.Air.exportJson (m5bAir D))
    IO.FS.writeFile names (namesJsonB D)
    let A := m5bAir D
    for (nm, t) in tableNamesB.zip A.tables do
      IO.println s!"{nm}: width {t.width}, constraints {t.allConstraints.length}, interactions {t.interactions.length}"
    return 0
  | ["tmpl-if", d, out, names] =>
    -- B-T1: the INTAKE + FINAL template (`Tmpl.m5tIF`)
    let D := d.toNat!
    IO.FS.writeFile out (ZkFormal.Air.Air.exportJson (m5tIF D))
    IO.FS.writeFile names (namesJsonT D tableNamesIF)
    for (nm, t) in tableNamesIF.zip (m5tIF D).tables do
      IO.println s!"{nm}: width {t.width}, constraints {t.allConstraints.length}, interactions {t.interactions.length}"
    return 0
  | ["tmpl-seg", d, out, names] =>
    -- B-T1: the STATE segment template (`Tmpl.m5tSeg`)
    let D := d.toNat!
    IO.FS.writeFile out (ZkFormal.Air.Air.exportJson (m5tSeg D))
    IO.FS.writeFile names (namesJsonT D tableNamesSeg)
    for (nm, t) in tableNamesSeg.zip (m5tSeg D).tables do
      IO.println s!"{nm}: width {t.width}, constraints {t.allConstraints.length}, interactions {t.interactions.length}"
    return 0
  | ["tmpl-segh", d, out, names] =>
    -- B-T1 item 3: the STATE segment template fed by lane A's HOST rows (`StHostIf.m5tSegH`)
    let D := d.toNat!
    IO.FS.writeFile out (ZkFormal.Air.Air.exportJson (m5tSegH D))
    IO.FS.writeFile names (namesJsonH D)
    for (nm, t) in tableNamesSegH.zip (m5tSegH D).tables do
      IO.println s!"{nm}: width {t.width}, constraints {t.allConstraints.length}, interactions {t.interactions.length}"
    return 0
  | ["tmpl-segc", d, out, names] =>
    -- B-T3: the STATE segment template with the `stRoot` opening (`Stc.m5tSegC`: + `STC`, `SRNG`)
    let D := d.toNat!
    IO.FS.writeFile out (ZkFormal.Air.Air.exportJson (m5tSegC D))
    IO.FS.writeFile names (namesJsonC D)
    for (nm, t) in tableNamesSegC.zip (m5tSegC D).tables do
      IO.println s!"{nm}: width {t.width}, constraints {t.allConstraints.length}, interactions {t.interactions.length}"
    return 0
  | ["apply", st] => applyOracle st
  | _ =>
    IO.eprintln "usage: m5a-tool air|airb|tmpl-if|tmpl-seg|tmpl-segh|tmpl-segc D AIR_JSON NAMES_JSON | m5a-tool apply STATE_JSON"
    return 2
