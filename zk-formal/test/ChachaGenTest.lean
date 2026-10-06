import Lean.Data.Json
import ZkFormal.Chacha.Gen

/-! Executable check of the honest ChaCha20 trace generator (run from `zk-formal/`:
`lake env lean --run test/ChachaGenTest.lean`).  Not part of the library.

Requests cover the first 32+ words of several streams of
`oracle/fixtures/v3/vectors/chacha.json` (key = `leWords seed`, block `ctr = k / 16`);
every constraint is evaluated on every row, every provided word is compared with the json
stream, and single-cell mutants must violate some constraint. -/

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Gen ZkFormal.Chacha.Table

/-- Kernel check of the spec against the first stream (`decide +kernel`). -/
example : (NearSpecV3.chachaBlock [1500564434, 1723811835, 101182958, 3846506349, 1097655455,
    2445571016, 844764872, 1895816817] 0).take 4 = [3609399144, 2273540435, 2450903282, 3503564609] := by
  decide +kernel

def mkTrace (reqs : List Req) : Trace Fp :=
  let rows := honestRows reqs
  let log := honestLog reqs
  let arr : Array (Array Fp) := (List.range (2 ^ log)).toArray.map fun r =>
    (List.range width).toArray.map fun c => Fp.ofNat (rowCell (rows.getD r .pad) c)
  ⟨fun _ => log, fun _ r c => (arr.getD r #[]).getD c 0⟩

def checkRows (tr : Trace Fp) (rows : List Nat) : List (Nat × Nat) := Id.run do
  let mut bad := []
  let cs := constraints.toArray
  for r in rows do
    for i in List.range cs.size do
      if (cs[i]!).eval tr 0 r [] != 0 then bad := (r, i) :: bad
  return bad.reverse

def checkConstraints (tr : Trace Fp) : List (Nat × Nat) := checkRows tr (List.range (tr.height 0))

/-- Active messages `(row, multiplicity, message as Nats)`. -/
def msgsOut (tr : Trace Fp) : List (Nat × Nat × List Nat) := Id.run do
  let mut out := []
  for r in List.range (tr.height 0) do
    for it in interactions 0 do
      let m := it.multNat tr 0 r []
      if m != 0 then out := (r, m, it.msg.map (fun e => (e.eval tr 0 r []).toNat)) :: out
  return out.reverse

def hexByte (s : String) (i : Nat) : Nat :=
  let d := fun (c : Char) => if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
  d s.toList[2 * i]! * 16 + d s.toList[2 * i + 1]!

def main : IO Unit := do
  let txt ← IO.FS.readFile "../oracle/fixtures/v3/vectors/chacha.json"
  let j ← IO.ofExcept (Lean.Json.parse txt)
  let streams ← IO.ofExcept (j.getObjValAs? (Array Lean.Json) "streams")
  let mut reqs : List Req := []
  let mut words : List (List Nat × List Nat) := []
  for si in [0, 1, 2] do
    let s := streams[si]!
    let seed ← IO.ofExcept (s.getObjValAs? String "seed")
    let u ← IO.ofExcept (s.getObjValAs? (List Nat) "u32")
    let key := NearSpecV3.leWords ((List.range 32).map fun i => (hexByte seed i).toUInt8)
    words := words ++ [(key, u)]
    for ctr in [0, 1] do
      -- stream 0: every word; others: a pattern
      let used := (List.range 16).map fun w => si == 0 || (w + ctr + si) % 3 != 0
      reqs := reqs ++ [⟨key, ctr, used⟩]
  let tr := mkTrace reqs
  IO.println s!"requests {reqs.length} rows {(honestRows reqs).length} height {tr.height 0} constraints {constraints.length}"
  let bad := checkConstraints tr
  IO.println s!"violations: {bad.length} first: {bad.take 10}"
  -- messages vs the json streams
  let out := msgsOut tr
  let mut wrong := 0
  for (_, m, msg) in out do
    let key := (List.range 8).map fun q => msg[2 * q]! + 65536 * msg[2 * q + 1]!
    let ctr := msg[16]!; let idx := msg[17]!; let w := msg[18]! + 65536 * msg[19]!
    match words.find? (·.1 == key) with
    | some (_, u) => if m != 1 || u[16 * ctr + idx]! != w then wrong := wrong + 1
    | none => wrong := wrong + 1
  let nUsed := (reqs.map fun R => (R.used.filter id).length).sum
  IO.println s!"messages {out.length} (expected {nUsed}), mismatches vs json: {wrong}"
  let expN := (expected reqs).map fun l => l.map Fp.toNat
  IO.println s!"expected list matches trace messages: {expN == out.map (·.2.2)}"
  -- mutants: one cell + 1
  let probes := [(0, 0), (0, 40), (1, 33), (1, 232), (2, 5), (2, 70), (3, 225), (5, 200),
    (40, 252), (40, 265), (81, 260), (82, 100), (83, 228), (84, 268), (85, 2), (86, 250),
    (100, 0), (171, 271), (600, 250)]
  let mut caught := 0
  let mut missed := []
  for (r, c) in probes do
    let tr' : Trace Fp := ⟨tr.log, fun t r' c' =>
      if r' = r ∧ c' = c then tr.cell t r' c' + (1 : Fp) else tr.cell t r' c'⟩
    let h := tr.height 0
    if (checkRows tr' [(r + h - 1) % h, r]).length > 0 then caught := caught + 1 else missed := (r, c) :: missed
  IO.println s!"mutants caught {caught}/{probes.length} missed {missed}"
