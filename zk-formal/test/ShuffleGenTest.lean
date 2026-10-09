import Lean.Data.Json
import ZkFormal.Chacha.Shuffle.Gen

/-! Executable check of the honest shuffle trace (`lake env lean --run test/ShuffleGenTest.lean`).
Not part of the library.

For shuffles of `oracle/fixtures/v3/vectors/chacha.json` (`{n, perm, seed}`; the list `[0..n)` is
shuffled with `ChaCha20Rng::from_seed(seed)`), one instance per vector (lid = vector index,
kstart = 0): every constraint is evaluated on every row, the memory bus must balance inside the
table, the outputs must equal the json permutation (and `NearSpecV3.shuffle`), and single-cell
mutants must violate a constraint or unbalance the memory bus. -/

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Shuffle.Table ZkFormal.Chacha.Shuffle.Gen

def busIn : Nat := 0
def busOut : Nat := 1
def busMem : Nat := 2
def busGen : Nat := 3
def busShuf : Nat := 4
def iss : List Interaction := interactions busIn busOut busMem busGen busShuf

def mkTrace (insts : List SInst) : Trace Fp :=
  let rows := honestRows insts
  let log := honestLog insts
  let arr : Array (Array Fp) := (List.range (2 ^ log)).toArray.map fun r =>
    (List.range width).toArray.map fun c => Fp.ofNat (rowCell (rows.getD r .pad) r c)
  ⟨fun _ => log, fun _ r c => (arr.getD r #[]).getD c 0⟩

def checkConstraints (tr : Trace Fp) : List (Nat × Nat) := Id.run do
  let mut bad := []
  let cs := constraints.toArray
  for r in List.range (tr.height 0) do
    for i in List.range cs.size do
      if (cs[i]!).eval tr 0 r [] != 0 then bad := (r, i) :: bad
  return bad.reverse

/-- Active messages `(bus, send, message)` (multiplicity bits are checked ≤ 1). -/
def msgs (tr : Trace Fp) : List (Nat × Bool × List Nat) := Id.run do
  let mut out := []
  for r in List.range (tr.height 0) do
    for it in iss do
      if it.multNat tr 0 r [] != 0 then
        out := (it.bus, it.send, it.msg.map (fun e => (e.eval tr 0 r []).toNat)) :: out
  return out.reverse

def memBalanced (ms : List (Nat × Bool × List Nat)) : Bool :=
  let mem := ms.filter (·.1 == busMem)
  let sends := (mem.filter (·.2.1)).map (·.2.2)
  let recvs := (mem.filter (! ·.2.1)).map (·.2.2)
  sends.length == recvs.length && sends.all (fun m => sends.count m == recvs.count m)

def hexByte (s : String) (i : Nat) : Nat :=
  let d := fun (c : Char) => if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
  d s.toList[2 * i]! * 16 + d s.toList[2 * i + 1]!

def main : IO Unit := do
  let txt ← IO.FS.readFile "../oracle/fixtures/v3/vectors/chacha.json"
  let j ← IO.ofExcept (Lean.Json.parse txt)
  let shs ← IO.ofExcept (j.getObjValAs? (Array Lean.Json) "shuffles")
  let mut insts : List SInst := []
  let mut perms : List (List Nat) := []
  for k in [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 20, 31, 2, 1] do
    let s := shs[k]!
    let n ← IO.ofExcept (s.getObjValAs? Nat "n")
    let perm ← IO.ofExcept (s.getObjValAs? (List Nat) "perm")
    let seed ← IO.ofExcept (s.getObjValAs? String "seed")
    if n ≥ 1 then
      let key := NearSpecV3.leWords ((List.range 32).map fun i => (hexByte seed i).toUInt8)
      insts := insts ++ [⟨k, key, 0, List.range n⟩]
      perms := perms ++ [perm]
  let tr := mkTrace insts
  IO.println s!"instances {insts.length} rows {(honestRows insts).length} height {tr.height 0} constraints {constraints.length}"
  let bad := checkConstraints tr
  IO.println s!"violations: {bad.length} first: {bad.take 10}"
  let ms := msgs tr
  IO.println s!"memory bus balanced: {memBalanced ms}"
  -- outputs vs json and vs the spec
  let mut wrongJson := 0
  let mut wrongSpec := 0
  for (I, perm) in insts.zip perms do
    let outs := (ms.filter fun m => m.1 == busOut && m.2.2[0]! == I.lid).map (·.2.2)
    let got := (List.range I.L).map fun x => ((outs.find? (·[1]! == x)).map (·[2]!)).getD 999999
    if got != perm then wrongJson := wrongJson + 1
    match NearSpecV3.shuffle I.vals (rngAt I.key 0) with
    | some (l', _) => if l' != got then wrongSpec := wrongSpec + 1
    | none => wrongSpec := wrongSpec + 1
  IO.println s!"outputs vs json perms: {wrongJson} wrong; vs NearSpecV3.shuffle: {wrongSpec} wrong"
  let nGen := (ms.filter (·.1 == busGen)).length
  let nShuf := (ms.filter (·.1 == busShuf)).length
  IO.println s!"gen_index receives {nGen}, shuffle headers {nShuf}"
  -- mutants: one cell + 1 (must break a constraint or the memory balance)
  -- (t2 is free on rows without a second read, so a t2 probe is placed on a row with s2 = 1 only)
  let probes := [(0, 25), (0, 26), (1, 5), (1, 27), (1, 28), (2, 22), (3, 4), (3, 72),
    (4, 75), (5, 76), (6, 3), (6, 2), (7, 74), (8, 23), (10, 0), (12, 30), (15, 60)]
  let mut caught := 0
  let mut missed := []
  for (r, c) in probes do
    let tr' : Trace Fp := ⟨tr.log, fun t r' c' =>
      if r' == r && c' == c then tr.cell t r' c' + 1 else tr.cell t r' c'⟩
    let b := checkConstraints tr'
    if !b.isEmpty || !memBalanced (msgs tr') then caught := caught + 1 else missed := (r, c) :: missed
  IO.println s!"mutants caught: {caught}/{probes.length} missed: {missed}"
