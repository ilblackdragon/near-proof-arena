import Lean.Data.Json
import ZkFormal.Chacha.Rng.Gen

/-! Executable check of the honest `genV3` (stream / `gen_index`) trace generator (run from
`zk-formal/`: `lake env lean --run test/RngGenTest.lean`).  Not part of the library.

The `gen_index` calls are those of real shuffles of `oracle/fixtures/v3/vectors/chacha.json`
(`"shuffles"`: key = `leWords seed`; a shuffle of length `n` calls `gen_index(q+1)` for
`q = n−1 … 1` at consecutive stream positions from `0`).  Every constraint is evaluated on every
row; the call results replayed as swaps on `[0, n)` must give the json permutation (and
`NearSpecV3.shuffle`); the table's bus traffic must be `expectedWords` / `expectedGen`; and
single-cell mutants must violate some constraint. -/

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Rng.Gen ZkFormal.Chacha.Rng.Table

def mkTrace (calls : List Call) : Trace Fp :=
  let rows := honestRows calls
  let log := honestLog calls
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

/-- Active messages of interaction `ii` as `(row, multiplicity, message)`. -/
def msgsOf (tr : Trace Fp) (ii : Nat) : List (Nat × Nat × List Nat) := Id.run do
  let mut out := []
  let it := (interactions 0 1)[ii]!
  for r in List.range (tr.height 0) do
    let m := it.multNat tr 0 r []
    if m != 0 then out := (r, m, it.msg.map (fun e => (e.eval tr 0 r []).toNat)) :: out
  return out.reverse

def hexByte (s : String) (i : Nat) : Nat :=
  let d := fun (c : Char) => if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
  d s.toList[2 * i]! * 16 + d s.toList[2 * i + 1]!

def main : IO Unit := do
  let txt ← IO.FS.readFile "../oracle/fixtures/v3/vectors/chacha.json"
  let j ← IO.ofExcept (Lean.Json.parse txt)
  let shuffles ← IO.ofExcept (j.getObjValAs? (Array Lean.Json) "shuffles")
  let mut calls : List Call := []
  let mut permOk := 0
  let mut nShuf := 0
  let mut fuelOk := true
  for s in shuffles do
    let n ← IO.ofExcept (s.getObjValAs? Nat "n")
    if n < 5 || n > 12 then continue
    nShuf := nShuf + 1
    let seedHex ← IO.ofExcept (s.getObjValAs? String "seed")
    let perm ← IO.ofExcept (s.getObjValAs? (List Nat) "perm")
    let seed := (List.range 32).map fun i => (hexByte seedHex i).toUInt8
    let key := NearSpecV3.leWords seed
    let mut kpos := 0
    let mut l := List.range n
    for i in List.range (n - 1) do
      let q := n - 1 - i
      let C : Call := ⟨key, kpos, q + 1⟩
      match genAt 64 C.n C.key C.kstart with
      | none => fuelOk := false
      | some (jj, kend) =>
        if kend ≥ 2 ^ 30 then fuelOk := false
        l := NearSpecV3.swapAt l q jj
        kpos := kend
        calls := calls ++ [C]
    let spec := (NearSpecV3.shuffle (List.range n) (NearSpecV3.Rng.ofSeed seed)).map Prod.fst
    if l == perm && spec == some perm then permOk := permOk + 1
    else IO.println s!"perm mismatch n={n}: got {l} json {perm} spec {spec}"
  let tr := mkTrace calls
  let rows := (honestRows calls).length
  IO.println s!"shuffles {nShuf} calls {calls.length} rows {rows} height {tr.height 0} constraints {constraints.length} all calls ok {fuelOk}"
  IO.println s!"permutations reproduced (replayed swaps = json = NearSpecV3.shuffle): {permOk}/{nShuf}"
  let bad := checkRows tr (List.range (tr.height 0))
  IO.println s!"violations: {bad.length} first: {bad.take 10}"
  -- bus traffic
  let recv := msgsOf tr 0
  let sent := msgsOf tr 1
  let expW := (expectedWords calls).map fun m => m.map Fp.toNat
  let expG := (expectedGen calls).map fun m => m.map Fp.toNat
  IO.println s!"busChacha receives {recv.length} (all mult 1: {recv.all (·.2.1 == 1)}), = expectedWords: {recv.map (·.2.2) == expW}"
  IO.println s!"busGen provides {sent.length} (all mult 1: {sent.all (·.2.1 == 1)}), = expectedGen: {sent.map (·.2.2) == expG}"
  let rejects := rows - calls.length
  IO.println s!"rejected draws: {rejects}"
  -- mutants: one cell + 1, on rows of the first call, a rejected row (if any), padding
  let rejRow := ((List.range rows).find? fun r => rowCell ((honestRows calls).getD r .pad) colAcc == 0).getD 1
  let probes := [(0, 16), (0, 17), (0, 21), (0, 22), (0, 23), (0, 37), (0, 51),
    (0, 67), (0, 81), (0, 97), (0, 111), (0, 127), (0, 128), (0, 129), (0, 130), (0, 136),
    (1, 16), (1, 136), (1, 130), (rejRow, 127), (rejRow, 111), (rejRow, 3), (rejRow, 20),
    (rows, 129), (rows, 128), (tr.height 0 - 1, 127), (rows - 1, 82)]
  let mut caught := 0
  let mut missed := []
  for (r, c) in probes do
    let tr' : Trace Fp := ⟨tr.log, fun t r' c' =>
      if r' = r ∧ c' = c then tr.cell t r' c' + (1 : Fp) else tr.cell t r' c'⟩
    let h := tr.height 0
    if (checkRows tr' [(r + h - 1) % h, r]).length > 0 then caught := caught + 1 else missed := (r, c) :: missed
  IO.println s!"mutants caught {caught}/{probes.length} missed {missed}"
  -- key limbs of a single-draw call and padding key cells are pinned by the bus only (the
  -- `busChacha` receive / `busGen` message), not by a local constraint: expected uncaught.
  let busOnly := [(0, 0), (0, 15), (rows, 0)]
  let mut localHits := 0
  for (r, c) in busOnly do
    let tr' : Trace Fp := ⟨tr.log, fun t r' c' =>
      if r' = r ∧ c' = c then tr.cell t r' c' + (1 : Fp) else tr.cell t r' c'⟩
    let h := tr.height 0
    if (checkRows tr' [(r + h - 1) % h, r]).length > 0 then localHits := localHits + 1
  IO.println s!"bus-only cells (key limbs of a 1-draw call, padding key): locally caught {localHits}/{busOnly.length} (expected 0)"
