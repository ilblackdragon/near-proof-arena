import ZkFormal.Chacha.Gen
import ZkFormal.Chacha.Rng.Gen
import ZkFormal.Chacha.Shuffle.Gen
import ZkFormal.NearV3.Sched.Gen.Run

/-!
# ZkFormal.NearV3.Sched.Gen.Lane — the lane v3-chacha honest traces for the scheduler's shuffles

The scheduler's shuffle instances (one per round: `lid = lidOf τ T`, the bucket entries, RNG
positions `kst → kend`), their `gen_index` calls and the ChaCha blocks of the drawn words.

The lane generators (`Chacha.Gen.rowCell`, `Rng.Gen.rowCell`, `Shuffle.Gen.rowCell`) recompute
ChaCha states / the RNG walk per cell (fine for proofs, far too slow to run on the 600 vectors).
`fastShuf`, `fastGen`, `fastChacha` give the **same rows** from per-instance / per-block
precomputation (the test compares them cell by cell with the lane generators on a sample).
-/

namespace ZkFormal.NearV3.Sched.Gen.Lane

open NearSpecV3 ZkFormal.Chacha ZkFormal.NearV3.Sched

/-! ## Instances of the run -/

def shufInsts (R : Run) : List Shuffle.Gen.SInst :=
  R.rounds.map fun rd => ⟨lidOf R.tau rd.T, R.key, rd.kst, rd.entries.map (·.ein)⟩

/-- `gen_index` calls of the run, in shuffle order (`q = L−1 … 1` per round). -/
def genCalls (R : Run) : Except String (List Rng.Gen.Call × List (Nat × Nat)) := do
  let mut calls := #[]
  let mut res := #[]
  for rd in R.rounds do
    let mut k := rd.kst
    for i in List.range (rd.Lr - 1) do
      let q := rd.Lr - 1 - i
      match genAt 64 (q + 1) R.key k with
      | none => throw "genAt"
      | some (j, k') => calls := calls.push ⟨R.key, k, q + 1⟩; res := res.push (j, k'); k := k'
    if k != rd.kend then throw "kend"
  return (calls.toList, res.toList)

/-- ChaCha block requests: every drawn word `0 … kfin − 1` is used once. -/
def chachaReqs (R : Run) : List Gen.Req :=
  (List.range ((R.kfin + 15) / 16)).map fun ctr =>
    ⟨R.key, ctr, (List.range 16).map fun w => decide (16 * ctr + w < R.kfin)⟩

/-- The stream words `0 … kfin − 1`. -/
def words (R : Run) : Array Nat :=
  ((List.range ((R.kfin + 15) / 16)).flatMap fun ctr => chachaBlock R.key ctr).toArray

/-! ## shufV3 rows -/

structure SPre where
  I : Shuffle.Gen.SInst
  js : Array Nat
  kb : Array Nat
  cv : Array Nat
  ov : Array Nat
  lw : Array (Array Nat)

def sPre (I : Shuffle.Gen.SInst) : SPre := Id.run do
  let L := I.vals.length
  let mut js := Array.replicate L 0
  let mut kb := Array.replicate L 0
  let mut k := I.kstart
  for i in List.range (L - 1) do
    let q := L - 1 - i
    kb := kb.set! q k
    let (j, k') := (genAt 64 (q + 1) I.key k).getD (0, k)
    js := js.set! q j
    k := k'
  if L ≥ 1 then kb := kb.set! 0 k
  let mut arr := I.vals.toArray
  let mut cv := Array.replicate L 0
  let mut ov := Array.replicate L 0
  for i in List.range L do
    let q := L - 1 - i
    cv := cv.set! q arr[q]!
    if 1 ≤ q then
      ov := ov.set! q arr[js[q]!]!
      let a := arr[q]!
      let b := arr[js[q]!]!
      arr := (arr.set! q b).set! js[q]! a
  -- lw[q][x] for x ∈ {q, js q}: smallest q' ∈ (q, L−1] with js q' = x < q', else L
  let lwOf (q x : Nat) : Nat := Id.run do
    for d in List.range (L - 1 - q) do
      let q' := q + 1 + d
      if js[q']! == x && x < q' then return q'
    return L
  let lw := (List.range L).toArray.map fun q => #[lwOf q q, lwOf q js[q]!]
  return ⟨I, js, kb, cv, ov, lw⟩

/-- Mirror of `Shuffle.Gen.SInst.cell`. -/
def sCell (X : SPre) (s r q col : Nat) : Nat :=
  let I := X.I
  let L := I.vals.length
  let step := decide (1 ≤ q)
  let s2 := step && decide (X.js[q]! < q)
  let jj := if step then X.js[q]! else 0
  let lw1 := X.lw[q]![0]!
  let lw2 := X.lw[q]![1]!
  open Shuffle.Table in
  if col = colLid then I.lid
  else if col = colRc then r
  else if col = colInst then s
  else if col = colL then L
  else if col = colQ then q
  else if col = colJ then jj
  else if 6 ≤ col ∧ col < 22 then (I.key.getD ((col - 6) / 2) 0 / 2 ^ (16 * ((col - 6) % 2))) % 65536
  else if col = colKq then X.kb[q]!
  else if col = colKn then (if step then X.kb[q - 1]! else 0)
  else if col = colKs then I.kstart
  else if col = colV0 then I.vals.getD q 0
  else if col = colC then X.cv[q]!
  else if col = colO then (if s2 then X.ov[q]! else 0)
  else if col = colT1 then lw1
  else if col = colT2 then (if s2 then lw2 else 0)
  else if 30 ≤ col ∧ col < 44 then (lw1 - q - 1) / 2 ^ (col - 30) % 2
  else if 44 ≤ col ∧ col < 58 then (if s2 then (lw2 - q - 1) / 2 ^ (col - 44) % 2 else 0)
  else if 58 ≤ col ∧ col < 72 then (if s2 then (q - X.js[q]! - 1) / 2 ^ (col - 58) % 2 else 0)
  else if col = colA then 1
  else if col = colSt then (if q + 1 = L then 1 else 0)
  else if col = colFin then (if q = 0 then 1 else 0)
  else if col = colEq then (if s2 then 0 else 1)
  else if col = colS2 then (if s2 then 1 else 0)
  else 0

def shufRows (insts : List Shuffle.Gen.SInst) : Array (Array Nat) := Id.run do
  let mut out := #[]
  let mut st := 0
  for I in insts do
    let X := sPre I
    let L := I.vals.length
    for e in List.range L do
      let r := out.size
      out := out.push ((List.range Shuffle.Table.width).toArray.map (sCell X st r (L - 1 - e)))
    st := st + L
  return out

def shufTrace (insts : List Shuffle.Gen.SInst) : ZkFormal.Air.Trace ZkFormal.Algebra.Fp :=
  mkTrace (shufRows insts) 0 fun r => (Array.replicate Shuffle.Table.width 0).set! Shuffle.Table.colRc r

/-! ## genV3 rows -/

/-- Mirror of `Rng.Gen.drawCell` with the drawn word `v`, the draw count `nd`. -/
def gCell (C : Rng.Gen.Call) (nd v d c : Nat) : Nat :=
  open Rng.Gen in
  let k := C.kstart + d
  let vl := v % 65536
  let vh := v / 65536 % 65536
  let m0 := vl * C.n % 65536
  let c0 := vl * C.n / 65536
  let m1 := (vh * C.n + c0) % 65536
  let m2 := (vh * C.n + c0) / 65536
  let acc := if d + 1 = nd then 1 else 0
  let dl := if d + 1 = nd then zOf C.n - 1 - m1 else m1 - zOf C.n
  if c < 16 then limbN (C.key.getD (c / 2) 0) (c % 2)
  else if c = 16 then k / 16
  else if c < 21 then bt (k % 16) (c - 17)
  else if c = 21 then vl
  else if c = 22 then vh
  else if c < 37 then bt C.n (c - 23)
  else if c < 51 then (if c - 37 = topBit C.n then 1 else 0)
  else if c < 67 then bt m0 (c - 51)
  else if c < 81 then bt c0 (c - 67)
  else if c < 97 then bt m1 (c - 81)
  else if c < 111 then bt m2 (c - 97)
  else if c < 127 then bt dl (c - 111)
  else if c = 127 then acc
  else if c = 128 then stOf d
  else if c = 129 then 1
  else if c < 136 then bt d (c - 130)
  else if c = 136 then C.kstart
  else 0

def genRows (calls : List Rng.Gen.Call) (res : List (Nat × Nat)) (word : Nat → Nat) :
    Array (Array Nat) := Id.run do
  let mut out := #[]
  for (C, (_, kend)) in calls.zip res do
    let nd := kend - C.kstart
    for d in List.range nd do
      out := out.push ((List.range Rng.Table.width).toArray.map (gCell C nd (word (C.kstart + d)) d))
  return out

def genTrace (rows : Array (Array Nat)) : ZkFormal.Air.Trace ZkFormal.Algebra.Fp :=
  mkTrace rows 0 fun _ => Array.replicate Rng.Table.width 0

/-! ## chachaV3 rows -/

/-- Mirror of `Chacha.Gen.rowCell` on the 86 rows of one block, states precomputed. -/
def blockRows (R : Gen.Req) : Array (Array Nat) := Id.run do
  let init := initArr R.key R.ctr
  let mut sts := #[init]
  for qq in List.range 80 do sts := sts.push (qrStep (qq % 8) sts[qq]!)
  let fin := sts[80]!
  let outW (i : Nat) : Nat := add32 fin[i]! init[i]!
  let mut out := #[]
  for m in List.range 86 do
    let X := Gen.posRow R m
    let (sW, xW, cC) : (Nat → Nat) × (Nat → Nat) × (Nat → Nat → Nat) :=
      if m < 2 then
        (fun i => init[i]!,
         fun mm => if m = 0 then (if mm < 6 then R.key.getD mm 0 else 0)
                   else if mm < 2 then R.key.getD (6 + mm) 0 else if mm = 2 then R.ctr else 0,
         fun _ _ => 0)
      else if m < 82 then
        let dr := (m - 2) / 8
        let p := (m - 2) % 8
        let s := sts[8 * dr + p]!
        let g := ZkFormal.Chacha.grp p
        let w := Gen.qw s[g.1]! s[g.2.1]! s[g.2.2.1]! s[g.2.2.2]!
        (fun i => s[i]!,
         fun mm => match mm with
           | 0 => w.b | 1 => w.d | 2 => w.a1 | 3 => w.c1 | 4 => w.a2 | 5 => w.c2 | _ => 0,
         fun qq l => match qq with
           | 0 => Gen.carry w.a w.b l | 1 => Gen.carry w.c w.d1 l | 2 => Gen.carry w.a1 w.b1 l
           | 3 => Gen.carry w.c1 w.d2 l | _ => 0)
      else
        let j := m - 82
        (fun i => fin[i]!,
         fun mm => if mm < 4 then outW (4 * mm + j) else 0,
         fun kk l => if kk < 4 then Gen.carry fin[4 * kk + j]! init[4 * kk + j]! l else 0)
    let kW (j : Nat) : Nat := if j < 8 then R.key.getD j 0 else if j = 8 then R.ctr else 0
    let row := (List.range Table.width).toArray.map fun c =>
      if c < 32 then Gen.limbN (sW (c / 2)) (c % 2)
      else if c < 224 then bt (xW ((c - 32) / 32)) ((c - 32) % 32)
      else if c < 232 then cC ((c - 224) / 2) ((c - 224) % 2)
      else if c < 250 then Gen.limbN (kW ((c - 232) / 2)) ((c - 232) % 2)
      else if c < 268 then Gen.kflag X.kd (c - 250)
      else if c < 272 then (if c - 268 < 4 then Gen.mflag X (c - 268) else 0)
      else 0
    out := out.push row
  return out

def chachaRows (reqs : List Gen.Req) : Array (Array Nat) :=
  reqs.foldl (fun acc R => acc ++ blockRows R) #[]

def chachaTrace (rows : Array (Array Nat)) : ZkFormal.Air.Trace ZkFormal.Algebra.Fp :=
  mkTrace rows 0 fun _ => Array.replicate Table.width 0

end ZkFormal.NearV3.Sched.Gen.Lane
