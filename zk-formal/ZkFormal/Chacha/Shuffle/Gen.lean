import ZkFormal.Chacha.Shuffle.Table
import ZkFormal.Chacha.ShuffleSpec
import ZkFormal.Chacha.Rng.Sound

/-!
# ZkFormal.Chacha.Shuffle.Gen — the honest trace of the shuffle table `shufV3`

One instance `(lid, key, kstart, vals)` shuffles `vals` (length `L ≥ 1`, entries `< p`) with the
RNG state `rngAt key kstart`.  Its `L` rows are `q = L−1, …, 0`; the table is padded with rows
that are zero except for the row counter.  Cell formulas (reference for a Rust generator):

| column | step / final row `q` of an instance starting at row `s`, global row `r` |
|---|---|
| `lid, rc, inst, L, q` | `lid`, `r`, `s`, `L`, `q` |
| `j` | `js q` (`= jAt q`, the `gen_index(q+1)` result); `0` on the final row |
| key limbs | limbs of `key` |
| `kq, kn, ks` | `kBefore q`, `kBefore (q−1)` (`0` on the final row), `kstart` |
| `v0, c, o` | `vals[q]`, `A_q[q]`, `A_q[js q]` if `js q < q` else `0` (`A_q = fyBefore js (L−1) vals q`) |
| `t1, t2` | stamp of the latest write of position `q` / `js q` before step `q` (`lastW`, else `L`) |
| bits | `t1−q−1`, `t2−q−1` (if `s2`), `q−j−1` (if a step with `j < q`) |
| `a, st, fin, eqj, s2` | `1`, `[q = L−1]`, `[q = 0]`, `[q = 0 ∨ js q = q]`, `[q ≥ 1 ∧ js q < q]` |
-/

namespace ZkFormal.Chacha.Shuffle.Gen

open NearSpecV3 ZkFormal.Chacha ZkFormal.Chacha.Shuffle.Table

/-- One shuffle instance. -/
structure SInst where
  lid : Nat
  key : List Nat
  kstart : Nat
  vals : List Nat

namespace SInst
variable (I : SInst)

def L : Nat := I.vals.length

/-- Stream position after `m` steps (steps go `q = L−1, L−2, …`). -/
def kAt (I : SInst) : Nat → Nat
  | 0 => I.kstart
  | m + 1 => ((genAt 64 (I.L - m) I.key (kAt I m)).map Prod.snd).getD 0

/-- Stream position before step `q`. -/
def kBefore (q : Nat) : Nat := I.kAt (I.L - 1 - q)

/-- The index drawn at step `q`. -/
def js (q : Nat) : Nat := ((genAt 64 (q + 1) I.key (I.kBefore q)).map Prod.fst).getD 0

/-- The list before step `q`. -/
def arr (q : Nat) : List Nat := fyBefore I.js (I.L - 1) I.vals q

/-- The shuffled list. -/
def final : List Nat := fyLoop I.js (I.L - 1) I.vals

/-- Stamp of the latest write of position `x` before step `q`. -/
def lw (q x : Nat) : Nat := (lastW I.js (I.L - 1) q x).getD I.L

def isS2 (q : Nat) : Bool := decide (1 ≤ q) && decide (I.js q < q)

/-- Cell `col` of the row of position `q` (global row `r`, instance start `s`). -/
def cell (s r q col : Nat) : Nat :=
  let step := decide (1 ≤ q)
  let s2 := I.isS2 q
  let jj := if step then I.js q else 0
  if col = colLid then I.lid
  else if col = colRc then r
  else if col = colInst then s
  else if col = colL then I.L
  else if col = colQ then q
  else if col = colJ then jj
  else if 6 ≤ col ∧ col < 22 then (I.key.getD ((col - 6) / 2) 0 / 2 ^ (16 * ((col - 6) % 2))) % 65536
  else if col = colKq then I.kBefore q
  else if col = colKn then (if step then I.kBefore (q - 1) else 0)
  else if col = colKs then I.kstart
  else if col = colV0 then I.vals.getD q 0
  else if col = colC then (I.arr q).getD q 0
  else if col = colO then (if s2 then (I.arr q).getD (I.js q) 0 else 0)
  else if col = colT1 then I.lw q q
  else if col = colT2 then (if s2 then I.lw q (I.js q) else 0)
  else if 30 ≤ col ∧ col < 44 then (I.lw q q - q - 1) / 2 ^ (col - 30) % 2
  else if 44 ≤ col ∧ col < 58 then (if s2 then (I.lw q (I.js q) - q - 1) / 2 ^ (col - 44) % 2 else 0)
  else if 58 ≤ col ∧ col < 72 then (if s2 then (q - I.js q - 1) / 2 ^ (col - 58) % 2 else 0)
  else if col = colA then 1
  else if col = colSt then (if q + 1 = I.L then 1 else 0)
  else if col = colFin then (if q = 0 then 1 else 0)
  else if col = colEq then (if s2 then 0 else 1)
  else if col = colS2 then (if s2 then 1 else 0)
  else 0

end SInst

/-- Row descriptors: row of position `q` of an instance starting at row `s`, or padding. -/
inductive Row where
  | pos (I : SInst) (s q : Nat)
  | pad

def instRows (I : SInst) (s : Nat) : List Row :=
  (List.range I.L).map fun e => Row.pos I s (I.L - 1 - e)

def honestRowsFrom : List SInst → Nat → List Row
  | [], _ => []
  | I :: Is, s => instRows I s ++ honestRowsFrom Is (s + I.L)

def honestRows (insts : List SInst) : List Row := honestRowsFrom insts 0

def clog2 (n : Nat) : Nat := go n 0 where
  go : Nat → Nat → Nat
    | 0, acc => acc
    | fuel + 1, acc => if n ≤ 2 ^ acc then acc else go fuel (acc + 1)

def honestLog (insts : List SInst) : Nat := max 1 (clog2 (honestRows insts).length)

def rowCell (X : Row) (r c : Nat) : Nat :=
  match X with
  | .pos I s q => I.cell s r q c
  | .pad => if c = colRc then r else 0

def honestCell (insts : List SInst) (r c : Nat) : Nat := rowCell ((honestRows insts).getD r .pad) r c

def honestTrace (insts : List SInst) : ZkFormal.Air.Trace ZkFormal.Algebra.Fp :=
  ⟨fun _ => honestLog insts, fun _ r c => ZkFormal.Algebra.Fp.ofNat (honestCell insts r c)⟩

end ZkFormal.Chacha.Shuffle.Gen
