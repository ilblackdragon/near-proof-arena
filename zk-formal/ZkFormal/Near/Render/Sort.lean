import ZkFormal.Near.Render.Common
import ZkFormal.Near.Tables.Sort

/-!
# ZkFormal.Near.Render.Sort — honest rows of the `sort` table

32 rows per receipt id, ids sorted ascending as little-endian 256-bit
integers; `diff = id_t − id_{t−1} − 1` byte-serially with carries; the delay
line `d j` holds the byte `j + 1` rows back (cyclically, so that the wrap-around
row `0` agrees with an active last row).

Closed form (`sortCell S H q col`, row `q = 32·t + i`), for the proofs
(`Render/Proof/Sort*.lean`).
-/

namespace ZkFormal.Near.Render

open NearSpec ZkFormal.Near

def leVal (b : List Nat) : Nat := b.foldr (fun x acc => x + 256 * acc) 0

def insertSorted (x : Nat × List Nat) : List (Nat × List Nat) → List (Nat × List Nat)
  | [] => [x]
  | y :: ys => if leVal x.2 ≤ leVal y.2 then x :: y :: ys else y :: insertSorted x ys

/-- `(receipt index, id bytes)` in receipt order. -/
def rawIds (I : Info) : List (Nat × List Nat) :=
  (I.e.rs.zip (List.range I.e.rs.length)).map fun (rc, r) => (r, toNats rc.receiptId)

/-- The ids sorted ascending (as little-endian integers). -/
def sortedIds (I : Info) : List (Nat × List Nat) := (rawIds I).foldr insertSorted []

namespace SortGen
variable (S : List (Nat × List Nat))

/-- Byte `j` of `x`. -/
def byte (x j : Nat) : Nat := x / 256 ^ j % 256

def idOf (t : Nat) : List Nat := (S.getD t (0, [])).2
def prevOf (t : Nat) : Nat := if t = 0 then 0 else leVal (idOf S (t - 1))
def diffOf (t : Nat) : Nat := if t = 0 then 0 else leVal (idOf S t) - prevOf S t - 1

/-- Carries of `x + y + c` byte by byte: `carryFrom x y c i` is the carry into byte `i`. -/
def carryFrom (x y c : Nat) : Nat → Nat
  | 0 => c
  | i + 1 => carryFrom (x / 256) (y / 256) ((x % 256 + y % 256 + c) / 256) i

/-- Carry into byte `i` of `prev + diff + 1` (segment `t > 0`; `[i = 0]` on `t = 0`). -/
def carry (t i : Nat) : Nat :=
  if t = 0 then (if i = 0 then 1 else 0) else carryFrom (prevOf S t) (diffOf S t) 1 i

/-- `bb` of row `q` (`0` on padding). -/
def bbAt (q : Nat) : Nat := if q < 32 * S.length then (idOf S (q / 32)).getD (q % 32) 0 else 0

/-- Active cells (row `q < 32·|S|`) of the columns `0 … 16`. -/
def actCell (q : Nat) : Nat → Nat
  | 0 => 1
  | 1 => if q % 32 = 0 then 1 else 0
  | 2 => if q % 32 = 31 then 1 else 0
  | 3 => if q / 32 = 0 then 1 else 0
  | 4 => (S.getD (q / 32) (0, [])).1
  | 5 => q % 32
  | 6 => bbAt S q
  | 7 => carry S (q / 32) (q % 32)
  | 8 => carry S (q / 32) (q % 32 + 1)
  | j + 9 => if j < 8 then byte (diffOf S (q / 32)) (q % 32) / 2 ^ j % 2 else 0

def cell (H q col : Nat) : Nat :=
  if 17 ≤ col then
    (if col < 49 then bbAt S ((q + 2 * H - 1 - (col - 17)) % H) else 0)
  else if q < 32 * S.length then actCell S q col else 0

end SortGen

def sortH (S : List (Nat × List Nat)) : Nat := 2 ^ logOf (32 * S.length)

def sortRowsAll (I : Info) : Array Row :=
  let S := sortedIds I
  mkTab (sortH S) Sort.width (SortGen.cell S (sortH S))

end ZkFormal.Near.Render
