import ZkFormal.Near.Render.Common
import ZkFormal.Near.Tables.Acct

/-!
# ZkFormal.Near.Render.Acct — honest rows of the `acct` table

16 rows per touched slot (ascending node id), lane `i`: amount byte `i` pre
and post, locked byte `i`, storage byte `i` (`i < 8`), code-hash bytes
`2i, 2i+1`; the running `Σ (255 − amount_i)` and its inverse on the last lane.
-/

namespace ZkFormal.Near.Render

open ZkFormal.Near

namespace AcctGen
variable (I : Info)

/-- `Σ_{j ≤ i} (255 − v_j)` -/
def dsumOf (v : List Nat) (i : Nat) : Nat := ((List.range (i + 1)).map fun j => 255 - v.getD j 0).sum

/-- Slot of segment `q / 16`. -/
def kOf (q : Nat) : Nat := I.touched.getD (q / 16) 0

/-- Active cells (row `q < 16·|touched|`), lane `i = q % 16`. -/
def actCell (q : Nat) : Nat → Nat
  | 0 => 1
  | 1 => if q % 16 = 0 then 1 else 0
  | 2 => if q % 16 = 15 then 1 else 0
  | 3 => kOf I q
  | 4 => q % 16
  | 5 => tlastOf I.e (kOf I q)
  | 6 => (I.vpre.getD (kOf I q) []).getD (q % 16) 0
  | 7 => (I.vpost.getD (kOf I q) []).getD (q % 16) 0
  | 8 => (I.vpre.getD (kOf I q) []).getD (16 + q % 16) 0
  | 9 => if q % 16 < 8 then (I.vpre.getD (kOf I q) []).getD (64 + q % 16) 0 else 0
  | 10 => (I.vpre.getD (kOf I q) []).getD (32 + 2 * (q % 16)) 0
  | 11 => (I.vpre.getD (kOf I q) []).getD (33 + 2 * (q % 16)) 0
  | 12 => if q % 16 < 8 then 1 else 0
  | 13 => dsumOf (I.vpre.getD (kOf I q) []) (q % 16)
  | 14 => if q % 16 = 15 then invP (dsumOf (I.vpre.getD (kOf I q) []) 15) else 0
  | 15 => if q % 16 < 8 then 1 else 0
  | _ => 0

def cell (q col : Nat) : Nat := if q < 16 * I.touched.length then actCell I q col else 0

end AcctGen

/-- 16 rows per touched slot (closed form `AcctGen.cell`), padded with zero rows. -/
def acctRowsAll (I : Info) : Array Row :=
  mkTab (2 ^ logOf (16 * I.touched.length)) Acct.width (AcctGen.cell I)

/-- Messages the `acct` table emits: `VPRE(k)`, `VPOST(k)`. -/
def acctMsgs (I : Info) : List Msg :=
  I.touched.flatMap fun k =>
    [⟨msgId K_VPRE k, I.vpre.getD k []⟩, ⟨msgId K_VPOST k, I.vpost.getD k []⟩]

end ZkFormal.Near.Render
