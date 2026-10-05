import ZkFormal.Near.Render.RcptSim
import ZkFormal.Near.Tables.Mrk
import ZkFormal.Near.Extract.SmallViews

/-!
# ZkFormal.Near.Render.Mrk — honest rows of the `mrk` table

Row 0: the root check.  Then levels `1, 2, …` (nearcore `merklize`): a hashed
node is a 64-row segment (`left ‖ right`), an odd last node a promote row.
At least one padding row follows (the last row must be inactive).
-/

namespace ZkFormal.Near.Render

open NearSpec ZkFormal.Near

/-- A merkle node: SHA message id, length, digest. -/
structure MNode where
  id : Nat
  len : Nat
  dig : List Nat
  deriving Inhabited

namespace MrkGen

/-- Size of level `j` (level `0`: the `n` leaves). -/
def size (n : Nat) : Nat → Nat
  | 0 => n
  | j + 1 => (size n j + 1) / 2

/-- Hashed nodes on the levels `1 … j − 1` (the `MRK` index of node `(j, 0)`). -/
def qBase (n : Nat) : Nat → Nat
  | 0 => 0
  | 1 => 0
  | j + 2 => qBase n (j + 1) + size n j / 2

/-- Nodes of level `j`. -/
def levels (I : Info) : Nat → List MNode
  | 0 => (List.range I.nRcpt).map fun r => ⟨msgId K_LEAF r, 68, shaN (leafBytes I r)⟩
  | j + 1 =>
    let prev := levels I j
    (List.range ((prev.length + 1) / 2)).map fun i =>
      if 2 * i + 1 < prev.length then
        let L := prev.getD (2 * i) default
        let R := prev.getD (2 * i + 1) default
        ⟨msgId K_MRK (qBase I.nRcpt (j + 1) + i), 64, shaN (L.dig ++ R.dig)⟩
      else prev.getD (2 * i) default

/-- The top level (first level of size 1). -/
def topJ (n : Nat) : Nat := ((mrkShape n).getLast?.map (·.1)).getD 1

/-- Row records `(j, i, hashed, p)` of the node rows, in table order. -/
def recs (n : Nat) : List (Nat × Nat × Bool × Nat) :=
  (mrkShape n).flatMap fun (j, i, h) => if h then (List.range 64).map fun p => (j, i, true, p) else [(j, i, false, 0)]

/-- Cells of node row `(j, i, h, p)`; `lv` the levels. -/
def nodeCell (n : Nat) (lv : List (List MNode)) (r : Nat × Nat × Bool × Nat) : Nat → Nat :=
  let (j, i, h, p) := r
  let sp := size n (j - 1)
  let s := size n j
  let q := qBase n j + i
  let C (k : Nat) : MNode := (lv.getD (j - 1) []).getD k default
  let ch := if p / 32 = 0 then C (2 * i) else C (2 * i + 1)
  fun col =>
    if col = Mrk.q then q else if col = Mrk.j then j else if col = Mrk.i then i
    else if col = Mrk.sp then sp else if col = Mrk.s then s else if col = Mrk.odd then sp % 2
    else if col = Mrk.lil then (if i + 1 = s then 1 else 0)
    else if col = Mrk.top then (if s = 1 then 1 else 0)
    else if col = Mrk.inv then (if s = 1 then 0 else invP (s - 1))
    else if col = Mrk.mj then j - 1
    else if h then
      if col = Mrk.sg then 1 else if col = Mrk.pw then p % 32 else if col = Mrk.wn then p / 32
      else if col = Mrk.wf then (if p % 32 = 0 then 1 else 0)
      else if col = Mrk.wl then (if p % 32 = 31 then 1 else 0)
      else if col = Mrk.sf then (if p = 0 then 1 else 0)
      else if col = Mrk.sl then (if p = 63 then 1 else 0)
      else if col = Mrk.cId then ch.id else if col = Mrk.cLen then ch.len
      else if col = Mrk.mi then 2 * i + p / 32
      else if col = Mrk.gM then (if p % 32 = 0 then 1 else 0)
      else if col = Mrk.gO then (if p = 0 then 1 else 0)
      else if col = Mrk.oId then (if p = 0 then msgId K_MRK q else 0)
      else if col = Mrk.oLen then (if p = 0 then 64 else 0)
      else if Mrk.reg 0 ≤ col ∧ col < Mrk.reg 32 then ch.dig.getD (p % 32 + (col - Mrk.reg 0)) 0
      else 0
    else
      if col = Mrk.pr then 1 else if col = Mrk.cId then (C (2 * i)).id
      else if col = Mrk.cLen then (C (2 * i)).len else if col = Mrk.mi then 2 * i
      else if col = Mrk.gM then 1 else if col = Mrk.gO then 1
      else if col = Mrk.oId then (C (2 * i)).id else if col = Mrk.oLen then (C (2 * i)).len
      else 0

/-- Cells of the root row. -/
def rootCell (n : Nat) (lv : List (List MNode)) (col : Nat) : Nat :=
  let root := (lv.getD (topJ n) []).getD 0 default
  if col = Mrk.rt then 1 else if col = Mrk.gM then 1 else if col = Mrk.mj then topJ n
  else if col = Mrk.cId then root.id else if col = Mrk.cLen then root.len else 0

def cell (n : Nat) (lv : List (List MNode)) (rs : List (Nat × Nat × Bool × Nat)) (q col : Nat) : Nat :=
  if q = 0 then rootCell n lv col
  else if q - 1 < rs.length then nodeCell n lv (rs.getD (q - 1) default) col else 0

end MrkGen

/-- Honest rows: root row, node rows, at least one padding row. -/
def mrkRowsAll (I : Info) : Array Row :=
  let n := I.nRcpt
  let lv := (List.range (n + 2)).map (MrkGen.levels I)
  let rs := MrkGen.recs n
  mkTab (2 ^ logOf (rs.length + 2)) Mrk.width (MrkGen.cell n lv rs)

/-- Messages `MRK(q)` (hashed nodes in table order). -/
def mrkMsgs (I : Info) : List Msg :=
  let n := I.nRcpt
  let lv := (List.range (n + 2)).map (MrkGen.levels I)
  (mrkShape n).filterMap fun (j, i, h) =>
    if h then
      let C (k : Nat) : MNode := (lv.getD (j - 1) []).getD k default
      some ⟨msgId K_MRK (MrkGen.qBase n j + i), (C (2 * i)).dig ++ (C (2 * i + 1)).dig⟩
    else none

end ZkFormal.Near.Render
