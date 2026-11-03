import WasmBase.M2Air
/-!
# WasmBase.M2RegAbsent — forcing a clear before a refill (`wasmBaseM2rAir`)

`wasmBaseM2Air`'s REG-C lets a register be overwritten through a **clear group** followed by a fill,
but nothing *forces* the clear: a fill row creates its register (`cFreshFill`, it consumes nothing),
so a prover can fill a live register again and leave two length messages in its slot
(`e2e-general/m2/README.md`, "Named open").  This file closes it with an **absent-register header**,
as a new AIR value; `wasmBaseM2Air`, `RegC.table` and every existing table are unchanged.

## The invariant: one live header per register

For every register id the run uses, exactly one *header* message is live at any time: either its
length message (tag 2) or its **absent** message

```
[6, lenSlot rid, 3, 0, 0, 0, 0, tp]          -- space 6, the length slot, tag `absentTag = 3`
```

* **RINIT** (new, last table) produces the absent message of every used register id at time 0, one
  row per id, ids **strictly increasing** (like MEMINIT's addresses), so each id gets exactly one;
* every **fill** group (`rd = 0`, the creation of a register) additionally **consumes** the absent
  message of its id on its length row, at a producer time `atp ≤ ts`;
* every **clear** group (`clr = 1`) additionally **re-produces** it on its length row, at its `ts`
  (the fill that must follow it, `cClrNext*`, consumes it at the same time);
* leftover absent messages (ids that end absent) go to DRAIN, whose `space · inv` rule accepts
  space 6.

A fill of a live register would need a second absent message for the same id; there is none (one
from RINIT, one per clear, and every clear consumes the live length message).

## REG-A (`Chips.RegA`): REG-C plus the header

Columns after REG-C's 22: `atp, ahp`.  New constraint and interactions:

| | expression | count |
|---|---|---|
| `cLenAct` | `(1 − nxt.f)·nxt.kind·(1 − nxt.act)` | a group's length row after a byte row is active |
| consume absent | `chRecv 6 lenSlot 3 [0,0,0,0] atp` | `fcnt = act·kind·(1 − rd)` (fill length row) |
| `atp ≤ ts` | `r16 (ts − atp − 2^16·ahp)`, `r16 (4·ahp)` | `fcnt` |
| produce absent | `chSend 6 lenSlot 3 [0,0,0,0] ts` | `ccnt = act·kind·clr` (clear length row) |

`cLenAct` is needed because the absent message is consumed on the **length** row: without it, a
fill group with bytes could end in an *inactive* length row and so create its bytes without
consuming the header.  (It also is the activity the group walk takes as its `hactL'` hypothesis.)
The time check is non-strict because the clear and the fill it precedes share their `ts`.

## The AIR

```
wasmBaseM2rAir = base (0–21) ++ [HOST' (22), HOSTO, HOSTT, HOSTB, IF (26), REG-A (27), CONV (28),
                                 UNREACH (29), RINIT (30)]
```

Tables 0–26, 28, 29 are `wasmBaseM2Air`'s; REG-A keeps REG-C's constraints and interactions as a
prefix, so `RegAt` (`Main/RegWalkG.lean`) holds at index 27 (`Main/M2RegAbsentFacts.lean`).
-/
namespace WasmBase
namespace Chips

namespace RegA
open Reg RegW RegC
/-- The absent message's tag (byte messages use 0, length messages 2). -/
def absentTag : Nat := 3
def atp : Nat := 22
def ahp : Nat := 23
def cols : List String := RegC.cols ++ ["atp", "ahp"]

/-- A fill group's length row. -/
def fcnt : Expr := v act * isL * fill
/-- A clear group's length row. -/
def ccnt : Expr := v act * isL * v clr

def cLenAct : Expr := (1 - nv f) * nv kind * (1 - nv act)
def newConstraints : List Expr := [cLenAct]
def constraints : List Expr := RegC.constraints ++ newConstraints

def newInters : List Inter :=
  [chRecv (Expr.c Register.space) lenSlotE (Expr.c absentTag) [0, 0, 0, 0] (v atp) fcnt,
   r16 (v ts - v atp - 65536 * v ahp) fcnt,
   r16 (4 * v ahp) fcnt,
   chSend (Expr.c Register.space) lenSlotE (Expr.c absentTag) [0, 0, 0, 0] (v ts) ccnt]
def inters : List Inter := RegC.inters ++ newInters

def table : Table := ⟨"REG", cols, constraints, inters⟩
theorem cols_len : cols.length = 24 := by decide
theorem constraints_prefix : RegC.constraints <+: constraints := List.prefix_append _ _
theorem inters_prefix : RegC.inters <+: inters := List.prefix_append _ _
end RegA

/-! ## RINIT: one absent message per used register id, ids strictly increasing -/
namespace RInit
def act : Nat := 0
def rid : Nat := 1
def gap : Nat := 2
def cols : List String := ["act", "rid", "gap"]
def cAct : Expr := bool (v act)
/-- Active rows form a prefix. -/
def cPrefix : Expr := .trans * ((1 - v act) * nv act)
/-- `nxt.rid = rid + 1 + nxt.gap` between active rows (`gap` 16-bit): strictly increasing. -/
def cInc : Expr := .trans * (nv act * (nv rid - v rid - 1 - nv gap))
def constraints : List Expr := [cAct, cPrefix, cInc]
def inters : List Inter :=
  [chSend (Expr.c Register.space) (v rid * Expr.c Register.cap) (Expr.c RegA.absentTag) [0, 0, 0, 0] 0
     (v act),
   r16 (v rid) (v act),
   r16 (v gap) (v act)]
def table : Table := ⟨"RINIT", cols, constraints, inters⟩
theorem cols_len : cols.length = 3 := by decide
end RInit

end Chips

open Chips in
/-- **The M2 AIR with the absent-register header**: `wasmBaseM2Air` with REG-C replaced by REG-A
(27) and RINIT appended (30).  A new AIR value; `wasmBaseM2Air` is unchanged. -/
def wasmBaseM2rAir (nloc ngl : Nat) : Air :=
  { tables := (wasmBaseAir nloc ngl).tables ++
      [HostR.table, HostO.table, HostTab.table, HostB.table, IfC.table, RegA.table, Conv.table,
        Unreach.table, RInit.table]
    numPub := (wasmBaseM2Air nloc ngl).numPub }

theorem m2r_air_len (nloc ngl : Nat) : (wasmBaseM2rAir nloc ngl).tables.length = 31 := by
  simp [wasmBaseM2rAir, wasmBaseAir]

/-- Every table but 27 and 30 is `wasmBaseM2Air`'s, at the same index. -/
theorem m2r_air_same (nloc ngl t : Nat) (ht : t < 30) (h27 : t ≠ 27) :
    (wasmBaseM2rAir nloc ngl).tables[t]? = (wasmBaseM2Air nloc ngl).tables[t]? := by
  simp only [wasmBaseM2rAir, wasmBaseM2Air]
  rcases (show t < 22 ∨ t = 22 ∨ t = 23 ∨ t = 24 ∨ t = 25 ∨ t = 26 ∨ t = 28 ∨ t = 29 by omega) with
    h | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [List.getElem?_append_left (by simp [wasmBaseAir]; exact h),
      List.getElem?_append_left (by simp [wasmBaseAir]; exact h)]
  all_goals simp [wasmBaseAir]

theorem m2r_air_27 (nloc ngl : Nat) :
    (wasmBaseM2rAir nloc ngl).tables[27]'(by rw [m2r_air_len]; decide) = Chips.RegA.table := by
  simp [wasmBaseM2rAir, wasmBaseAir]

theorem m2r_air_30 (nloc ngl : Nat) :
    (wasmBaseM2rAir nloc ngl).tables[30]'(by rw [m2r_air_len]; decide) = Chips.RInit.table := by
  simp [wasmBaseM2rAir, wasmBaseAir]

end WasmBase
