import WasmBase.M2RegAbsent
/-!
# WasmBase.M3Air — i32 host signatures and `memory.grow`/`memory.size` (`wasmBaseM3Air`)

`wasmBaseM2Air` admits three instruction kinds **without a chip** (records `0x240`–`0x242`, which no
FETCH query can produce): calls of hosts whose signature the HOST row cannot carry (`abort`: `i32`
parameters; `promise_yield_resume`: `i32` result), `memory.grow` and `memory.size`.  This file adds
chips for them, as a new AIR value on top of `wasmBaseM2rAir` (every existing table and AIR is
unchanged):

```
wasmBaseM3Air = base (0–21) ++ [HOST-W (22), HOSTO, HOSTT, HOSTB, IF (26), REG-A (27), CONV (28),
                                UNREACH (29), RINIT (30), MEMG (31), MSZ (32), GINIT (33)]
```

## HOST-W: per-host argument and result tags

HOST (and HOST') force every present argument's tag to `1` (`i64`) and push the result with tag `1`.
HOST-W replaces exactly those two facts by **table-bound** tags:

* columns `ti j` (argument `j` is `i32`), `tmask = Σ_j 2^j·ti j`, `ri` (the result is `i32`);
* `tagP j = pf j·(1 − ti j)` (`cTagW`, in place of HOST's `cTag`), `ti j ≤ pf j`, and an `i32`
  argument has zero upper limbs (`ti j·P j_2 = ti j·P j_3 = 0`);
* the result is pushed with tag `1 − ri`; an `i32` result has zero upper limbs; `ri ≤ ar`;
* the HOSTT lookup carries `[hid, np, ar, tmask, ri, 0, 0, 0]`: the host table row of the statement
  (`hostRowM3`, `WasmBase/M3Check.lean`) fixes `tmask`, `ri` per host id from the spec's linker
  signature (`hostSigs`).  Before, those two fields were `0`, so for every all-`i64` host the row is
  unchanged.

Everything else is HOST' (`Chips.HostR`): the same columns (plus the new ones at the end), the same
constraints, the same interactions in the same order.

## Memory size as a channel message

The memory size in pages is a single live CH message on **space 8** (space 7 is the segment AIR's
gas register): `[8, 0, 0, pages, 0, 0, 0, tp]`.

* **MSZ** (one active row, row 0): produces it at time 0 with `65536·pages = pubMem`;
* **MEMG** (`memory.size` 0x3F, `memory.grow` 0x40): consumes it (`tz < ts`) and re-produces it at
  `ts` (grown on a successful grow); DRAIN consumes the final one.
* `memory.size` pushes `pages` (`i32`).  `memory.grow` pops `n` (`i32`, `n < 2^27`) and, with
  `maxMemoryPages = 2048`, either succeeds (`ok = 1`: `old + n + d = 2048`, `d` 16-bit; pushes `old`,
  the size becomes `old + n`) or fails (`ok = 0`: `old + n = 2049 + e0 + 2^16·e1`; pushes `2^32 − 1`).
  `n0, n1, d, e0, e1` are R16-checked (`n1`, `e1` also as `32·x`, so `< 2^11`).
  Its linear fee: the record's field 4 is `lin` (the fee point is `.linear` with unit cost = the
  regular op cost), and `S` advances by `fee + lin·n` — exactly `charge`'s `n·R + c` in `R` units.

## Grown pages: GINIT

LOAD/STORE do not read the memory size: a byte is in bounds because its channel message exists,
and MEMINIT creates messages only for `ad < pubMem` (at time 0).  A grown byte gets its message from
**GINIT**: one row per touched grown byte, addresses strictly increasing (like MEMINIT), producing
`[3, ad, 0, 0,0,0,0, tg]` at the grow's time `tg`, with `65536·old ≤ ad < 65536·new` for a grow
`[tg, old, new]` that MEMG offers on the lookup bus `busGrow` (213), with multiplicity `gm`.
Only a successful grow row may offer (`gm·(1 − ok) = 0`): an inactive row's message is free, so
without this a GINIT row could create a zero byte anywhere at any time.  A load before the grow cannot consume the byte: its
producer time `tg` is not earlier than the load.
-/
namespace WasmBase
namespace Chips

/-- The memory-size channel space. -/
def memSizeSpace : Nat := 8
/-- The grow-range lookup bus (MEMG offers `[ts, old, new]`, GINIT queries it). -/
def busGrow : Nat := 213
/-- `cfg.maxMemoryPages` of PV86. -/
def maxPagesM3 : Nat := 2048
/-- FETCH opcodes of the memory chip (the Wasm bytes). -/
def opMemSize : Nat := 0x3F
def opMemGrow : Nat := 0x40

/-! ## HOST-W -/
namespace HostW
open Host
def ti (j : Nat) : Nat := 95 + j      -- 95..103
def tmask : Nat := 104
def ri : Nat := 105
def cols : List String := HostR.cols ++ (argRange.map fun j => s!"ti{j}") ++ ["tmask", "ri"]

def cTi (j : Nat) : Expr := bool (v (ti j))
def cTiPf (j : Nat) : Expr := v (ti j) * (1 - v (pf j))
/-- A present argument's tag is `1 − ti j` (`i64` = 1, `i32` = 0); an absent one's is 0. -/
def cTagW (j : Nat) : Expr := v (tagP j) - v (pf j) * (1 - v (ti j))
def cI32Hi (j : Nat) : List Expr := [v (ti j) * v (P j + 2), v (ti j) * v (P j + 3)]
def cMask : Expr := v tmask - sumE argRange (fun j => Expr.c (2 ^ j) * v (ti j))
def cRi : Expr := bool (v ri)
def cRiAr : Expr := v ri * (1 - v ar)
def cRiHi : List Expr := [v ri * v (rb + 2), v ri * v (rb + 3)]

def cPadsW : List Expr :=
  argRange.flatMap fun j => [cPad j, cTagW j] ++ cPadL j ++ cI32Hi j ++ [cTi j, cTiPf j]

def constraints : List Expr :=
  cBase ++ cFlags ++ cOrder ++ cPadsW ++ cGates ++ [cActNres] ++
  [HostR.cRrBit, HostR.cRrHid, HostR.cRrAct, HostR.cRrForce] ++
  [cMask, cRi, cRiAr] ++ cRiHi

/-- The HOSTT message: the host table row of `hid`, now with the tag fields. -/
def tMsg : List Expr := [v hid, v np, v ar, v tmask, v ri, 0, 0, 0]

def inters : List Inter :=
  [stateIn (v cPc) (v cTs) (v cS) (v kSb) (v kCid) (v act),
   stateOut (v cPc + 1) (v cTs + 1) (v cS + v cFee) (2 * v st) (v kSb) (v kCid) (v act),
   fetch (v cPc) (Expr.c opHost) (v cH) (v cFee) [v hid, v np, v ar, 0] (v act),
   ⟨busHostT, true, v act, tMsg⟩,
   ⟨busHostQ, true, v act, qMsg⟩,
   ⟨busHostR, false, v act, [v cTs, v st, rLo, rHi, gLo, gHi, v ar, 0]⟩] ++
  (List.range 4).map (fun i => r16 (v (ga + i)) (v act)) ++
  (List.range 4).map (fun i => r16 (v (rb + i)) (v act)) ++
  (argRange.flatMap fun j => (List.range 4).map (fun i => r16 (v (P j + i)) (v act))) ++
  (argRange.flatMap fun j =>
    [stkRecv (sbNew + Expr.c j) (v (tagP j)) (limbsOf (P j)) (v (tP j)) (v (pf j))] ++
    timeChk (v cTs) (v (tP j)) (v (hP j)) (v (pf j))) ++
  [stkSend sbNew (1 - v ri) (limbsOf rb) (v cTs) (v nres),
   ⟨busRegRd, true, HostR.rrCnt, HostR.rrMsg⟩]

def table : Table := ⟨"HOST", cols, constraints, inters⟩
theorem cols_len : cols.length = 106 := by decide
end HostW

/-! ## MEMG: `memory.size` and `memory.grow` -/
namespace MemG
def fGrow : Nat := 5
def fSize : Nat := 6
def n0 : Nat := 7
def n1 : Nat := 8
def tn : Nat := 9
def hn : Nat := 10
def old : Nat := 11
def tz : Nat := 12
def hz : Nat := 13
def ok : Nat := 14
def d : Nat := 15
def e0 : Nat := 16
def e1 : Nat := 17
def lin : Nat := 18
def gm : Nat := 19
def kSb : Nat := 20
def kCid : Nat := 21
def cols : List String := headerCols ++
  ["f_grow", "f_size", "n0", "n1", "tn", "hn", "old", "tz", "hz", "ok", "d", "e0", "e1", "lin", "gm"] ++
  frameCols

def act : Expr := v fGrow + v fSize
def nE : Expr := v n0 + 65536 * v n1
/-- The size after the row: `old + n` on a successful grow, `old` otherwise. -/
def newE : Expr := v old + v ok * nE
def op : Expr := Expr.c opMemGrow * v fGrow + Expr.c opMemSize * v fSize
/-- `memory.grow`'s result limbs: `old` on success, `2^32 − 1` on failure. -/
def r0 : Expr := v ok * v old + (v fGrow - v ok) * 65535
def r1 : Expr := (v fGrow - v ok) * 65535
def szSlot : Expr := 0

def cOk : Expr := v ok * (Expr.c maxPagesM3 - v old - nE - v d)
def cFail : Expr := (v fGrow - v ok) * (v old + nE - Expr.c (maxPagesM3 + 1) - v e0 - 65536 * v e1)

def constraints : List Expr :=
  [bool (v fGrow), bool (v fSize), bool act, bool (v ok), bool (v lin),
   v ok * (1 - v fGrow), v lin * (1 - v fGrow), cOk, cFail,
   -- only a successful grow offers its range (a padding row's message is free)
   v gm * (1 - v ok)]

def inters : List Inter :=
  [stateIn (v cPc) (v cTs) (v cS) (v kSb) (v kCid) act,
   stateOut (v cPc + 1) (v cTs + 1) (v cS + v cFee + v lin * nE) 0 (v kSb) (v kCid) act,
   fetch (v cPc) op (v cH) (v cFee) [v lin, 0, 0, 0] act,
   stkRecv (v kSb + v cH - 1) 0 [v n0, v n1, 0, 0] (v tn) (v fGrow)] ++
  timeChk (v cTs) (v tn) (v hn) (v fGrow) ++
  [stkSend (v kSb + v cH - 1) 0 [r0, r1, 0, 0] (v cTs) (v fGrow),
   stkSend (v kSb + v cH) 0 [v old, 0, 0, 0] (v cTs) (v fSize),
   chRecv (Expr.c memSizeSpace) szSlot 0 [v old, 0, 0, 0] (v tz) act] ++
  timeChk (v cTs) (v tz) (v hz) act ++
  [chSend (Expr.c memSizeSpace) szSlot 0 [newE, 0, 0, 0] (v cTs) act,
   ⟨busGrow, false, v gm, [v cTs, v old, newE]⟩,
   r16 (v n0) (v fGrow), r16 (v n1) (v fGrow), r16 (32 * v n1) (v fGrow),
   r16 (v old) act, r16 (v d) act, r16 (v e0) act, r16 (v e1) act, r16 (32 * v e1) act]

def table : Table := ⟨"MEMG", cols, constraints, inters⟩
theorem cols_len : cols.length = 22 := by decide
end MemG

/-! ## MSZ: the initial memory size -/
namespace MSz
def act : Nat := 0
def pg : Nat := 1
def cols : List String := ["act", "pg"]
def constraints : List Expr :=
  [bool (v act), Expr.first * (1 - v act), (1 - Expr.first) * v act,
   v act * (65536 * v pg - pv Boundary.pubMem)]
def inters : List Inter :=
  [chSend (Expr.c memSizeSpace) 0 0 [v pg, 0, 0, 0] 0 (v act),
   r16 (v pg) (v act)]
def table : Table := ⟨"MSZ", cols, constraints, inters⟩
end MSz

/-! ## GINIT: the zero bytes of grown pages -/
namespace GInit
def act : Nat := 0
def ad : Nat := 1
def tg : Nat := 2
def old : Nat := 3
def new : Nat := 4
def glo : Nat := 5
def ghi : Nat := 6
def dlo : Nat := 7
def dhi : Nat := 8
def elo : Nat := 9
def ehi : Nat := 10
def cols : List String := ["act", "ad", "tg", "old", "new", "glo", "ghi", "dlo", "dhi", "elo", "ehi"]
def constraints : List Expr :=
  [bool (v act),
   .trans * ((1 - v act) * nv act),
   .trans * (nv act * (nv ad - v ad - 1 - nv glo - 65536 * nv ghi)),
   v act * (v ad - 65536 * v old - v dlo - 65536 * v dhi),
   v act * (65536 * v new - 1 - v ad - v elo - 65536 * v ehi)]
def inters : List Inter :=
  [chSend 3 (v ad) 0 [0, 0, 0, 0] (v tg) (v act),
   ⟨busGrow, true, v act, [v tg, v old, v new]⟩,
   r16 (v glo) (v act), r16 (v ghi) (v act), r16 (32 * v ghi) (v act),
   r16 (v dlo) (v act), r16 (v dhi) (v act), r16 (32 * v dhi) (v act),
   r16 (v elo) (v act), r16 (v ehi) (v act), r16 (32 * v ehi) (v act)]
def table : Table := ⟨"GINIT", cols, constraints, inters⟩
end GInit

end Chips

open Chips in
/-- **The M3 AIR**: `wasmBaseM2rAir` with HOST' replaced by HOST-W (22) and MEMG (31), MSZ (32),
GINIT (33) appended.  A new AIR value. -/
def wasmBaseM3Air (nloc ngl : Nat) : Air :=
  { tables := (wasmBaseAir nloc ngl).tables ++
      [HostW.table, HostO.table, HostTab.table, HostB.table, IfC.table, RegA.table, Conv.table,
        Unreach.table, RInit.table, MemG.table, MSz.table, GInit.table]
    numPub := (wasmBaseM2rAir nloc ngl).numPub }

theorem m3_air_len (nloc ngl : Nat) : (wasmBaseM3Air nloc ngl).tables.length = 34 := by
  simp [wasmBaseM3Air, wasmBaseAir]

/-- Tables 23–30 are `wasmBaseM2rAir`'s, at the same index. -/
theorem m3_air_same (nloc ngl t : Nat) (ht : t < 31) (h22 : t ≠ 22) :
    (wasmBaseM3Air nloc ngl).tables[t]? = (wasmBaseM2rAir nloc ngl).tables[t]? := by
  simp only [wasmBaseM3Air, wasmBaseM2rAir]
  rcases (show t < 22 ∨ t = 23 ∨ t = 24 ∨ t = 25 ∨ t = 26 ∨ t = 27 ∨ t = 28 ∨ t = 29 ∨ t = 30 by omega)
    with h | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [List.getElem?_append_left (by simp [wasmBaseAir]; exact h),
      List.getElem?_append_left (by simp [wasmBaseAir]; exact h)]
  all_goals simp [wasmBaseAir]

theorem m3_air_22 (nloc ngl : Nat) :
    (wasmBaseM3Air nloc ngl).tables[22]'(by rw [m3_air_len]; decide) = Chips.HostW.table := by
  simp [wasmBaseM3Air, wasmBaseAir]
theorem m3_air_27 (nloc ngl : Nat) :
    (wasmBaseM3Air nloc ngl).tables[27]'(by rw [m3_air_len]; decide) = Chips.RegA.table := by
  simp [wasmBaseM3Air, wasmBaseAir]
theorem m3_air_31 (nloc ngl : Nat) :
    (wasmBaseM3Air nloc ngl).tables[31]'(by rw [m3_air_len]; decide) = Chips.MemG.table := by
  simp [wasmBaseM3Air, wasmBaseAir]
theorem m3_air_32 (nloc ngl : Nat) :
    (wasmBaseM3Air nloc ngl).tables[32]'(by rw [m3_air_len]; decide) = Chips.MSz.table := by
  simp [wasmBaseM3Air, wasmBaseAir]
theorem m3_air_33 (nloc ngl : Nat) :
    (wasmBaseM3Air nloc ngl).tables[33]'(by rw [m3_air_len]; decide) = Chips.GInit.table := by
  simp [wasmBaseM3Air, wasmBaseAir]

end WasmBase
