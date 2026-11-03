import WasmBase.RegMem
import WasmBase.M2Check
/-!
# WasmBase.M2Air — the E2E M2 AIR (`wasmBaseM2Air`)

```
wasmBaseM2Air = wasmBaseIfRegAir (0–26) ++ [REG-C (27), CONV (28), UNREACH (29)]
```

A new AIR value: every table of `wasmBaseIfRegAir` keeps its index, so every lemma stated for an
index `< 28` of an AIR whose tables agree there (`m2_air_prefix`) carries over.  The code records
come from `checkModuleM2` (`WasmBase/M2Check.lean`).

## CONV: `i32.wrap_i64` (0xA7), `i64.extend_i32_s` (0xAC), `i64.extend_i32_u` (0xAD)

Columns after the header: `f_wrap, f_extu, f_exts, a0..a3, ta, ha, sgn, rl`, then the frame.

| constraint | meaning |
|---|---|
| `bool f_*`, `bool act` | one-hot flags (`act = f_wrap + f_extu + f_exts`) |
| `(1 − f_wrap)·a2`, `(1 − f_wrap)·a3` | an extend consumes an `i32` (limbs 2, 3 are 0) |
| `bool sgn`, `f_exts·(a1 − 2^15·sgn − rl)` | sign bit of an `i32` (with `r16 (2·rl)`: `rl < 2^15`) |

The row consumes the top of the stack (slot `sb + h − 1`, tag `f_wrap`: an `i64` for wrap, an
`i32` for the extends) and produces at the same slot, tag `f_extu + f_exts`, the limbs
`[a0, a1, 65535·sgn·f_exts, 65535·sgn·f_exts]`:
* wrap: `a mod 2^32` = limbs `a0, a1`;
* extend_u: the same number, now `i64`;
* extend_s: limbs 2, 3 are `0xFFFF` exactly when bit 31 is set (`Num.extendS 64 32`).

## UNREACH: `unreachable` (0x00)

A trapping row: receives the state, charges the record's fee, and sends `halted = 2`, like DIV's
trap.  It consumes and produces no value (DRAIN collects the stack after a trap).
-/
namespace WasmBase
namespace Chips

namespace Conv
def kSb : Nat := 16
def kCid : Nat := 17
def fWrap : Nat := 5
def fExtU : Nat := 6
def fExtS : Nat := 7
def a : Nat := 8     -- 8..11
def ta : Nat := 12
def ha : Nat := 13
def sgn : Nat := 14
def rl : Nat := 15
def cols : List String := headerCols ++ ["f_wrap", "f_extu", "f_exts", "a0", "a1", "a2", "a3", "ta", "ha",
  "sgn", "rl"] ++ frameCols
def act : Expr := v fWrap + v fExtU + v fExtS
def op : Expr := 0xA7 * v fWrap + 0xAD * v fExtU + 0xAC * v fExtS
def tagIn : Expr := v fWrap
def tagOut : Expr := v fExtU + v fExtS
def hiOut : Expr := 65535 * v sgn * v fExtS
def outLimbs : List Expr := [v a, v (a + 1), hiOut, hiOut]
def constraints : List Expr :=
  [bool (v fWrap), bool (v fExtU), bool (v fExtS), bool act, bool (v sgn),
   (1 - v fWrap) * v (a + 2), (1 - v fWrap) * v (a + 3),
   v fExtS * (v (a + 1) - 32768 * v sgn - v rl)]
def inters : List Inter :=
  stdState kSb kCid op zeros4 act ++
  [stkRecv (v kSb + v cH - 1) tagIn (limbsOf a) (v ta) act] ++ timeChk (v cTs) (v ta) (v ha) act ++
  [stkSend (v kSb + v cH - 1) tagOut outLimbs (v cTs) act,
   r16 (2 * v rl) (v fExtS)]
def table : Table := ⟨"CONV", cols, constraints, inters⟩
theorem cols_len : cols.length = 18 := by decide
end Conv

namespace Unreach
def kSb : Nat := 6
def kCid : Nat := 7
def act : Nat := 5
def cols : List String := headerCols ++ ["act"] ++ frameCols
def constraints : List Expr := [bool (v act)]
def inters : List Inter :=
  [stateIn (v cPc) (v cTs) (v cS) (v kSb) (v kCid) (v act),
   stateOut (v cPc + 1) (v cTs + 1) (v cS + v cFee) 2 (v kSb) (v kCid) (v act),
   fetch (v cPc) (Expr.c WasmBase.opUnreach) (v cH) (v cFee) zeros4 (v act)]
def table : Table := ⟨"UNREACH", cols, constraints, inters⟩
theorem cols_len : cols.length = 8 := by decide
end Unreach

/-! ## REG-C: REG' plus the register **clear** (refill of a live register)

A fill row creates its register (`cFreshFill`), so a host call that overwrites a **live** register
(`storage_read` into a register that already holds a value, …) would leave two messages in the
register's slots.  REG-C adds one column `clr`: a **clear group** is a read group (`rd = 1`, so
every row consumes, `cReadFresh`) whose re-production is cancelled by an extra receive of the same
message at the same time:

```
chRecv 6 byteSlot byteTag [byte,0,0,0] ts   (count act·(1−kind)·clr)
chRecv 6 lenSlot  lenTag  [len,0,0,0]  ts   (count act·kind·clr)
```

so a clear group consumes the register's `len` byte messages and its length message and leaves
nothing.  It is bound to the refill: its length row must be followed by an active **fill** row of
the same register at the same time and host id (`cClrNext*`), so a clear exists only as the first
half of an overwrite.  REG' 's constraints and interactions stay a prefix, so the group walk
(`Main/RegWalkG.lean`) applies to a clear group as to any other. -/
namespace RegC
open Reg RegW
def clr : Nat := 21
def cols : List String := RegW.cols ++ ["clr"]
def cClr : Expr := bool (v clr)
def cClrRd : Expr := v clr * (1 - v rd)
def cClrWr : Expr := v clr * v wr
def cClrG : Expr := (1 - nv f) * (nv clr - v clr)
def endC : Expr := v clr * v kind
def cClrNxtRid : Expr := endC * (nv rid - v rid)
def cClrNxtTs : Expr := endC * (nv ts - v ts)
def cClrNxtHid : Expr := endC * (nv hid - v hid)
def cClrNxtFill : Expr := endC * nv rd
def cClrNxtClr : Expr := endC * nv clr
def cClrNxtAct : Expr := endC * (1 - nv act)
def newConstraints : List Expr :=
  [cClr, cClrRd, cClrWr, cClrG, cClrNxtRid, cClrNxtTs, cClrNxtHid, cClrNxtFill, cClrNxtClr, cClrNxtAct]
def constraints : List Expr := RegW.constraints ++ newConstraints
def newInters : List Inter :=
  [chRecv (Expr.c Register.space) byteSlotE (Expr.c Register.byteTag) [v bv, 0, 0, 0] (v ts)
     (v act * isB * v clr),
   chRecv (Expr.c Register.space) lenSlotE (Expr.c Register.lenTag) [v blen, 0, 0, 0] (v ts)
     (v act * isL * v clr)]
def inters : List Inter := RegW.inters ++ newInters
def table : Table := ⟨"REG", cols, constraints, inters⟩
theorem cols_len : cols.length = 22 := by decide
theorem constraints_prefix : RegW.constraints <+: constraints := List.prefix_append _ _
theorem inters_prefix : RegW.inters <+: inters := List.prefix_append _ _
end RegC

end Chips

open Chips in
/-- **The E2E M2 AIR**: `wasmBaseIfRegAir` with REG' replaced by REG-C (27), plus CONV (28) and
UNREACH (29). -/
def wasmBaseM2Air (nloc ngl : Nat) : Air :=
  { tables := (wasmBaseAir nloc ngl).tables ++
      [HostR.table, HostO.table, HostTab.table, HostB.table, IfC.table, RegC.table, Conv.table, Unreach.table]
    numPub := (wasmBaseIfRegAir nloc ngl).numPub }

theorem m2_air_len (nloc ngl : Nat) : (wasmBaseM2Air nloc ngl).tables.length = 30 := by
  simp [wasmBaseM2Air, wasmBaseAir]

/-- Tables 0–26 are `wasmBaseIfRegAir`'s. -/
theorem m2_air_prefix (nloc ngl t : Nat) (ht : t < 27) :
    (wasmBaseM2Air nloc ngl).tables[t]? = (wasmBaseIfRegAir nloc ngl).tables[t]? := by
  simp only [wasmBaseM2Air, wasmBaseIfRegAir]
  rcases (show t < 22 ∨ t = 22 ∨ t = 23 ∨ t = 24 ∨ t = 25 ∨ t = 26 by omega) with h | rfl | rfl | rfl | rfl | rfl
  · rw [List.getElem?_append_left (by simp [wasmBaseAir]; exact h),
      List.getElem?_append_left (by simp [wasmBaseAir]; exact h)]
  all_goals simp [wasmBaseAir]

theorem m2_air_27 (nloc ngl : Nat) :
    (wasmBaseM2Air nloc ngl).tables[27]'(by rw [m2_air_len]; decide) = Chips.RegC.table := by
  simp [wasmBaseM2Air, wasmBaseAir]

theorem m2_air_28 (nloc ngl : Nat) :
    (wasmBaseM2Air nloc ngl).tables[28]? = some Chips.Conv.table := by
  simp [wasmBaseM2Air, wasmBaseIfRegAir, wasmBaseAir]

theorem m2_air_29 (nloc ngl : Nat) :
    (wasmBaseM2Air nloc ngl).tables[29]? = some Chips.Unreach.table := by
  simp [wasmBaseM2Air, wasmBaseIfRegAir, wasmBaseAir]

end WasmBase
