import WasmBase.RegChip
/-!
# WasmBase.RegMem — `if` + registers + the `read_register` memory write (E2E milestone M1-a)

`docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §5 found that no AIR on main has both `IF` and `REG`, and
that `read_register` moved no bytes into linear memory: REG's `ptr` column was the "deferred MEMIO
link".  So the proved `d3tiny.run("hello")` returned `0000000000`.  This file defines the AIR that
closes it, `wasmBaseIfRegAir`, as a **new** AIR value: every existing AIR, table and index keeps its
meaning, so no existing proof changes.

```
wasmBaseIfRegAir = wasmBaseAir (0–21) ++ [HOST' (22), HOSTO (23), HOSTT (24), HOSTB (25), IF (26), REG' (27)]
```

## REG' (`Chips.RegW`): REG plus the write link

Five columns after REG's sixteen: `wr, ptrHi, mtp, mhp, ob`.  REG's `ptr` column is the low 16-bit
limb of the destination address, `ptrHi` the high limb.  `wr = 1` marks a **`read_register` group**
(`hid = 49`): a register read whose bytes are written to linear memory at `ptr + pos`.

On every byte row of a `wr` group (count `act · (1 − kind) · wr`):

```
chRecv 3 (ptr + pos) 0 [ob,0,0,0] mtp     -- the live memory byte being overwritten
chSend 3 (ptr + pos) 0 [byte,0,0,0] ts    -- the register byte, now in memory at the call's time
timeChk ts mtp mhp                        -- mtp < ts
```

This is STORE's shape (`Chips.Store`): consume the old byte at its producer time, produce the new
one at `ts`.  It is the LOAD/re-time shape of HOSTB's request bytes with a *different* value.

## Binding a `wr` group to a real call (bus 211)

An orphan `wr` group would rewrite memory with nothing in the program asking for it, and a missing
group would let `read_register` leave memory unchanged.  Both are closed by a permutation bus
`busRegRd = 211` between HOST' and REG':

* HOST' (`Chips.HostR`) adds `rr, rrInv` and the is-zero gadget
  `act · (1 − rr − (hid − 49) · rrInv) = 0`, `rr · (hid − 49) = 0`, `(1 − act) · rr = 0`:
  on an active row `rr = [hid = 49]`.  A successful `read_register` row (`rr · (1 − st) = 1`)
  **sends** `[ts, aLo 0, aHi 0, aLo 1, aHi 1]` (register id and pointer, both halves);
* REG' **receives** `[ts, rid, 0, ptr + 2^16·ptrHi, 0]` on the length row of every `wr` group.

The counts are bits, so this is a permutation: every successful `read_register` call has exactly one
`wr` group with its own `ts`, register id and pointer, and every `wr` group belongs to one.  The
call's `hid` is bound to the code by HOST's FETCH interaction, so `rr` cannot be cleared on a real
`read_register`.  An aborted call (`st = 1`) sends nothing: the spec's `read_register` aborts before
`set (writeBytes …)` (`HostCtx.writeMemH_mav`, `regGetH`'s missing-register error).

## The new REG' constraints

| name | expression | meaning |
|---|---|---|
| `cWr` | `wr·(wr−1)` | bit |
| `cWrHid` | `wr·(hid − 49)` | a write group is a `read_register` |
| `cWrRd` | `wr·(1 − rd)` | a write group is a read (it consumes the register) |
| `cWrAct` | `wr·(1 − act)` | only active rows write |
| `cReadFresh` | `act·rd·(1 − fresh)` | **every read row consumes the register's current message** |
| `cWrG`, `cPtrG`, `cPtrHiG` | `(1 − nxt.f)·(nxt.x − x)` | `wr` and the pointer are group-constant |
| `cPubR i`, `cPubRTrap i` | `(1 − nres)·r_i`, `(status − 1)·r_i` | the public result is 0 unless returned |

`cReadFresh` closes a hole in REG as it stands: nothing forced `fresh = 1` on a read row, so a
"read" could *produce* a register byte message without consuming one, i.e. forge register content
(the forged bytes would then be drained at the end).  With the write link those forged bytes would
reach memory, so the constraint is required here.

`cPubR`/`cPubRTrap` close the arity-0 statement gap (`docs/logs/pq-if-air-2026-10-22.md`; the one
accepted mutant of 93 in milestone 1): BOUNDARY receives the result only with count
`first · nres · (2 − status)`, so for a void function (or after a trap) the public result limbs were
free.  They are public-only polynomials; REG' is simply the table that carries them in this AIR.
-/
namespace WasmBase
namespace Chips

/-- The `read_register` request bus between HOST' and REG' (fresh id; 208–210 are HOSTQ/R/B). -/
def busRegRd : Nat := 211
/-- `read_register`'s host id (`hostFnsBase`). -/
def hidReadRegister : Nat := 49

theorem hidReadRegister_sig : hostSig hidReadRegister = some (2, 0) := by decide +kernel

/-! ## HOST': HOST with the `read_register` selector -/
namespace HostR
open Host
def rr : Nat := 93
def rrInv : Nat := 94
def cols : List String := Host.cols ++ ["rr", "rrInv"]

def cRrBit : Expr := bool (v rr)
def cRrHid : Expr := v rr * (v hid - Expr.c hidReadRegister)
def cRrAct : Expr := (1 - v act) * v rr
/-- On an active row `hid = 49` forces `rr = 1` (the inverse witness can only clear `rr` when
`hid ≠ 49`). -/
def cRrForce : Expr := v act * (1 - v rr - (v hid - Expr.c hidReadRegister) * v rrInv)

def constraints : List Expr := Host.constraints ++ [cRrBit, cRrHid, cRrAct, cRrForce]

/-- `[ts, register id (two halves), pointer (two halves)]`. -/
def rrMsg : List Expr := [v cTs, aLo 0, aHi 0, aLo 1, aHi 1]
def rrCnt : Expr := v rr * (1 - v st)

def inters : List Inter := Host.inters ++ [⟨busRegRd, true, rrCnt, rrMsg⟩]

def table : Table := ⟨"HOST", cols, constraints, inters⟩

theorem cols_len : cols.length = 95 := by decide
theorem rr_name : cols[rr]? = some "rr" := by decide
theorem rrInv_name : cols[rrInv]? = some "rrInv" := by decide
/-- HOST' keeps every HOST constraint and interaction, in order, as a prefix. -/
theorem constraints_prefix : Host.constraints <+: constraints := List.prefix_append _ _
theorem inters_prefix : Host.inters <+: inters := List.prefix_append _ _
end HostR

/-! ## REG': REG with the memory-write link -/
namespace RegW
open Reg
def wr : Nat := 16
def ptrHi : Nat := 17
def mtp : Nat := 18
def mhp : Nat := 19
def ob : Nat := 20
def cols : List String := Reg.cols ++ ["wr", "ptrHi", "mtp", "mhp", "ob"]

/-- The destination address `ptr + 2^16·ptrHi + pos`. -/
def addr : Expr := v ptr + 65536 * v ptrHi + v pos
def ptrE : Expr := v ptr + 65536 * v ptrHi
/-- A write byte row. -/
def wcnt : Expr := v act * isB * v wr
/-- The length row of a write group (where the request is received and the pointer range-checked). -/
def lcnt : Expr := v act * isL * v wr

def cWr : Expr := bool (v wr)
def cWrHid : Expr := v wr * (v hid - Expr.c hidReadRegister)
def cWrRd : Expr := v wr * (1 - v rd)
def cWrAct : Expr := v wr * (1 - v act)
def cReadFresh : Expr := v act * v rd * (1 - v fresh)
def cWrG : Expr := (1 - nv f) * (nv wr - v wr)
def cPtrG : Expr := (1 - nv f) * (nv ptr - v ptr)
def cPtrHiG : Expr := (1 - nv f) * (nv ptrHi - v ptrHi)
def cPubR (i : Nat) : Expr := (1 - pv Boundary.pubNres) * pv (Boundary.pubR + i)
def cPubRTrap (i : Nat) : Expr := (pv Boundary.pubStatus - 1) * pv (Boundary.pubR + i)

def newConstraints : List Expr :=
  [cWr, cWrHid, cWrRd, cWrAct, cReadFresh, cWrG, cPtrG, cPtrHiG] ++
  (List.range 4).map cPubR ++ (List.range 4).map cPubRTrap
def constraints : List Expr := Reg.constraints ++ newConstraints

def newInters : List Inter :=
  [chRecv 3 addr 0 [v ob, 0, 0, 0] (v mtp) wcnt,
   chSend 3 addr 0 [v bv, 0, 0, 0] (v ts) wcnt] ++
  timeChk (v ts) (v mtp) (v mhp) wcnt ++
  [r16 (v ptr) lcnt,
   r16 (32 * v ptrHi) lcnt,
   ⟨busRegRd, false, lcnt, [v ts, v rid, 0, ptrE, 0]⟩]
def inters : List Inter := Reg.inters ++ newInters

def table : Table := ⟨"REG", cols, constraints, inters⟩

theorem cols_len : cols.length = 21 := by decide
theorem constraints_prefix : Reg.constraints <+: constraints := List.prefix_append _ _
theorem inters_prefix : Reg.inters <+: inters := List.prefix_append _ _
end RegW

end Chips

open Chips in
/-- **The M1-a AIR**: the base tables, HOST' (22), HOSTO (23), HOSTT (24), HOSTB (25), IF (26),
REG' (27).  A new AIR value; `wasmBaseHostAir`/`wasmBaseIfHostAir`/`wasmBaseRegAir` are unchanged. -/
def wasmBaseIfRegAir (nloc ngl : Nat) : Air :=
  { tables := (wasmBaseAir nloc ngl).tables ++
      [HostR.table, HostO.table, HostTab.table, HostB.table, IfC.table, RegW.table]
    numPub := (wasmBaseAir nloc ngl).numPub }

theorem ifreg_air_len (nloc ngl : Nat) : (wasmBaseIfRegAir nloc ngl).tables.length = 28 := by
  simp [wasmBaseIfRegAir, wasmBaseAir]

theorem ifreg_air_22 (nloc ngl : Nat) :
    (wasmBaseIfRegAir nloc ngl).tables[22]'(by rw [ifreg_air_len]; decide) = Chips.HostR.table := by
  simp [wasmBaseIfRegAir, wasmBaseAir]

theorem ifreg_air_25 (nloc ngl : Nat) :
    (wasmBaseIfRegAir nloc ngl).tables[25]'(by rw [ifreg_air_len]; decide) = Chips.HostB.table := by
  simp [wasmBaseIfRegAir, wasmBaseAir]

theorem ifreg_air_26 (nloc ngl : Nat) :
    (wasmBaseIfRegAir nloc ngl).tables[26]'(by rw [ifreg_air_len]; decide) = Chips.IfC.table := by
  simp [wasmBaseIfRegAir, wasmBaseAir]

theorem ifreg_air_27 (nloc ngl : Nat) :
    (wasmBaseIfRegAir nloc ngl).tables[27]'(by rw [ifreg_air_len]; decide) = Chips.RegW.table := by
  simp [wasmBaseIfRegAir, wasmBaseAir]

/-- The base tables keep their indices. -/
theorem ifreg_air_base (nloc ngl t : Nat) (ht : t < 22) :
    (wasmBaseIfRegAir nloc ngl).tables[t]'(by rw [ifreg_air_len]; omega) =
      (wasmBaseAir nloc ngl).tables[t]'(by simp [wasmBaseAir]; omega) := by
  simp only [wasmBaseIfRegAir]
  rw [List.getElem_append_left]

/-- Bus 211 is used only by HOST' (send) and REG' (receive): no other non-parametric table of the
AIR touches it (BOUNDARY's interactions are on buses 0 and 2 only, `boundary_no_211`). -/
theorem busRegRd_fresh :
    [Chips.Add.table, Chips.Bit.table, Chips.Mul.table, Chips.Shift.table, Chips.Cmp.table,
      Chips.Const.table, Chips.Stack.table, Chips.Ctrl.table, Chips.Local.table, Chips.Div.table,
      Chips.Load.table, Chips.Store.table, Chips.Call.table, Chips.Ret.table, Chips.Range16.table,
      Chips.Byte.table, Chips.Code.table, Chips.Drain.table, Chips.MemInit.table, Chips.Data.table,
      Chips.Func.table, Chips.Host.table, Chips.HostO.table, Chips.HostTab.table, Chips.HostB.table,
      Chips.IfC.table, Chips.Reg.table].all
      (fun T => T.inters.all (·.bus != Chips.busRegRd)) = true := by
  decide +kernel

theorem boundary_no_211 (nloc ngl : Nat) :
    ∀ i ∈ Chips.Boundary.inters nloc ngl, i.bus ≠ Chips.busRegRd := by
  simp [Chips.Boundary.inters, Chips.chSend, Chips.chRecv, Chips.stkRecv, Chips.stateOut,
    Chips.busStk, Chips.busState, Chips.busRegRd]
  rintro a ((⟨j, -, rfl | rfl⟩) | (⟨g, -, rfl⟩) | rfl) <;> simp

end WasmBase
