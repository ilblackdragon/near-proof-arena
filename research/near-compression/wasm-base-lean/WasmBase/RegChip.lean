import WasmBase.HostChip
import WasmBase.RegisterSpace
/-!
# WasmBase.RegChip — the REG table: host bytes ↔ channel space 6

`results/pq-wasm-base/README.md` §14.2: "These live on the Wasm side as a new channel space 6, keyed
by `(register_id, pos)`, plus a length message per register.  A host function that fills a register
(`input`, context getters, `storage_read`, `promise_result`) receives the bytes on `HOSTB` from the
state side.  `read_register` / `write_register` are then Wasm-side only."

Registers are a **persistent state**, so a row is modelled like the globals (channel space 2): every
access **produces** the register's message at time `ts`, and consumes the previous one at `tp` unless
it is the first row that creates the register (`fresh = 0`).  That is what makes a register readable
twice: the read re-produces the message it consumed.

One REG row per **register byte** (`kind = 0`) or per **register length** (`kind = 1`):

```
act, kind, rd, rid, pos, len, byte, hid, ts, dir, gap, tp, hp, ptr
```

* `rd = 0` — **fill**: the row creates the register (`input`).  Its byte rows *receive* the bytes
  from `HOSTB` (`dir = 1`, state → Wasm); `HOSTB` carries the state-side half of the same message
  (`HOSTB.reg = 1`), so the wire balances across the two tables.  A fill row always has
  `fresh = 0` (`cFreshFill`).
* `rd = 1` — **read**: the row consumes the current message at `tp` and re-produces it at `ts`
  (`read_register`, `register_len`, `value_return` from a register).  A register read is Wasm-side
  only (README §14.2), so it emits no `HOSTB` message.  `ptr` is the destination address of a byte
  read, carried for the **deferred** MEMIO link (see below).

`dir = 1 − rd` on a byte row (`cDirRd`), matching `HOSTB`'s `reg = 1` half.

## Constraints (all degree ≤ 2)

| name | expression | meaning |
|---|---|---|
| `cAct` | `act·(act−1)` | row activity is a bit |
| `cKind` | `kind·(kind−1)` | `kind` is a bit |
| `cRd` | `rd·(rd−1)` | `rd` is a bit |
| `cDir` | `dir·(dir−1)` | `dir` is a bit |
| `cDirRd` | `act·(1−kind)·(dir − (1 − rd))` | a byte row's `dir` is `1 − rd` |
| `cFreshFill` | `act·(1−rd)·fresh` | a fill row creates the register (`fresh = 0`) |
| `cPosLtLen` | `act·(1−kind)·(len − pos − 1 − gap)` | `pos + gap + 1 = len` on an active byte row |
| time check | `r16 (ts−tp−1−65536·hp)`, `r16 (4·hp)` with count `act·fresh` | `tp < ts` on a consuming row |

plus the lookups: `byteQ 0 byte 0 0 (act·(1−kind))` (`byte < 256`), `r16 gap` (`act·(1−kind)`),
`r16 len` and `r16 rid` (`act`).

The counts are all bits (`act`, `kind`, `rd` are), so the space-6 and `HOSTB` sides of this table are
permutation buses in the sense of `WasmBase.Bus.perm_exact`.

## Domain conditions (explicit, decidable, not polynomial)

`rid, len, pos < 2^16` from the R16 lookups (all three are needed: `pos`'s lookup is what makes
`pos + gap + 1 = len` imply `pos < len` in the naturals rather than only mod `P`), which is inside the
register model's key domain `pos, len < 2^24` (`Register.posOK`/`lenOK`).  The model's stricter
`rid ≤ 99` (`maxNumberRegisters = 100`) is the stated register domain (`Register.regOK`); it is not
a row constraint (a wider `rid` is harmless for the wire, and the state side already bounds it).
`reg_row_key_bounds` below records the implication for the AIR-visible bounds.

## What is *not* constrained (the named blocking sub-problem)

1. **The group walk.**  Nothing forces the byte rows of one register to be exactly `pos = 0 .. len−1`
   with no gaps, duplicates or extra rows, nor forces the length row's `len` to equal that count.
   That is exactly `Register.RegLenAgree` (stated, not proved).  It needs a `next`-based structure
   keyed by `(rid, ts)` plus a `cLast`-style endpoint pin — the shape HOSTB already uses for
   `(ts, dir)`.
2. **Joining REG into the `wasmBaseHostAir` execution theorem.**  REG carries space-6 CH
   interactions, so `Main/ExecHost.msgs_ch_host` and the bus decomposition would have to include it.
   This lane keeps the proved 26-table AIR byte-identical and exports REG as the separate
   `wasmBaseRegAir` (`wasmBaseHostAir ++ [REG]`, REG at index 26); the trace generator and the KAT
   use that for register programs.
-/
namespace WasmBase
namespace Chips

namespace Reg
def act : Nat := 0
def kind : Nat := 1
def rd : Nat := 2
def rid : Nat := 3
def pos : Nat := 4
def blen : Nat := 5
def bv : Nat := 6
def hid : Nat := 7
def ts : Nat := 8
def dir : Nat := 9
def gap : Nat := 10
def fresh : Nat := 11
def tp : Nat := 12
def hp : Nat := 13
def ptr : Nat := 14
/-- Group-break flag: `f = 1` on the first row of a register-access group.

A **group** is one host call's contribution to the register wire: `len` byte rows
(`kind = 0`, `pos = 0 … len−1`) followed by exactly one length row (`kind = 1`,
`pos = 0`).  A length-only access (`register_len`) is a group with no byte rows.
`f` is the same shape `HOSTB` already uses for its `(ts, dir)` groups; the constraints
below turn it into the group walk that pins `pos` to exactly `0 … len−1`. -/
def f : Nat := 15

def cols : List String := ["act", "kind", "rd", "rid", "pos", "len", "byte", "hid", "ts", "dir",
  "gap", "fresh", "tp", "hp", "ptr", "f"]

/-- `1 − kind`: the byte rows. -/
def isB : Expr := 1 - v kind
/-- `kind`: the length rows. -/
def isL : Expr := v kind
/-- `1 − rd`: the fill (produce) rows. -/
def fill : Expr := 1 - v rd
/-- `rd`: the read (consume) rows. -/
def read : Expr := v rd

def cAct : Expr := bool (v act)
def cKind : Expr := bool (v kind)
def cRd : Expr := bool (v rd)
def cDir : Expr := bool (v dir)
def cFresh : Expr := bool (v fresh)
/-- On a byte row, `dir = 1 − rd`: a fill receives from the state, a read sends to it. -/
def cDirRd : Expr := v act * isB * (v dir - (1 - v rd))
/-- A fill row creates the register: nothing was there to consume. -/
def cFreshFill : Expr := v act * fill * v fresh

/-- `pos + gap + 1 = len` on an active byte row. -/
def cPosLtLen : Expr := v act * isB * (v blen - v pos - 1 - v gap)

/-! ### The group walk

A register access is emitted as one **group**: `len` byte rows (`kind = 0`) with
`pos = 0 … len−1`, then exactly one length row (`kind = 1`, `pos = 0`).  A length-only
access (`register_len`) is a group that is a single length row.  `f = 1` marks a group start.

The constraints below turn `f` into a real walk, which is what makes `Register.RegLenAgree`
provable (it was stated-but-unproved before these existed):

| name | expression | meaning |
|---|---|---|
| `cF` | `f·(f−1)` | `f` is a bit |
| `cFirst` | `first·(1−f)` | row 0 starts a group |
| `cLast` | `last·(1−f)` | the last row starts a group (cyclic `next` is safe) |
| `cRidG` | `(1−nxt.f)·(nxt.rid − rid)` | a group keeps its register id |
| `cTsG` | `(1−nxt.f)·(nxt.ts − ts)` | a group keeps its time |
| `cLenG` | `(1−nxt.f)·(nxt.len − len)` | a group keeps its length |
| `cRdG` | `(1−nxt.f)·(nxt.rd − rd)` | a group keeps its direction (fill vs read) |
| `cPosStep` | `(1−nxt.f)·(1−nxt.kind)·(nxt.pos − pos − 1)` | consecutive byte rows step `pos` by one |
| `cStartPos` | `f·(1−kind)·pos` | a group's first byte is at `pos = 0` |
| `cLastByte` | `(1−nxt.f)·nxt.kind·(len − pos − 1)` | the row before a length row is byte `len−1` |
| `cLenPos` | `kind·pos` | a length row has `pos = 0` |
| `cLenEnds` | `kind·(1−nxt.f)` | a length row ends its group |
| `cOnlyLenEnds` | `act·(1−kind)·nxt.f` | an active byte row is never followed by a group start |
| `cByteAct` | `(1−kind)·(1−act)` | every byte row is active |

`cFirst`/`cLast` are the endpoint pins (the table begins and ends at a group break, exactly as
`HOSTB`).  The generator pads with `act = 0, f = 1, kind = 1` rows (a closed empty group), which
satisfies every one of these constraints.

**Why these give the walk.**  Inside a group `rid`, `ts`, `len`, `rd` are constant (`cRidG`–`cRdG`).
A group's first byte is at `pos = 0` (`cStartPos`).  An active byte row is never followed by a
group start (`cOnlyLenEnds`), so it is followed either by another byte row — which steps `pos` by
one (`cPosStep`) — or by the group's length row, which forces `pos = len − 1` (`cLastByte`).  A
length row terminates its group (`cLenEnds`), so the only way out of a group is through its length
row.  `cPosLtLen` (`pos + gap + 1 = len`, `gap` R16-checked) bounds `pos < len` along the way.
Hence the byte rows of a group are exactly `pos = 0 … len − 1`, once each, and the length row
carries the same `len` — which is `Register.RegLenAgree`.

Together `cStartPos`, `cPosStep`, `cLastByte`, `cOnlyLenEnds` and `cLenEnds` also force every group
to *contain* a length row: a group with only byte rows could never be exited. -/
def cF : Expr := bool (v f)
def cFirst : Expr := .first * (1 - v f)
def cLast : Expr := .last * (1 - v f)
def cRidG : Expr := (1 - nv f) * (nv rid - v rid)
def cTsG : Expr := (1 - nv f) * (nv ts - v ts)
def cLenG : Expr := (1 - nv f) * (nv blen - v blen)
def cRdG : Expr := (1 - nv f) * (nv rd - v rd)
def cPosStep : Expr := (1 - nv f) * (1 - nv kind) * (nv pos - v pos - 1)
def cStartPos : Expr := v f * (1 - v kind) * v pos
def cLastByte : Expr := (1 - nv f) * nv kind * (v blen - v pos - 1)
def cLenPos : Expr := v kind * v pos
def cLenEnds : Expr := v kind * (1 - nv f)
def cOnlyLenEnds : Expr := v act * (1 - v kind) * nv f
/-- A byte row emits a message, so it is always active.  This is what makes the group's byte
*messages* number exactly `len` (without it, an inactive byte row would hold a position in the
`pos` walk without contributing a byte message).  Padding rows are length rows, so they are
unaffected. -/
def cByteAct : Expr := (1 - v kind) * (1 - v act)

def constraints : List Expr :=
  [cAct, cKind, cRd, cFresh, cDir, cDirRd, cFreshFill, cPosLtLen,
   cF, cFirst, cLast, cRidG, cTsG, cLenG, cRdG, cPosStep, cStartPos, cLastByte,
   cLenPos, cLenEnds, cOnlyLenEnds, cByteAct]

/-- The space-6 byte slot: `rid · 2^24 + pos + 1` (`Register.byteSlot rid pos`). -/
def byteSlotE : Expr := v rid * Expr.c Register.cap + v pos + 1
/-- The space-6 length slot: `rid · 2^24` (`Register.lenSlot rid`). -/
def lenSlotE : Expr := v rid * Expr.c Register.cap
/-- The `HOSTB` message of a fill byte. -/
def hbMsg : List Expr := [v ts, v hid, v dir, v pos, v bv]

def inters : List Inter :=
  [-- every active row produces the register's new message
   chSend (Expr.c Register.space) byteSlotE (Expr.c Register.byteTag) [v bv, 0, 0, 0] (v ts)
     (v act * isB),
   chSend (Expr.c Register.space) lenSlotE (Expr.c Register.lenTag) [v blen, 0, 0, 0] (v ts)
     (v act * isL),
   -- every active row except the creating fill consumes the previous message
   chRecv (Expr.c Register.space) byteSlotE (Expr.c Register.byteTag) [v bv, 0, 0, 0] (v tp)
     (v act * isB * v fresh),
   chRecv (Expr.c Register.space) lenSlotE (Expr.c Register.lenTag) [v blen, 0, 0, 0] (v tp)
     (v act * isL * v fresh),
   -- the HOSTB wire: a fill *receives* the byte from the state side
   ⟨busHostB, false, v act * isB * fill, hbMsg⟩,
   -- a read's producer time is earlier (`tp < ts`), as every CH consumer
   r16 (v ts - v tp - 1 - 65536 * v hp) (v act * v fresh),
   r16 (4 * v hp) (v act * v fresh),
   -- `byte < 256` and the 16-bit bounds
   byteQ 0 (v bv) 0 0 (v act * isB),
   r16 (v gap) (v act * isB),
   r16 (v blen) (v act),
   r16 (v rid) (v act),
   -- `pos` must be 16-bit: without this, `cPosLtLen` (`pos + gap + 1 = len`) is satisfiable with
   -- `pos + 1 + gap = len + P` (i.e. `pos = P − 1`, `len = 5`, `gap = 4`), so `pos < len` — the
   -- walk's only bound — would be FALSE.  A machine-checked counterexample is
   -- `reg_pos_lt_len_needs_r16` in `Main/RegWalk.lean`.
   r16 (v pos) (v act)]

def table : Table := ⟨"REG", cols, constraints, inters⟩
end Reg

end Chips

/-- The direct-Wasm base AIR with host calls **and the register wire**: `wasmBaseHostAir` plus REG
(index 26).  `wasmBaseHostAir` is untouched, so every proved index (0-25) is unchanged. -/
def wasmBaseRegAir (nloc ngl : Nat) : Air :=
  { tables := (wasmBaseHostAir nloc ngl).tables ++ [Chips.Reg.table]
    numPub := (wasmBaseHostAir nloc ngl).numPub }

theorem reg_air_len (nloc ngl : Nat) : (wasmBaseRegAir nloc ngl).tables.length = 27 := rfl

theorem reg_air_26 (nloc ngl : Nat) :
    (wasmBaseRegAir nloc ngl).tables[26]'(by rw [reg_air_len]; decide) = Chips.Reg.table := rfl

/-- REG answers (never queries) R16. -/
theorem reg_table_r16 : Chips.Reg.table.inters.all
    (fun i => i.bus != Chips.busR16 || i.send) = true := by decide

/-- Every REG CH interaction is on channel space 6 (register byte / length).  In particular REG never
touches the operand stack (space 0), the locals (`≥ 16`), the globals (2), the memory (3), the call
records (4) or the budget (5). -/
theorem reg_space_ok : Chips.Reg.table.inters.all (fun i =>
    i.bus != Chips.busStk || i.msg.head? == some (Expr.c Register.space)) = true := by decide

/-- **The AIR-visible key bounds are inside the register model's key domain.**  From the R16
lookups (`rid, len < 2^16`), `pos + gap + 1 = len` and `gap < 2^16` we get `pos < 2^24` and
`len < 2^24`; with the stated `rid ≤ 99`, that is `Register.regOK`, `posOK` and `lenOK`. -/
theorem reg_row_key_bounds {rid pos len gap : Nat} (hrid : rid ≤ 99) (hgap : gap < 65536)
    (hlen : len < 65536) (hpos : pos + gap + 1 = len) :
    Register.posOK pos = true ∧ Register.lenOK len = true ∧ Register.regOK rid = true := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Register.posOK_iff]; omega
  · rw [Register.lenOK_iff]; omega
  · rw [Register.regOK_iff]; exact hrid

end WasmBase
