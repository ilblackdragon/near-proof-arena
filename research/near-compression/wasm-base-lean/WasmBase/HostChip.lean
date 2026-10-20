import WasmBase.Chips
import NearSpecV3.Wasm.HostSigs
/-!
# WasmBase.HostChip — the HOST chip and the host-function table (direct-Wasm PQ base layer)

First slice of README §14.2: a `call` of an imported function is a straight-line instruction whose
signature is taken from a **fixed host table**, bound through a cached trace exactly like FUNC.
Every domain condition is explicit and decidable.

A HOST row (`np ≤ 2`, `ar ≤ 1`):

* consumes `np` values from the operand stack (channel space 0, in argument order);
* sends one request `[ts, hid, S, a0lo, a0hi, a1lo, a1hi, np]` on `HOSTQ`;
* receives one response `[ts, st, rlo, rhi, glo, ghi, ar, 0]` on `HOSTR`, where `st = 0` means
  success and `st = 1` means the host aborted (`g := g_after` still applies);
* produces `(1 − st)·ar` result words at the stack base `sb + h − np`;
* moves to `pc + 1` (`st = 0`) or stays at `pc` with `halted = 2` (`st = 1`);
* advances `S` by `fee + hostK`, `hostK` being the host ext cost in regular-op units; `g_after` is
  the budget after the spec's `g := remaining`.

`HOSTQ` / `HOSTR` are answered inside the trace by a witness **oracle** table `HOSTO` (one row per
call), whose rows are exactly the abstract host responses.  The soundness statement is therefore
relative to that oracle: the proof says "if the state side supplies these responses, the spec `run`
takes this host-call step".  Joining with the state proof (README §14.2) replaces `HOSTO` by the
state tables on the same buses.  Keeping the oracle in-trace also makes the native bus pre-check
exact rather than partial.

The HOST table is not appended to `wasmBaseAir`: that would shift every table index of the proved
F1/memory/globals/calls slice.  Host programs use `wasmBaseHostAir`, which appends HOST (22),
HOSTO (23) and the cached HOSTT table (24).
-/
namespace WasmBase
namespace Chips
open Expr

/-- Cross-proof host request / response, and the cached host table.

`HOSTQ`/`HOSTR` are **cross-proof** buses: the state side must use the same ids. They sit above
every shifted classical bus (the port maps classical bus `b` to `128 + b`, and the widest classical
AIR uses bus 75, so the occupied range is 128-203) and above every Wasm bus (0-9): hence 208/209.
`HOSTT` is a Wasm-internal cached table, not a cross-proof bus, and stays in the low range.
See `lane/pq-d3-join:research/near-compression/results/pq-d3-join/BUS-NUMBERING.md`. -/
def busHostQ : Nat := 208
def busHostR : Nat := 209
/-- `HOSTB` (byte strings).  208/209 are taken and the state side's shifted buses occupy 128-203. -/
def busHostB : Nat := 210
def busHostT : Nat := 9

/-- The message shape a HOST row can carry: at most two argument words (`np ≤ 2`) and at most one
result word (`ar ≤ 1`).  This is a property of the chip (its `HOSTQ` message has two argument slots
and its `stkSend` carries one result word), not of the host-function table: a function whose
signature does not fit is listed in `hostFns` with its **exact** arity but cannot be called in this
slice.  Widening the chip is a different lane's job. -/
def hostShapeOk (np ar : Nat) : Bool := np ≤ 2 && ar ≤ 1

/-- The HOST row's argument slots are **i64** (`cTag0`/`cTag1` force `tagP j = 1` and the trace
generator asserts `tag = 1`), so a function with an `i32` parameter cannot be called either: its
argument would carry tag `0`.  Only `gas` (`params = [i32]`) is affected.  Widening the tag to a bit
is a chip change, another lane's job. -/
def hostArgsI64 (name : String) : Bool :=
  match NearSpecV3.Wasm.hostSigs.find? (·.1 = name) with
  | some (_, ft) => ft.params.all (· == .i64)
  | none => false

/-- Fixed host table `(id, name, #params, #results)`, in **id order** (`hostFns[j]` has id `j`;
the cached `HOSTT` trace and the trace generator both index it by id).

Ids `0..7` are the first slice (bound and proved with the HOST chip).  Ids `8..21` are the D3α
*context / state-read* family added by `lane/pq-host-ctx`; their arities are the exact ones of
`NearSpecV3.Wasm.hostSigs` (`HostSigs.lean`).  Two are listed for completeness but are **outside the
HOST row's shape** and so rejected by `checkModuleH` (`hostChipIdOf = none`):

* `validator_stake` — `np = 3`, and the `HOSTQ` message has two argument slots;
* `gas` — its parameter is `i32`, and the row's argument slots are `i64`-tagged.

Both are recorded as blocked in `results/pq-host-ctx/README.md`.  Ids `0..7` are unchanged. -/
def hostFns : List (Nat × String × Nat × Nat) :=
  [(0, "block_index", 0, 1), (1, "block_timestamp", 0, 1), (2, "epoch_height", 0, 1),
   (3, "storage_usage", 0, 1), (4, "prepaid_gas", 0, 1), (5, "used_gas", 0, 1),
   (6, "register_len", 1, 1), (7, "panic", 0, 0),
   -- context / state-read family (D3α)
   (8, "current_account_id", 1, 0), (9, "chain_id", 1, 0),
   (10, "signer_account_id", 1, 0), (11, "signer_account_pk", 1, 0),
   (12, "predecessor_account_id", 1, 0), (13, "refund_to_account_id", 1, 0),
   (14, "account_balance", 1, 0), (15, "account_locked_balance", 1, 0),
   (16, "attached_deposit", 1, 0), (17, "random_seed", 1, 0),
   (18, "current_contract_code", 1, 1), (19, "gas", 1, 0),
   (20, "validator_total_stake", 1, 0),
   -- blocked: `np = 3` (the HOSTQ message has two argument slots)
   (21, "validator_stake", 3, 0)]

/-- Host id of an imported function name (`none`: not in the fixed table ⇒ outside the domain). -/
def hostIdOf (name : String) : Option Nat :=
  (hostFns.find? (fun x => x.2.1 = name)).map (·.1)

/-- Signature `(np, ar)` of a host id. -/
def hostSig (id : Nat) : Option (Nat × Nat) :=
  (hostFns.find? (fun x => x.1 = id)).map fun x => (x.2.2.1, x.2.2.2)

/-- Host id of `name` **if its signature fits the HOST row**: `np ≤ 2`, `ar ≤ 1`, and every
parameter is `i64`.  This is what the checker uses, so the two listed-but-unusable entries
(`validator_stake`, `gas`) are not callable. -/
def hostChipIdOf (name : String) : Option Nat :=
  (hostFns.find? (fun x => x.2.1 = name && hostShapeOk x.2.2.1 x.2.2.2 && hostArgsI64 name)).map (·.1)

/-- Signature of a host id, restricted to the shapes the HOST chip carries. -/
def hostChipSig (id : Nat) : Option (Nat × Nat) :=
  (hostSig id).bind fun (np, ar) =>
    if hostShapeOk np ar then
      (match hostFns.find? (·.1 = id) with
       | some x => if hostArgsI64 x.2.1 then some (np, ar) else none
       | none => none)
    else none

/-- The cached host-table row `[id, np, ar, 0, 0, 0, 0, 0]`. -/
def hostRow (id np ar : Nat) : List Nat := [id, np, ar, 0, 0, 0, 0, 0]

/-- FETCH opcode of an import call (not a Wasm opcode of the F1 family). -/
def opHost : Nat := 0x1FF

namespace Host
def act : Nat := 5
def hid : Nat := 6
def np : Nat := 7
def ar : Nat := 8
/-- response status: 0 = success, 1 = abort -/
def st : Nat := 9
def nres : Nat := 10
def ga : Nat := 11     -- g_after limbs 11..14
def rb : Nat := 15     -- result limbs 15..18
def pf (j : Nat) : Nat := 19 + j
def tagP (j : Nat) : Nat := 21 + 7 * j
def P (j : Nat) : Nat := 22 + 7 * j    -- 4 limbs
def tP (j : Nat) : Nat := 26 + 7 * j
def hP (j : Nat) : Nat := 27 + 7 * j
def kSb : Nat := 35
def kCid : Nat := 36

def cols : List String := headerCols ++
  ["act", "hid", "np", "ar", "st", "nres", "ga0", "ga1", "ga2", "ga3",
   "r0", "r1", "r2", "r3", "pf0", "pf1",
   "tagP0", "P0_0", "P0_1", "P0_2", "P0_3", "tP0", "hP0",
   "tagP1", "P1_0", "P1_1", "P1_2", "P1_3", "tP1", "hP1"] ++ frameCols

def sbNew : Expr := v kSb + v cH - v np
def aLo (j : Nat) : Expr := v (P j) + 65536 * v (P j + 1)
def aHi (j : Nat) : Expr := v (P j + 2) + 65536 * v (P j + 3)
def gLo : Expr := v ga + 65536 * v (ga + 1)
def gHi : Expr := v (ga + 2) + 65536 * v (ga + 3)
def rLo : Expr := v rb + 65536 * v (rb + 1)
def rHi : Expr := v (rb + 2) + 65536 * v (rb + 3)
def ok : Expr := 1 - v st

/-! Constraints.  `S` advances by the instruction `fee` only: host ext costs are burnt by the state
side (`sync`) and returned as `g_after`, not counted in instruction-gas units.  Each constraint is
named so its membership is `by simp`. -/
def cAct : Expr := bool (v act)
def cSt : Expr := bool (v st)
def cP0 : Expr := bool (v (pf 0))
def cP1 : Expr := bool (v (pf 1))
/-- `pf1 = pf0·pf1` (with `pf0` a bit: `pf1·(1−pf0) = 0`). -/
def cP1P0 : Expr := v (pf 1) - v (pf 0) * v (pf 1)
def cNp : Expr := v np - v (pf 0) - v (pf 1)
def cAr : Expr := bool (v ar)
/-- `nres = (1−st)·ar`. -/
def cNres : Expr := v nres - v ar + v st * v ar
def cGLo : Expr := gLo - (v ga + 65536 * v (ga + 1))
def cGHi : Expr := gHi - (v (ga + 2) + 65536 * v (ga + 3))
def cRLo : Expr := rLo - (v rb + 65536 * v (rb + 1))
def cRHi : Expr := rHi - (v (rb + 2) + 65536 * v (rb + 3))
/-- The argument padding: an absent argument has zero tag and zero limbs; a present one has tag 1. -/
def cPad0 : Expr := v (tagP 0) - v (pf 0) * v (tagP 0)
def cPad1 : Expr := v (tagP 1) - v (pf 1) * v (tagP 1)
def cTag0 : Expr := v (pf 0) * v (tagP 0) - v (pf 0)
def cTag1 : Expr := v (pf 1) * v (tagP 1) - v (pf 1)

def cPadL (j : Nat) : List Expr :=
  (List.range 4).map fun i => v (P j + i) - v (pf j) * v (P j + i)

/-- An inactive row emits nothing: the CH channels are gated by `pf j` / `nres`, so without these
links the `ChipFacts.inactive` premise fails (see `results/pq-host-gas/RESULTS.md` §3.3).  These
turn `pf j` and `nres` off on inactive rows, which is what makes the bus decomposition in
`Main/ExecHost.lean` follow from `Holds` alone. -/
def cActPf (j : Nat) : Expr := (1 - v act) * v (pf j)
def cActNres : Expr := (1 - v act) * v nres

def constraints : List Expr :=
  [cAct, cSt, cP0, cP1, cP1P0, cNp, cAr, cNres, cGLo, cGHi, cRLo, cRHi, cPad0, cPad1, cTag0, cTag1] ++
  cPadL 0 ++ cPadL 1 ++ [cActPf 0, cActPf 1, cActNres]

def inters : List Inter :=
  [stateIn (v cPc) (v cTs) (v cS) (v kSb) (v kCid) (v act),
   stateOut (v cPc + 1) (v cTs + 1) (v cS + v cFee) (2 * v st) (v kSb) (v kCid) (v act),
   fetch (v cPc) (Expr.c opHost) (v cH) (v cFee) [v hid, v np, v ar, 0] (v act),
   ⟨busHostT, true, v act, [v hid, v np, v ar, 0, 0, 0, 0, 0]⟩,
   ⟨busHostQ, true, v act, [v cTs, v hid, v cS, aLo 0, aHi 0, aLo 1, aHi 1, v np]⟩,
   ⟨busHostR, false, v act, [v cTs, v st, rLo, rHi, gLo, gHi, v ar, 0]⟩] ++
  (List.range 4).map (fun i => r16 (v (ga + i)) (v act)) ++
  (List.range 4).map (fun i => r16 (v (rb + i)) (v act)) ++
  [r16 (v (P 0)) (v act), r16 (v (P 0 + 1)) (v act), r16 (v (P 0 + 2)) (v act),
   r16 (v (P 0 + 3)) (v act), r16 (v (P 1)) (v act), r16 (v (P 1 + 1)) (v act),
   r16 (v (P 1 + 2)) (v act), r16 (v (P 1 + 3)) (v act)] ++
  ((List.range 2).flatMap fun j =>
    [stkRecv (sbNew + Expr.c j) (v (tagP j)) (limbsOf (P j)) (v (tP j)) (v (pf j))] ++
    timeChk (v cTs) (v (tP j)) (v (hP j)) (v (pf j))) ++
  [stkSend sbNew 1 (limbsOf rb) (v cTs) (v nres)]

def table : Table := ⟨"HOST", cols, constraints, inters⟩
end Host

namespace HostTab
def mult : Nat := 8
def cachedWidth : Nat := 8
def table : Table := ⟨"HOSTT", ["id", "np", "ar", "z0", "z1", "z2", "z3", "z4", "mult"], [],
  [⟨busHostT, false, v mult, (List.range 8).map v⟩]⟩
end HostTab

/-! The witness oracle of the host responses (one row per host call): it absorbs the HOSTQ request
and emits the HOSTR response; on the joined proof the state side plays this role. -/
namespace HostO
def q (i : Nat) : Nat := i        -- request columns 0..7
def st : Nat := 8
def rb : Nat := 9                 -- response word limbs 9..12
def ga : Nat := 13                -- g_after limbs 13..16
def ar : Nat := 17
def mult : Nat := 18
def cols : List String := ["q0", "q1", "q2", "q3", "q4", "q5", "q6", "q7", "st",
  "r0", "r1", "r2", "r3", "g0", "g1", "g2", "g3", "ar", "mult"]
def gLo : Expr := v ga + 65536 * v (ga + 1)
def gHi : Expr := v (ga + 2) + 65536 * v (ga + 3)
def rLo : Expr := v rb + 65536 * v (rb + 1)
def rHi : Expr := v (rb + 2) + 65536 * v (rb + 3)
def table : Table := ⟨"HOSTO", cols, [], [
  ⟨busHostQ, false, v mult, (List.range 8).map (fun i => v (q i))⟩,
  ⟨busHostR, true, v mult, [v (q 0), v st, rLo, rHi, gLo, gHi, v ar, 0]⟩]⟩
end HostO

/-! ## HOSTB: the byte-string wire of a host call

One row per byte moved by a host call, message `[ts, dir, pos, byte]`: `dir = 0` is a request
byte (Wasm → state), `dir = 1` a response byte (state → Wasm).  Rows are **groups** delimited by
the break flag `f = 1` on the first row of a group; inside a group `ts` and `dir` are constant and
`pos` increases by exactly one per row (so a `(ts, dir)` group is a contiguous run with distinct,
consecutive positions).
* `cFirst` — row 0 is a group start, so the cyclic `next` of the last row is a start and the
  continuation constraints do not fire across the wrap;
* `cLast` — the last row is a group start too: the table begins and ends at a group break (the
  final-row check, the analogue of RANGE16's endpoint pin).  The trace generator pads to a power
  of two with group-start rows, so this is always satisfiable;
* `act` is row activity (0 on padding rows); padding rows are group starts with `act = 0` and
  `byte = 0`, so their interactions have count 0 and are invisible on the bus;
* `byte < 256` is a `BYTE` kind-0 lookup with count `act`, as in every other byte-carrying chip.

All constraints have degree ≤ 2.

Not modelled here: the memory pointer, the byte length, the register space (space 6), and the
content of the byte strings (a byte value inside `0..255` is a free witness: it is not yet tied to
memory or to the state side). -/
namespace HostB
def ts : Nat := 0
def dir : Nat := 1
def pos : Nat := 2
def bv : Nat := 3
def blen : Nat := 4
def hid : Nat := 5
def gap : Nat := 6
def act : Nat := 7
def f : Nat := 8
/-- `len` is the group's byte count, committed on every row of the group (so it is a function of
`ts` rather than a free witness per row), and `hid` ties the group to the host call it belongs to.
Together they are the HOSTB <-> HOSTQ link: the same `(ts, hid)` pair appears on HOSTQ, so a byte
group cannot be spliced onto a different call.  The `(ptr, len)` memory range is still not modelled
(the bytes are not yet tied to linear memory). -/
def cols : List String := ["ts", "dir", "pos", "byte", "len", "hid", "gap", "act", "f"]

def cAct : Expr := bool (v act)
def cF : Expr := bool (v f)
def cDir : Expr := bool (v dir)
def cFirst : Expr := .first * (1 - v f)
def cLast : Expr := .last * (1 - v f)
/-- A group continues with the same `ts`. -/
def cTs : Expr := (1 - nv f) * (nv ts - v ts)
/-- A group continues with the same `dir`. -/
def cDirG : Expr := (1 - nv f) * (nv dir - v dir)
/-- A group continues at the next position (strictly increasing, consecutively). -/
def cPos : Expr := (1 - nv f) * (nv pos - v pos - 1)
/-- A byte position is inside its group's length: `pos < len`.

`pos < len` is not expressible as a polynomial without a comparison gadget, so it is delegated to
the same 16-bit comparison the chips use (`cmp`), exposed here as a lookup into the pre-existing
`RANGE16` table with the gap `len - pos - 1`: a 16-bit witness `g` with `pos + g + 1 = len` proves
`pos < len` for every `pos, len < 2^16`, and a `RANGE16` membership of `g` pins `g < 2^16`.  The
domain therefore requires `len < 2^16`, which is stated as a public bound. -/
def cPosLtLen : Expr := v act * (v blen - v pos - 1 - v gap)
/-- `len` is the same on every row of a group. -/
def cLenConst : Expr := (1 - nv f) * (nv blen - v blen)
/-- `hid` is the same on every row of a group. -/
def cHidConst : Expr := (1 - nv f) * (nv hid - v hid)

def constraints : List Expr :=
  [cAct, cF, cDir, cFirst, cLast, cTs, cDirG, cPos, cPosLtLen, cLenConst, cHidConst]

def msg : List Expr := [v ts, v hid, v dir, v pos, v bv]
/-- The Wasm side sends request bytes (`dir = 0`) and receives response bytes (`dir = 1`), each with
a 0/1 count (`act · dir` and `act · (1 − dir)` are bits).  Because the state side is not modelled
yet, both the send and the matching receive of every message sit in this table: the wire is
balanced by construction (a self-permutation), exactly as `HOSTO` stands in for the state side on
`HOSTQ`/`HOSTR`.  A joined proof keeps the two wasm-side interactions and replaces the other two
by the state tables on bus 210.  The bytes are free witnesses in `0..255` here (no memory pointer,
no length, no register space yet). -/
def inters : List Inter :=
  [⟨busHostB, true, v act * (1 - v dir), msg⟩,
   ⟨busHostB, false, v act * (1 - v dir), msg⟩,
   ⟨busHostB, true, v act * v dir, msg⟩,
   ⟨busHostB, false, v act * v dir, msg⟩,
   byteQ 0 (v bv) 0 0 (v act),
   r16 (v gap) (v act)]

def table : Table := ⟨"HOSTB", cols, constraints, inters⟩
end HostB

end Chips

/-- The direct-Wasm base AIR **with host calls**: the proved F1/memory/globals/calls tables plus
HOST (22), the response oracle HOSTO (23), the cached HOSTT table (24) and the byte wire HOSTB
(25). -/
def wasmBaseHostAir (nloc ngl : Nat) : Air :=
  { tables := (wasmBaseAir nloc ngl).tables ++
      [Chips.Host.table, Chips.HostO.table, Chips.HostTab.table, Chips.HostB.table]
    numPub := (wasmBaseAir nloc ngl).numPub }

end WasmBase
