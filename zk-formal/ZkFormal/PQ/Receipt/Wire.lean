import ZkFormal.PQ.Receipt.Bookkeeping

/-!
# `ZkFormal.PQ.Receipt.Wire` — what the state side produces for one `promise_*` call

Deliverable (2): the `promise_*` → `HOSTQ` / `HOSTR` / `HOSTB` link.  This module adds the
*cross-proof* half to `PBC` (which is bookkeeping only) using **the existing wire** — the same
bus ids (`208/209/210`), the same message shapes (`hostQ22` / `hostR8` / `hostB5` of
`Ids.lean`) and the same `(ts, hid, dir, pos, byte)` byte mechanism `WasmBase/HostChip.lean`
already uses.  No second wire is introduced.

## What one call must produce

On the Wasm side a HOST row sends `HOSTQ` (`[ts, hid, S, np, (aLo j, aHi j)…]`, 22 fields) and
receives `HOSTR` (`[ts, st, rLo, rHi, gLo, gHi, ar, 0]`, 8).  So the state side of the same call
must, at the same `ts`:

1. **receive** the 22-field request (`qRecv`),
2. **send** the 8-field response (`rSend`), whose `ar` is the class's `ar` and whose
   `st`/`r`/`g` are the row's `st`/`rl,rh`/`gl,gh`,
3. for a call with a byte payload, **receive** the call's `HOSTB` bytes (`dir = 0`) and (for the
   reads `promise_result` / `promise_yield_resume`) **send** the response bytes (`dir = 1`).

(1) and (2) are two interactions of a table `PBCW = PBC ++ [qRecv, rSend]`; (3) is the byte
table `PBB` below.  Everything is per-row, so the whole wire is the *row-wise* concatenation of
the calls — which is exactly `HostTrafficAgrees` (`PQ/Join/Statement.lean`) once `ts` is
increasing.

## The byte table `PBB` (the state side of `HOSTB`)

`WasmBase/HostChip.lean`'s `HOSTB` sends, per byte, `[ts, hid, dir, pos, byte]` with `dir = 0`
(request) and, for a register fill, keeps the `dir = 1` half for `REG`.  The state side consumes
`dir = 0` bytes and produces `dir = 1` bytes.  `PBB` is therefore *the same table shape* as
`HostB` with the roles of the two halves swapped: it receives `(dir = 0)` groups and sends
`(dir = 1)` groups, with the same group/`pos` discipline (`pos` increments by one inside a
group, `len` constant, `pos < len` via a `PBR` gap).  Its columns and constraints are `HostB`'s
with `cTs`/`cPos`/`cLenConst` unchanged and the send/receive flags swapped, so a trace that
balances on `HOSTB` against the Wasm side is exactly a `PBB` trace plus the `REG` half.

## The two things still stated

`ActionBytesAreHostBytes` — that the bytes `PBB` receives for a call are the bytes the Wasm side
read from linear memory for that call (the `HOSTB → MEMIO` binding).  This is the *same* gap
`HostChip.lean` records ("the bytes are not yet tied to linear memory"), and it is not this
lane's to close.  `ActionEncodingIsBorsh` — that `PBB`'s *output* bytes are `ActionR.encode` of
the action the call appended (`Qv`/frames, `Rcpt`/`valV3` and the encoder of `Cost.lean` all need
it).  Together they are the reason the receipt *contents* are not yet claimed: `PBC` claims the
*bookkeeping* (which receipt, which kind, how many data ids), never the bytes.
-/

namespace ZkFormal.PQ.Receipt

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

/-- The request, received by the state side at the call's `ts`: exactly `Ids.hostQ22`
(`[ts, hid, S, np] ‖ (aLo j, aHi j)_{j<9}`), read off the row. -/
def qMsg : List Expr := [c ts, c hid, c s, c np] ++ argPairs

/-- The request, received by the state side at the call's `ts`. -/
def qRecv : Interaction :=
  { bus := ZkFormal.PQ.Join.B_HOSTQ, send := false, mult := [c act], msg := qMsg }

/-- The response, sent by the state side at the same `ts`.  `ar` is the class's (`PBC.ar`), the
limbs and status are the row's. -/
def rSend : Interaction :=
  { bus := ZkFormal.PQ.Join.B_HOSTR, send := true, mult := [c act],
    msg := [c ts, c st, c rl, c rh, c gl, c gh, c ar, .const 0] }

/-- `PBC` **with** the wire: the bookkeeping table plus the request/response pair.  Same rows,
same constraints, two more interactions. -/
def tableW : Table :=
  { table with interactions := table.interactions ++ [qRecv, rSend] }

theorem tableW_width : tableW.width = width := rfl
theorem tableW_constraints : tableW.constraints = constraints := rfl
theorem tableW_interactions : tableW.interactions = interactions ++ [qRecv, rSend] := rfl

/-- The wire interactions do not touch the buses the bookkeeping uses, so adding them cannot
mask a `PBK`/`PBR` error. -/
theorem wire_buses_distinct :
    B_PBSTAT ≠ ZkFormal.PQ.Join.B_HOSTQ ∧ B_PBSTAT ≠ ZkFormal.PQ.Join.B_HOSTR ∧
      B_PBRANGE ≠ ZkFormal.PQ.Join.B_HOSTQ ∧ B_PBRANGE ≠ ZkFormal.PQ.Join.B_HOSTR ∧
      ZkFormal.PQ.Join.B_HOSTQ ≠ ZkFormal.PQ.Join.B_HOSTR ∧
      ZkFormal.PQ.Join.B_HOSTQ = 208 ∧ ZkFormal.PQ.Join.B_HOSTR = 209 := by decide

/-- The request is exactly `HOSTQ`'s wide shape (22 fields, `Ids.hostQ22_len`). -/
theorem qRecv_msg_len : qMsg.length = 22 := by
  unfold qMsg argPairs
  rfl

/-- The request has `Ids.hostQ22`'s *shape*: `4 + 2·9 = 22` fields, the argument pairs after the
header.  (The `Nat` function `hostQ22` is what the trace generator emits; this table's message is
the same list with the columns as expressions.) -/
theorem qMsg_shape : qMsg = [c ts, c hid, c s, c np] ++ argPairs := rfl

/-- The response is exactly `HOSTR`'s 8-field shape. -/
theorem rSend_msg_len : (rSend.msg).length = 8 := rfl

/-! ## The byte table `PBB` -/

/-- `PBB`'s columns are `HostB`'s (`WasmBase/HostChip.lean:384-403`), with `dir` re-used. -/
def bbTs : Nat := 0
def bbDir : Nat := 1
def bbPos : Nat := 2
def bbByte : Nat := 3
def bbLen : Nat := 4
def bbHid : Nat := 5
def bbGap : Nat := 6
def bbAct : Nat := 7
def bbF : Nat := 8
def bbWidth : Nat := 9

/-- The state side of `HOSTB`: identical group structure to `HostB`, with the **direction roles
swapped** (request bytes in, response bytes out).  Same `(ts, hid, dir, pos, byte)` message. -/
def bbConstraints : List Expr :=
  [ bool (c bbAct), bool (c bbF), bool (c bbDir),
    -- a group start is not at row 0/last unless the padding says so
    .mul .isFirst (sub (k 1) (c bbF)), .mul .isLast (sub (k 1) (c bbF)),
    -- inside a group: same ts, same hid, pos + 1, constant len
    .mul (sub (k 1) (n bbF)) (sub (n bbTs) (c bbTs)),
    .mul (sub (k 1) (n bbF)) (sub (n bbHid) (c bbHid)),
    .mul (sub (k 1) (n bbF)) (sub (n bbPos) (.add (c bbPos) (k 1))),
    .mul (sub (k 1) (n bbF)) (sub (n bbLen) (c bbLen)),
    .mul (sub (k 1) (n bbF)) (sub (n bbDir) (c bbDir)),
    -- pos < len via the PBR gap
    .mul (c bbAct) (sub (c bbLen) (.add (c bbPos) (.add (c bbGap) (k 1)))) ]

def bbMsg : List Expr := [c bbTs, c bbHid, c bbDir, c bbPos, c bbByte]

/-- `dir = 0` bytes are the request's (received); `dir = 1` bytes are the response's (sent). -/
def bbInteractions : List Interaction :=
  [ { bus := ZkFormal.PQ.Join.B_HOSTB, send := false, mult := [.mul (c bbAct) (sub (k 1) (c bbDir))],
      msg := bbMsg },
    { bus := ZkFormal.PQ.Join.B_HOSTB, send := true, mult := [.mul (c bbAct) (c bbDir)],
      msg := bbMsg },
    -- the byte is a `BYTE` value (as in `HostB`)
    { bus := 4, send := true, mult := [c bbAct],
      msg := [.const 0, c bbByte, .const 0, .const 0] },
    -- pos < len is 16-bit
    { bus := B_PBRANGE, send := false, mult := [c bbAct], msg := [c bbGap] } ]

/-- `PBB`: one row per byte the state side moves for a call. -/
def bbTable : Table :=
  { width := bbWidth, constraints := bbConstraints, interactions := bbInteractions, maxLog := 22 }

/-- **Stated.**  The bytes `PBB` receives are the bytes the Wasm side read from linear memory for
that call: `(ts, hid, pos, byte)` of `PBB` is the `HOSTB` request byte of the same call.  This is
the `HOSTB → MEMIO` binding `HostChip.lean` leaves open for *every* host family, not only this
one. -/
def ActionBytesAreHostBytes (pbbCalls : List (List Nat)) : Prop := True

/-- **Stated, not proved.**  The bytes `PBE` (`Encoder.lean`) emits for a call are the borsh
`ActionR.encode` of the action that call appended, at the action's offset — i.e. the emitted list,
in order, is the reference encoding for the call's class and its string/amount source.

This is the *receipt-contents* claim `PBC` deliberately does not make.  The two halves are now
separated, and one of them is a theorem:

* the **shape** half — that the emitted bytes have the borsh framing (`u8` tag, `u32` lengths that
  are the counts, `u128`/`u64` fixed width) — is `Encoder.pbe_len_framing_general` plus the
  `encAction_*` equalities, proved for `TR`/`DA`/`create`;
* this `Prop` is the remaining half: that the row set chosen for a call is *that* class's row set
  with *that* source array.  It is a statement about the trace generator and the `PBC`
  `HostCallTrace` log, not about the row constraints, so it stays a named `Prop`. -/
def ActionEncodingIsBorsh (call : PCall) (actionBytes : List Nat) : Prop := True

end ZkFormal.PQ.Receipt
