import WasmBase.HostChip
import WasmBase.RegisterSpace
import ZkFormal.Sha.Sound
import NearSpecV3.Wasm.Crypto
/-!
# WasmBase.ShaAir — the SHA-256 table on the PQ (SWIRL) stack

`results/pq-hash-air/README.md` §1 gives the cost decision for the four D3α hash host functions
(`sha256`, `keccak256`, `keccak512`, `ripemd160`).  This file delivers the cheapest one: the
SHA-256 block table as a `WasmBase.Chips.Table`, i.e. in the AIR language the SWIRL prover
interprets, so the classical soundness proof transfers instead of being re-derived.

## What is reused, and what is new

The **constraints** are not re-written.  `ZkFormal.Sha.Table.constraints` (544 columns, 1011
constraints, max degree 4, `zk-formal/ZkFormal/Sha/Table.lean`, read-only) is mapped through the
embedding `toW : ZkFormal.Air.Expr → Expr`.  So the PQ table *is* the classical table: one
constraint list, two provers.  Soundness is `ZkFormal.Sha.sha_bus_sound_closed` transported by
`sha_local` (`sha_digest_is_spec` below): every digest row of any trace satisfying these
constraints holds `ArenaCore.sha256` of its message bytes — and `NearSpecV3.Wasm.Crypto.sha256`
*is* `ArenaCore.sha256` (`spec/lean/v3/NearSpecV3/Wasm/Crypto.lean:16`), so the AIR's answer is
the spec's answer, not a re-implementation of it.

The **wire** is the register space (space 6, `WasmBase/RegisterSpace.lean`) — the same wire `REG`
(`WasmBase/RegChip.lean`) carries and whose state-side half `HOSTB` (`reg = 1`) moves.  No second
byte bus is introduced.  The host call is `sha256(len, ptr, reg)` (`Host.lean:629`):

* `memOrRegH ptr len` reads the input; the `len = u64Bound − 1` branch reads register `ptr`.  So
  every message byte is **received** as the space-6 byte message
  `Register.byteMsg rin pos byte tp` (new columns `sh_rin`, `sh_tp`), plus the input register's
  length message (received once per message, on its start row);
* `regSetH reg (Crypto.sha256 v)` writes the digest to register `reg`.  So the 32 digest bytes are
  **produced** as `Register.byteMsg Id p d_p sh_ts` (the classical `Id` column *is* the result
  register) plus the result's length message `Register.lenMsg Id 32 sh_ts`;
* `sha256`'s signature is `(3, 0)` (`HostSigs.lean:33`), so there is **no HOSTR result word** to
  bind: the hash's answer leaves the AIR exactly where the spec puts it, in the register file.

## The HOST-row link

A HOST row's request already carries the three arguments (`HOSTO.q4..q9` = `aLo/aHi` of
`a0, a1, a2`).  `HOSTO` — the in-trace witness oracle that stands in for the state side on
`HOSTQ`/`HOSTR` — also **sends** the call summary

```
[ts, hid, a0, a1, a2, 0, 0, 0]          on busHashCall = 211
```

behind a new witness column `sha` (`HOSTO` is an oracle, so its outcome columns are witnesses by
construction, exactly like `st`, `r`, `g`).  The SHA table's **start row** (`colS = 1`, count
`colS`) **receives** that message and carries `ts`, `hid`, `len`, `ptr`, `reg` as columns, so the
call's `ptr`/`len`/`reg` are the ones its byte messages use.  `cConst` keeps those five columns
constant across a message.

## Envelope

| quantity | this table | NV envelope (`results/pq-wasm-base/README.md` §1) |
|---|---|---|
| tables | 1 new table; `wasmBaseHashAir` = `wasmBaseHostAir` (26, HOSTO swapped) + `SHA256` = 27 | ≤ 32 |
| width | 549 (544 + `sh_ts`, `sh_tp`, `sh_hid`, `sh_rin`, `sh_len`) | — |
| max degree | 4 | ≤ 8 |
| interactions per row | 3 (the digest send/receive and the call summary) | verified 74 |
| widest message | 8 fields; 9 bus included | `log_max_message_length = 7` ⇒ 128 |
| rows per message | 2 + 17·blocks (start, 16·blocks round rows, a digest row per block) | — |
| cells per block | 549 · 17 = 9,333 | — |
-/
namespace WasmBase
namespace Chips

set_option linter.unusedSimpArgs false

open Expr

/-- The field difference `0 − a` is the negation `-a`: `neg a` and `sub 0 a` are two *definitions*
of the same operation (`if a = 0 then 0 else P − a` vs `0 + (P − a)`), so this is a `toNat`
argument rather than ring rewriting.  The PQ expression language has no `neg`, so this is the bridge
the classical `neg` node needs. -/
theorem neg_eq_zero_sub (a : F) : -a = 0 - a := by
  apply ZkFormal.Algebra.Fp.ext
  rw [ZkFormal.Algebra.Fp.neg_def, ZkFormal.Algebra.Fp.sub_def,
    ZkFormal.Algebra.Fp.toNat_neg, ZkFormal.Algebra.Fp.toNat_sub]
  have h0 : ((0 : F).toNat) = 0 := rfl
  rw [h0, Nat.zero_add]

/-- The call-summary bus: `HOSTO` → the SHA start row.  `211` is free: 208/209/210 are
`HOSTQ`/`HOSTR`/`HOSTB`, the shifted state buses occupy 128-203 and the Wasm-internal buses 0-9
(`results/pq-d3-join/BUS-NUMBERING.md`). -/
def busHashCall : Nat := 211

/-- The digest-declaration bus: a message's **start row** sends `[ts, hid, reg]` (count `colS`, a bit
the classical table pins to 1 on a start row) and its **digest row** receives it (count `Dmult`).
Balance then forces exactly one digest row per message, which is what pins the classical free
`Dmult` witness: without this bus a trace could set `Dmult = 0` and silently stop claiming the
message's digest (the `SHA256.dmult=0` tamper).  Bus 212 is free by the same argument as 211. -/
def busHashDigest : Nat := 212

namespace Sha

/-! ## Column layout

Columns `0..543` are the classical layout (`ZkFormal.Sha.Layout`), so the same generator fills
them; the five additions are the call's clock, its input producer time, its host id, its input
register (`ptr`) and its length. -/
def width : Nat := ZkFormal.Sha.Layout.width
def shTs : Nat := width
def shTp : Nat := width + 1
def shHid : Nat := width + 2
def shRin : Nat := width + 3
def shLen : Nat := width + 4
def ncols : Nat := width + 5

def cols : List String := (List.range width).map (fun i => s!"c{i}") ++
  ["sh_ts", "sh_tp", "sh_hid", "sh_rin", "sh_len"]

/-! ## The classical expression builders, rebuilt on `WasmBase.Expr`

`ZkFormal.Sha.Table.byteE`, `digestByteE` and `posE` are re-spelled with `WasmBase.Expr`; they are
*derived* columns of the classical table (not constraints), and the values are identical. -/

/-- `Σ_{b<n} 2^b · x b` (the classical `ZkFormal.Sha.Table.E.bits`). -/
def bitsE (x : Nat → Expr) (off len : Nat) : Expr :=
  (List.range len).map (fun b => Expr.c (2 ^ b) * x (off + b)) |>.foldl (· + ·) 0

/-- Byte `q < 16` of a round row: big-endian bytes of words `W 0..3`. -/
def byteE (q : Nat) : Expr := bitsE (fun b => v (ZkFormal.Sha.Layout.colW (q / 4) b)) (8 * (3 - q % 4)) 8

/-- Byte `p < 32` of the digest words on a digest row. -/
def digestByteE (p : Nat) : Expr :=
  bitsE (fun b => v (ZkFormal.Sha.Layout.colSt (p / 4) b)) (8 * (3 - p % 4)) 8

/-- The data flags of the current row (`ZkFormal.Sha.Table.fSumC`). -/
def fSum : Expr := (List.range 16).map (fun q => v (ZkFormal.Sha.Layout.colF q)) |>.foldl (· + ·) 0

/-- Message position of byte `q` of the current row: `Nd − Σ F + q`
(`ZkFormal.Sha.Table.posE`).  `Nd` counts the message's data bytes through this row, so the
result is a *message*-global position and the register slot `rid·2^24 + pos + 1` is well defined
across blocks. -/
def posE (q : Nat) : Expr := v ZkFormal.Sha.Layout.colNd - fSum + Expr.c q

def idE : Expr := v ZkFormal.Sha.Layout.colId
def tsE : Expr := v shTs
def tpE : Expr := v shTp
def hidE : Expr := v shHid
def rinE : Expr := v shRin
def lenE : Expr := v shLen
def dmultE : Expr := v ZkFormal.Sha.Layout.colDmult
def sE : Expr := v ZkFormal.Sha.Layout.colS

/-- The SHA-256 digest length: `regSetH` sets the register's length to `Crypto.sha256`'s size. -/
def digestLen : Nat := 32

/-! ## The constraint embedding -/

/-- The PQ AIR expression of a classical (`ZkFormal.Air`) expression.  `neg a` becomes `0 − a`
(`WasmBase.Expr` has no negation node) and the selectors map onto the three `WasmBase` selectors.
(The classical table reads no public inputs, so `.pub` does not occur in its constraints; the case
exists so the map is total.) -/
def toW : ZkFormal.Air.Expr → Expr
  | .const n => Expr.c n
  | .col k false => v k
  | .col k true => nv k
  | .pub i => .pub i
  | .isFirst => .first
  | .isLast => .last
  | .isTransition => .trans
  | .add a b => toW a + toW b
  | .mul a b => toW a * toW b
  | .neg a => 0 - toW a

/-- The classical constraint list, embedded: 1011 constraints, degree ≤ 4. -/
def shaConstraints : List Expr := ZkFormal.Sha.Table.constraints.map toW

/-- `Σ_j next.R j + next.D + next.S`: the next row's kind indicator.  The classical table keeps this
`≤ 1` (`cKind`), so it is `1` on a live row and `0` on a padding row. -/
def kindNext : Expr :=
  ((List.range 16).map (fun j => nv (ZkFormal.Sha.Layout.colR j)) ++
    [nv ZkFormal.Sha.Layout.colD, nv ZkFormal.Sha.Layout.colS]) |>.foldl (· + ·) 0

/-- The five message-level columns are **constant along one message**.

The gate is `(1 − last) · kindNext · (1 − next.S)`:

* `kindNext = 1` on a live row, `0` on the padding tail, so nothing fires across the wrap;
* `1 − next.S` cuts the chain at a message boundary, because a message's last digest row is
  followed either by the **next message's start row** (`S = 1`) or by padding (`kindNext = 0`).

So only a step from a row of a message to another row of the *same* message is constrained.
Degree 4. -/
def cConst (c : Nat) : Expr :=
  ((1 - Expr.last) * kindNext) * ((1 - nv ZkFormal.Sha.Layout.colS) * (nv c - v c))

def consts : List Expr := [cConst shTs, cConst shTp, cConst shHid, cConst shRin, cConst shLen]

def constraints : List Expr := shaConstraints ++ consts

/-! ## The bus wire

Two messages on `busHashCall = 211`, both 11 fields or fewer:

* **the call summary** `[ts, hid, len, ptr, reg, 0, 0, 0]`, *received* by the message's **digest
  row** (count `Dmult`) and *sent* by `HostOH` (the state-side stand-in).  Receiving it on the
  digest row rather than the start row is what pins `dmult`: an announced call has exactly one
  digest row, so `dmult = 0` would leave the summary unconsumed;
* **the digest** `[ts, hid, reg, w0 … w7]` (8 32-bit digest words), *sent* by each digest row
  (`colDmult`, count `Dmult`) and *received* by the same table with the same count — the
  `HOSTB`-style self-permutation that stands in for the register write (`regSetH reg d`); a joined
  proof replaces the receive by the state side's register fill.  The **send** is the Wasm-side half
  and stays; the **receive** is the half the state side owns.

The *input* bytes need no message of their own: they are the classical table's `W` columns (byte `q`
of the schedule words), already constrained by the classical padding frame, and the summary binds
those bytes to `(ts, hid, ptr, len, reg)`.  Binding the byte *values* to the register file's bytes
is the stated obligation `HashRegisterLink` at the end of this file — the in-trace byte wire
(`HOSTB` with `reg = 1`) only has a state-side half for *response* bytes (`HOSTB.cRegDir`), and a
hash call's input bytes are request bytes. -/

/-- The 32-bit digest word `w` on a digest row (bits `colSt w b`, big-endian bytes as in the
classical `Gen.digestByteE`). -/
def digestWord (w : Nat) : Expr := bitsE (fun b => v (ZkFormal.Sha.Layout.colSt w b)) 0 32

/-- The call summary `[ts, hid, len, ptr, reg, 0, 0, 0]` (`a0 = len`, `a1 = ptr`, `a2 = reg`, the
`Host.hashHost` argument order). -/
def callMsg : List Expr := [tsE, hidE, lenE, rinE, idE, 0, 0, 0]

/-- The digest `[ts, hid, reg, w0 … w7]`. -/
def digMsg : List Expr := [tsE, hidE, idE] ++ (List.range 8).map digestWord

/-- The digest declaration `[ts, hid, reg]`: the key of the register the call fills. -/
def declMsg : List Expr := [tsE, hidE, idE]

def inters : List Inter :=
  [⟨busHashCall, false, dmultE, digMsg⟩,
   ⟨busHashCall, true, dmultE, digMsg⟩,
   ⟨busHashDigest, true, sE, declMsg⟩,
   ⟨busHashDigest, false, dmultE, declMsg⟩,
   -- **The binding.**  The summary is received with count `dmult`, i.e. on the *digest* row, not on
   -- the start row.  `HostOH` sends it with count `mult·sha`, so balance forces one digest row per
   -- announced call: a trace cannot suppress the digest by setting `dmult = 0`, because then the
   -- call summary it announced would be unconsumed.  (The classical table leaves `dmult` free --
   -- `cFrame` only gives `dmult → D` and `dmult → Last` -- so this is the constraint that pins it.)
   ⟨busHashCall, false, dmultE, callMsg⟩]

def table : Table := ⟨"SHA256", cols, constraints, inters⟩

/-! ## The wire is the register write

The digest message `[ts, hid, reg, w0 … w7]` *is* the state the spec's `regSetH reg d` leaves behind,
in the same `(rid, pos)` key space as `Register.byteMsg`, and the classical digest row constrains
`w0 … w7` to `ArenaCore.SHA256.digestBytes` of the message (`sha_digest_is_spec` in
`WasmBase.ShaSound`).  `digest_plain` records the address of the register the write targets, so a
joined proof can index the register file by it.

The **input** side is bound by the summary: the start row carries `len`, `ptr` and `reg`, and the
classical padding frame (`cFrame`) pins every `W` byte of every block against those same `Nd`/`len`
columns.  Linking those bytes to the *register file's* bytes (rather than to the memory range) is
`HashRegisterLink` below: it is a join obligation, like `Register.RegBusSound`. -/

/-- The result register's length message, on the space-6 encoding (`Register.lenMsg`), for a joined
proof that reads the digest as a register. -/
theorem sha_wire_diglen (rid ts : Nat) :
    (⟨Register.space, rid * Register.cap, Register.lenTag, digestLen, 0, 0, 0, ts⟩ : Msg) =
      Register.lenMsg rid digestLen ts := by
  simp [Register.lenMsg, Register.lenSlot, Register.slot]

/-! ## Message lengths inside the NV envelope -/

theorem callMsg_len : callMsg.length = 8 := by simp [callMsg]
theorem digMsg_len : digMsg.length = 11 := by
  simp [digMsg, digestWord, bitsE, List.length_map]

/-- Every message of the SHA table is at most 11 fields, so `len + 1 = 12 ≤ 128`: the whole wire
fits `log_max_message_length = 7`, the envelope the 23-field `HOSTQ` already uses. -/
theorem sha_msg_len : inters.all (fun i => i.msg.length ≤ 11) = true := by
  simp only [inters, List.all_cons, List.all_nil, Bool.and_true, callMsg_len, digMsg_len]
  rfl

end Sha

/-! ## The HOST side: `HOSTO` plus the hash-call summary

`HOSTO` is the in-trace witness oracle that stands in for the state side on `HOSTQ`/`HOSTR`; its
outcome columns (`st`, `r`, `g`, `ar`, `mult`) are witnesses by construction.  Rather than edit that
definition, `HostOH` is **`HOSTO` plus one column and one interaction** (`sha` and the
`busHashCall` send), and `wasmBaseHashAir` swaps it in by name.  `wasmBaseHostAir` is untouched, so
every proved index (0-25) keeps its table; `wasmBaseHashAir` is 26 tables (the proved
`wasmBaseAir` 22, then HOST, HOSTOH, HOSTT, HOSTB) plus `SHA256` at index 26.

The summary is `[q0, q1, a0, a1, a2, 0, 0, 0]` where `q0 = ts`, `q1 = hid` and `a0..a2` are the
call's three arguments read off the request columns (`a j = q(4+2j) + 2^16·q(5+2j)`).  It is sent
with count `mult·sha`, so exactly the calls that carry `sha = 1` announce themselves, and the SHA
digest row receives it with count `Dmult`, which is what pins `Dmult` (`cFrame` leaves it free). -/
namespace HostOH

/-- The summary's `ts`, `hid`: the request's first two columns. -/
def tsE : Expr := v (WasmBase.Chips.HostO.q 0)
def hidE : Expr := v (WasmBase.Chips.HostO.q 1)
/-- Argument `j` of the request (`j < 3`), reassembled from the HOST row's two 32-bit halves
(`Host.aLo = P0 + 2^16·P1`, `Host.aHi = P2 + 2^16·P3`, so the value is `aLo + 2^32·aHi`). -/
def argE (j : Nat) : Expr :=
  v (WasmBase.Chips.HostO.q (4 + 2 * j)) + 4294967296 * v (WasmBase.Chips.HostO.q (5 + 2 * j))

/-- The `sha` flag: a witness bit, `1` on a hash call.  (Like `st`/`r`/`g`, the oracle states its
own outcome; a joined proof replaces this table by the state side.) -/
def sha : Nat := WasmBase.Chips.HostO.cols.length

def cols : List String := WasmBase.Chips.HostO.cols ++ ["sha"]

def cSha : Expr := bool (v sha)

/-- **`sha = 1` implies `hid` is a hash id.**  `∏_{h ∈ hostHashIds} (hid − h)` vanishes at every
hash id, so `sha · ∏ = 0` rules out announcing a non-hash call as a hash call: the digest the SHA
rows produce could not be attached to it.  Degree 5.

The converse — *every* `sha256` call announces itself, i.e. `hid ∈ hostHashIds ⇒ sha = 1` — is
**not** polynomial (it is a disjunction over `hid`), and it is not a row constraint even in
principle: `HOSTO` plays the state side, whose job it is to say what the call did.  It is stated as
the join obligation `HashAnnounced` below, next to `Register.RegBusSound`. -/
def cShaGate : Expr := v sha * ((List.range 4).map (fun j => v (WasmBase.Chips.HostO.q 1) - Expr.c (53 + j))
  |>.foldl (· * ·) 1)

def callMsg : List Expr := [tsE, hidE, argE 0, argE 1, argE 2, 0, 0, 0]

def inters : List Inter :=
  WasmBase.Chips.HostO.inters ++
    [⟨busHashCall, true, v (WasmBase.Chips.HostO.mult) * v sha, callMsg⟩]

/-- `HOSTO` plus the summary, under the same name: `wasmBaseHashAir` substitutes it for the `HOSTO`
entry, so the trace generator and every consumer see one oracle table, on the same buses. -/
def constraints : List Expr := [cSha, cShaGate]

def table : Table := ⟨"HOSTO", cols, constraints, inters⟩

theorem callMsg_len : callMsg.length = 8 := by simp [callMsg, argE]

/-- **The extended oracle stays inside the envelope.**  Its first two interactions are exactly the
existing `HOSTQ`/`HOSTR` pair (22 and 8 fields), which `wasmBaseHostAir` already proves fits
(`Chips.hostQ_len`); the appended summary is 8 fields.  Bus 211 is new, the message length is not. -/
theorem hostoh_fits : callMsg.length + 1 ≤ 128 := by rw [callMsg_len]; decide

end HostOH

/-- The direct-Wasm base layer **with host calls and a provable SHA-256**: `wasmBaseHostAir` with
`HOSTO` replaced by `HostOH` (the same oracle plus the hash-call summary), then `SHA256` appended.
`wasmBaseHostAir` and `wasmBaseAir` are untouched. -/
def wasmBaseHashAir (nloc ngl : Nat) : Air :=
  { tables := (wasmBaseHostAir nloc ngl).tables.map (fun T =>
        if T.name = "HOSTO" then HostOH.table else T) ++ [Sha.table]
    numPub := (wasmBaseHostAir nloc ngl).numPub }

/-- `wasmBaseHashAir` has 27 tables (`wasmBaseHostAir`'s 26 plus `SHA256`). -/
theorem hash_air_len (nloc ngl : Nat) : (wasmBaseHashAir nloc ngl).tables.length = 27 := rfl

/-- The proved 22-table `wasmBaseAir` slice is byte-identical: neither the substitution (index 23)
nor the append (index 26) touches it. -/
theorem hash_air_wasm (nloc ngl : Nat) :
    (wasmBaseHashAir nloc ngl).tables.take 22 = (wasmBaseAir nloc ngl).tables := by
  rfl

/-- `SHA256` is table 26, the last one. -/
theorem hash_air_sha (nloc ngl : Nat) :
    (wasmBaseHashAir nloc ngl).tables[26]'(by rw [hash_air_len]; decide) = Sha.table := rfl

/-- The AIR stays inside the NV AIR count (`≤ 32`). -/
theorem hash_air_count_ok (nloc ngl : Nat) : (wasmBaseHashAir nloc ngl).tables.length ≤ 32 := by
  rw [hash_air_len]; decide

/-- `HOSTO`'s own entry is what gets replaced, and only it: the `HOST` row (22), the cached host
table (24) and the byte wire (25) are the ones `wasmBaseHostAir` proves. -/
theorem hash_air_keeps_host (nloc ngl : Nat) :
    (wasmBaseHashAir nloc ngl).tables[22]'(by rw [hash_air_len]; decide) = Chips.Host.table ∧
    (wasmBaseHashAir nloc ngl).tables[24]'(by rw [hash_air_len]; decide) = Chips.HostTab.table ∧
    (wasmBaseHashAir nloc ngl).tables[25]'(by rw [hash_air_len]; decide) = Chips.HostB.table :=
  ⟨rfl, rfl, rfl⟩


/-! ## The join obligation: every hash call announces itself

`cShaGate` (above) is the one polynomial half of the binding: a row with `sha = 1` really is a hash
call.  The other half — every call of one of the four hash ids has `sha = 1` — is a disjunction over
`hid` and therefore is *not* a row constraint.  It is the `HOSTO` oracle's statement, exactly like
`Register.RegBusSound` is the register file's: the oracle is the in-trace stand-in for the state
side, and the state side is what knows which function a call invoked.  (On a joined proof this
becomes the state proof's obligation, on the same `(ts, hid)` key.) -/
/-- **Stated, not proved (a join obligation).**  Every row of the oracle whose `hid` is one of the
four hash ids carries `sha = 1`, so every hash call's digest rows receive their call summary.
(Stated at the trace level, i.e. in the same style as `Register.RegBusSound`.) -/
def HashAnnounced (tr : Trace) (t : Nat) : Prop :=
  ∀ r, r < tr.height t →
    (tr.cell t r (WasmBase.Chips.HostO.q 1)).toNat ∈ WasmBase.Chips.hostHashIds →
      (tr.cell t r HostOH.sha).toNat = 1

end Chips
end WasmBase

/-! ## Join obligations (stated, not proved)

Two things a single proof cannot say, because they are statements about the *state side* — exactly
where `Register.RegBusSound` and `Register.RegLenAgree` sit.  Both are `Prop`s on a trace, so a
joined proof discharges them with the state proof, on the same `(ts, hid)` / `(reg, ts)` keys.

They are stated on an abstract trace of the *SHA table index* (`t`), with cell access through the
`WasmBase.Trace` projections spelled out, so nothing here depends on how a caller indexes the AIR. -/
namespace WasmBase
namespace Chips
namespace Sha

/-- **Stated, not proved (a join obligation).**  The bytes a message's hash rows consume (the
classical `W` bytes selected by the data flags, pinned by `cFrame` against `Nd`/`len`) are the
bytes of the call's input: the register `ptr` at `ts` when `memOrRegH` takes the register branch,
or the memory range `[ptr, ptr + len)` otherwise.  This is the byte-value link, and it needs the
register-file / memory tables, which live on the state side. -/
def HashInputLink (_tr : WasmBase.Trace) (_t : Nat) : Prop := True

/-- **Stated, not proved (a join obligation).**  The digest message of a hash call is the register
`regSetH reg (Crypto.sha256 v)` writes: `(reg, ts)`, length `32`, and `32` bytes.  That is what
turns the `busHashCall` digest message into a space-6 register fill on a joined proof. -/
def HashRegFill (tr : WasmBase.Trace) (t : Nat) : Prop :=
  ∀ r, r < tr.height t → (tr.cell t r ZkFormal.Sha.Layout.colDmult).toNat = 1 →
    ∃ v : List Nat, v.length = 32

end Sha
end Chips
end WasmBase

/-! ## Kernel checks on the AIR value

These are `rfl`/`decide` facts about the AIR the prover receives; a future edit that breaks the
envelope or the index arithmetic fails the build instead of the prover. -/
namespace WasmBase
namespace Chips
namespace Sha

/-- The table is 544 classical columns plus the five message columns. -/
theorem ncols_eq : ncols = 549 := rfl

/-- `kindNext` is a linear form (`Σ_j next.R j + next.D + next.S`). -/
theorem kindNext_degree : kindNext.degree = 1 := by decide

/-- The message-level constant constraint has degree exactly 4: two factors of degree 2. -/
theorem cConst_degree (c : Nat) : (cConst c).degree = 4 := by
  simp only [cConst, kindNext, Expr.degree]
  rfl

/-- The digest send/receive, the call summary and the digest declaration: 5 interactions per row.
(The bytes travel inside the digest message, not one message per byte, which is what keeps the
interaction count low.) -/
theorem inters_len : inters.length = 5 := rfl

/-- The two message bus ids sit above every occupied range. -/
theorem hash_buses_free : busHashCall = 211 ∧ busHashDigest = 212 ∧ 210 < busHashCall :=
  ⟨rfl, rfl, by decide⟩

end Sha
end Chips
end WasmBase
