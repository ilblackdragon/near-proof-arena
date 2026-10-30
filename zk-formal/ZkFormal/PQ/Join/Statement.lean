import ZkFormal.NearV3.D3.ContractData
import ZkFormal.V2.Air
import NearSpecV3.D3.FunctionCall
import NearSpecV3.D3.Signed

/-!
# `ZkFormal.PQ.Join.Statement` — the joint statement of a Wasm FunctionCall proof and a state proof

Lane `pq-d3-join`.  **This file states the joint relation; it proves nothing about a full AIR.**
Every `Prop` here is a *definition of the obligation*, labelled unproved, and is meant to be
discharged by the two side theorems plus the cross-proof bus balance.

## The two proofs

* **Wasm FunctionCall proof** (`lane/pq-wasm-base`, §14.2 of its README): the base AIR
  `wasmBaseAir` over the contract code, with the HOST chip, the register space and the
  `g_after` budget register.  Its public values are the base statement (`N, S_final, nres, rtag,
  result, status, mem, dataEnd, local tags, globals, stackRem`) plus the cached-commitment
  statement components (`code_root`, and `code_hash` from the state side), plus the HOST
  traffic's cached commitments.
* **State proof** (this lane's D0a/D1 port, plus the D3 `ContractData` work): `nearAirV3D1`
  (or `nearAirV3` for D0a) with the walk/`upsV3`/SHA tables, producing `HoldsP` and then the
  D3 relation through `runCall` (`NearSpecV3.D3.functionCall`, `d3Hooks`).

The proofs are **not** merged into one AIR: each is independently proved and verified, and the
join is a statement over their public values plus a shared host wire.  This mirrors
`docs/logs/pq-gap-analysis-2026-10-19.md` §2.1–2.3 and `pq-wasm-base` §14.2.

## The host wire

A `storage_write` on the Wasm side is one `HOSTQ` request, a `HOSTB` byte stream for the key and
value, and one `HOSTR` response.  The state side consumes `HOSTQ` as the driver of a ContractData
walk and an `upsV3` upsert, and produces `HOSTR` from the gas and value it computed.  The messages
are field-element lists over BabyBear; bytes are one field element each, exactly as the existing
`VBYTES (vid, pos, byte)` and `BYTES (Id, pos, byte)` buses.

## Revision (2026-10-21, lane `pq-actionr`): the wire is now the HOST chip's wire

The first version of this file predated the widened HOST chip
(`research/near-compression/wasm-base-lean/WasmBase/HostChip.lean`, `pq-host-promise` DESIGN
§1.3).  It declared `HOSTQ` as 8 fields (`[ts, hid, S, a0 … a4]`) and `HOSTB` as 4
(`[ts, dir, pos, byte]`).  Those shapes are **not** the chip's, so a joined proof using them could
never balance: `Receipt/Ids.lean`'s `hostQ_no_bridge`/`hostB_no_bridge` prove the widths differ.
This file now matches the chip:

| bus | id | shape | fields |
|---|---:|---|---:|
| `HOSTQ` | 208 | `[ts, hid, S, np, (aLo j, aHi j) for j < 9]` | **22** |
| `HOSTR` | 209 | `[ts, status, r_lo, r_hi, g_after_lo, g_after_hi, ar, 0]` | 8 |
| `HOSTB` | 210 | `[ts, hid, dir, pos, byte]` | **5** |

Three shape facts, all proved here (`hostQ_width`, `hostR_width`, `hostB_width`) and two gap facts
(`hostQ_old_not_current`, `hostB_old_not_current`):

* the request carries the **full 9-argument window** as `(aLo j, aHi j)` 16-bit limb pairs, plus
  the signature arity `np`.  `np` is a function of `hid` (the fixed host table, bound like
  `FUNC`); the slots `j ≥ np` are zero, which `hostQOfArgs_pad'` proves for the canonical request
  builder.  The chip's `Host.qMsg` is this list (same fields, same order).
* `HOSTR`'s seventh field is the signature's result count `ar` (`0` or `1`), not a literal zero:
  the chip sends `[ts, st, rLo, rHi, gLo, gHi, ar, 0]` and the state side's `rSend`
  (`Receipt/Wire.lean`) forwards the class's `ar`.  A `0` there would make an `ar = 1` response
  unbalanceable.  Width is unchanged at 8.
* `HOSTB` groups carry `hid` next to `ts`: that pair is what ties a byte group to the request it
  belongs to.  Without it a byte stream could be spliced onto another call with the same `ts`
  policy.

`dir = 0` is Wasm → state (key/value bytes of a write), `dir = 1` is state → Wasm (a register
filled by `storage_read`, the `input`, a context string).  `ts` is the Wasm row clock and is
strictly increasing across the calls of one execution; `S` is the instruction-gas count so far.
`hid` indexes the fixed host-function table (bound to the statement like `FUNC`).

The HOST buses are `208/209/210`: above `nearBuses = 77` and above the `pq-state-port` export's
`BUS_OFFSET = 128` shift (so a classical bus `b` exports as `128 + b ≤ 128 + 76 = 204`, and the
HOST ids must therefore be `> 204`), and above the Wasm base family's ids `0 … 9`
(`WasmBase/HostChip.lean`: `HOSTQ = 208`, `HOSTR = 209`, `HOSTB = 210`, `HOSTT = 9`).  Checked by
`host_bus_safe` below. -/

namespace ZkFormal.PQ.Join

open ZkFormal.Air ZkFormal.V2

/-- The HOST request bus id.  Must lie outside every classical bus after the `pq-state-port`
`BUS_OFFSET = 128` shift (`128 + 76 = 204`) and outside the Wasm base ids (`0 … 9`, of which
`HOSTQ/HOSTR/HOSTT` are `208/209/9`). -/
def B_HOSTQ : Nat := 208
/-- The HOST response bus id. -/
def B_HOSTR : Nat := 209
/-- The HOST byte bus id. -/
def B_HOSTB : Nat := 210

/-- `BUS_OFFSET` used by `research/near-compression/native/pq-state-port/src/main.rs`. -/
def stateBusOffset : Nat := 128
/-- The largest classical bus id (`nearBuses - 1`). -/
def stateBusMax : Nat := 76
/-- The largest Wasm base bus id.  `WasmBase/Chips.lean` uses `0 … 6` and the HOST chip adds
`HOSTT = 9` (`WasmBase/HostChip.lean:60`), so the family reaches 9 — the same constant as
`PQ/StatePort/Join.lean`'s `wasmBusMax`. -/
def wasmBusMax : Nat := 9

/-- The join's bus ids do not collide with either side's shifted ids.  Kernel fact. -/
theorem host_bus_safe :
    wasmBusMax < B_HOSTQ ∧ stateBusOffset + stateBusMax < B_HOSTQ ∧
      B_HOSTQ + 1 = B_HOSTR ∧ B_HOSTR + 1 = B_HOSTB := by
  decide +kernel

/-! ## Host messages

The three message builders below are the wire the HOST chip speaks
(`WasmBase/HostChip.lean`): `Host.qMsg`, `HostR`'s receive and `HostB.msg`.  They are *the*
definitions on the join side; `Receipt/Ids.lean`'s `hostQ22`/`hostB5`/`hostR8` are the same
functions, and `Ids.hostQ22_eq_join` / `hostB5_eq_join` / `hostR8_split` prove the two spellings
coincide.  So there is one wire, not two. -/

/-- Split a `Nat` into two 16-bit limbs. -/
def lo16 (n : Nat) : Nat := n % 65536
def hi16 (n : Nat) : Nat := n / 65536

/-- The HOST chip's argument-window width (`Host.nArgs = 9`): the D3α maximum
(`promise_then`, `promise_yield_create_with_id`,
`promise_batch_action_add_key_with_function_call`). -/
def nHostArgs : Nat := 9

/-- One argument of a HOST request, in the chip's two-word form: `lo` is limbs 0–1 and `hi` is
limbs 2–3 of the argument's 64-bit value (`HostChip.lean:241-242`: `aLo j = P₀ + 2¹⁶·P₁`,
`aHi j = P₂ + 2¹⁶·P₃`). -/
def argWords (w : Nat) : Nat × Nat := (lo16 w, hi16 w)

/-- `(aLo j, aHi j)` for the whole argument window, zero after the call's `np` arguments. -/
def argWindow (args : List Nat) (j : Nat) : Nat × Nat :=
  argWords (args.getD j 0)

/-- Argument `j` of a request, as the chip lays it out: the low and high words as a two-element
list.  Splitting `hostQ` this way makes the length and indexing lemmas elementary. -/
def pairAt (a : Nat → Nat × Nat) (j : Nat) : List Nat := [(a j).1, (a j).2]

/-- **`HOSTQ`: the request of one host call** (`Host.qMsg`): the 4-field header
`[ts, hid, S, np]` then the 9 `(aLo j, aHi j)` pairs — 22 fields.

`ts` is the Wasm row clock, `hid` the fixed host-table id, `S` the instruction-gas count so far
and `np` the call's arity (`np ≤ nHostArgs`).  The slots `j ≥ np` are `(0, 0)`; `hostQOfArgs_pad`
proves the builder puts them there, so the *shape* does not depend on `np`. -/
def hostQ (ts hid s np : Nat) (a : Nat → Nat × Nat) : List Nat :=
  [ts, hid, s, np] ++ (List.range nHostArgs).flatMap (pairAt a)

/-- **`HOSTR`: the response** (`[ts, st, rLo, rHi, gLo, gHi, ar, 0]`, 8 fields).  `st = 0` is ok,
`1` a host abort (the chip's `g := g_after` still applies); `r` is the result word; `gAfter` is
the state side's resynchronised budget; `ar` is the *signature's* result count (0 or 1), which the
chip sends and the state side forwards (`Receipt/Wire.lean`'s `rSend`). -/
def hostR (ts status r gAfter ar : Nat) : List Nat :=
  [ts, status, lo16 r, hi16 r, lo16 gAfter, hi16 gAfter, ar, 0]

/-- **`HOSTB`: one byte of a payload** (`HostB.msg`): `[ts, hid, dir, pos, byte]`, 5 fields.
`dir = 0` is Wasm → state, `dir = 1` state → Wasm; `hid` ties the byte group to its request. -/
def hostB (ts hid dir pos byte : Nat) : List Nat := [ts, hid, dir, pos, byte]

/-- The request of a call whose arguments are listed in order: `np = args.length` (capped at the
window) and the tail slots are zero.  This is the constructor the row lemmas below are about. -/
def hostQOfArgs (ts hid s : Nat) (args : List Nat) : List Nat :=
  hostQ ts hid s (min args.length nHostArgs) (argWindow args)

/-! ### Elementary list facts about the two-field encoding

`hostQ` is a `flatMap` of two-element lists, so its length and its `getD` at `4 + 2j` are two
inductions over `List.range`.  They are proved once, here, and every shape lemma is then `rfl` or
one rewrite. -/

/-- `getD` of a prefix is the prefix's own `getD`. -/
theorem getD_append_left (a b : List Nat) (i d : Nat) (hi : i < a.length) :
    (a ++ b).getD i d = a.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- `getD` past a prefix is the suffix's `getD`. -/
theorem getD_append_right (a b : List Nat) (i d : Nat) :
    (a ++ b).getD (a.length + i) d = b.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

theorem flatMap_range_succ (f : Nat → List Nat) (k : Nat) :
    (List.range (k + 1)).flatMap f = (List.range k).flatMap f ++ f k := by
  rw [List.range_succ, List.flatMap_append]
  simp

/-- A `flatMap` of two-element lists over `range n` has `2n` entries.  (Stated for the literal
`2` rather than a general stride: that is all the chips' pair encodings need, and the induction is
then `Nat.mul_succ`.) -/
theorem flatMap_range_len2 (f : Nat → List Nat) (hf : ∀ k, (f k).length = 2) :
    ∀ n, ((List.range n).flatMap f).length = 2 * n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [flatMap_range_succ, List.length_append, ih, hf, Nat.mul_succ]

/-- Element `2j + i` of the pair encoding is entry `i` of pair `j`. -/
theorem flatMap_range_getD2 (f : Nat → List Nat) (hf : ∀ k, (f k).length = 2) :
    ∀ n j i, j < n → i < 2 →
      ((List.range n).flatMap f).getD (2 * j + i) 0 = (f j).getD i 0 := by
  intro n
  induction n with
  | zero => intro j i hj _; omega
  | succ k ih =>
    intro j i hj hi
    rw [flatMap_range_succ]
    by_cases h : j < k
    · have hl : ((List.range k).flatMap f).length = 2 * k := flatMap_range_len2 f hf k
      have hl2 : 2 * j + i < ((List.range k).flatMap f).length := by rw [hl]; omega
      rw [getD_append_left _ _ _ _ hl2]
      exact ih j i h hi
    · have hj' : j = k := by omega
      subst hj'
      have hl : ((List.range j).flatMap f).length = 2 * j := flatMap_range_len2 f hf j
      rw [show 2 * j + i = ((List.range j).flatMap f).length + i by rw [hl]]
      rw [getD_append_right]

/-! ### The wire's shape lemmas -/

/-- **`HOSTQ` is 22 fields**: `4 + 2·9`. -/
theorem hostQ_width (ts hid s np : Nat) (a : Nat → Nat × Nat) :
    (hostQ ts hid s np a).length = 22 := by
  unfold hostQ nHostArgs
  rw [List.length_append, flatMap_range_len2 _ (fun k => rfl)]
  rfl

/-- **`HOSTR` is 8 fields.** -/
theorem hostR_width (ts status r gAfter ar : Nat) : (hostR ts status r gAfter ar).length = 8 := rfl

/-- **`HOSTB` is 5 fields.** -/
theorem hostB_width (ts hid dir pos byte : Nat) : (hostB ts hid dir pos byte).length = 5 := rfl

/-- The `HOSTQ` header: the first four fields are `ts, hid, S, np` in that order.  This is what
makes `hid` a *function of the request* — the state side can tie a byte group (`HOSTB`'s `hid`) to
the call it belongs to. -/
theorem hostQ_header (ts hid s np : Nat) (a : Nat → Nat × Nat) :
    (hostQ ts hid s np a).take 4 = [ts, hid, s, np] := by
  unfold hostQ
  simp

/-- Field `4 + 2j` of a `HOSTQ` is argument `j`'s low word and `5 + 2j` its high word — the chip's
`aLo j` / `aHi j` at their message positions. -/
theorem hostQ_arg (ts hid s np : Nat) (a : Nat → Nat × Nat) {j : Nat} (hj : j < nHostArgs) :
    (hostQ ts hid s np a).getD (4 + 2 * j) 0 = (a j).1 ∧
      (hostQ ts hid s np a).getD (5 + 2 * j) 0 = (a j).2 := by
  constructor
  · rw [show (4 + 2 * j) = ([ts, hid, s, np] : List Nat).length + (2 * j + 0) by
      simp only [List.length_cons, List.length_nil]; omega]
    rw [hostQ, getD_append_right, flatMap_range_getD2 _ (fun k => rfl) _ _ 0 hj (by decide)]
    rfl
  · rw [show (5 + 2 * j) = ([ts, hid, s, np] : List Nat).length + (2 * j + 1) by
      simp only [List.length_cons, List.length_nil]; omega]
    rw [hostQ, getD_append_right, flatMap_range_getD2 _ (fun k => rfl) _ _ 1 hj (by decide)]
    rfl

/-- `getD` past the end is the default. -/
theorem getD_of_le (l : List Nat) (i d : Nat) (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]

/-- The unused slots of a request built from `args` are zero: a request carries `(0, 0)` in every
slot past the call's arity.  This is what makes the *shape* of the wire independent of `np`. -/
theorem hostQOfArgs_pad' (ts hid s : Nat) (args : List Nat) {j : Nat}
    (hj : args.length ≤ j) (hj' : j < nHostArgs) :
    (hostQOfArgs ts hid s args).getD (4 + 2 * j) 0 = 0 ∧
      (hostQOfArgs ts hid s args).getD (5 + 2 * j) 0 = 0 := by
  unfold hostQOfArgs
  obtain ⟨h1, h2⟩ := hostQ_arg ts hid s (min args.length nHostArgs) (argWindow args) hj'
  rw [h1, h2]
  unfold argWindow argWords lo16 hi16
  have hle : args.length ≤ j := by omega
  rw [getD_of_le _ _ _ hle]
  exact ⟨rfl, rfl⟩

/-- The used slots of a request built from `args` carry the arguments' two words. -/
theorem hostQOfArgs_arg (ts hid s : Nat) (args : List Nat) {j : Nat} (_hj : j < args.length)
    (hj' : j < nHostArgs) :
    (hostQOfArgs ts hid s args).getD (4 + 2 * j) 0 = lo16 (args.getD j 0) ∧
      (hostQOfArgs ts hid s args).getD (5 + 2 * j) 0 = hi16 (args.getD j 0) :=
  hostQ_arg ts hid s _ (argWindow args) hj'

/-- **`HOSTR`'s seventh field is the signature's `ar`**, which is what makes an `ar = 1` response
balance against a state row whose class wants a result word. -/
theorem hostR_ar (ts status r gAfter ar : Nat) : (hostR ts status r gAfter ar).getD 6 0 = ar := rfl

/-- `HOSTR`'s status is its second field. -/
theorem hostR_status (ts status r gAfter ar : Nat) : (hostR ts status r gAfter ar).getD 1 0 = status :=
  rfl

/-- `HOSTB`'s fields, in order: `(ts, hid, dir, pos, byte)`.  The `(ts, hid)` pair is the group
key that ties a byte to its request. -/
theorem hostB_fields (ts hid dir pos byte : Nat) :
    (hostB ts hid dir pos byte).getD 0 0 = ts ∧ (hostB ts hid dir pos byte).getD 1 0 = hid ∧
      (hostB ts hid dir pos byte).getD 2 0 = dir ∧
      (hostB ts hid dir pos byte).getD 3 0 = pos ∧
      (hostB ts hid dir pos byte).getD 4 0 = byte :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A request byte is `dir = 0`; a response byte `dir = 1`. -/
theorem hostB_dir_bit (ts hid pos byte : Nat) :
    (hostB ts hid 0 pos byte).getD 2 0 = 0 ∧ (hostB ts hid 1 pos byte).getD 2 0 = 1 :=
  ⟨rfl, rfl⟩

/-- The host-function table.  Only the entry the `storage_write` prototype needs is named; the
full table is the Wasm statement's (`WasmBase/HostChip.lean` `hostFns`), bound like `FUNC`.

**Note.**  The widened chip's `hostFns` does not yet contain `storage_write` (it is the storage
lane's addition, and its id is that lane's to choose).  This module only needs *some* id for the
request it drives, so the value here is a placeholder bound to the statement's `host_id` slot;
nothing below depends on which id it is. -/
def hostIdStorageWrite : Nat := 0

/-- The request arguments of `storage_write(key_len, key_ptr, val_len, val_ptr, register_id)`
(`Host.lean:693-725`): `np = 5`, all five slots used.  The bytes themselves travel on `HOSTB`,
keyed by `(ts, hid)`; the request gives the lengths and the register. -/
def storageWriteQ (ts gas keyLen keyPtr valLen valPtr regId : Nat) : List Nat :=
  hostQOfArgs ts hostIdStorageWrite gas [keyLen, keyPtr, valLen, valPtr, regId]

/-- **The `storage_write` request is a 22-field `HOSTQ`** — the same width as every other call. -/
theorem storageWriteQ_width (ts gas keyLen keyPtr valLen valPtr regId : Nat) :
    (storageWriteQ ts gas keyLen keyPtr valLen valPtr regId).length = 22 :=
  hostQ_width _ _ _ _ _

/-- The `storage_write` request's argument slots: the five arguments in order (slot `4 + 2j`, and
`5 + 2j` for the high word), slots 5–8 zero.  Note `HOSTQ`'s layout: argument `j` occupies fields
`4+2j` (`aLo j`) and `5+2j` (`aHi j`). -/
theorem storageWriteQ_slots (ts gas keyLen keyPtr valLen valPtr regId : Nat) :
    (storageWriteQ ts gas keyLen keyPtr valLen valPtr regId).getD 4 0 = lo16 keyLen ∧
      (storageWriteQ ts gas keyLen keyPtr valLen valPtr regId).getD 6 0 = lo16 keyPtr ∧
      (storageWriteQ ts gas keyLen keyPtr valLen valPtr regId).getD 8 0 = lo16 valLen ∧
      (storageWriteQ ts gas keyLen keyPtr valLen valPtr regId).getD 10 0 = lo16 valPtr ∧
      (storageWriteQ ts gas keyLen keyPtr valLen valPtr regId).getD 12 0 = lo16 regId := by
  have h0 := (hostQOfArgs_arg ts hostIdStorageWrite gas
    [keyLen, keyPtr, valLen, valPtr, regId] (j := 0) (by simp) (by decide)).1
  have h1 := (hostQOfArgs_arg ts hostIdStorageWrite gas
    [keyLen, keyPtr, valLen, valPtr, regId] (j := 1) (by simp) (by decide)).1
  have h2 := (hostQOfArgs_arg ts hostIdStorageWrite gas
    [keyLen, keyPtr, valLen, valPtr, regId] (j := 2) (by simp) (by decide)).1
  have h3 := (hostQOfArgs_arg ts hostIdStorageWrite gas
    [keyLen, keyPtr, valLen, valPtr, regId] (j := 3) (by simp) (by decide)).1
  have h4 := (hostQOfArgs_arg ts hostIdStorageWrite gas
    [keyLen, keyPtr, valLen, valPtr, regId] (j := 4) (by simp) (by decide)).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [storageWriteQ] using h0
  · simpa [storageWriteQ, show (6 : Nat) = 4 + 2 * 1 by omega] using h1
  · simpa [storageWriteQ, show (8 : Nat) = 4 + 2 * 2 by omega] using h2
  · simpa [storageWriteQ, show (10 : Nat) = 4 + 2 * 3 by omega] using h3
  · simpa [storageWriteQ, show (12 : Nat) = 4 + 2 * 4 by omega] using h4

/-- The `storage_write` request's **unused** slots (`j = 5 … 8`) are zero. -/
theorem storageWriteQ_pad (ts gas keyLen keyPtr valLen valPtr regId j : Nat)
    (hj : 5 ≤ j) (hj' : j < nHostArgs) :
    (storageWriteQ ts gas keyLen keyPtr valLen valPtr regId).getD (4 + 2 * j) 0 = 0 ∧
      (storageWriteQ ts gas keyLen keyPtr valLen valPtr regId).getD (5 + 2 * j) 0 = 0 :=
  hostQOfArgs_pad' _ _ _ _ (by simp; omega) hj'

/-! ### The pre-widening shapes, kept only to state the gap

Before `pq-host-promise` widened the HOST chip, this file declared `HOSTQ` as 8 fields
`[ts, hid, S, a0 … a4]` and `HOSTB` as 4 (`[ts, dir, pos, byte]`).  Those definitions are gone
from the wire; they are kept here, spelled exactly, **so that `Receipt/Ids.lean`'s
`hostQ_no_bridge` / `hostB_no_bridge` can still state what was wrong**: a message of the old width
can never be a message of the current width, so a joined proof that kept them would fail to
balance loudly rather than merge two different wires. -/

/-- The pre-widening `HOSTQ`: 8 fields, at most five arguments, no `np`. -/
def hostQOld (ts hid gas : Nat) (args : List Nat) : List Nat :=
  [ts, hid, gas] ++ args ++ List.replicate (5 - min args.length 5) 0

/-- The pre-widening `HOSTB`: 4 fields, no `hid`. -/
def hostBOld (ts dir pos byte : Nat) : List Nat := [ts, dir, pos, byte]

/-- The old `HOSTQ` is 8 fields wide when at most five arguments are present. -/
theorem hostQOld_width (ts hid gas : Nat) (args : List Nat) (h : args.length ≤ 5) :
    (hostQOld ts hid gas args).length = 8 := by
  unfold hostQOld
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  omega

/-- The old `HOSTB` is 4 fields wide. -/
theorem hostBOld_width (ts dir pos byte : Nat) : (hostBOld ts dir pos byte).length = 4 := rfl

/-- **The old and current `HOSTQ` are different messages.**  8 fields against 22. -/
theorem hostQ_old_not_current (ts hid gas : Nat) (args : List Nat) (h : args.length ≤ 5)
    (ts' hid' s' np' : Nat) (a : Nat → Nat × Nat) :
    hostQOld ts hid gas args ≠ hostQ ts' hid' s' np' a := by
  intro he
  have h1 := congrArg List.length he
  rw [hostQOld_width ts hid gas args h, hostQ_width] at h1
  exact absurd h1 (by decide)

/-- **The old and current `HOSTB` are different messages.**  4 fields against 5. -/
theorem hostB_old_not_current (ts dir pos byte ts' hid' dir' pos' byte' : Nat) :
    hostBOld ts dir pos byte ≠ hostB ts' hid' dir' pos' byte' := by
  intro he
  have h1 := congrArg List.length he
  rw [hostBOld_width, hostB_width] at h1
  exact absurd h1 (by decide)

/-! ## The wire

One `wire` is the shared, time-ordered stream of host messages.  It is the *only* cross-proof
object: the two proofs each project it onto their own bus traffic, and the aggregation checks that
both projections are the same multiset. -/

structure Wire where
  /-- every request, in `ts` order -/
  q : List (List Nat)
  /-- every response, in `ts` order -/
  r : List (List Nat)
  /-- every byte, in `(ts, dir, pos)` order -/
  b : List (List Nat)
  deriving Repr, DecidableEq, Inhabited

/-- `ts` strictly increases along the request stream.  This is what lets the state side process
requests as a sequence and reuse the trie overlay in order. -/
def Wire.tsIncreasing (w : Wire) : Prop :=
  (w.q.map (·.getD 0 0)).Pairwise (· < ·)

/-- Every response answers the request at the same `ts`. -/
def Wire.responsesMatch (w : Wire) : Prop :=
  w.q.map (·.getD 0 0) = w.r.map (·.getD 0 0)

/-- The byte group of the wire at `(ts, hid, dir)` — the bytes of one payload in one direction. -/
def Wire.group (w : Wire) (ts hid dir : Nat) : List (List Nat) :=
  w.b.filter fun m => m.getD 0 0 = ts ∧ m.getD 1 0 = hid ∧ m.getD 2 0 = dir

/-- **`HOSTB` well-formedness.**  Every byte is a 5-field message (`hostB_width`), and for every
`(ts, hid, dir)` group the positions are exactly `0, 1, … , n−1` in wire order — the contiguous
`pos` discipline `WasmBase/HostChip.lean`'s `HostB` table enforces (`cPos`).  Grouping by
`(ts, hid, dir)` rather than by `(ts, dir)` is what the widened `HOSTB` message forces: two calls
in one execution can share a `ts` policy but not a `(ts, hid)` pair, because `hid` is a field of
the request (`hostQ_header`). -/
def Wire.bytesWellFormed (w : Wire) : Prop :=
  (∀ m ∈ w.b, m.length = 5) ∧
    ∀ ts hid dir, (w.group ts hid dir).map (·.getD 3 0) = List.range (w.group ts hid dir).length

/-! ## The side statements -/

/-- The Wasm base statement's public values (`WasmBase/Chips.lean`, `Boundary.pubN …`).  The
`code_root` is the cached CODE commitment; `code_hash` is the receipt's contract code hash,
bound on the state side. -/
structure WasmStmt where
  codeRoot : Nat
  codeHash : List Nat
  steps : Nat
  finalGas : Nat
  nres : Nat
  resultTag : Nat
  result : List Nat
  status : Nat
  memSize : Nat
  dataEnd : Nat
  /-- HOST traffic, projected from the wire -/
  hostQ : List (List Nat)
  hostR : List (List Nat)
  hostB : List (List Nat)

/-- The state statement: the D2/D3 claim plus the parts the join reads.  `walks` and `finals` are
the `walkV3`/`cdWalkV3` and `FINAL` views; `values` are the `valV3` value records; `overlay` is
the `RealStore.writes` log committed by the state proof (`TrieStore.lean:168`). -/
structure StateStmt where
  prevRoot : List Nat
  postRoot : List Nat
  /-- `account -> contract code hash` as read by the account table (the `w.shape` binding) -/
  contractOf : List Nat → Option (List Nat)
  /-- `(walk id, instance) -> key path` accepted by the walk table -/
  walkPath : Nat → Nat → Option (List Nat)
  /-- `walk id -> (fk, k)` from the terminal row (`walkV3`'s `FINAL`) -/
  walkFinal : Nat → Option (Nat × Nat)
  /-- value record id -> bytes (`valV3`) -/
  valueRecord : Nat → Option (List Nat)
  /-- the ordered write log of a successful call (`RealStore.writes`) -/
  writes : List (List Nat × Option (List Nat))
  hostQ : List (List Nat)
  hostR : List (List Nat)
  hostB : List (List Nat)

/-- The state proof's code binding: the executing account's contract hash equals the Wasm
statement's `code_hash`.  This is the `receipt → code_hash` link `pq-wasm-base` §5 leaves open. -/
def CodeBound (w : WasmStmt) (s : StateStmt) (account : List Nat) : Prop :=
  s.contractOf account = some w.codeHash

/-- The cached `code_root` is a deterministic function of the code hash (the state side's deploy
or account value determines the code; V_d recomputes the root, `pq-wasm-base/STATEMENT.md` §2).
Stated as an abstract predicate: the join consumes it, it is not proved here. -/
def CodeRootBound (w : WasmStmt) (s : StateStmt) : Prop :=
  ∃ code, s.contractOf code = some w.codeHash

/-! ## The state half of one `storage_write` -/

/-- One `storage_write` as the join sees it. -/
structure StorageWrite where
  ts : Nat
  /-- account id bytes (one field element per byte) -/
  account : List Nat
  /-- data key bytes -/
  key : List Nat
  /-- value bytes being written -/
  value : List Nat
  /-- the value in the pre-state trie at `contractDataKey account key`; `none` = the write is an
  insertion (`ContractData` path absent / branch without a value).  This is what the walk sees. -/
  preValue : Option (List Nat) := none
  /-- `true` iff the call succeeded and the write is committed; a failed call rolls back
  (`FunctionCall.lean:322-329`) and the write appears in `writes` but not in the overlay. -/
  committed : Bool

/-- **The state half of a `storage_write`, stated.**  For the write's `ts` there is a walk id and
a value record such that

1. the walk table's path is the ContractData path `[9] ‖ account ‖ [44] ‖ key`
   (`D3.ContractData.contractDataPath`) — this is the piece the D1 port does not have;
2. the terminal describes the **pre-state**: `FINAL` kind `1` (`FK_ABS`) when the key is absent
   (an insertion), or kind `0` (`FK_VAL`) into a value record equal to `preValue` when the key is
   present (an overwrite).  The walk is over the pre-state trie; the new value enters only through
   `upsV3`, never through the walk;
3. the state's write log contains `(contractDataKey account key, some value)` at a position
   matching `ts`'s order;
4. if `committed`, the `upsV3` post-state applies that write: `postRoot` is the root of the
   pre-state with the log applied.

Parts (1)–(3) are the walk/value/write facts; (4) is the `upsV3` obligation.  This `Prop` is
**stated, not proved**. -/
def StateHalfStorageWrite (s : StateStmt) (w : StorageWrite) (preUpsertPost : List Nat) : Prop :=
  -- (1) the path the walk table accepts is the ContractData path, not the account key
  (∃ wid tau,
      s.walkPath wid tau = some (ZkFormal.NearV3.D3.contractDataPath (w.account.map UInt8.ofNat)
        (w.key.map UInt8.ofNat))) ∧
  -- (2) the terminal describes the *pre*-state: absent (ABS) for an insertion, VAL into a value
  -- record equal to the old bytes for an overwrite.  The new value never enters the walk.
  (match w.preValue with
    | none => ∃ wid, s.walkFinal wid = some (1, 0)
    | some old => ∃ wid vid, s.walkFinal wid = some (0, vid) ∧ s.valueRecord vid = some old) ∧
  -- (3) the ordered write log carries `(full trie key, some new value)`
  ((ZkFormal.NearV3.D3.contractDataKey (w.account.map UInt8.ofNat) (w.key.map UInt8.ofNat)).map
      UInt8.toNat, some w.value) ∈ s.writes ∧
  -- (4) a committed write is applied by `upsV3`
  (w.committed = true → s.postRoot = preUpsertPost)

/-- The write-log order matches the wire's `ts` order: the state applies the calls in the order
the Wasm proof made them.  `storage_write`s only (the prototype's scope). -/
def WritesAlignedWithWire (s : StateStmt) (ws : List StorageWrite) : Prop :=
  ws.map (fun w => (ZkFormal.NearV3.D3.contractDataKey (w.account.map UInt8.ofNat)
    (w.key.map UInt8.ofNat)).map UInt8.toNat) = s.writes.map (·.1)

/-! ## The cross-proof bus balance -/

/-- A side's projection of the wire is the wire.  This is the *whole* cross-proof obligation for
the HOST buses: the Wasm proof's `HOSTQ`/`HOSTR`/`HOSTB` traffic and the state proof's must be
the same multiset, which — because both sides project the same ordered wire — is equality of the
projections each side's public values expose. -/
def HostTrafficAgrees (w : WasmStmt) (s : StateStmt) : Prop :=
  w.hostQ = s.hostQ ∧ w.hostR = s.hostR ∧ w.hostB = s.hostB

/-- The joint bus balance: on every bus and message, sends from both sides equal receives from
both sides.  Over the HOST buses this is `HostTrafficAgrees` plus the direction convention (the
Wasm side sends `HOSTQ` and receives `HOSTR`/`HOSTB`; the state side receives `HOSTQ` and sends
`HOSTR`/`HOSTB`).  On the state side's own buses it is the `HoldsP.balance` of the state AIR; on
the Wasm side it is the `Holds` balance of the base AIR.  Stated structurally, not proved. -/
def JointBusBalance (w : WasmStmt) (s : StateStmt) : Prop :=
  HostTrafficAgrees w s ∧
    (∀ m ∈ w.hostQ, m ∈ s.hostQ) ∧ (∀ m ∈ s.hostQ, m ∈ w.hostQ) ∧
    (∀ m ∈ w.hostR, m ∈ s.hostR) ∧ (∀ m ∈ s.hostR, m ∈ w.hostR) ∧
    (∀ m ∈ w.hostB, m ∈ s.hostB) ∧ (∀ m ∈ s.hostB, m ∈ w.hostB)

/-! ## The joint statement -/

/-- The two side relations, as opaque `Prop`s: `WasmHolds` is the HOST-extended base relation
(`Holds (wasmBaseAir …)` plus the HOST chip's traffic), `StateHolds` is the state relation
(`HoldsP nearAirV3D1 …` plus the D3 `runCall` fold).  They are parameters because each side's
theorem lives in its own lane; this file states how they compose. -/
structure JointStmt where
  /-- the claim's pre-state root (`prev_state_root`), as field elements -/
  prevRoot : List Nat
  /-- the claim's post-state root -/
  postRoot : List Nat
  /-- the executing account id -/
  account : List Nat
  /-- the Wasm contract code hash (sha256 of the code) -/
  codeHash : List Nat
  wasm : WasmStmt
  state : StateStmt
  wire : Wire
  /-- the storage writes of this FunctionCall, in `ts` order -/
  writes : List StorageWrite
  /-- each write's `upsV3` post-state root -/
  postAfter : StorageWrite → List Nat
  /-- **Wasm side**: the base relation holds with the HOST traffic -/
  wasmHolds : WasmStmt → Wire → Prop
  /-- **State side**: the state relation holds with the HOST traffic -/
  stateHolds : StateStmt → Wire → Prop

/-- **The joint statement** (stated, not proved).

A Wasm FunctionCall proof and a state proof compose when

* each side's relation holds with the same host wire (`wasmHolds`, `stateHolds`);
* the roots agree: `state.prevRoot = prevRoot`, `state.postRoot` is the post root after the
  writes, and the Wasm side's `code_hash` equals the state side's contract hash for `account`
  (`CodeBound`);
* the wire is well formed (`ts` increasing, responses match, bytes have the right shape);
* every `storage_write` has its state half (`StateHalfStorageWrite`), and the write log is in
  the wire's order (`WritesAlignedWithWire`);
* the cross-proof bus balance holds (`JointBusBalance`).

The joint public values are exactly the union of the two sides' public values plus the wire's
three commitments; `prevRoot`, `postRoot`, `account` and `codeHash` are duplicated on both sides
and must agree.  This `def` is the specification; the soundness theorem (the two side theorems
plus the balance imply `RelD3`) is **not** proved here and is the remaining join obligation. -/
def Joint (j : JointStmt) : Prop :=
  j.wasmHolds j.wasm j.wire ∧
  j.stateHolds j.state j.wire ∧
  j.wire.tsIncreasing ∧ j.wire.responsesMatch ∧ j.wire.bytesWellFormed ∧
  j.state.prevRoot = j.prevRoot ∧
  j.state.postRoot = j.postRoot ∧
  CodeBound j.wasm j.state j.account ∧
  (j.wasm.codeHash = j.codeHash) ∧
  (∀ w ∈ j.writes, StateHalfStorageWrite j.state w (j.postAfter w)) ∧
  WritesAlignedWithWire j.state j.writes ∧
  JointBusBalance j.wasm j.state

/-! ## What the two side theorems must supply

Stated as separate `Prop`s so the checklist can name them:

* `WasmHalf` — `wasm_base_sound` (`pq-wasm-base` `Main/Final.lean`) extended with the HOST chip:
  under `check`, `CodeOK`, `PubOK` and the statement conditions, the run ends with the public
  result/status and the HOST traffic is exactly the wire (`pq-wasm-base` §8 lists the missing
  OOG/import pieces).
* `StateHalf` — the D0a/D1 extraction (`pq-state-port` `D0a.pq_d0a_rel`) plus the D3 `runCall`
  fold: a `HoldsP` proof of the state tables yields `RelD3` for the receipt, with the storage
  writes replayed in order.
* `Compose` — `Joint → RelD3` for the chunk's FunctionCall receipt. -/

/-- Wasm half (stated). -/
def WasmHalf (j : JointStmt) : Prop :=
  j.wasmHolds j.wasm j.wire →
    j.wasm.status = 1 ∨ j.wasm.status = 2

/-- State half (stated). -/
def StateHalf (j : JointStmt) : Prop :=
  (∀ w ∈ j.writes, StateHalfStorageWrite j.state w (j.postAfter w))

/-- Composition (stated): the joint statement implies the chunk relation for this receipt.
`RelD3` is `NearSpecV3.D3.RelD3`; the composition is the join's main remaining proof. -/
def Compose (chunkClaim chunkWitness : NearSpec.Bytes) (j : JointStmt) : Prop :=
  Joint j → NearSpecV3.D3.RelD3 chunkClaim chunkWitness

end ZkFormal.PQ.Join
