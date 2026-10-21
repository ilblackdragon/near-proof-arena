import ZkFormal.PQ.Join.Statement

/-!
# `ZkFormal.PQ.Receipt.Ids` — the bookkeeping class table of the `promise_*` family

Lane `pq-receipt-air`.  This module is the *data* half of the state-side receipt/promise AIR:
the per-host-function behaviour record every `promise_*` call needs, transcribed from
`spec/lean/v3/NearSpecV3/Wasm/Host.lean` (the `promise_*` arms of `hostCall`) and from
`research/near-compression/results/pq-host-promise/DESIGN.md` §2 (the arities).

## Why a class table and not 23 constraints

Every one of the 23 functions does the same five things, with different parameters:

1. consume `np` arguments from the stack and one `HOSTQ` request,
2. append a **receipt** (or not),
3. push a **promise** index (or not),
4. append an **action** to a receipt (or not),
5. consume **data ids** (`thenDataIdsH` / `dataCount + 1`), read a **dependency list**, and
   return a **word**.

So a row needs `(addR, addP, addA, hasTgt, hasDep, retKind, knd, rtag)` — all *static* per
`hid` — and the dynamic pieces `(addD, dep, tgt, rlo, …)`.  The static part is a cached table
`PBK` bound exactly like `HOSTT` (`WasmBase/HostChip.lean`): its rows are the constant list
`promiseClasses` below.  The dynamic part is the `PBC` call row (`Bookkeeping.lean`).

## What the transcription is checked against

`promiseClasses` is the `promiseFns` list of `WasmBase/HostChip.lean` (ids `8..30`) with the
behaviour read off `Host.lean`.  The kernel checks (§`decide`) that the ids are exactly
`8..30`, that every `np ≤ 9` and `ar ≤ 1` (the widened HOST chip's window), that every
`knd ≤ 10` (the `ActionR` tag universe of `D2/Types.lean`), that `dadd`-policy is well formed,
and — the interesting one — that the counter policy is `Host.lean`'s, restated as
`specAddR`/`specAddP`.

## The wire

This module's `hostQ22` / `hostB5` / `hostR8` are now **the same functions** as
`PQ/Join/Statement.lean`'s `hostQ` / `hostB` / `hostR`
(`hostQ22_eq_join` / `hostB5_eq_join` / `hostR8_eq_join`, all `rfl`), which in turn are the HOST
chip's `Host.qMsg` / `HostB.msg` / `HostR` shapes (22 / 5 / 8 fields).  There is one wire.

The *pre-widening* shapes (`PQ/Join/Statement.lean` once declared `HOSTQ` as 8 fields
`[ts, hid, S, a0 … a4]` and `HOSTB` as 4 `[ts, dir, pos, byte]`) are kept as `Join.hostQOld` /
`Join.hostBOld`.  `hostQ_stale_len`/`hostB_stale_len` prove their widths and
`hostQ_no_bridge`/`hostB_no_bridge` prove a message of the old width can never be a message of
the current width — so a joined proof that kept the old shapes would *fail to balance* rather
than silently merge two wires.  That is a correctness fact about the interface, not a design
preference: `(ts, hid, S, np, args…)` and `(ts, hid, S, a0…a4)` are different multisets.
-/

namespace ZkFormal.PQ.Receipt

open ZkFormal.Air

/-! ## Buses -/

/-- `PBK → PBC`: the cached per-`hid` class row.  Above the classical range after the
`pq-state-port` `+128` shift (max `203`) and above the HOST buses (`208, 209, 210`). -/
def B_PBSTAT : Nat := 211

/-- `PBC → PBR`: a 16-bit range lookup (`PBR`'s row `r` carries `r`). -/
def B_PBRANGE : Nat := 212

theorem pb_buses_distinct :
    B_PBSTAT ≠ B_PBRANGE ∧ B_PBSTAT = 211 ∧ B_PBRANGE = 212 := by decide

/-- The two new buses do not collide with the join's HOST buses or the state range. -/
theorem pb_buses_safe :
    ZkFormal.PQ.Join.B_HOSTB < B_PBSTAT ∧ B_PBSTAT < B_PBRANGE := by decide

/-! ## The behaviour record -/

/-- What a `promise_*` call does, statically.  Every field is a small natural (`decide`-checked
below), so the record is a `Nat` tuple in the AIR (`PBK`'s columns).

* `np`, `ar` — the host signature (`Host.lean`'s `popArgs`/`pushRet`);
* `knd` — the `ActionR` tag this call appends (`15` = "no action": the value is outside
  `0..10`, which is what `PBC` checks);
* `addR`, `addP`, `addA` — receipt / promise / action appended (bits);
* `hasTgt` — argument 0 is a *promise* index, resolved to a receipt index by
  `promiseReceiptH` / `receiptReceiver` (so the row carries `tgt < rcpt`);
* `hasDep` — the call reads a dependency list (`promise_then`, `promise_batch_then`,
  `promise_and`), so `dep ≤ maxInputDataDependencies = 128`;
* `retKind` — `0` no result, `1` a promise index (`pushPromiseH`'s return), `2` the result
  count (`promise_results_count`), `3` a result status (`promise_result`), `4` the i32
  `0/1` of `promise_yield_resume*`;
* `rtag` — the stack result tag: `1` (`i64`) everywhere except the two `yield_resume`
  functions, which push an `i32` (`Host.lean` `pushRet … (is64 := false)`) — DESIGN §2 P1;
* `dadd` — data ids consumed, **when static**: `1` for `yield_create*`, `0` otherwise.  The
  `then` family is dynamic (`thenDataIdsH deps.size`), recorded as `dadd = dep` in `PBC`. -/
structure PB where
  hid : Nat
  np : Nat
  ar : Nat
  knd : Nat
  addR : Nat
  addP : Nat
  addA : Nat
  hasTgt : Nat
  hasDep : Nat
  retKind : Nat
  rtag : Nat
  dadd : Nat
  /-- does the call consume a byte payload on `HOSTB` (method/args/code/pk/account/key)? -/
  hasBytes : Nat
  /-- results pushed on the stack: `1` iff `retKind ≠ 0` (`pushRet` in every arm that returns) -/
  nres : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The 23 `promise_*` entries.  `np`/`ar` are `WasmBase/Chips.lean`'s `promiseFns`; the
behaviour is `Host.lean`'s, arm by arm (the comment on each line is the `Host.lean` line). -/
def promiseClasses : List PB :=
  [ -- promise_create: CR + FC action, promise, data 0                       (Host.lean:841)
    ⟨8, 8, 1, 2, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩,
    -- promise_then: CR(deps) + FC, deps list, dynamic data ids              (Host.lean:850)
    ⟨9, 9, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1⟩,
    -- promise_and: joint promise only, deps list                            (Host.lean:823)
    ⟨10, 2, 1, 15, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1⟩,
    -- promise_batch_create: CR only                                         (Host.lean:805)
    ⟨11, 2, 1, 15, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1⟩,
    -- promise_batch_then: CR(deps), deps list, dynamic data ids             (Host.lean:814)
    ⟨12, 3, 1, 15, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩,
    -- promise_set_refund_to: RT entry on receipt r                          (Host.lean:866)
    ⟨13, 3, 0, 15, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩,
    -- promise_batch_action_create_account                                   (Host.lean:874)
    ⟨14, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0⟩,
    -- promise_batch_action_deploy_contract                                  (Host.lean:880)
    ⟨15, 3, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩,
    -- promise_batch_action_function_call                                    (Host.lean:890)
    ⟨16, 7, 0, 2, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩,
    -- promise_batch_action_function_call_weight                             (Host.lean:893)
    ⟨17, 8, 0, 2, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩,
    -- promise_batch_action_transfer                                         (Host.lean:896)
    ⟨18, 2, 0, 3, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0⟩,
    -- promise_batch_action_stake                                            (Host.lean:905)
    ⟨19, 4, 0, 4, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩,
    -- promise_batch_action_add_key_with_full_access                         (Host.lean:914)
    ⟨20, 4, 0, 5, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩,
    -- promise_batch_action_add_key_with_function_call                       (Host.lean:922)
    ⟨21, 9, 0, 5, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩,
    -- promise_batch_action_delete_key                                       (Host.lean:941)
    ⟨22, 3, 0, 6, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0⟩,
    -- promise_batch_action_delete_account                                   (Host.lean:949)
    ⟨23, 3, 0, 7, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0⟩,
    -- promise_yield_create: YC + FC, promise, one data id                   (Host.lean:966)
    ⟨24, 7, 1, 2, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1⟩,
    -- promise_yield_create_with_id                                          (Host.lean:523)
    ⟨25, 9, 1, 2, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1⟩,
    -- promise_yield_resume: i32 result, no receipt/promise/action           (Host.lean:990)
    ⟨26, 4, 1, 15, 0, 0, 0, 0, 0, 4, 0, 0, 1, 1⟩,
    -- promise_yield_resume_with_yield_id                                    (Host.lean:996)
    ⟨27, 4, 1, 15, 0, 0, 0, 0, 0, 4, 0, 0, 1, 1⟩,
    -- promise_results_count                                                 (Host.lean:956)
    ⟨28, 0, 1, 15, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1⟩,
    -- promise_result                                                        (Host.lean:957)
    ⟨29, 2, 1, 15, 0, 0, 0, 0, 0, 3, 1, 0, 1, 1⟩,
    -- promise_return                                                        (Host.lean:970)
    ⟨30, 1, 0, 15, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩]

/-- Host id of a `promise_*` class row. -/
def PB.idOf (p : PB) : Nat := p.hid

/-- The class row of a host id (`none` = not a `promise_*` function). -/
def classOf (hid : Nat) : Option PB := promiseClasses.find? (·.hid = hid)

/-- The `promise_*` ids are exactly `8 … 30`, once each. -/
theorem promiseClasses_ids : promiseClasses.map PB.hid = List.range' 8 23 := by decide

/-- The class table covers the whole family and nothing else. -/
theorem classOf_isSome (hid : Nat) :
    (classOf hid).isSome = true ↔ hid ∈ List.range' 8 23 := by
  unfold classOf
  rw [List.find?_isSome, ← promiseClasses_ids, List.mem_map]
  constructor
  · rintro ⟨p, hp, h⟩; exact ⟨p, hp, of_decide_eq_true h⟩
  · rintro ⟨p, hp, h⟩; exact ⟨p, hp, by rw [h]; exact decide_eq_true rfl⟩

theorem promiseClasses_complete (hid : Nat) :
    (classOf hid).isSome = true ↔ 8 ≤ hid ∧ hid < 31 := by
  rw [classOf_isSome, List.mem_range']
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨hid - 8, by omega, by omega⟩

/-- Every entry fits the widened HOST chip (`np ≤ 9`, `ar ≤ 1`) — the same window
`HostChip.hostFns_shape` checks on the Wasm side. -/
theorem promiseClasses_shape :
    promiseClasses.all (fun p => p.np ≤ 9 && p.ar ≤ 1) = true := by decide

/-- Every action kind is in the `ActionR` tag universe `0 … 10` (`D2/Types.lean`, tags
`0..7` and `9..12`; `8` (deploy-global) is excluded by D3's `oodHosts`, so `0..7` is the
reachable set and `15` is "no action"). -/
theorem promiseClasses_kind :
    promiseClasses.all (fun p => p.knd ≤ 10 ∨ p.knd = 15) = true := by decide

/-- The flags are bits and the static data-id count is `≤ 1`. -/
theorem promiseClasses_flags :
    promiseClasses.all (fun p =>
      p.addR ≤ 1 && p.addP ≤ 1 && p.addA ≤ 1 && p.hasTgt ≤ 1 && p.hasDep ≤ 1 &&
      p.retKind ≤ 4 && p.rtag ≤ 1 && p.dadd ≤ 1 && p.hasBytes ≤ 1 && p.nres ≤ 1) = true := by decide

/-- **The counter policy is `Host.lean`'s.**  Restated from the spec's arms: the functions that
`pushAction { text := s!"CR…" }` or `YC:` (a receipt), the ones that `pushPromiseH`, the ones
that `pushAction` an `ActionR`/`RT` entry, the ones reading a dependency list, and the ones
consuming one data id.  `decide` checks the transcription against the table. -/
def specAddR : List Nat := [8, 9, 11, 12, 24, 25]
def specAddP : List Nat := [8, 9, 10, 11, 12, 24, 25]
def specAddA : List Nat := [8, 9, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
def specHasTgt : List Nat := [9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 30]
def specHasDep : List Nat := [9, 10, 12]
def specDadd1 : List Nat := [24, 25]
def specI32 : List Nat := [26, 27]

/-- `nres` is `pushRet`'s: a word iff the call returns something. -/
theorem promiseClasses_nres :
    promiseClasses.all (fun p => decide (p.nres = 1) = decide (p.retKind ≠ 0)) = true := by decide

theorem promiseClasses_policy :
    promiseClasses.all (fun p =>
      (decide (p.addR = 1) = specAddR.contains p.hid) &&
      (decide (p.addP = 1) = specAddP.contains p.hid) &&
      (decide (p.addA = 1) = specAddA.contains p.hid) &&
      (decide (p.hasTgt = 1) = specHasTgt.contains p.hid) &&
      (decide (p.hasDep = 1) = specHasDep.contains p.hid) &&
      (decide (p.dadd = 1) = specDadd1.contains p.hid) &&
      (decide (p.rtag = 0) = specI32.contains p.hid)) = true := by decide

/-! ## The wire: one definition, two spellings

`HOSTQ` (Wasm → state, `HostChip.qMsg`) is `[ts, hid, S, np]` then `(aLo j, aHi j)` for
`j = 0..8`: 22 fields.  `HOSTB` (`HostChip` `HostB.msg`) is `[ts, hid, dir, pos, byte]`: 5.
`HOSTR` (state → Wasm) is `[ts, st, rLo, rHi, gLo, gHi, ar, 0]`: 8.

These are **`PQ/Join/Statement.lean`'s** definitions.  The names below are kept because the wire
was first spelled here (before `Statement.lean` was migrated, this lane could not edit it); each
one is now *proved equal* to the join's, so the two spellings can never fork again.  The
`≠`-lemmas of `hostQ_no_bridge`/`hostB_no_bridge` are unaffected — they compare the *old* shapes
(now `Join.hostQOld`/`Join.hostBOld`) against these. -/

/-- `HOSTQ`, 22 fields: the request one `promise_*` call must consume.  Equal to
`ZkFormal.PQ.Join.hostQ` (`hostQ22_eq_join`). -/
def hostQ22 (ts hid s np : Nat) (a : Nat → Nat × Nat) : List Nat :=
  [ts, hid, s, np] ++ (List.range 9).flatMap fun j => [((a j).1), ((a j).2)]

/-- `HOSTB`, 5 fields: one byte of a call's payload.  Equal to `ZkFormal.PQ.Join.hostB`. -/
def hostB5 (ts hid dir pos byte : Nat) : List Nat := [ts, hid, dir, pos, byte]

/-- `HOSTR`, 8 fields, in **limb form**: what a state-side table's columns carry (the row stores
`rl, rh, gl, gh` separately, because `PBC` range-checks each of them through `PBR`).  The join's
`hostR` takes the two words and splits them; `hostR8_split` is the equality. -/
def hostR8 (ts st rLo rHi gLo gHi ar : Nat) : List Nat :=
  [ts, st, rLo, rHi, gLo, gHi, ar, 0]

/-- **The wide `HOSTQ` here *is* the join's.**  `rfl`: `Join.nHostArgs = 9` and its `pairAt` is
the two-element list below. -/
theorem hostQ22_eq_join (ts hid s np : Nat) (a : Nat → Nat × Nat) :
    hostQ22 ts hid s np a = ZkFormal.PQ.Join.hostQ ts hid s np a := rfl

/-- **The wide `HOSTB` here *is* the join's.** -/
theorem hostB5_eq_join (ts hid dir pos byte : Nat) :
    hostB5 ts hid dir pos byte = ZkFormal.PQ.Join.hostB ts hid dir pos byte := rfl

/-- **The join's `HOSTR` is this limb form at the split of its words.**  A state row's limbs split
its result and budget words, so the two spellings agree exactly when the limbs are the split. -/
theorem hostR8_split (ts st r gAfter ar : Nat) :
    ZkFormal.PQ.Join.hostR ts st r gAfter ar =
      hostR8 ts st (ZkFormal.PQ.Join.lo16 r) (ZkFormal.PQ.Join.hi16 r)
        (ZkFormal.PQ.Join.lo16 gAfter) (ZkFormal.PQ.Join.hi16 gAfter) ar := rfl

theorem hostQ22_len (ts hid s np : Nat) (a : Nat → Nat × Nat) :
    (hostQ22 ts hid s np a).length = 22 :=
  ZkFormal.PQ.Join.hostQ_width ts hid s np a

theorem hostB5_len (ts hid dir pos byte : Nat) : (hostB5 ts hid dir pos byte).length = 5 :=
  ZkFormal.PQ.Join.hostB_width ts hid dir pos byte

theorem hostR8_len (ts st rLo rHi gLo gHi ar : Nat) :
    (hostR8 ts st rLo rHi gLo gHi ar).length = 8 := rfl

/-! ## The stale (pre-widening) shapes, and why they cannot be bridged by re-encoding

`PQ/Join/Statement.lean` declared, before this lane's migration, `HOSTQ` as 8 fields
`[ts, hid, S, a0 … a4]` and `HOSTB` as 4 (`[ts, dir, pos, byte]`).  Those shapes are now kept as
`Join.hostQOld`/`Join.hostBOld` **only** so the gap stays a named, proved fact: a message of the
old width is never a message of the current width, so a joined proof that kept the old shapes
would *fail to balance* rather than silently merge two different wires.  That was a correctness
property of the interface, not a design preference — `(ts, hid, S, np, args…)` and
`(ts, hid, S, a0…a4)` are different multisets. -/

/-- The old `HOSTQ` is 8 fields wide (when at most five arguments are present). -/
theorem hostQ_stale_len (ts hid gas : Nat) (args : List Nat) (h : args.length ≤ 5) :
    (ZkFormal.PQ.Join.hostQOld ts hid gas args).length = 8 :=
  ZkFormal.PQ.Join.hostQOld_width ts hid gas args h

/-- The old `HOSTB` is 4 fields wide. -/
theorem hostB_stale_len (ts dir pos byte : Nat) :
    (ZkFormal.PQ.Join.hostBOld ts dir pos byte).length = 4 :=
  ZkFormal.PQ.Join.hostBOld_width ts dir pos byte

/-- **No old-width `HOSTQ` is a wide `HOSTQ`**: the stale lane shape cannot be silently merged with
the current wire.  8 fields against 22. -/
theorem hostQ_no_bridge (ts hid gas : Nat) (args : List Nat) (h : args.length ≤ 5)
    (ts' hid' s' np' : Nat) (a : Nat → Nat × Nat) :
    ZkFormal.PQ.Join.hostQOld ts hid gas args ≠ hostQ22 ts' hid' s' np' a :=
  ZkFormal.PQ.Join.hostQ_old_not_current ts hid gas args h ts' hid' s' np' a

/-- **No old-width `HOSTB` is a wide `HOSTB`.**  4 fields against 5. -/
theorem hostB_no_bridge (ts dir pos byte : Nat) (ts' hid' : Nat) (dir' pos' byte' : Nat) :
    ZkFormal.PQ.Join.hostBOld ts dir pos byte ≠ hostB5 ts' hid' dir' pos' byte' :=
  ZkFormal.PQ.Join.hostB_old_not_current ts dir pos byte ts' hid' dir' pos' byte'

end ZkFormal.PQ.Receipt
