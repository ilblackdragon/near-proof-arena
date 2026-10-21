# pq-host-memio — REG group walk proved; HOSTB range-check hole closed

Lane `lane/pq-host-memio`, 2026-10-21. Baseline `319e9f889`.

This lane had two parts. **Part 1 is complete.** **Part 2 is half done**: the predicted soundness
hole is closed and generated/KAT-verified; the `(ptr, len)` → linear-memory *link* is designed and
scoped but not built, for the reason recorded in §3.

Everything below is `Holds`-only or generator-only; no `sorry`, no `axiom`, no `native_decide`.

---

## 1. Part 1 — the REG group walk and `Register.RegLenAgree`

### 1.1 The headline result is that the stated obligation was **false**

`Register.RegLenAgree` (`RegisterSpace.lean`) said: for every length message at producer time `tp`,
the number of *byte* messages of that register at `tp` equals `len`.

A `register_len` call emits exactly one length row (`kind = 1`, `f = 1`) and **no byte row**. At that
producer time the register therefore has a length message and zero byte messages, so the stated
equality fails for every `len ≠ 0`. This is not hypothetical:

* `tracegen.rs` emits exactly this shape for host id 6 (`reg_rows.push([1, 1, 1, rid, 0, blen, …])`);
* `programs/gen.py`'s `regkat` really calls `register_len(0)`;
* and even `regloopN` calls it on its own.

Machine-checked refutation: **`regLenAgree_lone_length`** (`Main/RegWalk.lean`).

```lean
theorem regLenAgree_lone_length {rid len tp : Nat} (hlen : len ≠ 0) :
    ¬ Register.RegLenAgree [Register.lenMsg rid len tp] rid
```

The definition is kept (with a deprecation note pointing at the refutation) so the stale statement
and its disproof stay side by side. **A reviewer should treat `Register.RegLenAgree` as a statement
to be *replaced*, not a proof to be found.**

### 1.2 The correct obligation, and its proof

The AIR enforces the *group-local* fact: a length message is produced by the length row that
terminates a group, and that group has exactly `len` byte rows at `pos = 0 … len−1`. That is
**`regLenAgree_group`**, proved from the walk:

```lean
theorem regLenAgree_group … :
  let L := rowNat tr 26 r0 Reg.blen
  r0 + L < tr.height 26 ∧
  rowNat tr 26 (r0 + L) Reg.kind = 1 ∧
  rowProd … 26 (r0 + L) = [Register.lenMsg rid L ts] ∧
  (∀ i, i < L → rowProd … 26 (r0 + i) = [Register.byteMsg rid i (bv i) ts])
```

`L = 0` is the length-only case and is handled: the byte claim is vacuous and the length row starts
the group. So the corrected statement is true for *every* register access, including
`register_len`.

### 1.3 What was added (all in `Main/RegWalk.lean` unless noted)

| theorem | content |
|---|---|
| `reg_air_get`, `reg_air_22`…`reg_air_25`, `reg_air_15r`, `reg_air_16b`, `reg_air_base`, `reg_air_host_constr`, `reg_air_byte_constr`, `reg_range16_values` | table access for `wasmBaseRegAir = wasmBaseHostAir ++ [REG]` (`Main/RegFacts.lean`) |
| `reg_row0_f` | row 0 starts a group (`cFirst` ⇒ `f = 1`) |
| **`reg_byte_not_last`** | a byte row is never the last row — the walk's termination witness |
| `reg_group_bounds` | every offset `n ≤ L` lands inside the table (an induction, not an assumption) |
| `reg_step`, `reg_step_ids` | successor facts: `f = 0`, and `len`/`rid`/`ts` constant |
| `reg_rid_const`, `reg_ts_const` | `cRidG` / `cTsG` row lemmas |
| **`reg_group_walk`** | the walk: bytes are `pos = 0 … L−1`, then the length row |
| `reg_group_ids` | `rid`/`ts` constant along the whole group |
| **`reg_pos_lt_len`** | `pos < len` on an active byte row |
| `reg_gap_lt`, `reg_r16_recv` | `gap < 2^16`, and the RANGE16 answer characterisation for REG traces |
| `reg_byteslot_eval`, `reg_lenslot_eval`, `reg_ch_sends`, `reg_byte_msg`, `reg_len_msg`, `reg_byte_row_msg`, `reg_len_row_msg` | the space-6 slot encodings and the exact send messages |
| **`regLenAgree_group`** | the corrected obligation |
| **`regLenAgree_lone_length`** | the refutation of the stated one |

### 1.4 Why the walk is shaped the way it is (the two traps)

* **Row existence must be carried.** `reg_byte_succ_not_start` is about the *next* row; deriving
  that it exists from the walk itself is circular. The induction carries `r0 + n < height`
  (`reg_group_bounds`).
* **Termination is `cFirst`/`cLast`, not `pos < len`.** A byte row's successor has `f = 0`
  (`cOnlyLenEnds`) while the last row starts a group (`cLast`), so a byte row is never last
  (`reg_byte_not_last`) and the walk cannot fall off the table. `pos < len` is then a *consequence*
  at the terminator, not an input. (The previous session tried to terminate via `pos < len` and got
  a circular dependency.)

### 1.5 Correction to the handoff on `r16 pos`

The handoff says `2e536d4b7`'s `r16 pos` is what makes `reg_pos_lt_len` provable, and that without it
`pos < len` is false. **That is not the operative reason.** `reg_pos_le` (already proved in that
commit) gives `pos ≤ r < 2^24`, so `pos + 1 + gap < 2^24 + 2^16 < P` and `cPosLtLen` is already an
exact natural equation; `pos < len` follows with **no** R16 facts about `pos`.

The R16 lookups that *are* load-bearing for `reg_pos_lt_len` are the existing ones: `r16 gap`
(via `reg_gap_lt`) and the fact that `pos ≤ r`. The added `r16 pos` is harmless and it *does* pin
`pos` to a value below `2^16` (useful independently), but keeping it is a belt-and-braces choice,
not the difference between true and false. The lane log records this so the next reader does not
re-derive the wrong justification.

---

## 2. Part 2 (a) — the predicted HOSTB soundness hole, closed

The handoff predicted, correctly, that `HostB.inters` looked up only `byte` and `gap`, leaving `pos`
and `len` free, and that `cPosLtLen` (`pos + gap + 1 = len`) would then be satisfiable with
`pos = P−1, len = 5, gap = 4`. Verified: HOSTB's non-`busHostB` lookups were exactly
`byteQ 0 byte …` and `r16 gap`.

**Fix.** `HostB.inters` now also carries `r16 (v pos)` and `r16 (v blen)`, both counted
`act·(1−reg)` — the same fix shape that was applied to `REG`. With `pos, len < 2^16` and
`gap < 2^16`, `cPosLtLen` is exact and `pos < len`.

**Cost.** Two lookups on the HOSTB table: no new columns, no new constraints, +2 interactions on the
preexisting `busR16` (3). Row count of every trace is unchanged (these are per-row lookups).

**Generator.** The three HOSTB emitting sites in `tracegen.rs` now answer both (sites with
`reg = 1` have count 0 for these, matching how REG already answers them; the log/return payload and
the placeholder stream answer both).

**Evidence.**

* `lake build` — whole library, 138 jobs, green.
* KAT: `KAT: 88 passed, 0 failed`.
* Tamper: `TAMPER summary 101/101 rejected`, including the two new cases
  `HOSTB[row r].pos=2^16` and `HOSTB[row r].len=2^16`, which are precisely the values the hole
  admitted.
* Axioms of the Part 1 headline theorems: subset of `[propext, Classical.choice, Quot.sound]`.

---

## 3. Part 2 (b) — `(ptr, len)` → linear memory: designed, **not built**

The handoff asked for `HOSTB` request bytes to be tied to channel space 3 (`chRecv 3 … / chSend 3 …`
per `Chips.Load`'s pattern). I implemented it, and it does not compose with the existing join without
a further piece of work. Recording this precisely is the deliverable here.

**What breaks.** Space-3 (memory) messages ride `busStk = 2`. Adding them to `HOSTB` makes `HOSTB`
an emitter on the CH bus, which:

1. invalidates `env_inters_nil` / `hostb_avoids_state_ch` (`HOSTB` is no longer CH-free) — mechanical;
2. invalidates `host_part_nil_env` / `msgs_ch_host` — mechanical;
3. **breaks `ch_raw_host` (`Main/HostBus.lean`), and this is the real one.** The join's CH statement
   is `init ++ glob ++ budget ++ instrRows ++ memRaw ++ hostRows` versus the consumed side. HOSTB's
   memory bytes are *not* instruction rows and *not* `memRaw`; they belong to the host call's buffer,
   which is exactly the `memView` / `HeapOK` / `RelW` machinery that tracks which memory bytes are
   live. Tying HOSTB to memory therefore requires extending the memory **view** (what `memRaw`
   enumerates and what `HeapOK`/`RelW` promise), i.e. the deferred MEMIO work — which the handoff
   itself lists as a separate sub-problem ("`ptr` is the destination address of a byte read, carried
   for the **deferred** MEMIO link").

**A partial design that does compose, and why it is not enough.** Emitting `chRecv 3 addr … ts` and
`chSend 3 addr … ts` *at the same time* makes HOSTB's CH block a **no-op on the multiset** (a recv
and a send of the identical message), so the permutation statement is unchanged and the join closes
mechanically. It also forces `memory[addr] = bv` at `ts`, which is the real semantic content. What it
does **not** do is model the host *consuming* the byte at an earlier time (the `tp < ts` part of
LOAD's shape), so it does not yet prove "the bytes are the memory contents at the moment the host
reads them" — only "equal at the call's time". That is an honest weaker statement, and it is the
maximum that fits without the MEMIO view extension.

**Recommendation.** Land the range-check fix (§2) now — it is a real hole and it is closed. Do the
`(ptr, len)` link together with the MEMIO view extension in a dedicated lane; attempting it here
would have meant either expanding `HeapOK`/`RelW` (a change to the base memory model, beyond this
lane's remit and touching proved files) or shipping the same-time no-op form and overstating what it
proves.

**What is ready for that lane.** `HOSTB`'s `inters` has a commented, working `memAddr` expression
(`ptrLo + 65536·ptrHi + pos`) and the two `chRecv`/`chSend` space-3 interactions, plus a
`cStartPos`/group structure that makes `pos = 0 … len−1` a group property. The generator already
knows `(ptr, len)` at every payload site (`args[0]`, `args[1]`).
