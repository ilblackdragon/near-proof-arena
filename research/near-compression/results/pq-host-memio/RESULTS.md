# pq-host-memio — REG group walk proved; HOSTB `(ptr, len)` MEMIO link built

Lane `lane/pq-host-memio`, 2026-10-21. Baseline `319e9f889`.

This lane had two parts. **Both are complete.** Part 1 (§1) is the REG group walk and the closed
HOSTB range-check hole. Part 2 (§2–§4) is the `(ptr, len)` → linear-memory link: the predicted
soundness hole is closed, the MEMIO view extension is built (`BufOK`, `heap_retime`), `HOSTB`'s
request bytes are space-3 messages in the LOAD shape (`mtp < ts`), the Rust generator was brought up
to the 14-column HOSTB and the memory re-timing, and KAT/tamper/axiom verification is green. The last
open step — `hostb_mem_distinct` (`mtp ≠ ts` as a *derived* fact) — is now **proved**
(`Main/MemIOLink.lean`), together with the `heap_retime` wiring into `HostStepRely.heap`.  See §3.5.

No `sorry`, no `axiom`, no `native_decide`.  **Two honest caveats, stated up front:**
~~`regLenAgree_group` still takes the R16 `hsend` bound as a *hypothesis*~~ **CLOSED 2026-10-22:**
the handoff's Step 1.1 (`reg_r16_send_bits`) is proved as `reg_hsend_r16` (`Main/RegSend.lean`) from
`Holds` alone, and `regLenAgree_group_of_holds` is the hypothesis-free form.  See §1.6.
~~`hostb_mem_distinct` (`mtp < ts`) not derived~~ **CLOSED 2026-10-23:** proved from `Holds` via the
row's own `timeChk` queries (`Main/MemIOLink.lean`, §3.5).  What remains a *hypothesis* is the
interface obligation itself — `hostb_mem_consumed` takes "the row's consumed space-3 message is live
in the pre-heap" as its premise, exactly as `RowFactsSeg` carries `hin` for an action row.  It is not
derivable from bus balance alone (§3.5, "What is still a hypothesis").

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
| **`reg_gap_wraparound`** | `gap = P−1` satisfies `cPosLtLen` at `pos = len` (why `hsend` is needed) |

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

### 1.6 Step 1.1 — the R16 send bound, **closed**

`regLenAgree_group` used to take

```
hsend : ∀ o ∈ occs (wasmBaseRegAir …) tr pub, o.2.1 = true → o.2.2.2 ≤ 1
```

**It is load-bearing, not cosmetic.** Termination needs `gap < 2^16`: at offset `L` the constraint
`cPosLtLen` reads `L − L − 1 − gap = 0`, and `gap = P − 1` satisfies that for *every* `L` — proved as
`reg_gap_wraparound`. Only the R16 bound on `gap` excludes a byte row at offset `len`, and that bound
comes from `reg_r16_query_16bit`, i.e. from `lookup_sound`, which needs the send bound.

**The stated global form was too strong.** `HOSTO`'s two interactions are counted with a free column
`mult` (`HostO.table.constraints = []`), so "every send of the trace has count ≤ 1" is *false* for any
host trace. `Bus.lookup_sound` already takes the bus-restricted form `o.1 = b → o.2.1 = true →
count ≤ 1`, and the walk applies it at `b = busR16`. So the hypothesis in `reg_r16_query_16bit`,
`reg_gap_lt` and `regLenAgree_group` was narrowed to the R16 instance — the true and sufficient one.

**`reg_hsend_r16` (`Main/RegSend.lean`) proves it from `Holds` alone:**

```
∀ o ∈ occs (wasmBaseRegAir …) tr pub, o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1
```

* tables 0–21: `occ_bits_of` was split out of the base `occ_bits` (`Main/Exec.lean`) so it needs only
  *row constraints*, never the base AIR's bus balance.  `reg_base_constr` supplies them from
  `Holds (wasmBaseRegAir …)`, since tables 0–21 of the REG AIR are literally `wasmBaseAir`'s.
* HOST (22): R16 counts are `act` or `pf j` (`host_r16_cases`), both bits by HOST's own constraints.
* HOSTO (23), HOSTT (24): no R16 interaction (`hosto_no_r16`, `hostT_no_r16`).
* HOSTB (25): R16 counts are `memCnt = act·(1−dir)·(1−reg)` or `act·(1−reg)` (`hostb_r16_cases`).
* REG (26): six R16 queries counted `act·fresh`, `act·(1−kind)`, `act` (`reg_r16_cases`).

The per-chip count bits are *derived*, not assumed: `reg_chip_counts` applies each chip's
constraint-only `*_counts_of` lemma (`Main/Row*`) at the REG AIR's own table index — so no `ChipFacts`
hypothesis is needed.  `regLenAgree_group_of_holds` is the resulting hypothesis-free group theorem.
Axiom audit: `reg_hsend_r16`, `reg_chip_counts` and `regLenAgree_group_of_holds` depend only on
`[propext, Classical.choice, Quot.sound]`.

The `*_of` split that made this possible (constraint-only forms for the chip `*_flags`/`*_counts`
lemmas, with the `Holds`-against-`wasmBaseAir` versions kept as one-line wrappers, so no call site
changed) touches no proof of the group walk itself.

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

## 3. Part 2 (b) — `(ptr, len)` → linear memory: **built**

The handoff asked for `HOSTB` request bytes to be tied to channel space 3 (`chRecv 3 … / chSend 3 …`
per `Chips.Load`'s pattern). This section records what that costs and how it was composed; §4 records
the final verification.

### 3.1 The design that was rejected

The tempting cheap version is a *same-time* pair — `chRecv 3 addr … ts` and `chSend 3 addr … ts` of
the **identical** message. It looks like it "composes mechanically and also forces `memory[addr] = bv`".
That is **false**, and it is the trap in this design:

`busNat` (`Air.lean`) matches occurrences on `(bus, direction, message)`. A recv and a send of the
*identical* message therefore contribute `+c` and `−c` to the **same** bucket, so the pair cancels
identically for every `c` — it imposes **no constraint whatsoever**. It is the same vacuous device
as HOSTB's pre-existing `reg = 0` "self-permutation" (whose own module docstring says it stands in
for the state side). Such a pair would have been a link in name only. Machine-checked as
`MemIO.ch_pair_vacuous`. It was not shipped.

### 3.2 The shape that is shipped

The real LOAD shape is `chRecv … mtp` then `chSend … ts` with `mtp < ts` and **different** messages.
That one is not vacuous: the recv at `mtp` can only balance against a message some other table
produced — i.e. it genuinely asserts "memory byte `bv` at `ptr + pos` was live at `mtp`" — and the
send re-times it to `ts`. `HostB.inters` (14 columns) carries:

```
chRecv 3 (ptrLo + 2^16·ptrHi + pos) 0 [byte,0,0,0] mtp   cnt = act·(1−dir)·(1−reg)
chSend 3 (ptrLo + 2^16·ptrHi + pos) 0 [byte,0,0,0] ts    cnt = act·(1−dir)·(1−reg)
timeChk ts mtp hp                                        cnt = act·(1−dir)·(1−reg)
```

with `cPtrLoConst`/`cPtrHiConst` making `ptr` a group constant, `r16 ptrLo` and `r16 (32·ptrHi)`
pinning the 27-bit address, and the pre-existing `r16 gap`/`r16 pos`/`r16 blen`/`byteQ` completing
the row's lookups. It changes the CH multiset (one message at `mtp` consumed, one at `ts` produced),
and `memRaw`/`HeapOK`'s `tpm` map is what absorbs that re-timing.

### 3.3 What this breaks, and how each break was closed

Space-3 (memory) messages ride `busStk = 2`. Adding them to `HOSTB` makes `HOSTB` an emitter on the
CH bus, which:

1. invalidates `env_inters_nil` / `hostb_avoids_state_ch` (`HOSTB` is no longer CH-free);
2. invalidates `host_part_nil_env` / `msgs_ch_host`;
3. **breaks `ch_raw_host` (`Main/HostBus.lean`).** The join's CH statement is
   `init ++ glob ++ budget ++ instrRows ++ memRaw ++ hostRows` versus the consumed side. HOSTB's
   memory bytes are *not* instruction rows and *not* `memRaw`; they belong to the host call's buffer,
   which is exactly the `memView` / `HeapOK` / `RelW` machinery that tracks which memory bytes are
   live. Tying HOSTB to memory therefore requires extending the memory **view**.

Each was closed as follows (five commits on top of `c6761629d`):

| commit | what it does |
|---|---|
| `728fabae7` | MEMIO view extension: `BufOK`, `heap_retime_readByte`, `heap_retime`, `ch_pair_vacuous` |
| `df81c7436` | HOSTB's 14 columns (`ptrLo`, `ptrHi`, `mtp`, `hp`), `cPtrLoConst`/`cPtrHiConst`, the space-3 recv/send pair and `timeChk` |
| `ebd1298e0` | HOSTB joins the CH bus decomposition (`msgs_ch_host`, `flatMap_prodCH_perm`/`flatMap_consCH_perm`) |
| `30352dc58` | HOSTB is a CH emitter; its space-3 count is a bit (`hostb_memCnt_bit`, `hostb_touches_ch`, `hostb_avoids_state`) |
| `16a1abad0` | fold HOSTB's space-3 block onto its host call (`hostb_partition`, `hostb_partition_prod`/`_cons`) |

**The view half.** `MemIO.heap_retime` is `StepMem.heap_update`'s read counterpart: the bytes
`[ea, ea + w)` keep their values, only their producer times move to `t`, so `HeapOK` at `t + 1`
follows with **no change to `s` at all**. `heap_retime_readByte` is the value-preservation half. This
is what lets `HostStepRely`'s heap field be *discharged* rather than assumed for a request read.
`BufOK` carries the statement-level `ptr + len ≤ memBytes` bound, which is not polynomial (`ptr` and
`len` are each range-checked, their sum is not); `BufOK.addr_lt` puts every buffer byte in bounds.

**The partition.** `hostb_partition` proves the fold of the active `HOSTB` block over the active HOST
rows is a `Perm`: every active `HOSTB` row belongs to exactly one active HOST row (given
`HostBLinked`), and inactive rows emit nothing (`hostb_inactive_nil`, which rests on `rowAct` being
`memCnt = 1` — `hostb_rowAct_iff` — and on `memCnt` being a product of three bits,
`hostb_memCnt_bit`). `flatMap_prodCH_perm`/`flatMap_consCH_perm` are the generic `flatMap`+`filter`
rearrangements the partition needs.

### 3.4 The generator gap (the reason KAT was red at first)

The Lean AIR declared 14 `HOSTB` columns and the space-3 pair, but `tracegen.rs` still wrote 10
columns and never re-timed memory: **21 of 97 KAT programs failed** with `buses: unbalanced` on bus 2
(space 3) and bus 3 (`RANGE16`). Three separate generator defects, all in the HOSTB emission sites:

1. **Row width.** `hostb_rows` was `[u64; 10]`; the AIR wants 14. Fixed to `[u64; 14]` and the
   emission loop now writes `ptrLo, ptrHi, mtp, hp` too.
2. **The payload arm never fired.** It tested host ids `[8, 9, 10, 15]`, which in this spec are
   `promise_create`/`promise_then`/`promise_and`/`promise_batch_action_deploy_contract`, not the
   log/return ids. The real ids are `Chips.hostLogFns`: `log_utf8 = 45`, `log_utf16 = 46`,
   `panic_utf8 = 47`, `value_return = 50`. The KAT could not see the miss: an absent `HOSTB` group
   still balances.
3. **The argument order was reversed.** The spec's signature is `log_utf8(len, ptr)` (`utf8H a[0] a[1]`
   then `readMemH ptr len`), so `args[0]` is the **length** and `args[1]` the pointer. The lane's arm
   had `(ptr, blen) = (args[0], args[1])`, which for `log_utf8(5, 0)` gave `blen = 0` — zero rows.

With those three fixed and the memory link implemented, every request byte now does what the AIR
says: `mem.get(ptr + pos)` → `(b, mtp)`, `st.tchk(ts, mtp)` (which asserts `mtp < ts` and records the
two `timeChk` R16 lookups), `mem.cur.insert(ptr + pos, (b, ts))` to re-time the byte to `ts`, plus the
row's five lookups (`byteQ`, `r16 gap`, `r16 pos`, `r16 blen`, `r16 ptrLo`, `r16 32·ptrHi`). A
`reg = 1` fill row keeps all four memory columns at zero: `memCnt = act·(1−dir)·(1−reg) = 0` there, so
its byteQ/r16 queries all have count 0 and only the bus-210 send `act·reg` remains (which `REG`
receives). The placeholder arm (non-REG AIRs) now emits its request half as a real memory read at
buffer base 0 when the program has at least four bytes of memory, and otherwise emits only the
response half (`dir = 1`), which is state-side data and never touches memory.

### 3.5 `hostb_mem_distinct` and the `heap_retime` wiring — **CLOSED 2026-10-23**

Both obligations named in the handoff are proved in `wasm-base-lean/WasmBase/Main/MemIOLink.lean`
(424 lines, no `sorry`/`axiom`/`native_decide`, axiom audit clean):

| theorem | statement |
|---|---|
| `host_base_constr` | base tables 0–21 of `wasmBaseHostAir` are `wasmBaseAir`'s, so their row constraints hold verbatim (`host_air_get`) |
| `hostb_bit` | a `Chips.bool`-constrained HOSTB column is 0 or 1 |
| `hostb_act_one_minus_reg_le` | the un-folded R16 count `act·(1−reg)` is ≤ 1 |
| `host_send_base` | every base-table R16 send has count ≤ 1 |
| `host_hsend_r16` | **the R16 send bound for `wasmBaseHostAir`** (the `hsend` `lookup_sound` needs) |
| `host_r16_recv` | an R16 *receive* with nonzero count is a single value `< 2^16` |
| `host_r16_sound_at` | R16 soundness per bus: `lookup_sound` at `busR16` |
| `host_time_chk` | `mtp + 1 + n ≡ ts (mod P)`, `n < 2^30 + 2^16`, from the row's two `timeChk` queries |
| `hostb_timechk_occ` | the row's two `timeChk` queries as occurrences of the host AIR |
| **`hostb_mem_distinct`** | **`rowNat 25 r mtp ≠ rowNat 25 r ts` for an active HOSTB row, from `Holds` alone** |
| `hostb_mem_consumed` | a request byte's consumed message is the live memory byte (`StepMem.heap_read`) |
| `hostb_addr_lt` | `BufOK` + `pos < len` ⇒ the address is in bounds |
| `stepLive_space` | re-timing only touches space-3 messages |
| **`host_step_rely_buf`** | **the `HostStepRely` of a request read with `heap` discharged by `heap_retime`** |
| **`host_rel_restart_buf`** | **the end-to-end `RelW` restart for a request read (pre-heap + read facts replace `HostStepRely.heap`)** |

`hostb_mem_distinct` is the step the handoff called "the one open step".  Its proof is exactly the
`timeChk` argument the AIR already enforces: the row's `timeChk ts mtp hp memCnt` block emits two
R16 sends with count `memCnt = 1`, so `lookup_sound` (`host_hsend_r16`) bounds both queried values
below `2^16`, and the field equation `ts − mtp − 1 = lo + 2^16·hi` gives `mtp + 1 + n ≡ ts (mod P)`
with `n < 2^30 + 2^16`.  Since `mtp, ts < P` and `1 + n < P`, `mtp = ts` would force either
`1 + n = 0` or `1 + n = P`, both impossible — so `mtp ≠ ts`.  The recv message `encB a bv mtp` and
the send `encB a bv ts` therefore **differ**, and the AIR's space-3 pair is a genuine re-timing
rather than the vacuous same-time cancellation of `MemIO.ch_pair_vacuous`.

**What is still a hypothesis.**  `hostb_mem_consumed` takes as a premise that the row's consumed
space-3 message is live in the pre-heap.  That is an *interface* obligation, not a bus-balance
consequence: `Holds.balance` is a per-message count equality modulo `P`, which gives "the number of
sends equals the number of receives" but not "this row's receive is matched by that send".  The
same is true of the existing action-row design, where `RowFactsSeg` carries the row's input message
`hin` as a premise of the composition theorem.  For HOSTB the analogue is the grouping premise
`HostBLinked` (trace-level `HOSTB → HOSTQ` grouping) plus the row's `hin`; the Lean layer states the
obligation explicitly rather than assuming it away.

**The wiring.**  `host_step_rely_buf` and `host_rel_restart_buf` are the composition: the pre-heap
`HeapOK E s t` plus "the `[ea, ea+w)` bytes are live at their old times" gives `HeapOK` at `t + 1`
by `heap_retime` + `HeapOK.mono`, and `CallsOK.mono` carries the call chain across because
`stepLive_space` shows the re-timed messages are all space 3 (never 4/5/≥16).  `host_rel_restart_buf`
is a separate theorem rather than an application of `host_rel_restart` because the read *re-times*
the bytes it touches: the post-state's live set is `retimedEnv`'s, so one `Env` cannot serve both
sides.

---

## 4. Final verification (2026-10-22)

All numbers below were produced in the worktree `/data/illia/nearproof-wt/pq-host-memio` on
`lane/pq-host-memio`, **not** merged to `main`.

### 4.1 Build

* `lake build` in `wasm-base-lean`: **229 jobs, "Build completed successfully"** (log
  `/tmp/build-final-memio.log`). This resolves the `Main/SoundHost` failure (`Unknown identifier
  host_buses`) recorded in §1.6's note.
* `cargo build --release` in `native/wasm-base`: clean (9 warnings, all pre-existing dead-code /
  naming lints).

### 4.2 KAT and tamper

* `./run_kat.sh /tmp/kat-memio` → **`KAT: 97 passed, 0 failed`** (python ref = Lean spec = Rust trace
  + AIR pre-check). Reconciles with both baselines: the lane's own `88 passed, 0 failed` and main's
  `97 passed, 0 failed` — the extra 9 are main's SHA programs. Before the generator fix this was
  **21 failed**.
* `nearproof-wasm-base tamper /tmp/kat-memio/airR-0-g0.json progs/regkat.prep.json` →
  **`TAMPER summary 101/101 rejected`**, no regression. Includes the two HOSTB range-check cases from
  §2 (`pos = 2^16`, `len = 2^16`) and the five HOSTB column cases (`byte`, `dir = 2`, duplicate `pos`,
  `len`, `hid`, `gap`) plus the REG group cases.

### 4.3 Axiom audit

`lake env lean AxiomsMemio.lean` (`AxiomsMemio.lean`, new, untracked). Every headline theorem is
within the standard three; the three structural ones need nothing at all:

| theorem | axioms |
|---|---|
| `heap_retime` | `[propext, Classical.choice, Quot.sound]` |
| `heap_retime_readByte` | `[propext, Classical.choice, Quot.sound]` |
| `BufOK.addr_lt` | `[propext, Classical.choice, Quot.sound]` |
| `ch_pair_vacuous` | `[propext, Quot.sound]` |
| `hostb_partition` | `[propext, Classical.choice, Quot.sound]` |
| `hostb_partition_prod` | `[propext, Classical.choice, Quot.sound]` |
| `hostb_partition_cons` | `[propext, Classical.choice, Quot.sound]` |
| `flatMap_prodCH_perm` | `[propext, Classical.choice, Quot.sound]` |
| `flatMap_consCH_perm` | `[propext, Classical.choice, Quot.sound]` |
| `host_hch` | `[propext, Classical.choice, Quot.sound]` |
| `host_buses` | `[propext, Classical.choice, Quot.sound]` |
| `hostb_memCnt_bit` | `[propext, Classical.choice, Quot.sound]` |
| `hostb_inactive_nil` | `[propext, Classical.choice, Quot.sound]` |
| `hostb_rowAct_iff` | `[propext, Quot.sound]` |
| `hostb_r16_cases` | `[propext, Quot.sound]` |
| `regLenAgree_group_of_holds` | `[propext, Classical.choice, Quot.sound]` |
| `reg_group_walk` | `[propext, Classical.choice, Quot.sound]` |
| `reg_gap_lt` | `[propext, Classical.choice, Quot.sound]` |
| `reg_pos_lt_len` | `[propext, Classical.choice, Quot.sound]` |
| `reg_gap_wraparound` | `[propext, Classical.choice, Quot.sound]` |
| `regLenAgree_lone_length` | `[propext, Quot.sound]` |
| `wasm_base_exec_host_holds` | `[propext, Classical.choice, Quot.sound]` |
| `hostb_inters_stk` | — (none) |
| `hostb_touches_ch` | — (none) |
| `hostb_avoids_state` | — (none) |

The `(ptr, len)` link (`Main/MemIOLink.lean`) is audited in the same file:

| theorem | axioms |
|---|---|
| `host_base_constr` | `[propext, Classical.choice, Quot.sound]` |
| `hostb_bit` | `[propext, Classical.choice, Quot.sound]` |
| `hostb_act_one_minus_reg_le` | `[propext, Classical.choice, Quot.sound]` |
| `host_send_base` | `[propext, Classical.choice, Quot.sound]` |
| `host_hsend_r16` | `[propext, Classical.choice, Quot.sound]` |
| `host_r16_recv` | `[propext, Classical.choice, Quot.sound]` |
| `host_r16_sound_at` | `[propext, Classical.choice, Quot.sound]` |
| `host_time_chk` | `[propext, Classical.choice, Quot.sound]` |
| `hostb_timechk_occ` | `[propext, Classical.choice, Quot.sound]` |
| **`hostb_mem_distinct`** | `[propext, Classical.choice, Quot.sound]` |
| `hostb_mem_consumed` | `[propext, Classical.choice, Quot.sound]` |
| `hostb_addr_lt` | `[propext, Classical.choice, Quot.sound]` |
| `stepLive_space` | `[propext, Classical.choice, Quot.sound]` |
| **`host_step_rely_buf`** | `[propext, Classical.choice, Quot.sound]` |
| **`host_rel_restart_buf`** | `[propext, Classical.choice, Quot.sound]` |

### 4.4 Soundness hygiene

`grep -rn "sorry\|admit\b\|native_decide"` over `MemIO.lean`, `Main/MemIOBus.lean`,
`Main/MemIOLink.lean`, `HostChip.lean`, `Main/SoundHost.lean`, `Main/ExecHost.lean`,
`Main/HostBus.lean`, `Main/SegHarness.lean`, `Main/RegSend.lean`, `Main/HostChipBits.lean`:
**empty**. No `axiom` declarations in the MEMIO files.

### 4.5 Status

Green: build, KAT (97/97), tamper (101/101), axiom audit. **Pending integration into `main`; the earlier merged claim was incorrect.** Both
formerly-open steps (§3.5: `hostb_mem_distinct`, and the `HostStepRely.heap` wiring of
`heap_retime`) are closed.
