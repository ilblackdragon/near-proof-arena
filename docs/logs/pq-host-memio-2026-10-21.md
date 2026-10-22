# pq-host-memio — lane log (2026-10-21)

Continuation of `pq-host-memio-handoff-2026-10-21`. Worktree `/data/illia/nearproof-wt/pq-host-memio`.
Full write-up: `research/near-compression/results/pq-host-memio/RESULTS.md`.

## Landed

| commit | what |
|---|---|
| `6cb97d77f` | REG group walk: `reg_byte_not_last`, `reg_group_bounds`, `reg_step`, `reg_group_walk`; plus `reg_air_get`/`reg_air_2x`/`reg_air_15r`/`reg_air_16b`/`reg_range16_values` in `RegFacts` |
| `ff7cf31b4` | `reg_rid_const` / `reg_ts_const` (`cRidG` / `cTsG` row lemmas) |
| `d9ca88fac` | `regLenAgree_group` (the corrected obligation) + `reg_pos_lt_len`, `reg_gap_lt`, `reg_r16_recv`, the slot/message lemmas |
| `ae666c104` | HOSTB `r16 pos` + `r16 blen`; generator + two tamper cases |

## What is still open (do not overclaim Part 1)

`regLenAgree_group` takes the R16 `hsend` bound as a **hypothesis** — that is the handoff's Step 1.1
(`reg_r16_send_bits`), not closed. It is load-bearing (`reg_gap_wraparound`: `gap = P−1` satisfies
`cPosLtLen` at `pos = len` for every `len`, so only `gap < 2^16` kills the byte row at offset `len`)
and not derivable from `Holds (wasmBaseRegAir)` alone (REG's space-6 traffic means a REG trace does
not satisfy `Holds (wasmBaseAir)`, so the base AIR's `occ_bits` does not apply). Closing it means
restating the 13 chips' `*_flags` bounds for `wasmBaseRegAir`; it does not touch the walk argument.

## The finding a reviewer must know

**`Register.RegLenAgree` is false as stated**, not merely unproved. `register_len` emits one length
row and no byte row, so counting byte messages at the length message's producer time gives `0 ≠ len`.
Machine-checked: `regLenAgree_lone_length`. The trace generator really does emit that shape and
`gen.py`'s `regkat` really does call `register_len`, so this is not a corner case.

The AIR obligation is *group-local* and is proved: `regLenAgree_group`. `RegisterSpace.lean`'s
definition is kept but marked deprecated, with a pointer to the refutation, so nobody re-attempts the
false statement.

## Correction to the handoff

The handoff attributes `pos < len` to `2e536d4b7`'s `r16 pos`. It is not that lookup: `reg_pos_le`
already gives `pos ≤ r < 2^24`, which makes `cPosLtLen` exact. `r16 gap` is the load-bearing one for
this argument. `r16 pos` remains in the AIR and is harmless (it does pin `pos < 2^16`), but the
justification recorded in `RegChip.lean`/the handoff overstates it. Left the constraint in place;
corrected the reasoning here.

Second thing the handoff got right and worth restating: the **HOSTB hole is real** and is now closed
(`r16 pos`, `r16 blen`). Predicted exactly.

## A trap I fell into and corrected in my own write-up

I first recorded that a *same-time* `chRecv`/`chSend` pair on space 3 would "compose mechanically and
force `memory[addr] = bv`". **That is false.** `busNat` matches on `(bus, direction, message)`, so two
identical messages in opposite directions land in the same bucket and cancel for every count — the
pair is vacuous (the same device as HOSTB's pre-existing `reg = 0` self-permutation). Only the real
`tp < ts` LOAD shape, which *re-times* the message, asserts anything. RESULTS.md §3 now records this.

## Part 2(b) was not built, deliberately

The `(ptr, len)` → space-3 link requires extending the memory *view* (`memRaw` / `HeapOK` / `RelW`):
once HOSTB emits space-3 messages, `ch_raw_host` (`Main/HostBus.lean`) no longer closes, because a
host call's buffer bytes are neither instruction rows nor the `memRaw` block. That is the deferred
MEMIO work the handoff itself names. See RESULTS.md §3 for the same-time no-op design that *would*
close mechanically, and why it is a strictly weaker statement.

## Process notes

* The handoff's process lessons held: `set` does not exist, `by_contra` failed once (used
  `rcases Classical.em`), `Nat.find` absent, and `#check`-ing the goal before choosing a tactic saved
  a lot of time. `decMsg_cast` (`Main/Rows.lean`) is the right tool for the `Msg`-shape lemmas — it
  removed a long cast fight.
* Row/successor lemmas must be defined **before** their users in the file; two build failures came
  from appending a helper after `end WasmBase`.
* Beware editing by string replace when the same docstring appears twice (a duplicate block landed
  after `end WasmBase` once and cost a debugging cycle).

## Verification

* `HEAVY_MEM=16G taskset -c 8-15,24-31 heavy lake build` — 138 jobs, green.
* KAT `88 passed, 0 failed`; tamper `101/101 rejected` (99 pre-existing + `pos=2^16`, `len=2^16`).
* `#print axioms`: `regLenAgree_group`, `reg_group_walk`, `reg_gap_lt`, `reg_pos_lt_len` ⊆
  `[propext, Classical.choice, Quot.sound]`.

## Merge into main (2026-10-21)

Merged `main` (`4885e5834`) into the lane in the worktree and re-verified before fast-forwarding
main. One conflict, in `native/wasm-base/src/tracegen.rs`: main added the SHA-256 host block
(`has_sha` / `sha_calls`) at the same point where this lane updated the register-wire comment.
Resolution keeps main's SHA block and this lane's corrected host ids (48/49, not the pre-canonical
12/13). No semantic overlap.

Post-merge verification (all in the worktree, before touching main):

* `lake build` — **225 jobs** (main's Keccak/SHA modules added), green.
* KAT — **97 passed, 0 failed** (main's SHA programs included; was 88).
* tamper — **101/101 rejected** (99 pre-existing + this lane's `HOSTB pos=2^16`, `len=2^16`).
* axioms of `regLenAgree_group`, `reg_group_walk`, `reg_gap_wraparound` ⊆ the standard three;
  `regLenAgree_lone_length` ⊆ `[propext, Quot.sound]`.

## Next

A dedicated MEMIO lane for the `(ptr, len)` link, with `memRaw`/`HeapOK`/`RelW` extended to the host
buffer. `HOSTB.inters` has the `memAddr` expression ready (commented) and `cStartPos` gives the group
structure.

## 2026-10-22 — Step 1.1 closed: `hsend` for REG traces

`Main/RegSend.lean` (new) proves the R16 send-side bound for `wasmBaseRegAir` from `Holds` alone:

* `reg_chip_counts` — the 14 instruction tables' count bits, by applying each chip's
  constraint-only `*_counts_of` lemma at the REG AIR's own table index.  No `ChipFacts` assumption.
* `reg_hsend_r16` — `∀ o ∈ occs (wasmBaseRegAir …), o.1 = busR16 → o.2.1 = true → count ≤ 1`:
  tables 0–21 via `occ_bits_of` + `reg_base_constr`; HOST/HOSTB via their R16 count shapes;
  HOSTO/HOSTT have no R16 send; REG via `reg_r16_cases`.
* `regLenAgree_group_of_holds` — the group theorem with no `hsend` hypothesis.

The stated global `hsend` (`o.2.1 = true → count ≤ 1`, all buses) is **false**: `HOSTO`'s two
interactions are counted with the free column `mult`.  `Bus.lookup_sound` already takes the
bus-restricted form, and the walk only ever applies it at `busR16`, so the hypotheses of
`reg_r16_query_16bit`, `reg_gap_lt` and `regLenAgree_group` were narrowed to that instance.

Axiom audit: `[propext, Classical.choice, Quot.sound]` for all three.  No `sorry`/`axiom`/`native_decide`.

Note: `WasmBase` as a whole still fails at `Main/SoundHost` (`Unknown identifier host_buses`) — that is
the separate, in-progress HOSTB space-3/MEMIO work (`HostBus`/`SegHarness`/`SoundHost`/`MemIOBus`),
untouched by this change.  `RegSend`, `RegWalk` and `RegFacts` build green individually.

## 2026-10-22 — MEMIO landed: the `(ptr, len)` link is built and verified

The deferred MEMIO work (RESULTS §3) is in. Five commits on top of `c6761629d`, HEAD `16a1abad0`:

| commit | what |
|---|---|
| `728fabae7` | `WasmBase/MemIO.lean` — `BufOK`, `heap_retime_readByte`, `heap_retime`, `ch_pair_vacuous` |
| `df81c7436` | `HostB` 14 columns (`ptrLo`, `ptrHi`, `mtp`, `hp`), `cPtrLoConst`/`cPtrHiConst`, the space-3 `chRecv`/`chSend` pair and `timeChk` |
| `ebd1298e0` | HOSTB joins the CH bus decomposition (`msgs_ch_host`, `flatMap_prodCH_perm`, `flatMap_consCH_perm`) |
| `30352dc58` | HOSTB is a CH emitter; its space-3 count is a bit (`hostb_memCnt_bit`, `hostb_touches_ch`, `hostb_avoids_state`) |
| `16a1abad0` | fold HOSTB's space-3 block onto its host call (`hostb_partition`, `hostb_partition_prod`/`_cons`) |

The link is the **LOAD shape**, not a same-time pair: a request byte (`dir = 0`, `reg = 0`) consumes
`encB (ptr+pos) byte mtp` and re-produces it at `ts`, with `timeChk ts mtp hp` forcing `mtp < ts`. The
same-time variant is vacuous (`ch_pair_vacuous`: `busNat` keys on `(bus, direction, message)`, so an
identical recv/send cancels for every count) and was rejected.

### The generator was the blocker, and it had three defects

KAT was red at first: **21 of 97 programs failed** with `buses: unbalanced` on bus 2 (space 3) and
bus 3 (`RANGE16`). The Lean AIR declared 14 `HOSTB` columns and the space-3 pair, but
`native/wasm-base/src/tracegen.rs` still wrote 10 columns and never re-timed memory. Fixed:

1. **Row width** — `hostb_rows` was `[u64; 10]`; now `[u64; 14]`, and the emission loop writes
   `ptrLo, ptrHi, mtp, hp`.
2. **The payload arm never fired** — it tested host ids `[8, 9, 10, 15]`, which are
   `promise_create`/`promise_then`/`promise_and`/`promise_batch_action_deploy_contract`, not the
   log/return ids. The real ids are `Chips.hostLogFns`: `log_utf8 = 45`, `log_utf16 = 46`,
   `panic_utf8 = 47`, `value_return = 50`. (An absent `HOSTB` group still balances its bus, so the
   KAT could not see the miss — this is exactly the "absent group" blind spot main's version warns
   about.)
3. **The argument order was reversed** — the spec's signature is `log_utf8(len, ptr)`
   (`utf8H a[0] a[1]` then `readMemH ptr len`), so `args[0]` is the **length** and `args[1]` the
   pointer. The arm had `(ptr, blen) = (args[0], args[1])`, so `log_utf8(5, 0)` produced `blen = 0`
   and zero rows.

Each request byte now does `mem.get(ptr+pos) → (b, mtp)`, `st.tchk(ts, mtp)` (asserts `mtp < ts` and
records the two `timeChk` R16 lookups), `mem.cur.insert(ptr+pos, (b, ts))` to re-time the byte, and
answers the row's five lookups (`byteQ`, `r16 gap`, `r16 pos`, `r16 blen`, `r16 ptrLo`,
`r16 32·ptrHi`). A `reg = 1` fill row leaves all four memory columns zero (`memCnt = 0` there, so its
byteQ/r16 queries have count 0 and only the bus-210 send `act·reg` remains, which `REG` receives).
The placeholder arm (non-REG AIRs) emits its request half as a real memory read at base 0 when the
program has ≥ 4 bytes of memory, and otherwise only the response half (`dir = 1`, state-side data
that never touches memory).

### Verification (final)

* `lake build` (`wasm-base-lean`): **229 jobs, "Build completed successfully"** — this closes the
  `Main/SoundHost` `Unknown identifier host_buses` failure noted above. Log `/tmp/build-final-memio.log`.
* `cargo build --release`: clean (9 pre-existing warnings).
* KAT: **`KAT: 97 passed, 0 failed`** (`./run_kat.sh /tmp/kat-memio`) — reconciles with both the
  lane's `88 passed, 0 failed` and main's `97 passed, 0 failed` (the extra 9 are main's SHA programs).
  Was **21 failed** before the generator fix.
* Tamper: **`TAMPER summary 101/101 rejected`** — no regression. Includes the §2 range-check cases
  (`pos = 2^16`, `len = 2^16`) and the HOSTB column cases (`byte`, `dir = 2`, duplicate `pos`, `len`,
  `hid`, `gap`), plus the REG group cases.
* Axiom audit (`AxiomsMemio.lean`, `lake env lean`): **every headline theorem ⊆
  `[propext, Classical.choice, Quot.sound]`** — `heap_retime`, `heap_retime_readByte`,
  `BufOK.addr_lt`, `hostb_partition`, `hostb_partition_prod`/`_cons`, `flatMap_prodCH_perm`/
  `flatMap_consCH_perm`, `host_hch`, `host_buses`, `hostb_memCnt_bit`, `hostb_inactive_nil`,
  `regLenAgree_group_of_holds`, `reg_group_walk`, `reg_gap_lt`, `reg_pos_lt_len`,
  `reg_gap_wraparound`, `wasm_base_exec_host_holds`. Three structural lemmas
  (`hostb_inters_stk`, `hostb_touches_ch`, `hostb_avoids_state`) need no axioms at all.
* `grep -rn "sorry\|admit\b\|native_decide"` over the nine MEMIO/HOSTB/REG files: **empty**. No
  `axiom` declarations.

### The one open step

**`hostb_mem_distinct` (`mtp < ts`) is not proved as a derived fact about the trace.** It is enforced
on *generated* traces by `st.tchk`'s assertion and by the AIR's `timeChk` lookups — which is what
makes the pair non-vacuous — but there is no theorem taking `Holds` to `mtp ≠ ts` for an arbitrary
trace. Together with wiring `heap_retime` into `host_rel_restart`'s `HostStepRely.heap` field, that is
what remains. Nothing merged to `main`.
