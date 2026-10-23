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

## Step 1.1 closed — the R16 send bound for REG (2026-10-22)

Landed on `main` from a clean branch off `main` (`lane/pq-reg-hsend`), *without* the branch's
unfinished MEMIO WIP: the three MEMIO commits (`df81c7436`, `ebd1298e0`, `30352dc58`) are not on
`main`, they break `HostBus`, and `Main/MemIOBus.lean` still ends in a `sorry`. So the `hsend` work
was re-applied on top of `main`'s `HostChip.lean`/`HostChipBits.lean` instead of the lane's HOSTB
columns.

### What was actually open, and what was wrong with the statement

`regLenAgree_group` took

```
hsend : ∀ o ∈ occs (wasmBaseRegAir …) tr pub, o.2.1 = true → o.2.2.2 ≤ 1
```

and reached it via `reg_gap_lt → reg_r16_query_16bit → lookup_sound`. Two corrections:

* **The global form is false.** `HOSTO`'s two interactions are counted with a free column `mult`
  and `HostO.table.constraints = []`, so "every send of the trace has count ≤ 1" fails for any host
  trace. `Bus.lookup_sound` already takes the bus-restricted form, and the walk uses `b = busR16`.
  The hypothesis in `reg_r16_query_16bit`, `reg_gap_lt` and `regLenAgree_group` is therefore narrowed
  to `o.1 = busR16 → o.2.1 = true → o.2.2.2 ≤ 1` — the true and sufficient statement.
* **`Holds (wasmBaseAir)` cannot be reused.** REG traces add space-6 CH traffic, so they do not
  satisfy the base AIR; base `occ_bits` was unavailable. Split `occ_bits_of` out of `occ_bits`
  (`Main/Exec.lean`): constraint-only, no bus balance.

### The proof (`Main/RegSend.lean`, 408 lines, new)

* `reg_base_constr`: tables 0–21 of `wasmBaseRegAir` are literally `wasmBaseAir`'s, so `Holds` gives
  their row constraints; `occ_bits_of` then yields their count bits.
* `reg_chip_counts`: each chip's constraint-only `*_counts_of` lemma applied at the REG AIR's table
  index — no `ChipFacts` hypothesis needed, the bits are *derived*.
* Host tables: HOST (22) counts are `act` or `pf j`; HOSTO (23)/HOSTT (24) have no R16 interaction;
  HOSTB (25) counts are `act·(1−reg)`; REG (26) counts are `act·fresh`, `act·(1−kind)`, `act`.
* `reg_hsend_r16`: the bus-restricted bound, from `Holds` alone.
* `regLenAgree_group_of_holds`: hypothesis-free form of the group theorem.

### Refactor (additive only)

`table_constr_eq` (`Extract/Row.lean`); `occ_bits_of` (`Main/Exec.lean`); `meminit_bits_of` /
`meminit_counts_of` (`Main/MemInit.lean`); `*_flags_of` / `*_counts_of` in the 13 `Main/Row*.lean`
chips. Every old `Holds (wasmBaseAir)` statement is kept as a one-line wrapper, so no call site
changed and no statement was weakened. The group-walk proofs are untouched; only `hsend`'s
provenance changed. `WasmBase.lean` imports `Main.RegSend` so the module is in the build graph
(root-import trap).

### Verification (on `main`, clean branch)

* `lake build` — **236 jobs**, green.
* `#print axioms` — `reg_hsend_r16`, `reg_chip_counts`, `regLenAgree_group_of_holds`,
  `regLenAgree_group` all ⊆ `[propext, Classical.choice, Quot.sound]`.
* `grep` for `sorry` / `admit` / `native_decide` / `axiom` across all 20 touched files: none.

### Deliberately not included

The MEMIO `(ptr, len)` → linear-memory link (§3 of RESULTS.md) stays deferred. The lane's HOSTB
space-3 `chRecv`/`chSend` pair and `memCnt` column are WIP that does not build and would have
dragged `MemIOBus`'s `sorry` into `main`. That work belongs in its own lane, starting from the memory
step (`hostb_mem_step`) rather than from the columns.
