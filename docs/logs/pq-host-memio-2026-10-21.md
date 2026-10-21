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

## Next

A dedicated MEMIO lane for the `(ptr, len)` link, with `memRaw`/`HeapOK`/`RelW` extended to the host
buffer. `HOSTB.inters` has the `memAddr` expression ready (commented) and `cStartPos` gives the group
structure.
