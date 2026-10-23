# MEMIO lane finalization and integration — 2026-10-23

Integrated `lane/pq-host-memio` through `c87be91ee` (including its six previously unmerged
checkpoints) against main `65f7e3d3e`. Integration worktree: `integration/memio-finalize-20261023`.

## What is now implemented

HOSTB has 14 columns, including `ptrLo`, `ptrHi`, `mtp` and `hp`. Request bytes emit a space-3
receive of the prior byte and a send of the same byte at the host-call timestamp. The generator
supplies the pointer/time range witnesses and updates memory producer times, so later reads and
the final drain see the re-timed bytes. Main's corrected log/return host IDs and argument order,
IF/storage support, and RIPEMD modules were preserved during conflict resolution.

The Lean additions include the memory view (`BufOK`, `heap_retime`, `heap_retime_readByte`),
HOSTB partition into host-call channel messages, timestamp distinctness, consumed-byte readout,
and `host_step_rely_buf` / `host_rel_restart_buf`. REG's R16 send bound now covers both HOSTB
count shapes. `Main.MemIOLink` is imported by the `WasmBase` umbrella.

## Integration correction: response rows must not be memory-active

The lane's `HostBLinked.linked_inv` required every HOSTB row sharing an active host key to be
CH-active. That excludes response bytes (`dir = 1`) and register bytes (`reg = 1`), whose
`memCnt = act·(1−dir)·(1−reg)` is zero even when they share a real call's `(ts,hid)`.

Removed that premise. `hostb_partition` now uses the host-AIR `Holds` already available at its
callers and `hostb_inactive_nil` to show those rows contribute no space-3 messages. Forward
request-byte grouping and unique host-call keys remain explicit hypotheses. The proof is checked;
no extra axiom or assumed inverse grouping replaces the removed field.

## Fresh validation

See `research/near-compression/results/pq-host-memio/FINAL-VALIDATION.json` for exact results,
source fingerprints and evidence hashes. All tests use the integrated source, not the old tracked
Rust binary or stale AIR exports.

* `lake build WasmBase wasmbase-tool`: 246 jobs, success; affected dependencies rebuilt.
* `lake env lean AxiomsMemio.lean`: 40 declarations, axioms restricted to
  `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
* Isolated `cargo build --release --locked --offline -j 8`: success.
* `run_kat.sh`: 98 passed, zero failed (Python/spec/trace agreement and AIR checks).
* `d3tiny` with `prepIf` and `airIfH`: eligible, `CHECK OK`; HOSTB width 14 and IF/storage
  traffic coexist in the integrated trace.
* Three base-AIR exports (`nloc/ngl = 0/0, 1/0, 2/1`) are byte-identical to main's prior tool.
* Proof-level log/register tamper runs include honest proofs verified first. Added six targeted
  MEMIO controls: each pointer limb, producer timestamp and gap witness changed; `mtp = ts`;
  and `ptrHi = 2^11`. **Log-memory: 86/86 rejected; register: 101/101 rejected.**
* `make pin-check` and whitespace/conflict checks pass.

Logs and scratch artifacts: `/data/illia/memio-finalize-20261023/`. The hung `systemd-run` build
attempts were not used as evidence. Builds ran directly with bounded Cargo parallelism and test
thread counts; no shared dependency or host configuration was changed.

## Exact remaining boundary

This closes the MEMIO implementation/interface checkpoint, not the full host/D3 proof.
`HostBLinked.linked` and `.unique` still need an interface instantiation. `hostb_mem_consumed`
requires the consumed message to be live in the pre-heap; `BufOK` is an explicit buffer bound.
The whole-host execution theorem still carries `H0`, `HoldRow`, segment and boundary premises.
The timestamp theorem proves `mtp ≠ ts`, not a standalone natural-order theorem from modular
field equations. General response writes, arbitrary host payload coverage, and the state/Wasm
join are not established by these lemmas.

The diagnostic generator retains its pre-existing 40-byte log/return cap and placeholder payload
slice for other calls. Tests establish the supported fixtures, not general NEAR host semantics.
Old "both complete" / "merged" lane notes are superseded by this scoped report and fresh evidence.
