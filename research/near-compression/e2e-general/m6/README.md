# E2E milestone M6 (lane A side): binding host answers — scope

Plan: `docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §3.3 (the Wasm ↔ state join), §4.2 (row M6).
Date 2026-11-03. Labels as in `m4/README.md`: **[M]** measured, **[K]** kernel-checked Lean
(standard axioms, no `sorry`), **[S]** stated / design only.

## 1. What the Wasm proof assumes about host calls today [K]

`seg_sound` (`wasm-base-lean/WasmBase/Main/SegSoundX.lean`) and `wasm_base_sound_m2` are relative
to the host answers. Per active HOST row (table 22) they take:

| premise | content | where it comes from today |
|---|---|---|
| `HoldRowS` (`RowFactsSeg` of the HOST row) | the row is one spec `step` (a `call` of an import): from a related pre-state, `step = .cont s'` with `Rel` at the restarted gas segment `(S + fee, g_after)`, or `.abort` | AIR facts `host_rowfacts` [K] + `HostOK` (the `HOSTR` response is the abstract `HostResp` of the state) + `HostStepRely` (stack depth/types, heap, calls after the call) via `host_rel_restart` [K] |
| `HostRely.reg` (`HostRegRely`) | the row's space-6 (register) traffic tracks the host function's register effect | named |
| `HostRely.sp`, `HostRely.wf` | the row produces messages in allowed spaces only; the register file stays well formed (distinct ids) | named |
| `HostBLinked`, `RegCLinked` | every HOSTB / REG-C row carries the `(ts, hid)` of an active HOST row | named (trace grouping; not implied by the bus balance) |

Inside the trace the requests (`HOSTQ [ts, hid, S, args…]`) and responses (`HOSTR [ts, st, r, g_after]`)
are answered by the witness table `HOSTO` (one row per call): a free oracle. The memory bytes a
host function reads or writes travel on `HOSTB [ts, pos, byte]` and the CH bus (space 3); register
contents on REG-C (space 6). So today the proof says: *if* these answers are the host function's,
the Wasm run is the spec's.

## 2. What a host function can touch (spec, `NearSpecV3/Wasm/Host.lean`, `Exec.lean`) [S]

`callHost s name` = `sync` (settle the gas counter) → the arm `hostCall name` (an `EStateM String St`
program) → `.cont {s with gas.g := remaining}` or `.abort`. Reading the arms:

* frames: never written (`host_frames_eq` [K]); operand stack: only through `popArgs`/`pushRet`
  (`host_numS` [K]);
* linear memory: only through `readMemH`/`writeMemH` (`readBytes`/`writeBytes`, bounds-checked);
* registers: `regGetH`/`regSetH` (+ `register_len`); globals: never;
* the **host-side state** `σ`: every other `St` field — `gas`, `ctx`, `ret`, `balance`,
  `storageUsage`, `regUsage`, `logs`, `totalLogLen`, `promises`, `trie`/`real` (storage),
  `actions`, `dataCount`, `subsidized`, the curve flag.

`WasmView`'s boundary already splits a cut state the same way: the viewed parts (stack, frames,
globals, registers in `ctxDigest`; pages in `memRoot`) and the remainder `blank s`, committed by
`vmCtxDigest` (`WasmView.lean`).

## 3. The target contract `HostIf` [S]

One bus-level contract, the host analogue of the SHA chip's `ChipIf`, between the HOST rows and
whatever answers them (today HOSTO; after the join, lane B's state rows in the same trace, plan
§3.3):

> There is a sequence of host-side states `σ_0, …, σ_m` (one per host call of the segment, in STATE
> time order), with `σ_0` the in-boundary's `blank s0` and `σ_m` the out-boundary's, such that for
> the `j`-th HOST row with request `(hid, S, args)`, the bytes it reads (HOSTB, with addresses) and
> the register contents it reads (REG-C): running the arm `hostCall hid` on any state whose
> host-side part is `σ_j` and whose memory/registers agree on what the row read yields
> the row's response `(st, result, g_after)`, exactly the bytes it writes, exactly its register
> writes, and host-side state `σ_{j+1}`.

Obligations, by owner:

* **M6.1 footprint [lane A, spec-level]:** each arm factors through (`σ`, args, the memory bytes it
  reads, the registers it reads) and changes only (`σ`, pushed results, the bytes it writes, the
  registers it writes): `callHost` commutes with the projection to the Wasm-visible part. Per arm
  (75 arms), mechanical; the primitives (`readMemH`, `writeMemH`, `regGetH`, `regSetH`, `popArgs`,
  `pushRet`, gas ops) first.
* **M6.2 `HostIf ⇒ HoldRowS ∧ HostRely` [lane A]:** with M6.1, `HostOK` and `HostStepRely` become
  consequences of `HostIf` + the AIR (`host_rowfacts`, HOSTB/REG-C row lemmas); the space clause
  (`HostRely.sp`) and `RegWF` (`HostRely.wf`, `regSetH` keeps ids distinct) are AIR/spec facts
  without any contract.
* **M6.3 `HostBLinked` / `RegCLinked` [lane A, AIR]:** a key lookup from HOSTB / REG-C rows to the
  HOST row's `(ts, hid)` (HOST offers it with multiplicity) makes both derivable from `HoldsX`
  (`unique` already follows from distinct STATE times).
* **M6.4 the producer [lane B]:** the state template's host-semantics rows produce `HOSTR`/`HOSTB`/
  REG answers from the working set, the VMContext digest and the receipt counters, and prove
  `HostIf` (with `σ` in the segment boundary as the remainder digest).
* **M6.5 the call tape [lane E]:** `σ_0` of a call's first segment is the host-side part of the
  entry state (`preConf q`), and the last segment's `σ` gives the call's `Run` (logs, promises,
  return data, gas), so the VM leaf of lane E's `RCM` (answered by `callResult q`) is the
  composition of the segments (`cuts_csteps` / the chained-segments theorem).

## 4. Status

* 2026-11-03: scope (this file).
* **Finding [K/S]:** `RelW` reads a state only through its Wasm-visible part and `gas.g`
  (`relW_of_vis`, `relW_sigma`, `Main/HostFoot.lean`). The HOST-row premises quantify over every
  related pre-state, so they fail whenever a continuing host call's answer depends on `σ` (always:
  `g := remaining`). Until `σ` is pinned per call, every segment theorem is vacuous on host
  traces. This makes §3's `HostIf` (σ-indexed) the necessary shape, not just a convenient one.
* **First proofs [K]:**
  * `hostRely_sp`: the space clause at HOST rows, no premises (`Main/HostSpace.lean`).
  * M6.1 footprint, stability half: `Inv`/`Stab` framework, the `inv_auto` tactic, all 75
    `hostCall` arms and 14 curve arms. `callHost_hinv`: frames, globals, tables, stack budget and
    page count unchanged; pages well-sized; register ids distinct; stack integer
    (`Main/HostFoot.lean`, `HostArms.lean`).
  * `step_regIds`: every step keeps register ids distinct; `HostRely.wf` ⇐ `HostRegCap`
    (`Main/HostRegWF.lean`).
* **Open:**
  * Noninterference half of M6.1: an arm's result factors through `σ` + bytes/registers read.
  * The σ-pinned restatement (SIGMA sub-lane; see the lane log).
  * M6.2–M6.5.
