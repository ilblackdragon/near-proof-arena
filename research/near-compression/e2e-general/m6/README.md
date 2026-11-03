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
  * The two-run footprint of `callHost`, which would make honest `HoldRowSσ`/`HostRelyσ` (M6.2) a
    theorem.
  * M6.3–M6.5.
* **σ-pinned restatement [K]:** `HostVacuity.lean` (mechanised counterexample), `SegSigma.lean`,
  `SegSoundSigma(MP).lean`, `SegChainSigma.lean` (`seg_sound_σ`, `seg_sound_cσ`, `seg_chain_σ`).
  The thread `sideR` is the host side plus the register file.

## 6. Proposed `WasmBnd` diff for lane E (gasLeft, register-id order) [S]

The integrator routes this to lane E; lane A does not edit `spec/`. Target file:
`spec/lean/v3/NearSpecV3/E2E/Boundary.lean`. Lane A's matching side is
`wasm-base-lean/WasmBase/Main/WasmView.lean` (`airBnd`, `fbBnd`, `blank`).

**Why.** Today the AIR branch puts `blank s` in the `vmCtxDigest` remainder, and `blank s` keeps
two things that move:

* (a) the whole `s.gas`, including the Wasm gas register `gas.g`;
* (b) the register ids in insertion order (`regIds`).

Every instruction changes `gas.g`. A segment would therefore have to recompute the remainder digest
at every cut, although nothing else in the remainder moves between host calls. The register-id
order moves when a host call creates a register (`regSetH` appends). The view (`cutView`) is a set,
so it cannot carry that order.

With the σ-thread (§4), the remainder becomes the host side `sideR` without `gas.g` and without the
registers. It changes only at HOST rows (`step_sideG`), and there the state side produces it (M6.4).

### 6.1 Lane E diff (Boundary.lean)

```diff
 /-- The Wasm part of a boundary (present iff `inCall`). -/
 structure WasmBnd where
   pc : Nat
   sp : Nat
   stackRem : Nat
   fuel : Nat
+  /-- the Wasm gas register `s.gas.g` (u64); the AIR has it as `segb − R·(S − S_seg)` -/
+  gasLeft : Nat
   framesDigest : ArenaCore.Bytes
   memRoot : ArenaCore.Bytes
   memPages : Nat
   globalsDigest : ArenaCore.Bytes
   registersDigest : ArenaCore.Bytes
   vmCtxDigest : ArenaCore.Bytes
   promisesDigest : ArenaCore.Bytes
   codeRoot : ArenaCore.Bytes
   funcRoot : ArenaCore.Bytes
   deriving DecidableEq

 def WasmBnd.codec : Codec WasmBnd :=
-  mapC (pairC u64C (pairC u64C (pairC u64C (pairC u64C (pairC digC (pairC digC (pairC u64C
-      (pairC digC (pairC digC (pairC digC (pairC digC (pairC digC digC))))))))))))
-    (fun w => (w.pc, w.sp, w.stackRem, w.fuel, w.framesDigest, w.memRoot, w.memPages,
+  mapC (pairC u64C (pairC u64C (pairC u64C (pairC u64C (pairC u64C (pairC digC (pairC digC
+      (pairC u64C (pairC digC (pairC digC (pairC digC (pairC digC (pairC digC digC)))))))))))))
+    (fun w => (w.pc, w.sp, w.stackRem, w.fuel, w.gasLeft, w.framesDigest, w.memRoot, w.memPages,
       w.globalsDigest, w.registersDigest, w.vmCtxDigest, w.promisesDigest, w.codeRoot, w.funcRoot))
-    (fun (a, b, c, d, e, f, g, h, i, j, k, l, m) => ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩)
+    (fun (a, b, c, d, g0, e, f, g, h, i, j, k, l, m) => ⟨a, b, c, d, g0, e, f, g, h, i, j, k, l, m⟩)
     (fun _ => rfl)
```

The following do not change: `BndRec`, `BndRec.codec`, `WF`, `decode_encode`, `encode_inj`. The
record grows by 8 bytes. `registersDigest` keeps its type and gets a new value on lane A's side
(§6.2), so the register-id order needs no structural change.

### 6.2 Lane A side (WasmView.lean, after lane E lands 6.1)

| field | today | proposed |
|---|---|---|
| `gasLeft` | n/a | AIR branch `s.gas.g`; fallback `0` |
| `registersDigest` | `fd` (= `framesDigest`, redundant) | `bdigest (regIdBytes s.registers)`: the u64 ids in order, as a counted list |
| `blank s` (remainder) | `gas` whole; `registers := regIds s.registers` | `gas := {s.gas with g := 0}`; `registers := #[]` |

* `InDom` gains `s.gas.g < 2^64`. This follows from `RelW` (`g ≤ segb < 2^64`).
* Binding:
  * `blank_inj` takes `gas.g` from `gasLeft`.
  * It takes the register order from `registersDigest`. `regIdBytes` is injective on id sequences,
    so a mismatch is a `bdigest` collision (`Sha384Coll`).
  * `reconstruct` is unchanged.
* What a segment must produce:
  * `gasLeft` comes from the AIR's `(S, S_seg, segb)`.
  * `registersDigest` changes only at a HOST row that creates a register. The state side produces
    it together with σ (M6.4). An AIR without host calls copies it from in to out.
  * `vmCtxDigest` is then constant across host-free segments.

**Alternative for the order (not preferred).** Canonicalise the spec's register file, sorted by id,
with `regSetH` inserting in order. That is a semantic spec change, even though behaviour does not
depend on the order once ids are distinct (`step_regIds`). §6.2 avoids it.
