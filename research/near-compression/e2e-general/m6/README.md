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
* 2026-11-21: M6 results are in §5. Its open list (§5.6) supersedes the "Open" items below.
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

## 5. M6 results (lane A, sixth session, 2026-11-03 … 2026-11-21) [K][M]

All Lean below lives in `wasm-base-lean/WasmBase/Main/` unless noted. Every theorem uses only
standard axioms, and no proof uses `sorry`. `lake build WasmBase wasmbase-tool` is green (727 jobs,
rebased on main `7358a938d`). `make pin-check` is ok. `spec/` is unchanged. Sub-lanes: FOOT2,
HOSTIF, COVER (item 1/3), CHAIN (item 2), GROW, GROW2 (item 4), FIX214 (AIR bug).

### 5.1 Item 1: the honest run satisfies the pinned host premises (M6.1, M6.2) [K]

* **The two-run footprint of `callHost`.** All 75 `hostCall` arms and the 14 curve arms are
  covered.
  * Files: `HostTwoRun.lean` (relational framework: `Low`, `Tw`, `Rel2`, the lock-step tactic
    `rel_auto`), `HostTwoRunArms.lean` (`readSetOf`, `nargs`, `arm2_*`/`arm2c_*`) and
    `HostTwoRunCall.lean`.
  * **`callHost_two_run`**: if `Low A k s s'` holds, `HostArm s name`, `nargs name ≤ k`, and
    `readSetOf name s ⊆ A`, then the two calls correspond: both continue, abort, or are unmodeled
    alike.
  * On `.cont`, both post-states are **one `HostEff` applied to the two pre-states**. They have
    equal `sideR` and `gas.g`, the same pops and pushes and the same bytes written; everything else
    stays each side's own.
  * Both mock `trie` and trie-backed `real` storage are covered.
  * Read sets are exact on continuing runs, except supersets for NUL-terminated `log_utf8`/
    `panic_utf8`, `log_utf16`, `abort`, and `ed25519_verify`'s early return.
* **Spec-level non-vacuity check** (`HostTwoRunStep.lean`). It would have caught the HostVacuity
  issue.
  * `pinned_cont_g`: on the σ-thread with read coverage, two continuing pre-states land on equal
    `g` and `sideR`, so `not_rowSpecSeg_of_sigma`'s hypothesis cannot be met.
  * `Vacuity2.sideR_sA_ne_sB`: the refuting pair is excluded by the pin.
  * `Vacuity2.twin_witness`: a σ-twin `sC` of `sA` (an extra stack entry, other globals)
    continues to the same `g` and the same pushed 10. It is checked by `decide` and through
    `step_host_two_run`.
* **Bridge to the segment premises.**
  * `HostSigmaBridge.lean`: `rowSpecSegJ_of_twin`, `holdRowSσ_of_cover`.
  * `HostCover.lean`: read coverage from the row's consumed stack and space-3 messages via
    `RelW.live`/`HeapOK` (`hostReadCovered_of_msgs`).
  * `HostEffTwin.lean`: **`rel_twin_post`**, which moves the honest post-relation to the twin.
  * `HostTwinP.lean`, `SegSoundSigmaP.lean`: the page count rides on the thread (`SigP`; `RelW`
    does not pin `pages.size`). The relies are needed only at the row's own gas segment (`RowQS`,
    `exec_rowsJS`, `seg_sound_σP`).
  * `HostCoverAir.lean`: AIR facts for the message shape (`host_sp4`, `host_cons_stk`,
    `host_prod_stk`, `host_pf_lt_np`, `host_prod3_paired`).
  * `HostCodeFetch.lean`: `HostFeeOK`, `HostCodeT`.
  * `HostRowsTimesAir.lean`: times.
  * **`seg_sound_hostIf_air`**: `seg_sound_σ` on the segment AIR, with every HOST-row premise
    discharged except the following, which stay named:
    * **`HostIf` + `HostAnsCov`** — the producer contract (lane B, M6.4).
    * **`HostWritesCovT`** — the AIR gap in §5.5.
    * **`HostProdNodup`** — overlapping request buffers in one call are outside the AIR's domain.
    * **`HostCallsNotLinear`** — a static module fact: the checker does not pin the gas kind of
      call records.

### 5.2 Item 2: one chain statement, entry, pinned `wasm_base_sound_m2` [K]

* **`Cuti.seg_chain_all_mp`** (the default MP AIR) / `seg_chain_all` (base AIR), plus their
  `_csteps` forms on lane E's call machine. Files: `SegChainAll.lean`, `SegSoundAll.lean`,
  `SegExecJH.lean`.
  * One premise per segment (`SegPremAMP`) combines the σ-pinned host premises, the key bus 214
    (no `HostBLinkedL`/`RegCLinked`), and the memory root (no `memIn`/`memOut`).
  * In/out relations `InSA`/`OutSA` = BndC, RegWF, ctx digest, MsgWF, memory root and geometry,
    `InDom`, plus the σ pin.
  * Conclusion: `Sha384Coll` or `foldSegments` reaches `sN` with `OutSA`.
* **Entry** (`SegCallSigma.lean`): `entry_inSA_mp`. The verifier's first-segment checks are the
  **decidable `EntryPub`**: `t`, `S`, `pc = offOf k`, `sb = cid = 0`, `ctx_in` = digest of
  `cutView s0`, `mem_in` = `memRootOf s0`, and the geometry. `EntrySeed` (the `Bnd` seed) stays
  named.
* **Exit, M6.5 shape:** `seg_sound_haltσS`/`_mp` and `call_chain_halt_csteps_mp`. Then
  **`callResult_of_segments_mp`**: from `CSteps q .pre (.ent …)` and the segments, we get
  `Sha384Coll` or `callResult q = afterMethod (entPost r)`, where `r` is the step of the pinned
  last state (`HaltOut`, and `HaltOut.unique` makes it a function of the Wasm part, `g` and σ).
* **`wasm_base_sound_m2σ`** (`M2SoundSigma.lean`). The old theorem is unchanged.

### 5.3 Item 3: host answers ↔ σ-thread ↔ call tape [K][M]

* **Frequency** (`host_freq.py`, `host-freq.json`/`.md`): eligible calls use `input`(48),
  `read_register`(49), `register_len`(6), `storage_write`(58) in 1,927 calls each, and `log_utf8`(45),
  `value_return`(50) in 1,755 calls each. By static imports weighted by calls, all 27,197 calls give
  the same order (26,964 / 24,551 / 20,376), plus `ed25519_verify` in 127 calls.
* **`HostIf`** (`HostIf.lean`): host times `hts` are the active HOST rows. The answer of the call
  of rank `j` is from host side `σc j` to `σc (j+1)` (`HostWit`), with register steps and a cap. The
  thread is `thread hts σc t = σc (rank hts t)`.
  * `sigKeep_of_hostIf_seg`, `thread_in`/`_out`: σ is constant between host rows, and the in/out
    pins hold.
  * `host_msgs_of_thread`: each HOST row's HOSTR/HOSTB/REG-C messages are those of the thread's
    arm run.
* `HostIfCover.lean`, `HostIfCover2.lean`: `holdRowSσ_of_hostIf_cover`, `seg_sound_hostIf'`/`''`.
* **Tape tie** (`HostIfTape.lean`): `cden_of_parts`, and `callResult_of_chainσ`, which gives
  `Sha384Coll` or `callResult q = cden q (.ent … sN …)` with `OutSσ`.
* **Lane B obligations (M6.4)**, stated as `ProducerObl`: per HOST row, `A.ans name σc_j args mem`
  gives HOSTR status/word/`g_after`, HOSTB bytes written, registers and `σc (j+1)`.
* **Answer functions** (`HostAns.lean`), proved equal to the arm on all branches:
  `register_len_ans`, `input_ans`, `read_register_ans`. Not yet done: `storage_write`, `log_utf8`,
  `value_return`, `ed25519_verify`.

### 5.4 Item 4: `memory.grow` segments [K][M]

* **Lean:**
  * GROW: `SegGrowStep.lean` (`SzC` size clause, `segg_size_track`, `step_memGrow_ok`/`_fail`,
    `step_memSize`, `HeapOK.grow`), `SegExecQ.lean` (`exec_rowsJQ`), `SegGrowCode.lean`,
    `SegGrowRow.lean`.
  * GROW2: `M3Ctx.lean` (`m3OpNat`, `ModFacts3`, `M3Ctx` with the M2Ctx API and the M2 shadow
    `toM2`), `SegSpaceG.lean`, `SegGrowFetch.lean`, `SegGrowMemg*.lean`.
  * **`seg_sound_g`** / `seg_sound_g_view` (`SegSoundG.lean`): the cut case, σ form, with
    `nblk_out = 64·|sN.pages|`. All MEMG rows are proved. The non-MEMG action layer is the named
    `SegGLayer`: base-row FETCH under `CodeOK3`, MEMBG pairing, the CUT link on the grow AIR, and
    the per-row fee bound for failed grows.
* **Corpus [M]:**
  * 385 `d3rich` calls execute `memory.grow`; 378 equal the chunk's outcome.
  * 1,315 segments planned, 1,309 built.
  * After FIX214, **1,309/1,309 pass pre-check**, and 372 of the 378 calls are OK. The other 6
    stop at the i32-host generator limit.
  * **215/215 grow segments proved and verified**, plus 25/25 newly passing ones: 1.41–1.81 MB,
    median 53 s prove, 69–167 ms verify, 268.2 bits.
  * Tampers 65/65 rejected. Logs: `logs/m6-grow-*`.

### 5.5 Findings

* **Bus-214 completeness bug (fixed, FIX214) [M][K].**
  * Cause: multi-group host calls (e.g. `storage_write`'s value group) put HOSTB bytes under wire id
    `hid + 256·g`, but HOST offered only `[ts, hid]`. Every segment with such a call failed
    pre-check, including on the default MP AIR.
  * Fix: `Seg.HostBK` gets group bits `hg0`, `hg1` (2 cells/row, 4 degree-2 constraints). `hid`
    holds the base id, and the bus-210 wire id is `hid + 256·hg0 + 512·hg1`.
  * Re-proved: `hostBK_part_stk`, `hostb_act_seg_bit`, `seg_hostBLinkedL`.
  * Re-checked: d3tiny repro, refill (4/4 proved), 1.13 M benchmark, `run_grow.sh`.
  * Tampers: d3tiny 49, refill MP 47 + 54, refill M4 34 + 36, grow 26 + 23 + 17, all rejected.
  * One `storage_write` segment proves: 1,332,045 B, 32 s.
  * Open: a prover can relabel a whole group index inside a segment. Segment soundness reads by
    address, so this matters only once the state side consumes wire ids.
* **Write-coverage AIR gap (COVER, open, needs an AIR change).**
  * Memory writes reach the bus only through REG write rows, which `cWrHid` limits to
    `read_register`.
  * Five hosts write 16 bytes through `setU128H` with no space-3 message: `account_balance`,
    `account_locked_balance`, `attached_deposit`, `validator_stake`, `validator_total_stake`. For
    them `HostIf.ans` has no honest witness.
  * Proposed constraint: HOSTB old-byte column `ob`. With count `act·dir·(1−reg)`, add
    `chRecv 3 (ptr+pos) [ob] mtp`, `chSend 3 (ptr+pos) [bv] ts`, and `timeChk`, the same shape as
    REG writes.
  * None of the five has a dynamic call among the eligible calls, but `d3rich` (`fbc015a8`)
    imports all five (18,621 calls). The gap therefore blocks `d3rich` calls that reach them.
* **Page count is not in `RelW`.** It is now carried on the thread (`SigP`). The grow AIR's size
  clause `SzC` gives it there.
* **Failed `memory.grow` fee** `fee + lin·n` is unbounded per row (`n < 2^27`). It needs an AIR
  bound or a stronger `hstepgas`.

### 5.6 Open after M6

* The producer contract `HostIf` + `HostAnsCov` (lane B's state rows, M6.4, `ProducerObl`).
* The write-coverage AIR change (§5.5).
* `HostProdNodup` and `HostCallsNotLinear` (a checker fact).
* `EntrySeed`.
* Answer functions for the 4 remaining corpus hosts.
* The grow `SegGLayer`, then the memory root with MEMBG/MEMBH, the halting case and the chain step
  for grow segments.
* Lane E side: `preConf q` reaches `.ent p .method (.cont s0) n`. The `EntK.start` entry is still
  to be composed.

## 5b. Next milestone after M6: Wasm segments as aggregation-tree leaves [S]

Requested by the integrator for lane D's aggregation tree (main `0f59988a6`, plan §5.0.1.4).
All costs below are estimates from the M4c/M6 measurements, not new runs.

| requirement | today | work | cost estimate |
|---|---|---|---|
| (1) Parameters and table heights fixed per template, not per call | Heights are chosen per segment: instruction/lookup tables, the SHA-512 chip (2^13 for a 2-step segment up to 2^17 for 2^18 steps), HOSTB/REG-C, MEMB/MPATH by blocks touched | A few templates, e.g. 2^14/2^16/2^18 steps, each with fixed heights from the per-template maximum; dead rows padded with `act = 0` | Cells grow up to the template maximum. For the 2^18 template, ≈28 M cells at today's worst case (`wasmBaseSegAirMP`, 680 compressions). Small segments pay the padding of the smallest template that fits. Proof size is unchanged (same stacked shape). |
| (2) CODE/FUNC (and tape) roots inside the statement/circuit | The verifier checks the CODE/FUNC matrices outside the circuit against the canonical matrix (`CodeIs`/`FuncIs`) | Commit the code and function tables once per contract: a SHA-384 Merkle root over records, as `codeRoot`/`funcRoot` in `WasmBnd`. Per segment, open only the records it FETCHes, with the same batched multiproof as MPATH. Tape root: HOSTR/HOSTB answers bound to the state side's σ (§3, M6.4). | Per segment, ≈ touched records/8 leaf compressions plus multiproof nodes. Hashing the whole code table per segment would be about `codeSize·64 B / 128 B` compressions, which is too much for large contracts. The per-contract root proof is one-off. |
| (3) Proof + vk saved to disk in the stack's format | Proofs are verified in-process | Serialisation through the stack's existing format | Engineering only |

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
