# E2E lane A (Wasm), 2026-11-03: M1-a, M1-b, M3, M2 corpus coverage, M4 segment cuts

Plan: `docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §5 (owner adopted D-1..D-7 the same day).
Details and logs:
* `research/near-compression/e2e-general/m1/README.md` (section "Update 2026-11-03");
* `research/near-compression/e2e-general/m3/README.md`;
* `research/near-compression/e2e-general/m2/README.md` (second session).

No Lean spec, checker or signed file changed. `make pin-check` ok.

## M1-a: `read_register` writes linear memory

* **AIR.** `wasmBaseIfRegAir` (`wasm-base-lean/WasmBase/RegMem.lean`) is a new AIR value:
  base + HOST' + HOSTO + HOSTT + HOSTB + IF + REG'.
  * **REG' write rows** use STORE's shape on `ptr + pos`.
  * **Bus 211** binds each write group to a successful `read_register` HOST row (`rr = [hid = 49]`,
    is-zero gadget).
* **Two holes found and closed.**
  * A REG read row did not have to consume (`fresh` was free on reads), so register bytes could be
    forged. Now `act·rd·(1−fresh) = 0`.
  * The arity-0 result gap: the public result limbs are now 0 unless returned.
* **T2 `d3tiny.run("hello")`.**
  * CHECK OK; `value_return` on HOSTB is `68656c6c6f`, the chunk's.
  * Proof verifies: 1,474,766 B, 268.2-bit, prove 18.1 s, verify 29 ms, 8 threads.
  * Tamper **136/136 rejected**. The cases cover wrong return bytes, wrong host answers, forged
    register bytes, skipped and orphan writes, `rr` forgery, pointer and time witnesses, and
    `pub.result`.
  * One gap is reported, not counted: a consistent HOST + HOSTO `g_after` change verifies (the
    oracle is free until M6).
* **Lean** (`WasmBase/Main/RegMemLink.lean`, `AxiomsRegMem.lean`; standard axioms, no `sorry`):
  * `writeBytes_facts`;
  * `read_register_run`: the spec's post-state is `writeBytes s4 ptr d`;
  * `heap_read_register`;
  * `regw_write_msgs`: a write row's CH messages;
  * `read_register_rows_heap`: the group's produced messages are the spec post-state's heap entries;
  * `regw_pub_result`;
  * `regw_time_lt`: the algebraic step of `mtp < ts`.
* **Open.** The REG walk and R16 send bound are not yet re-instantiated at the new AIR's index 27.

## M1-b: storage bytes on HOSTB

* Storage key bytes are on HOSTB for `storage_read/write/remove/has_key`.
* `storage_write` also puts its value bytes there, with wire id `hid + 256`.
* Both are request groups with the MEMIO link.
* T2 carries key `74` and value `68656c6c6f`.

## M3: the chunk's own host tape

* **Tape.** `wasmbase-tape` wraps the checker's compiled Wasm entry at link time
  (`-Wl,--wrap` + `tape_shim.c`). The wrapper:
  * returns the real result unchanged;
  * replays each call with the spec's `step` from the checker's own context and trie-backed store;
  * records the host answers.
* **Corpus run.** Over d3c7–d3c10: 19,007 cases, all `accept`, and 27,197 Wasm calls.
  * Replay mismatches: 0.
  * **3,414 / 3,414** calls the AIR covers equal the chunk's outcome when traced with their own
    answers (status, burnt gas, logs, return).
  * This includes **1,755 / 1,755** `d3tiny` calls, and T1 and T2. T1 is the evicted
    `storage_write` path.
* **T1 proof.** T1 with its chunk tape proves (1,476,278 B, verify 50 ms).
* **Coverage.** 23,317 calls are outside `checkModuleIfH` (M2).

## Builds

* `lake build WasmBase wasmbase-tool` is green.
* `build-tape.sh` (`wasmbase-tape`) is green; it builds the needed `spec/lean/v3` Successor
  modules, unchanged.
* The release `nearproof-wasm-base` is green.

## M2 (second session): corpus coverage at `wasmBaseM2Air`

* **Census** (`wasmbase-tool census`): the uncovered calls need wrap/extend, `if` with a result,
  `unreachable`, `ed25519_verify`, and in `d3rich` also `memory.grow`, `abort` (`i32` params) and
  `promise_yield_resume` (`i32` result). No discarding branch, `call_indirect`, bulk memory or
  float occurs in d3c7–d3c10, so those were not built (T3 work).
* **Built.** `checkModuleM2`; `wasmBaseM2Air` = tables 0–26 of `wasmBaseIfRegAir` + REG-C (27,
  register refill) + CONV (28) + UNREACH (29). Instructions the HOST row or the memory model cannot
  carry (`memory.grow`, `memory.size`, `abort`, `promise_yield_resume`) are admitted with opcodes
  no chip can fetch, so a run that executes one is not provable (sound, incomplete).
* **Sweep** (19,007 cases, 27,197 calls, 0 replay mismatches, **0 different**): 21,438 equal +
  4,480 equal-abort = **25,918 / 26,731** method calls; every call of `d3tiny`, `3b1ad423`,
  `e1fe4f9c`, `d3ed`, `d3hostx`; 17,409 / 18,222 of `d3rich`. Remainder 813 (`d3rich.run`):
  `memory.grow` 385, `abort` 120, `promise_yield_resume` 58, stack-budget trap 124, address
  `≥ 2^27` 89, out-of-gas at a Wasm instruction 37.
* **Mutants**: CONV/UNREACH/REG-C, 37 / 37 rejected over three corpus calls (one with a refill, one
  ending in `unreachable`); the full battery at `wasmBaseM2Air` on the refill call, 211 / 211
  (plus the documented HOSTO `g_after` gap, reported not counted).
* **Lean** (`propext`/`Classical.choice`/`Quot.sound` only, no `sorry`): `Main/M2Link.lean`
  (`conv_row_spec`, `step_conv`, `execNum_conv`, `unreach_row`, `regc_clear_cancels`,
  `regc_clear_next`); `Main/RegWalkG.lean`: the REG group walk, `pos < len` and `RegLenAgree` for any
  AIR carrying REG's constraints, instantiated at index 27 of `wasmBaseIfRegAir` and
  `wasmBaseM2Air` (item 2's walk half).
* **Host note.** The shared `zkbuild.slice` sat above its `memory.high` (sibling scopes held
  ~41 GB), which throttled every job in it to near zero (the first sweep under `heavy` stalled for
  40 min). The final builds, sweep and mutants ran in their own `systemd-run --user --scope` with
  `MemoryMax` 16–24 G, `MemorySwapMax=0`, `taskset` 8 CPUs.
* `spec/lean/v3` default `lake build` green; `wasm-base-lean` `lake build WasmBase wasmbase-tool
  wasmbase-tape` green; `make pin-check` ok. No Lean spec, checker or signed file changed.

## Next

* R16 send bound for `wasmBaseIfRegAir`/`wasmBaseM2Air` (then `mtp < ts` and `RegWalkG`'s `hsend`
  are theorems about `Holds`).
* An M2 `Ctx` + row-to-step dispatch (`wasm_base_sound` for M2).
* `d3rich` remainder: `memory.grow` chip, `i32` host tags, stack-budget and out-of-gas abort rows,
  the `2^27` address range.
* Force a clear before every refill (absent-register messages) before M6 binds fill bytes.
* M4 (segment cuts): not started this session.
* M6: replace HOSTO.

## Third session: M4 segment cuts, M2 gaps, coverage

Details: `research/near-compression/e2e-general/m4/README.md`; m2 README sections "Update: R16
send bound", "Update: M2 soundness", "Update: absent-register header", "Update: coverage chips".
Lean work by four sub-lanes (worktree branches), cherry-picked onto the lane branch.

### M4 (priority 1)

* **AIR** `wasmBaseSegAir` (`WasmBase/SegAir.lean`): M2's chips unchanged at their indices, plus
  SEGB (boundary STATE + gas register from public values), CUTI/CUTO (SHA-384 `ctxDigest` of the
  sorted live non-memory channel messages, ids relabelled to depths via the CIDMAP lookup), DROP
  (dead locals of tombstoned activations; RET sends the tombstone), MEMB/MPATH (SHA-384 Merkle
  `memRoot` over 1 KiB blocks, old and new paths, root chain), HOST with the gas register, and the
  native SHA-512 chip v4 (copied from `native/sha384-air4` via M5a's prover) on bus 103.
* **Prover** (`native/wasm-base`: `seg.rs`, `segcmd.rs`, `tracegen::generate_cuts`):
  `segcheck`/`segprove`/`segtamper`. The call is traced once; at each cut the generator snapshots
  the machine, resets every live message's time to the cut and relabels ids to depths.
* **Result [M]:** `segbench(24000)` (1,128,011 steps; stores/loads over 32 blocks, a global, calls
  of depth 2) as 5 segments of 2^18 steps (≈ 2^20 trace rows each), one key, chained by hand:
  1.73–1.75 MB per proof, prove 596–823 s each (8 threads), verify 63–223 ms, 268.2-bit. The corpus
  call `3b1ad423.run` (host calls, register refill) as 4 segments: 1.33–1.35 MB, ~60 s each.
* **Boundary cost [M]:** a written 1 KiB block costs 18 leaf + 32 path compressions (`D = 16`:
  NEAR prepares 1,024 initial pages), ≈ 0.53 M chip cells; 59 % of a 2^18-step segment in the
  benchmark. Levers listed in the README.
* **Tampers [M]:** 54 / 54 rejected on two segments of the refill call (forged public boundary
  fields; CUT/MEMB/MPATH/DROP/SEGB/gas-register cells).
* **Two AIR soundness bugs found by the Lean sub-lanes and fixed:** MEMB's split values (`r16(8192·s5)`
  admits `s5 = 245761`, `memb_split_counterexample`; fixed with a BYTE pair lookup) and CUT's padding
  length limb (`gl_padding_counterexample`; fixed with `r16 gl`). The five benchmark proofs ran
  before the `gl` fix; on the final AIR the benchmark re-pre-checks and chains, the refill call's 4
  segments and the benchmark's last segment re-prove (`m4/recheck.sh`).
* **Lean [K]:** `exec_of_rows_cut`, `cuts_foldSegments`/`cuts_halt`/`cuts_csteps`/`cuts_cden`,
  `RelW.relabel`/`Bnd.relabel` (`SegCut`); MEMB/CUT/DROP lemmas, `cutView`, `cutDigest_binds`
  (`SegRows`); `mpath_block`, `rch_chain` (`SegMpath`); `leaf_link`, MEMB block walk and byte
  messages (`SegMemb`); `seg_hsend_r16` and distinct touched blocks (`SegSend`); `R16Audit`.
  Open: `cutView` = relabelled live list (four `RelW` facts missing), leaf = SHA-384 of the bytes,
  a Lean SHA-512 chip model, the composed segment-soundness theorem, lane E's `wasmD`.

### M2 gaps (priority 2)

* R16 send bound `m2_hsend_r16` (and for IfReg); REG walk and `mtp < ts` unconditional.
* `Ctx` split (`ModFacts`, `M2Ctx.toCtx`); base row lemmas on constraints only and for every `Ctx`;
  `m2_hsend_fetch`; `m2_rowfacts` (every non-HOST instruction row of a `wasmBaseM2Air` trace).
  Open: the STATE/CH bus split over the M2 tables, then `wasm_base_sound_m2`.
* Absent-register header `wasmBaseM2rAir` (RINIT + REG-A): the double fill verifies at
  `wasmBaseM2Air` and is rejected here; 25 / 25 tampers; row lemmas. Open: the bus-level count.

### Coverage (priority 3)

* `wasmBaseM3Air`: i32 host tags (HOST-W), `memory.grow`/`memory.size` (size message MEMG/MSZ,
  grown bytes GINIT), `checkModuleM3`. **555 / 813** M2 remainder calls now equal (0 different),
  25 / 25 tampers. Remainder 258, all pre-existing generator limits: 129 stack-budget traps, 91
  addresses `≥ 2^27`, 38 out-of-gas at an instruction. The full sweep was not rerun (only the
  798 cases holding the remainder).

### Builds

`wasm-base-lean` `lake build WasmBase wasmbase-tool` green (393 jobs; standard axioms, no
`sorry`); prover release build green; `make pin-check` ok; no file under `spec/` changed (checker
sha256 `644495ff…` untouched). Heavy jobs in `systemd-run --user --scope` with `MemoryMax ≤ 24G`,
`taskset` ≤ 8 CPUs; sub-lanes 12 G / 6 CPUs.

### Next

* Compose segment soundness (the `cutView` equality, leaf = SHA-384 of bytes), lane E's `wasmD`.
* Boundary cost levers; segments with `memory.grow`.
* M2 bus split and `wasm_base_sound_m2`; the generator limits; M6 (replace HOSTO).

## Fourth session: M4b

Details: `research/near-compression/e2e-general/m4/README.md` §8. Six Lean/prover sub-lanes in
worktrees (V view, S1 `cutView`, S2 SHA streams, S3 CUTO link, S4 `CutSeg` from the trace, C
boundary cost, M2 `wasm_base_sound_m2`), cherry-picked onto the lane branch. `wasm-base-lean` now
requires `StateM5a` (lane B's `Sha512If` and Merkle lemmas, reused).

* **Item 1 [M]:** tamper battery on the final `wasmBaseSegAir` (after `r16 gl`): 26/26 + 28/28
  rejected, honest verifies (`m4/logs/m4b-segtamper-final-s*.log`).
* **Findings:** `Holds (wasmBaseSegAir …)` unsatisfiable (`seg_holds_false`; the M4 Lean results
  were vacuous) → `HoldsX` + named chip contract `ChipIf`; CUTO filler not forced to zero
  (`cuto_filler_counterexample`) → `Cut.rowWords` gated by `act`. The fixed AIR re-checks the
  benchmark (5 segments, chained), proves the refill call (4 segments) and rejects 54/54 tampers
  (`m4/logs/m4b-fix-*`).
* **Item 2 [K]:** `WasmView.lean`: concrete `wasmD`, `wasmD_binding : Coll wasmD → Sha384Coll`,
  `viewImpl_hwasm`, `reconstruct`, `wasmD_air`. `BndRec` mismatch resolved on our side
  (globals/registers digests = the single ctxDigest); optional proposal `WasmBnd.gasLeft`.
* **Item 3 [K]:** `seg_sound` (cut case, `SegSoundX.lean`) from `HoldsX` + `ChipIf`: `CutSeg` built
  from the trace, `BndC` (register/space clauses, `fns` Nodup, CUTO field bounds) preserved,
  public `ctx_out` = SHA-384 of `cutView X sN`; MEMB leaf = `sha384` of block bytes, MPATH node =
  `sha384 (l ‖ r)`. Named: host relies (M6), `HostBLinked`, `RegCLinked`, `CodeOK`/`FuncOK`,
  `TombDead`, in-boundary `Nodup`. Not yet conjuncts: memory root, CUTI side, halting segments.
* **Item 4 [K]:** `wasm_base_sound_m2` with `m2_hst`/`m2_hch` (`RegCLinked` named).
* **Item 5 [M][K]:** `wasmBaseSegAirMP` (batched Merkle multiproof MPATH, `mp_tree`): 1,610 → 680
  compressions per 2^18-step segment, chip 2^18 → 2^17, 38.86 M → 27.91 M cells, boundary 59 % →
  43 %, peak RSS 19.4 → 17.2 GB; proof size/time unchanged (same stacked shape); 39/39 + 46/46
  tampers rejected, also after the filler fix.
* **Item 6:** `memory.grow` segments not started.
* Builds: `lake build WasmBase wasmbase-tool` green (433 jobs; standard axioms, no `sorry`); prover
  release build green; `make pin-check` ok; nothing under `spec/` changed. Heavy jobs in
  `systemd-run --user --scope` (`MemoryMax ≤ 24G`, ≤ 8 CPUs).

### Next

* `seg_sound`: memory-root conjunct, CUTI side, `TombDead`, halting segments, `InDom` from `BndC`;
  port to `wasmBaseSegAirMP`.
* `memory.grow` segments; generator limits; M6 (replace HOSTO, discharge the host relies).

## Fifth session: M4c

Details: `research/near-compression/e2e-general/m4/README.md` §9; M6 scope
`research/near-compression/e2e-general/m6/README.md`. The lead fixed a shared interface first
(`Main/SegIface.lean`). Nine sub-lanes ran in worktrees and were cherry-picked onto the lane branch:
CORE, CUTI, MEM, MP, NV, GROW, LINK, M6, SIGMA.

* **Finding (M6 sub-lane):** the HOST-row premises (`HoldRowS`, `HostRegRely`, `HostRely.wf`)
  quantify over every `RelW`-related pre-state. `RelW` does not pin the host-side state
  (`relW_sigma` [K]), so these premises are unsatisfiable on any trace with a continuing host call,
  and the segment theorems and `wasm_base_sound_m2` are vacuous there. The fix is σ pinning (SIGMA
  sub-lane, below).
* **Item 1 [K]:**
  * `seg_tombDead`, `seg_inDom`, `seg_sound_halt`/`_any`, `seg_sound_c` (CORE).
  * `cuti_view`, `initS_nodup`, `seg_reentry`, `seg_chain(_csteps)` (CUTI).
  * `seg_membIn`, `seg_mem_frame`, `seg_memRootOut`, `seg_chain_mem` (MEM).
  * Discharge attempts:
    * `HostBLinked.unique` is a theorem.
    * `HostBLinked.linked`/`RegCLinked`: AIR change, item LINK.
    * `CodeOK`/`FuncOK` reduce to the verifier's canonical-matrix check (`CodeIs`/`FuncIs`).
* **Item 2 [K][M] (MP):** generic `HoldsXS` layer (generated copies, `gen/segS`). `seg_sound_mp`,
  `seg_sound_c_mp`, `seg_chain_mp`, `seg_chain_mem_mp` and `seg_chain_k_mp` are proved. MP is the
  default segment AIR (`SEG_AIR`). Refill call: re-check passes and 39/39 tampers are rejected.
* **Item 3 [K][M] (NV):** sound executable `Holds`/`HoldsX`/`ChipIf` checkers plus premise
  checkers.
  * Honest dumps satisfy every trace-level relation the live theorems use.
  * `wasm_base_exec_host_holds` (pre-M2) looks vacuous on host traces.
* **Item 4 [M][K] (GROW):** `wasmBaseSegAirG`.
  * 7-segment grow call chains; 2 segments proved; 49/49 tampers rejected.
  * `memRootOf_memGrow` [K]; `segG_hsend_r16`, `membg_grow_link` [K].
  * `seg_sound` for it is open: the relation needs a size clause.
* **LINK [M][K]:** call-key bus 214 in the segment AIRs.
  * `seg_hostBLinkedL`/`seg_regCLinked` [K]; `seg_sound_k`/`seg_chain_k` (`_mp`).
  * Refill: 4 segments proved; tampers MP 45/45, M4 32/32; benchmark re-checks; grow re-checks;
    non-vacuity rerun.
* **Item 5 (M6) [S][K]:** scope (`m6/README.md`).
  * `hostRely_sp` (space clause, no premises).
  * Host footprint for all 75 + 14 arms (`callHost_hinv`, `inv_auto` tactic).
  * `step_regIds` (`RegWF` kept by every step); `HostRely.wf` ⇐ `HostRegCap`.
* **SIGMA [K]:**
  * Mechanised counterexample (`HostVacuity.lean`: `vacuity_witness`, `not_holdRowS_of_sigma`).
  * σ-pinned statements `seg_sound_σ`/`seg_sound_cσ`/`seg_sound_σ_mp` and `Cuti.seg_chain_σ`. The
    thread is the host side plus the registers (`step_sideG`).
  * That an honest run satisfies `HoldRowSσ` is argued, not proved. It needs the two-run
    `callHost` footprint (M6.2).
* Builds: `lake build WasmBase wasmbase-tool` green (695 jobs; standard axioms, no `sorry`); prover release
  build green; `make pin-check` ok; nothing under `spec/` changed. Heavy jobs ran in
  `systemd-run --user --scope` (Lean ≤ 12 G / 4 CPUs; provers ≤ 24 G under one `flock`).

### Next

* M6: the two-run `callHost` footprint, so that an honest run provably satisfies `HoldRowSσ`
  (`HostIf ⇒ HoldRowSσ ∧ HostRelyσ`).
* The σ form of `wasm_base_sound_m2`; one chain statement with σ + memory + key bus.
* One combined chain statement; the first segment's `h0` from `enter`; `seg_sound` for the grow AIR
  (size clause); the corpus grow calls.
