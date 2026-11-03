# E2E milestone M4: Wasm segment cuts

Plan: `docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §3.1–3.2, §4.2 (row M4), §5. Date 2026-11-03.
Labels: **[M]** measured here, **[K]** kernel-checked Lean (`propext`/`Classical.choice`/`Quot.sound`
only, no `sorry`), **[S]** stated / design only.

## 1. Result

A **1,128,011-step** Wasm call is proved as **5 segments of 2^18 steps** (each segment trace about
2^20 rows in total: 574,656 rows of Wasm and boundary tables + 262,144 SHA-512 chip rows),
chained by hand: each segment proof verifies against its own public boundary, and
`B_out(k) = B_in(k+1)` for every `k` [M]. Forged boundaries are rejected: 54 / 54 tampers (§5). The boundary cost
is measured (§4).

Exit test from the plan: "a 10^6-step call proved as 2^20-row segments chained by hand; a forged
boundary rejected; boundary cost measured" — **met**, see §3–§5 for the exact numbers, and §7 for
what is still open (the Lean statement of segment soundness is in pieces).

## 2. Design (`wasm-base-lean/WasmBase/SegAir.lean`, `wasmBaseSegAir`)

`wasmBaseM2Air`'s table list with: BOUNDARY (0) → `SEGB`, RET (14) → RET + tombstone, DRAIN (18)
→ `DROP`, MEMINIT (19) → `MEMB`, DATA (20) → `MPATH`, HOST' (22) → HOST + gas register, plus
`CUTI` (30), `CUTO` (31) and the native SHA-512 compression chip v4 (`native/sha384-air4`, bus
103). Every other table is unchanged, at the same index. Timestamps are global (`t_in + 1 … t_out`).

| boundary field | public values | tables |
|---|---|---|
| `pc, t, S, sb, cid` (STATE), `halted` (out) | 11–15, 21–25, 8 | `SEGB` sends `[pc_in, t_in+1, S_in, 0, sb_in, cid_in]`, receives the last STATE message |
| gas segment `(S_seg, segb)` (spec `g = segb − R·(S − S_seg)`) | 16–20, 26–30 | channel space 7: `SEGB` produces it at `t_in`, every HOST row consumes it and produces `(S + fee, g_after)`, `SEGB` consumes the last |
| `ctxDigest`: SHA-384 of the sorted list of every live non-memory channel message (operand stack, locals, call records, globals, stack budget, registers) | 31–48, 49–66 | `CUTI` produces the messages at `t_in` from the hashed rows; `CUTO` consumes the live messages and hashes them |
| `memRoot`: SHA-384 Merkle root over 1 KiB blocks, depth `D` (pub 103), `nblk` (pub 104) | 67–84, 85–102 | `MEMB` (9 rows per touched block: 8 × 128 bytes produced at `t_in` and consumed at the end, both hashed, + the padding row), `MPATH` (one row per block and level: old and new path; root chain `RCH` from `memRoot_in` to `memRoot_out`) |

* **Activation ids become depths at every cut.** `cid` (the CALL row's `ts`) is an AIR artefact.
  `CUTO` consumes the call records in increasing `cid` order and gives them depths 1, 2, … (`dep`);
  `CIDMAP` (bus 14) is the lookup `cid ↦ depth`. Locals are hashed in space `16 + depth`, a record's
  caller field likewise, the final STATE's `cid` is published as a depth. The next segment produces
  them with `cid = depth`; later CALLs get `cid = ts > t_in ≥ depth`. So the boundary is a
  function of the spec state and `t`.
* **Dead locals are dropped, not kept.** RET sends a tombstone `[cid]` (bus 12); `DROP` turns it into
  a lookup (bus 13) and consumes locals of tombstoned activations only. Live locals can only be
  kept (they need `CIDMAP` of a live record). The Lean sub-lane found independently that keeping
  dead locals would make the relabelling unsound (`RelW.relabel` needs them gone).
* **Encoding of `ctxDigest`.** A message is 7 fields `< 2^30` (relabelled), each one 64-bit word
  `lo + 2^21·hi + 2^42·mark`, plus a zero word; 2 messages per SHA-512 block; one all-zero filler if
  odd; then the SHA-384 padding block. `CUTO` range-checks the halves and the strict
  `(space, slot)` order; `CUTI` needs no checks (its digest is the previous segment's).
* **Memory words.** A block's bytes enter the chip as big-endian 64-bit words; the limb split
  `[0,21) [21,42) [42,64)` cuts bytes 5 and 2 of each word, with split values checked by R16 and by a
  BYTE pair lookup. The BYTE lookup was added after the Lean sub-lane found that the R16 checks alone
  admit `s5 = 245761` (`P ≡ 1 mod 2^13`), which hashes a different word (`memb_split_counterexample`).
* **Read-only blocks** (`ro = 1`): out-bytes = in-bytes, the out hash and the new path are skipped.

## 3. Commands

```sh
cd research/near-compression/wasm-base-lean && lake build wasmbase-tool
cd ../native/wasm-base && cargo build --release
research/near-compression/e2e-general/m4/run.sh WORK 262144      # inside a memory-capped scope
```

* `gen_bench.py`: the benchmark `segbench(24000)`: `main` loops over `f(i, h)` (depth 1: i64
  stores/loads spread over 32 KiB = 32 blocks, a global update, a call of `g`, depth 2).
* `nearproof-wasm-base segcheck|segprove <airSeg> <airM2> <prep> <steps_per_segment>`: the call is
  traced once (`tracegen::generate_cuts`, which snapshots the machine at each cut and then resets
  every live message's time to the cut and relabels ids), each segment is built (`seg.rs`),
  pre-checked (every constraint, every bus incl. the chip interface), proved with **one verifying
  key**, verified, and its statement checked (public boundary, `code_root`, `func_root`); then the
  chain is checked.
* `segtamper … <segment>`: the tamper battery on one segment (§5).

## 4. Measurements [M]

Main stack (unified SWIRL, BabyBear Ext12, SHA-384 MMCS, 42-B digests, stacked WHIR), 268.2-bit
calculator, 8 threads, `MemoryMax=24G` scope, shared host. Logs: `logs/`.

**`segbench(24000)`, 1,128,011 steps, 2^18 steps per segment** (`n_stack 22`, one key):

| segment | steps | boundary msgs in/out | blocks (ro) | dead locals / tombs | compressions | cells (total) | proof | prove | verify |
|---|---|---|---|---|---|---|---|---|---|
| 0 | 262,144 | 4 / 11 | 32 (0) | 22,308 / 11,154 | 1,610 | 38.86 M | 1,738,471 B | 822.8 s | 63 ms |
| 1 | 262,144 | 11 / 4 | 32 (0) | 22,312 / 11,156 | 1,610 | 38.86 M | 1,737,085 B | 609.0 s | 208 ms |
| 2 | 262,144 | 4 / 9 | 32 (0) | 22,308 / 11,154 | 1,609 | 38.86 M | 1,746,535 B | 596.1 s | 63 ms |
| 3 | 262,144 | 9 / 8 | 32 (0) | 22,312 / 11,156 | 1,611 | 38.86 M | 1,734,061 B | 712.9 s | 65 ms |
| 4 (returns) | 79,435 | 8 / 5 | 32 (0) | 6,760 / 3,380 | 1,609 | 27.39 M | 1,733,109 B | 748.1 s | 223 ms |

Total prove 3,489 s (8 threads, shared host, load from sibling lanes), peak RSS 19.8 GB; one
verifying key (`n_stack 22`), every statement check ok, `B_out(k) = B_in(k+1)` for all k.
Pre-check (every constraint on every row, every bus incl. the chip interface) 0.9–4.2 s per
segment. These five proofs ran on the AIR before the last fix (`r16 gl`, §5); on the final AIR the
whole benchmark re-pre-checks and chains (`logs/final-segcheck-bench.log`), the refill call's 4
segments re-prove (`logs/final-segprove-refill.log`) and the benchmark's last segment re-proves
(1,730,001 B, prove 943.8 s on 6 threads, verify 82 ms; `logs/final-segprove-bench-s4.log`, `recheck.sh`).

Per segment (seg 1, 262,144 steps): instruction + lookup tables 16.02 M cells; boundary tables
1.08 M cells (`MEMB` 286 k, `MPATH` 77 k, `DROP` 721 k (22,312 dead locals + 11,156 tombstones),
`CUTI`/`CUTO` < 2 k); SHA-512 chip 21.76 M cells (1,610 compressions → chip height 2^18).

**Boundary cost model.** At a cut, per touched 1 KiB block: 9 + 9 compressions (in/out leaf
hash) + 2·D path compressions; NEAR prepares every contract with 1,024 initial pages (64 MiB), so
`D = 16` and a written block costs **50 compressions ≈ 0.53 M chip cells**, a read-only block 25.
The small-state stream costs 1 compression per 2 messages per side (here 4–11 messages: 9–11
compressions). For this memory-heavy benchmark the boundary is 59 % of a 2^18-step segment's cells
(22.8 M of 38.9 M); it is fixed per cut, so it halves with 2^19-step segments. Levers, not built:
a smaller tree (depth from the pages actually used), leaf hashing only on write, 4-ary nodes,
word-granular memory messages.

**Corpus call with host calls and a register refill** (`3b1ad423.run`, 96 steps, cut every 30
steps; 4 segments, `n_stack 18`): every segment proves and verifies, 1.34 MB each, prove 51–58 s,
verify 69–132 ms; segment 2 has a read-only block, 2 dead-local drops and 2 tombstones, the last
segment carries 40 boundary messages (registers) [M].

## 5. Tampers [M]

`segtamper` on the refill call, segments 0 (a written block) and 2 (read-only block, drops,
tombstones). Each case is re-proved; it counts as rejected if the prover fails, the verifier fails,
or the statement check (the public boundary the chain requires) fails.

| case (each on segment 0 and segment 2 of the refill call) | rejected by |
|---|---|
| public boundary +1, honest rows: `ctx_out`, `ctx_in` limb | verifier (the CUT digest constraint reads the public value) |
| `mem_out`, `mem_in` limb | prover (RCH bus 16 unbalanced) |
| `pc_out`, `S_out`, `t_out`, `halted`, `cid_in`, `sb_in` | prover (STATE bus 0) |
| `segb_out` limb | prover (gas register, CH space 7) |
| CUTI message value +1 (digest kept) | prover (CH + SHA interface) |
| CUTO hashed value +1; message not consumed (`act = 0`); local relabelled to another depth | prover (CH/R16/IF; row constraints) |
| DROP a local of another activation (`c + 1`); tomb multiplicity +1 (seg 2) | prover (bus 13 / CH) |
| MEMB in-byte, out-byte, out-tp, `blk` +1; read-only flag flipped | prover (CH, BYTE, IF; row constraints) |
| MPATH sibling limb, direction bit, `ri`, `rt` | prover (IF) or verifier |
| SEGB final `cid` +1; HOST gas-register limb +1 | prover (STATE + CIDMAP; CH space 7) |

**Segment 0: 26 / 26 rejected; segment 2: 28 / 28 rejected; 0 accepted** (`logs/segtamper-refill-s*.log`).
The honest segment verifies in both runs. A self-consistent forged in-boundary (rows re-generated
from a forged state) would verify on its own and is rejected by the chain check
`B_out(k) = B_in(k+1)` (the digest differs unless SHA-384 collides).

## 6. Lean [K]

* `WasmBase/SegAir.lean`: the AIR value; `seg_air_len`, `seg_air_same` (the 24 unchanged tables are
  `wasmBaseM2Air`'s at the same indices).
* `WasmBase/Main/SegCut.lean` (sub-lane): **`exec_of_rows_cut`** — rows from an arbitrary related
  boundary state (`Bnd X sg s t S m L`: any frame stack, init messages at `tp ≤ t_in`) to a cut
  (`seg n s0 = .cont sN`, the final live set is exactly the consumed messages) or to a halt
  (`.fin`/`.abort`), host gas segments restarting; chaining `cuts_foldSegments`, `cuts_halt`, and on
  lane E's call machine **`cuts_csteps`** (`CSteps q (.ent p k (.cont s0) n) (.ent p k (.cont sN) …)`)
  and `cuts_cden`; **`RelW.relabel` / `Bnd.relabel`** (live ids → depths, dead locals dropped).
* `WasmBase/Main/SegRows.lean` (sub-lane): MEMB packing (`dataW_eq_wl`, `dataW_inj`, the
  counterexample, `split5_of_r16`/`split2_of_r16`); CUT encoding (`cut_word_inj`, `cut_order`,
  `cut_rec_order`, `cuto_dep` on the trace); DROP (`drop_only_tombstoned`: a dropped local's
  activation sent a tombstone from a taken RET, bus level); the boundary view `cutView`, its
  encoding `cutBytes`/`cutDigest` (SHA-384 of lane E's `Bnd.sha384`), `cutBytes_inj`,
  `cutDigest_binds`, `cutDigest_binds_set`.
* `WasmBase/Main/SegMpath.lean` (sub-lane): `mpath_block` (per block: old root = Merkle fold of the
  old leaf under the siblings, new root of the new leaf, `ro → rt = ri`, `blk = Σ bit·2^l`), `mp_kb`,
  `rch_chain` (bus level: `memIn` → … → `memOut`, `nbt` = #blocks). The SHA-512 compression is a
  hypothesis on the limbs MPATH sends (no Lean model of the native chip).
* `WasmBase/Main/SegMemb.lean` (sub-lane): `leaf_link` (every MPATH bottom row's
  `[blk, ro, old, new]` is a MEMB padding row's, bus 15), `regAt_seg` (the REG walk on segment
  traces), the MEMB block walk (`memb_pos`, `memb_blk_const`), `memb_byte_msg` (each data row
  produces exactly `[3, 1024·blk + 128·k + i, 0, b_i, 0,0,0, t_in]`), `memb_addr_inj`.
* `WasmBase/Main/SegSend.lean` (sub-lane): `seg_hsend_r16` (R16 send bound of `wasmBaseSegAir`
  from `Holds` alone), hence `memb_blk_strict_of_holds` / `memb_blk_distinct_of_holds` (touched
  blocks strictly increasing, distinct).
* `WasmBase/Main/R16Audit.lean` (sub-lane): every scaled range check `r16(2^k·x)` of every AIR
  classified sound (exact / combined / time check / sign split, with lemmas) or not: the CUT
  padding length limb `gl` was not (`gl_padding_counterexample`), fixed by `r16 gl`.

## 7. Open

1. **`cutView` = the relabelled live list** is not proved: `RelW` lacks (a) a register clause
   (space 6 ↔ `Register.view`), (b) a rule for spaces 1, 7–15 (space 7, the gas register, must be
   split off), (c) `X.M.fns` Nodup (caller index), (d) the `< 2^30` field bounds. Then the segment
   soundness statement is `exec_of_rows_cut` + `Bnd.relabel` + `cutDigest_binds` + `rch_chain` +
   `leaf_link` + `memb_blk_distinct_of_holds` + `memb_byte_msg`; what is missing besides `cutView` is
   the leaf = SHA-384 of the block's bytes (via `dataW_eq_wl`, modulo the chip hypothesis) and the
   composition itself.
2. **Lean model of the SHA-512 chip** (the compression hypothesis of `SegMpath`, and of the CUT and
   MEMB streams).
3. **Lane E's `WasmBnd`** has separate frames/globals/registers digests; this AIR has one
   `ctxDigest` for all non-memory channel state, plus `sb`, the gas register and `D`. Proposed to
   lane E: `wasmD` maps a configuration to `(pc, t, S, sb, depth, S_seg, segb, ctxDigest, memRoot,
   D)`; `Coll wasmD` reduces to SHA-384 via `cutDigest_binds` and the Merkle lemmas.
4. Domain conditions of the boundary (enforced by `canon`/`CUTO`): message fields `< 2^30` (register
   ids `< 32`), `nblk ≤ 2^16` (64 MiB), segments of `< 2^29` steps (`t_in + n + 2^30 + 2^16 < P`
   in `exec_of_rows_cut`); raw record slots `< 2^28` come from CALL's range check.
5. Not built: the boundary for host calls in flight (a cut never splits a step, so none is needed),
   the in-circuit outer `bdigest(BndRec)` (the node's job, M8), one key per segment *template* across
   contracts (CODE/FUNC are cached per contract), `memory.grow` (memRoot depth change).

Items 1–3 of this list are addressed in §8 (M4b).

## 8. M4b (2026-11-03, fourth session)

Six sub-lanes (V, S1–S4, C, M2), merged onto lane A's branch. All Lean is [K] (`propext`,
`Classical.choice`, `Quot.sound` only, no `sorry`); `lake build WasmBase wasmbase-tool` green
(433 jobs). Nothing under `spec/` changed. `wasm-base-lean` now requires lane B's `StateM5a`
(its `Sha512If` chip contract and SHA-384 Merkle lemmas are reused, not copied).

### 8.1 Two soundness findings, both fixed

* **`Holds (wasmBaseSegAir …)` is unsatisfiable** (`seg_holds_false`, `Main/SegHoldsX.lean`):
  `Holds` balances bus 103 over the Lean tables only, and the SHA-512 chip that sends on it is
  native. Every M4 theorem stated from `Holds` was vacuous. The segment relation is now `HoldsX`
  (`Holds` without the external bus-103 balance; the chip enters as the named contract `ChipIf`),
  and every segment lemma (SegRows, SegMpath, SegMemb, SegSend and everything below) is stated over
  it.
* **CUTO's odd-stream filler row was not forced to the zero message**
  (`cuto_filler_counterexample`): `ctx_out` could be SHA-384 of prover-chosen filler words, so the
  boundary digest was not a function of the boundary state. **Fix:** `Cut.rowWords` gates the
  message limbs by `act` instead of `kD` (degree unchanged; `cuto_filler_fixed`). Honest traces are
  unchanged; the AIR json and key change.

### 8.2 Tampers and re-validation [M]

| AIR | runs | result | logs |
|---|---|---|---|
| `wasmBaseSegAir` after the `r16 gl` fix (item 1) | tamper battery, refill segments 0 and 2 | **26/26 + 28/28 rejected**, honest verifies | `logs/m4b-segtamper-final-s*.log` |
| + filler fix | bench 5 segments segcheck + chain; refill 4 segments proved (1.33–1.34 MB, 42–59 s, verify 65–99 ms) and chained; tampers | **26/26 + 28/28 rejected** | `logs/m4b-fix-*` |
| `wasmBaseSegAirMP` (§8.4) | bench segprove segs 1, 4; refill 4/4 proved; tampers incl. 17 / 21 new MPATH-MP cases | **39/39 + 46/46 rejected** | `logs/m4b-segprove-*-mp.log`, `logs/m4b-segtamper-refill-mp-s*.log` |
| `wasmBaseSegAirMP` + filler fix | bench 5 + refill 4 segcheck + chain; tampers | **39/39 + 46/46 rejected** | `logs/m4b-mpfix-*` |

### 8.3 Lean: segment soundness as one theorem, and the Wasm view

**`seg_sound`** (`Main/SegSoundX.lean`, cut case). From `HoldsX (wasmBaseSegAir …) pub tr`, the chip
contract `ChipIf compressW` (lane B's `Sha512IfContract` with the spec's `SHA512.compress`, plus the
bus-103 balance including the chip's sends), `X : M2Ctx`, a cut (`halted_out = 0`), and `s0`
related by `BndC` to SEGB's first STATE message and the in-boundary live list `initS` (CUTI ∪ MEMB
∪ SEGB gas register): `t_out = t_in + n`, `seg n s0 = .cont sN` (and `run` continues from `sN`),
`BndC` at the out cut for `finS` (CUTO ∪ MEMB ∪ SEGB ∪ DROP), `cutoList tr = cutView X sN`, and
**the public `ctx_out` limbs are `cutDigest (cutView X sN)`, the SHA-384 of the spec state's
boundary view**, every view entry `MsgWF`. The `CutSeg` (rows, STATE and CH permutations) is built
from the trace (`SegBus.lean`: `seg_hst`, `seg_hch`, `seg_finSplit`; `SegRowsX.lean`:
`seg_rowfacts`).

The four facts the state relation lacked (§7.1) are in **`BndC`** (= `Bnd` + register clause `RegC`
+ space clause `SpC`, layered on `RelW`, `Main/SegView.lean`): registers via
`StepRegs.step_registers` (a non-host step keeps the register file; every `exec` arm) and
`seg_instr_regKeep` (an instruction row is not a host call); spaces as a per-row invariant
(`exec_of_rows_cutQ`); `X.M.fns.Nodup` proved for both checkers (`CtxNodup.lean`); field bounds
from CUTO at the out cut (`cuto_wf`). `cutView_eq`/`cutView_eqL`: the relabelled kept live list is
`cutView X s`. `cuto_link` (`SegLink.lean`): CUTO's hashed list is exactly the depth-relabelled
kept live messages (CIDMAP functional on the ids that occur, `cuto_k4_dep`). `ctx_out_sha`
(`SegCutWords.lean`): the CUTO stream words are `cutWords (cutoList tr)`.

SHA streams (`SegSha*.lean`, the chip as `ChipIf`): `consumer_sound` / `consumer_node_sha384`
(layout-independent); **`memb_leaf_in`/`memb_leaf_out`: a MEMB leaf digest is `sha384` of the
block's 1024 bytes in address order** (`memb_leaf_out` assumes the `bo` columns are bytes: they are
memory-channel values, not range-checked by MEMB); `mpath_block_sha`, `memRoot_in_sha`,
`memRoot_out_sha` (MPATH node = `sha384 (l48 ‖ r48)`); `cut_stream_digest`.

Named premises of `seg_sound`: `CodeOK`/`FuncOK` (commitment bindings), `HostBLinked`,
`RegCLinked`, `SegKeepM2`, `HoldRowS` (HOST-row facts incl. the gas register), `HostRely` (the HOST
rows' register/space clauses: the host-chip contract, M6), `ChipIf` + `CutoHiLimbs` (chip),
`TombDead` (a taken RET's activation id is not live at the cut: an execution fact that needs
`exec_of_rows_cut` to export its per-row trace), `(initS tr pub).Nodup` (the MEMB/SEGB parts are
distinct by construction but unproved; CUTI's part only via the previous segment's view), size
bounds (`hlen`, `htin`, `hfeeN`, `hstepgas`, `hg64`) and the in-boundary relation `h0`. Not yet
conjuncts: the memory root (S2's per-block lemmas and C's `mp_tree` hold separately), `ctx_in =
cutDigest (cutView X s0)` (CUTI side), and the new clauses for halting segments.

**`wasm_base_sound_m2`** (`Main/M2Sound.lean`, item 4): the STATE/CH decomposition of
`wasmBaseM2Air` (`m2_hst`, `m2_hch`, `Main/M2Bus.lean`; REG-C clear pairs cancel, REG-C net traffic
is folded into its host call under the named `RegCLinked`) composed with `m2_rowfacts` and
`exec_of_rows_seg`: `run … s0 = .fin sN` / `.abort sN e` with the gas equation, from `Holds` of that
AIR alone. Named: `CodeOK`/`FuncOK`, `HostBLinked`, `RegCLinked`, `HoldRowM2`, `SegKeepM2`, boundary.

**The Wasm component of lane E's `ViewImpl`** (`Main/WasmView.lean`, item 2): a concrete
`wasmD : WmV → Option WasmBnd`; **`wasmD_binding : Coll (wasmD P) → Sha384Coll`**; `viewImpl_hwasm`
(exactly the `hwasm` premise of `viewImpl_binding_bad`); `wasmD_air` (on the AIR branch
`framesDigest = (cutDigest (cutView X s)).take 42`, `memRoot = (memRootOf s).take 42`);
`wasmBnd_ok` (lane E's `WF`). The core is `reconstruct`: `InDom X s`, `InDom X s'`, equal
`cutView`, equal top pc/base and register-id order give equal stack, frames, globals and registers
(`off_decode` from the checker's `layoutOk`); `memRoot_binding`/`pages_eq` use lane B's
`merkle_binding`.

| `WasmBnd` field | value on the AIR branch (fallback: constants, the full `(q, cc)` in the remainder) |
|---|---|
| `pc`, `sp` | `X.offOf (X.kOf f.fn) + f.pc` (the AIR's global pc), `f.base` (the AIR's `sb`) |
| `stackRem`, `fuel`, `memPages` | `s.stackRem`, `n`, `s.pages.size` |
| `framesDigest` | `bdigest (cutBytes (cutView X s))`: the AIR's `ctxDigest`, 42 bytes |
| `globalsDigest`, `registersDigest` | `= framesDigest` (**derived**: one ctxDigest covers stack, locals, records, globals, budget, registers) |
| `memRoot` | the SHA-384 Merkle root over 1 KiB blocks, exactly `seg.rs`'s tree, 42 bytes |
| `vmCtxDigest` | `bdigest (encRest (q, p, k, s with the viewed parts blanked))` |
| `promisesDigest` | `bdigest []` (promises are in the remainder) |
| `codeRoot`, `funcRoot` | params of `(q, p)` |

Params obligations: `ctxOf`, `codeRootOf`/`funcRootOf` (42 B), `encRest` injective (lane E's
encoders). `InDom`: a running frame, an `MsgWF` view, `FrameOK` frames, numeric stack and globals,
`PagesOK`, distinct register ids with data `< 2^24`, 64-bit counters.

**The `BndRec` mismatch is resolved on lane A's side: no `BndRec` change is needed for binding.**
The separate frames/globals/registers digests are instantiated as the single ctxDigest; `t`, `S`,
the gas segment, `D`, `nblk` and `halted` are AIR-internal or derived. **Proposed to lane E
(optional, for M8's in-circuit boundary):** add `gasLeft : Nat` (u64, `s.gas.g`) to `WasmBnd`.
Today `s.gas` sits in the `vmCtxDigest` remainder, which a segment would then have to recompute
(the AIR has `g = segb − R·(S − S_seg)`). Also for lane E/M6: the remainder carries the register-id
order (the view is a set), so a segment that creates a register changes `vmCtxDigest`; either the
AIR adds a digest of the id sequence, or the spec canonicalises the order. Register ids `≥ 64`
(allowed by the spec; `MsgWF` needs `rid·2^24 + i + 1 < 2^30`) fall to the fallback branch: still
binding, but not AIR-connected.

### 8.4 Boundary cost: a batched Merkle multiproof [M]

`wasmBaseSegAirMP` (`WasmBase/SegAirMP.lean`) is `wasmBaseSegAir` with table 20 replaced
(`segMP_same`): MPATH has one row per **touched tree node** (old and new digests, a
touched/untouched flag per child; an untouched sibling is one witness for both trees; node bus 17;
the root talks to SEGB over RCH as before), so shared upper levels are hashed once. Exported by
`airSegMP`; the prover picks the variant from the AIR json. Lean: `mp_tree` (`Main/SegMP.lean`):
`memIn`/`memOut` are one partial tree `PTree` (leaf/stub/node) evaluated with the old/new leaf
digests; its leaves are exactly the bus-15 leaf messages, distinct, in `[0, 2^D)`; `pos_unique`
(one row per node), `root_unique`. The node hash is a hypothesis as in `SegMpath`;
`consumer_node_sha384` instantiates it.

| `segbench`, 2^18-step segment 1 | M4 (same run conditions) | multiproof |
|---|---|---|
| compressions | 1,610 (576 leaf + 1,024 path + 10) | **680** (576 leaf + 94 node + 10) |
| SHA-512 chip | 2^18 rows, 21.76 M cells | **2^17 rows, 10.88 M cells** |
| total cells | 38.86 M | **27.91 M (−28 %)** |
| boundary share (boundary tables + chip) | 59 % | **43 %** |
| proof / prove / verify / peak RSS | 1,733,431 B / 599 s / 61 ms / 19.4 GB | 1,733,175 B / 586 s / 81 ms / **17.2 GB** |

Proof size and prove time do not move on the current backend: the stacked-WHIR shape
(`n_stack 22`, `w_stack 8`) has room for about 134 M cells either way, and the next smaller shape
needs about 21 M cells or fewer. The remaining 576 leaf compressions (in and out per touched block)
already exceed 512, so the chip cannot drop below 2^17 rows without changing what `memRoot` commits
to. The other listed levers are worse: 4-ary nodes (192 B + padding = 2 compressions per level, half
the levels: no gain), a smaller tree (changes the commitment), word-granular messages (rows, not
compressions). `wasmBaseSegAir` stays the AIR of `seg_sound`; porting the theorem to
`wasmBaseSegAirMP` means using `mp_tree` instead of `rch_chain` + `mpath_block` (every other table
is equal).

### 8.5 Open

1. `seg_sound` premises: `TombDead`, `initS` Nodup (the MEMB/SEGB part), the CUTI side
   (`ctx_in = cutDigest (cutView X s0)`), the memory-root conjunct (compose `memb_leaf_*` with
   `mp_tree`/`rch_chain`, plus a collision-resistance comparison against the full memory tree),
   halting segments, and `InDom X sN` from `BndC` (so `wasmD_air` applies and the public boundary is
   literally `wasmD`'s). The host-side premises are M6.
2. Port `seg_sound` to `wasmBaseSegAirMP`.
3. Segments containing `memory.grow` (item 6): not started (`D`/`nblk` change; `wasmBaseM3Air`'s
   MEMG/MSZ/GINIT chips are not in the segment AIR).
4. `WasmBnd.gasLeft` and the register-id order (§8.3), for lane E.

Status of these items after M4c: §9.

## 9. M4c (2026-11-03, fifth session)

Eight Lean/prover sub-lanes in worktrees (CORE, CUTI, MEM, MP, NV, GROW, LINK, M6) plus a
follow-up (SIGMA), cherry-picked onto the lane branch. The shared interface was fixed up front:
`WasmBase/Main/SegIface.lean` (`PubDigIs`, `MemGeom`, `MembIn`, `MemRootIn`, `MemRootOut`).

### 9.1 Findings

* **The HOST-row premises are unsatisfiable on any trace with a continuing host call.**
  `RelW` constrains a state only through its Wasm-visible part and `gas.g` (`relW_of_vis`,
  `relW_sigma`, `Main/HostFoot.lean` [K]). `HoldRowS` (via `RowSpecSeg`), `HostRegRely` and
  `HostRely.wf` quantify over *every* related pre-state, but `callHost` sets `g := gas.remaining`
  and arms read `ctx` (`block_index`, `input`), none of which the relation pins, while the row's
  `g_after` and messages are fixed. So `seg_sound*`, `seg_chain*` and `wasm_base_sound_m2` hold
  vacuously for segments that contain a continuing host call. Host-free segments are unaffected.
  The mechanised counterexample and the σ-pinned restatement are §9.6 item 1. The non-vacuity checker (§9.5) cannot see this: these premises
  mention the spec state, not the trace.
* **`wasm_base_exec_host_holds` (pre-M2, `Main/SoundHost.lean`) looks vacuous on host traces**
  [M]: it assumes `Holds` of both `wasmBaseHostAir` and `wasmBaseAir` for one trace, and on the two
  host test programs the base relation fails (buses 0–4, the HOST rows' traffic). It is superseded
  by `wasm_base_sound_m2` and not used downstream.
* **`HostBLinked.linked` / `RegCLinked` were not derivable** from `HoldsX`: no bus carries a
  HOSTB/REG-C row's `(ts, hid)` to HOST, so a foreign-key HOSTB group satisfies everything. Fixed by
  an AIR change (§9.4).
* MEMB at index 19 cannot describe memory above 64 MiB (`r16 blk` checks), so honest traces after a
  grow need `MEMBH` (§9.3). This is a completeness limit, not a soundness bug.

### 9.2 Segment soundness [K]

All standard axioms, no `sorry`. Statements are for `wasmBaseSegAir` and, via the `HoldsXS` layer,
for `wasmBaseSegAirMP`. `HoldsXS` (`Main/SegHoldsS.lean`) is `HoldsX` without table 20 and buses
15/16/17/103; `SegSha.ChipIfS` is the matching chip contract. `wasmBaseSegAirMP` is now the
**default segment AIR** (`run.sh`/`recheck.sh`: `SEG_AIR=${SEG_AIR:-airSegMP}`). The `HoldsXS`
copies of the `seg_sound` chain (`Main/SegS/*`, about 150 declarations `foo` → `fooS`) are
generated by `gen/segS/gen.py` and `gen_mp.py`; regenerate them after editing an original.

| theorem | file | what |
|---|---|---|
| `seg_tombDead` | `SegTomb` (+ `SegRowRel.exec_rows_rel`) | `TombDead` discharged: a space-4 slot is produced at most once (the in-boundary caller chain, or the CALL row at that time), the taken RET consumes it, CH balance |
| `seg_inDom`, `seg_wasmD` | `SegDom` | `InDom X sN` from `Bnd` + `RegWF` + view `MsgWF` + page bound (from `MemGeom`); so `wasmD_air` applies at the out-boundary |
| `seg_sound_halt`, `seg_sound_any` | `SegHalt`, `SegSoundC` | halting segments (`halted_out = 1/2`): `.fin sN` (results = CUTO's space-0 rows) or `.abort`, with the gas equation |
| `hostBLinked_of` | `SegLinkage` | `HostBLinked.unique` from the STATE chain |
| `seg_sound_c` (`_mp`) | `SegSoundC`, `SegSoundCMP` | `seg_sound` without `TombDead`, `HostBLinked → .linked`; adds `RegWF sN` and `MemGeom → InDom` |
| `cuti_stream`, `cuti_view` | `SegCuti` | CUTI's productions decode from the hashed words (`decF w = (w mod 2^21 + 2^16·(w/2^21 mod 2^21)) mod P`); `ctx_in = cutDigest L` ⇒ CUTI part `= L.map (ofFields · t_in)` or `Sha384Coll` |
| `initS_nodup` | `SegCuti` | in-boundary distinctness (view, MEMB via `memb_complete`, SEGB; disjoint spaces) |
| `RelW.ofView`, `seg_reentry`, `seg_cid_out` | `SegReentry` | the next segment's `h0` from the previous out-`BndC` (retimed view, new touched set, gas register); `cid_out` = depth |
| `seg_membIn` (`_mp`) | `SegMemRoot`, `SegMemRootMP` | `MemGeom ∧ MemRootIn pub s0 ⇒ MembIn ∨ Sha384Coll` (byte-level Merkle path binding; MP via `mp_tree` + a partially-injective `batch_update_sound`) |
| `seg_mem_frame` (`_mp`) | `SegMemFrame`, `SegMemFrameMP` | untouched bytes and the page count are unchanged across the segment (byte frame by re-running with the byte added to both boundary blocks; page count per row, HOST rows by `HostPagesRely`) |
| `seg_memRootOut`, `seg_mem_sound` (`_mp`) | `SegMemRoot`, `SegMemRootMP` | `(MemRootOut pub sN ∧ MemGeom pub sN) ∨ Sha384Coll` |
| `seg_hostBLinkedL`, `seg_regCLinked` | `SegKey` | from `HoldsXS` via bus 214 (§9.4) |
| `seg_sound_k`, `seg_sound_any_k` (`_mp`) | `SegSoundK` | `seg_sound_c` without `HostBLinked`/`RegCLinked` |
| `chain_abs`, `seg_chain`, `seg_chain_csteps` (`_mp`) | `SegChain`, `SegChainMP` | consecutive segments linked by publics (pc/t/S/sb/cid, gas segment, ctx and mem limbs) ⇒ `Sha384Coll` or `CSteps q (.ent p k (.cont s0) n) (.ent p k (.cont sN) (n − Σ len))` with the last out-relation |
| `seg_chain_mem` (`_mp`) | `SegChainMem`, `SegChainMemMP` | the chain with the memory interface discharged (`LinkPubM` adds equal `pubDepth`/`pubNblk`) |
| `seg_chain_k` (`_mp`) | `SegSoundK` | the chain without `HostBLinked`/`RegCLinked` |

Named premises left in the chain:
* `ChipIf` (+ `CutoHiLimbs`).
* `CodeOK`/`FuncOK`. These reduce to `CodeIs`/`FuncIs` (the cached matrix is canonical), which is
  what the verifier's `check_code_root` checks.
* `SegKeepM2`, and the host relies `HoldRowS`/`HostRely`/`HostPagesRely` (M6; see §9.1).
* Size bounds, `hstepgas`/`hg64`, and `Dn pub ≤ 30` (MP only).
* For the **first segment only**: `h0`, `RegWF`, `MemRootIn`, `MemGeom` and
  `ctx_in = cutDigest (cutView X s0)`.

Changes to the host relies:
* `HostRely.sp` is now a theorem (`hostRely_sp`, `Main/HostSpace.lean`).
* `HostRely.wf` reduces to `HostRegCap` (register length `< 2^24`), via `host_rowQ_regWF` and
  `step_regIds`.
* The host footprint (`Main/HostFoot.lean`, `HostArms.lean`) is proved for all 75 `hostCall` arms
  and 14 curve arms (`callHost_hinv`: frames, globals, tables, stack budget and page count
  unchanged; register ids stay distinct).

`seg_chain_mem` and `seg_chain_k` discharge different premises (memory vs. linking) and are not yet
one statement; composing them is mechanical.

### 9.3 `memory.grow` segments (`wasmBaseSegAirG`, `WasmBase/SegAirG.lean`) [M][K]

**Depth.** NEAR has 1024 initial pages and a 2048-page maximum, so the tree depth changes at most
once per call, 16 → 17 (`memDepth_pages`).

**Root.** Padding leaves are already `zleaf`, so a grow that keeps the depth leaves `memRootOf`
unchanged, and the first grow past 1024 pages makes it `nodeH root Z_16` (`memRootOf_memGrow`,
`Main/SegGrowMerkle.lean`). **The `memRoot`/`wasmD` interface is unchanged.**

**AIR.** `wasmBaseSegAirMP` plus four tables:
* MEMG (32): M3's table.
* SEGG (33): the size message `[8,0,0,pages,…]` across the cut, and the depth-17 root on a lift
  (1 compression).
* MEMBG (34): blocks grown in the segment. Their bytes are produced as zero at the grow and only the
  final bytes are hashed (9 compressions).
* MEMBH (35): MEMB for blocks above 64 MiB.

There are 108 public values: 103 is `D_out`, 104 `min(nblk_in, 2^16)`, 105/106 `nblk_in/out`, 107
`D_in`.

**Tests** (`gen_grow.py`, `run_grow.sh`): `growbench(20)` is a 3,144-step call cut every 500 steps.
* All 7 segments pre-check and chain.
* Segment 1 (1024 → 1025 pages, the depth lift) and segment 4 (1025 → 1027, `memory.size`, a
  failing grow) prove: ≈1.44 MB, 58 s, verify 74 ms.
* Tampers: 26/26 and 23/23 rejected (`logs/m4c-grow-*`).

**Lean.** `segG_msgs`/`segG_state`, the SEGG/MEMBG row lemmas, `segG_hsend_r16`, and
`membg_grow_link` (grown blocks belong to a successful grow row).

**Open.**
* `seg_sound` for this AIR needs a size clause in the relation: `RelW` has none for the space-8
  size message, and `exec_of_rows_cutQ` must hand its invariant to the row spec.
* It also needs a G-specific `HoldsXS` layer, because the new tables use STATE/CH.
* The corpus `d3rich` grow calls were not run.

### 9.4 Call-key bus 214 (`HostBLinked`/`RegCLinked`) [M][K]

**AIR** (segment AIRs only; M2 unchanged):
* HOST gets a column `nk` with `(1 − act)·nk = 0`, and offers `[ts, hid]` on bus 214 with
  multiplicity `nk`.
* The segment copies `HostBK`/`RegCK` of HOSTB/REG-C look their `(ts, hid)` up with count `act`.
* Degree is unchanged. Prover: `seg::fill_hkey`.

**Runs** (`logs/m4c-link-*`):
* Refill call: `segcheck` passes on both AIRs; all 4 segments `segprove`d and chained.
* `segtamper` on segment 0: MP 45/45 and M4 32/32 rejected. The 6 new cases include the
  foreign-key HOSTB/REG-C group of §9.1 and `nk ± 1`.
* The 1.13 M-step benchmark re-checks (5 segments chained), the grow test re-checks, and the
  non-vacuity script passes again.

### 9.5 Non-vacuity [K][M]

**Checkers.** `WasmBase/Check/HoldsCheck.lean` has a concrete trace format and Boolean checkers
with kernel-proved soundness:
* `checkHolds_sound` and `checkHoldsX_sound`.
* `checkSeg_sound` (→ `HoldsX ∧ ChipIf compressW`): the chip's bus-103 messages are recomputed with
  the Lean `compressW`.
* The balance check is a `mergeSort` plus one scan.

Premise checkers (`PremCheck.lean`): `CutoHiLimbs`, `HostBLinked`, `RegCLinked`, `TombDead`,
`initS` Nodup, `hst0`, `hlen`, `htin`, and M2's init premises. The prover writes the dumps
(`segdump`, `dump`), `wasmbase-tool holds` runs the checks, and `nonvacuity.sh` drives both.

**Satisfied by honest traces** (`logs/m4c-nonvacuity.log`, `m4c-link-nonvacuity.log`):
* `HoldsX ∧ ChipIf` of `wasmBaseSegAir` and `wasmBaseSegAirMP` (refill call, 4 segments).
* `Holds` of `wasmBaseM2Air`/`M2rAir`/`M3Air` (used by `wasm_base_sound_m2`).
* `Holds` of the base/host/reg/hash/if AIRs (test programs).
* `Holds (seg…)` fails only on bus 103, as `seg_holds_false` predicts.

**Not covered:** premises that mention the module or a spec state (`CodeOK`, `HoldRowS`,
`HostRely`, `h0`, …) are not trace-decidable. The §9.1 finding is of that kind.

### 9.6 Open

1. **Host-row premises (§9.1): restated; honest satisfiability open.**
   * `HostVacuity.lean` mechanises the counterexample [K]. `vacuity_witness` (by `decide`) is
     `call 0` to `block_index` from two related states that differ in `gas.burnt` and
     `ctx.blockHeight`; `not_holdRowS_of_sigma` then refutes `HoldRowS`.
   * `SegSigma.lean` restricts the row premises to pre-states on a ghost thread `sideR s = σ t`.
     `sideR` is the host side with `gas.g` blanked, **plus the register file**, which `RelW` does
     not see either. A non-host step keeps it (`step_sideG`). The induction is one copied
     `exec_rowsJ`.
   * **`seg_sound_σ`, `seg_sound_cσ`, `seg_sound_σ_mp`, `Cuti.seg_chain_σ`/`seg_chain_csteps_σ`**
     [K] take `HoldRowSσ`/`HostRelyσ`, `SigKeep` and the in-boundary pin, and conclude
     `sideR sN = σ (t_out+1)`.
   * Open: that an honest run satisfies `HoldRowSσ`/`HostRelyσ.reg`. This is argued in the header
     of `SegSoundSigma.lean`; proving it needs the two-run footprint of `callHost`, i.e. M6.2.
   * Also open: the σ form of `wasm_base_sound_m2`, and merging σ with
     `seg_chain_mem`/`seg_chain_k`.
2. One combined chain statement (memory + key bus + MP), and the first segment's `h0` from the
   entry state after `enter`.
3. `seg_sound` for `wasmBaseSegAirG` (size clause), and the corpus grow calls.
4. `CodeIs`/`FuncIs` as verifier facts (cached-commitment binding), and `HostRegCap` vs. the spec's
   100 MiB registers (the AIR caps registers at 2^16 bytes, a completeness limit).
5. `WasmBnd.gasLeft` and the register-id order, for lane E (unchanged from §8.5).
