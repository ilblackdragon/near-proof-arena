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
