# Lane A milestone A-T1: T1's Wasm call end to end

Plan: `docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §4.2 (M10), tracker `docs/zk-formal/E2E-T1-CRITICAL-PATH.md`.
Labels: **[M]** measured, **[K]** kernel-checked Lean (standard axioms, no `sorry`), **[S]** stated / design.

T1 = `/data/illia/nearproof-deps/corpora/d3c8/d3/02-h10196-s3`: one FunctionCall to `d3tiny`
(code `8152bed2…`, 345 B), method `run`, input `again`, 26 Wasm steps, six host calls:
`input`, `register_len`, `read_register`, `storage_write` (existing key), `log_utf8`, `value_return`.

**Update 2026-11-25 (A-T2, §9).**
* The template now pins tight heights, so T1's two leaves give one lane D leaf program.
* PREP is stopped at a statement change.
* Finding: `WasmViewParams` is uninhabited, so §6's theorems are vacuous until the remainder
  encoder is restated (§9.2).

## 0. T1's call segments pre-check and prove at lane A's head [M] (2026-11-21)

Lane I reported that T1's only call could not be cut into segments on `wasmBaseSegAirMP` at any cut
size: the `storage_write` value group went on HOSTB under wire id `hid + 256 = 314`, and the HOST
row offers its bus-214 call key with `hid = 58` only. This is the bus-214 multi-group bug that
lane A's M6 fix FIX214 (`m6/README.md` §5.5) removed: `HOSTB.hid` is the base id, the group index
is the bits `hg0, hg1`, and the bus-210 wire id is `hid + 256·hg0 + 512·hg1`. Lane I's run used a
base or a `wasmbase-tool` / prover binary from before FIX214.

At main `7acdc7b82` (includes FIX214), with a fresh `wasmbase-tool` and a fresh release prover:

* `segcheck` at every cut size `K = 1 … 26`: **26/26 pass**. Every segment pre-checks (every
  constraint on every row, every bus balanced including bus 214 and the SHA-512 chip interface),
  and the boundaries chain (`logs/t1-segcheck-k1-26.txt`).
* `segprove` at `K = 8` (4 segments): 1,320,569–1,339,059 B, prove 15.6–30.0 s, verify 46–55 ms,
  statement ok (boundary public values, `code_root`, `func_root`), peak RSS ≈ 1.3 GB
  (`logs/t1-segprove-k8.txt`).
* `segprove` at `K = 26` (1 segment): 1,332,633 B, 25.5 s, verify 49 ms (`logs/t1-segprove-k26.txt`).
* Lane I's driver `t1/run_t1.sh` (`PROVE=1`, `STEPS=13`) with these binaries
  (`WASMBASE_TOOL`, `WB_PROVER`): "Wasm segments (wasmBaseSegAirMP) **pass** — 2 seg, precheck 2,
  chained True"; whole call proved and verified (`logs/t1-harness-k13.txt`).

Reproduce: `sweep.sh`, `harness.sh` (paths in `/data/illia/nearproof-deps/e2e-laneA/at1/env.sh`).
**Rebuild both binaries from the current tree**: the prover (`native/wasm-base`, `cargo build
--release`) and `lake build wasmbase-tool`. The AIR JSON comes from the Lean tool, so a stale tool
exports the pre-FIX214 HOSTB (no `hg0`/`hg1`) and reproduces exactly the reported failure.

## 1. Item 1: the write-coverage AIR gap closed (HOSTB write pair) [M] (Lean side: §1.4)

### 1.1 The gap, demonstrated on a proof [M]

`u128kat.wat` fills memory 96..175 with `0xAB`, calls `account_balance(96)`,
`attached_deposit(112)`, `account_locked_balance(128)` and `validator_total_stake(144)` (each writes 16
bytes through `setU128H`), then loads the written bytes and returns their sum (the spec returns 0:
the harness context's values are 0). 151 steps, cut every 20 steps: 8 segments.

* **Old AIR** (`wasmBaseSegAirMP` at main): all 8 segments pre-check and chain
  (`logs/u128-segcheck-old-air.txt`). The tracer has no way to move the 16 bytes into memory, so
  segment 6 (the four host calls) has its memory block **read-only**: the proved out-memory-root
  omits the writes, and the later loads read `0xAB`. The AIR accepts a run whose memory and result
  differ from the spec's. This is the soundness gap of m6/README §5.5, now shown end to end.
* **New AIR**: segment 6's block is written (`read-only 0`), and the loads see the host's bytes.

### 1.2 The change

`Seg.HostBK` (the HOSTB table of every segment AIR) gets column `ob` (index 16, after `hg0`, `hg1`)
and, with count `wcnt = act·dir·(1−reg)` (a response byte that fills no register),
`chRecv 3 (ptr+pos) 0 [ob,0,0,0] mtp`, `chSend 3 (ptr+pos) 0 [byte,0,0,0] ts` and
`timeChk ts mtp hp` — the STORE shape of REG's `read_register` write rows (`RegW.newInters`). `mtp` and
`hp` are shared with the request rows (disjoint by `dir`). The Lean definition is sub-lane WCOV's
(§1.4). Before it landed, `patch_air_json.py` applied the change to the exported JSON
(`AIR_PATCH=1`). After WCOV's commit, `wasmbase-tool airSegMP 0 0` exports a JSON **equal** to the
patched one (all tables; HOSTB: same 17 columns, same 20 interactions), so every measurement below
holds for the Lean AIR as is.

Tooling:
* `wasmbase-tool prep*` (`ToolCore.lean`): every host event carries `wr` = `[ptr, 16 bytes]` for
  the `setU128H` hosts (ids 37, 38, 39, 43, 44), read off the spec's own post-state.
* Tracer (`tracegen.rs`): when HOSTB has `ob`, one response group of 16 write rows per `wr` entry,
  each consuming the live byte at its producer time and producing the new byte at `ts`. `segments()`
  gives the M2 full-run HOSTB an `ob` witness column (no M2 constraint reads it).

### 1.3 Results [M]

* `u128kat`: **8/8 segments pre-check, chain, prove and verify** (1.32–1.33 MB, 37–40 s,
  `logs/u128-segprove.txt`).
* Tamper battery on segment 6 (the write segment): **54/54 rejected** (`logs/u128-segtamper-s6.txt`),
  including 7 new write-pair cases: written byte, old byte `ob`, `mtp`, `ptrLo`, `pos` changed; a
  write row relabelled as a read; the whole write group dropped with HOST's key multiplicity
  adjusted (the old-gap shape). Every case is recounted (BYTE/RANGE16 multiplicities).
* T1 at the new AIR: unchanged behaviour (no write rows); its template leaves (§3) use the new AIR.

### 1.4 Lean (sub-lane WCOV) [K]

All Lean below is in `wasm-base-lean/WasmBase/`. `lake build WasmBase wasmbase-tool` is green (732 jobs); the
axioms are standard; there is no `sorry`.

* **The AIR** (`SegAir.lean`, `Seg.HostBK`): 17 columns (`ob` = 16); 20 interactions
  (`wireInters` 0–14, `keySend` 15, `writeInters` 16–19); constraints unchanged.
* **Re-proved for the new table:**
  * `pairSp_hostbk` / `pairSp_hostbw`;
  * the HOST-row space, stack and time lemmas (`host_prod/cons_space`, `host_prod3_paired`,
    `host_cons/prod_stk`, `host_prod_times`, `host_cons_times`);
  * the CH-balance assembly (`seg_ch_assemble`, `seg_hch`/`seg_hchS`, same statements). The
    write rows are grouped to their call through bus 214 (`SegKeyBase.lean`:
    `hostb_key_linked`, `seg_hostbW_partition`); no new premise.
* **Changed statements:**
  * `HostBK.inters_filter` needs `b ≠ busStk`, `b ≠ busR16`.
  * `hostBK_part_stk` is now a permutation: HostB's traffic plus the write table `HostBW`.
  * `prodCHS`/`consCHS` now include the call's write pairs.
* **`HostWritesCovT` is derived, not assumed** (`Main/HostWriteCov.lean`).
  * `hostWritesCovT_of`: `HoldsX` + `HostIf` + `HostAnsCovW` + `HostCodeT` ⇒ `HostWritesCovT`.
  * **`seg_sound_hostIf_airW`**: `seg_sound_hostIf_air` with no `HostWritesCovT` premise.
  * The producer contract `HostAnsCovW` = `HostAnsCov` + `HostNoTouch`, at the honest witness:
    an unconsumed byte, set to any value, is left alone by the call.
  * Why a clause is needed: a byte rewritten with its own value is invisible on one twin and
    visible on another, so values alone cannot exclude a write to an unconsumed address.
  * Honest runs satisfy it: only `read_register` (REG write rows) and the five `setU128H` arms (the
    new rows) call `writeMemH`. Lane B checks it from `ProducerObl.spec`/`.resp`; that link is not
    formalised yet.
* **Non-vacuity** (`Main/HostWriteCovCheck.lean`):
  * `decide +kernel` on a 16-byte `attached_deposit` group: the write pairs consume a message at
    every address 100–115 and produce the new bytes at `ts`; the old HostB produces nothing.
  * `hostNoTouch_attached_deposit`: the clause holds at an honest witness, for any state with
    `PagesOK`.
* **Failed `memory.grow` fee (analysis, not changed).**
  * The spec charges `n·lin + c` before the grow, so a continuing failed grow has
    `amt ≤ g < 2^64`, and the per-row bound `mf = maxFee + maxLin·2^27` is honest.
  * But `hfee : S_in + (rows+1)(mf+1) < P` then allows only about 15 rows: a vacuity risk for grow
    segments.
  * Fix (open): bound the segment by the sum of the actual per-row fees, or add an AIR range check
    `Lmax − lin·n` with `Lmax` public. Not needed for T1, which does no grow.

## 2. Item 2: answer functions for T1's hosts (sub-lane ANS) [K]

The files are `Main/HostAns2.lean`, `HostAnsT1.lean` and `HostAnsGas.lean`. The build is green
(741 jobs), the axioms are standard, and there is no `sorry`.

* **Answer functions, proved equal to the spec arm on every branch and error:**
  * `value_return_ans`: memory or register source; the returned-length limit; the data-receipt byte
    burn; `ret`.
  * `log_utf8_ans`: the count limit; both UTF-8 read modes, including the NUL scan with per-byte
    charges; `BadUTF8`; the log charges; the total raised before its limit check.
  * `storage_write_ans`: key and value from memory or register; length limits; byte charges; the
    mock `trie` and the trie-backed `real` backends (with `TTN.storageWrite`'s node and evicted-byte
    charges and the recorder); storage usage; the evicted value into a register (`regSetH`'s
    checks) and result 1, or result 0.
  * Side effects that persist after an error are kept.
* **The T1 host set:**
  * `ansT1` / `ansT1F` cover all six T1 hosts (`input`, `register_len`, `read_register`,
    `storage_write`, `log_utf8`, `value_return`).
  * `ansT1_arm`, `ansT1_congr`: the answer reads host fields only.
  * `ansT1_mem`: memory is read only on the read set.
  * `ansT1_side`: the host side after the call.
  * `HostAnsGas` (`ansT1_sideR`, `ansT1_next`): the answer at `sideR s` (gas register blanked)
    agrees with the run from `s`. So lane B's `st`/`word`/`gas`/`regs`/`next` obligations are
    satisfiable on honest runs.
* **Finding: `ProducerObl.spec` is unsatisfiable for `value_return`, `log_utf8` and
  `storage_write`.** `runOf` cannot change `ret`, `logs` or storage. It is restated as `SpecU` (an
  answer with a host-side update `upd`; a `len ≤ stack size` premise; no σ premise). **`specU_T1`
  discharges it for every trace whose HOST rows call T1's hosts.** Two named premises remain, both
  honest: the row's `np` is the arity, and the request bytes cover the read set. Lane B's
  `ProducerObl` should take the `SpecU` form.
* **Non-vacuity on T1's own calls** (`decide +kernel`):
  * `t1_log_utf8` logs "tiny"; `t1_value_return` returns "again". Both have remaining gas equal
    to the tape's `gAfter` / `gFinal`.
  * `t1_storage_write_mock`: result 1, register 1 = "self". Its gas differs from the tape by
    exactly the trie-backed backend's 11 node and 4 evicted-byte charges (the backend T1 ran; it
    is not evaluated in Lean).
* **Open, `callResult_of_chainσ` for T1** (`hostIf_of_producerObl`):
  * `HostIf.reg`/`.cap` follow from `ProducerObl` directly.
  * `HostIf.ans` needs (i) the honest pre-state per row as a named premise and (ii) a bridge
    `hostPost_of_answer`: the `call` step through `callHost`, the out STATE/result/gas messages, the
    written bytes and `RelW` of the post-state. That is the construction-direction counterpart of
    `holdRowSP_of`, estimated at several hundred lines.
  * The answer side is complete.

## 3. Item 3: T1's call as pinned-shape tree leaves [M]

### 3.1 What was built

* **The stack's backend.** The segment prover builds unchanged against lane D's backend
  (`pq-chunk-e2e` deps: `native/wasm-base/build_stack.sh`), so the leaf proofs and their vk hashing
  are the verifier's.
* **The stack's base configuration** (`seg_base_params`, `main.rs`): first-order DKT certificates
  (`final-soundness/calc/dkt_certs_o2.json` minus `lean/DKTCertsO2_big.keys`, the stack's pair),
  list decoding m = 64, `k_first` 2, the stack's WHIR levers, domain odd factor 15, 268-bit
  per-round target, **24 query-grinding bits** (never seg-v1 with 32).
* **Pinned per-template heights** (`seg::TEMPLATE`, `tmpl_h`): every table, CODE/FUNC/HOSTT
  (rows repeated, multiplicities recounted) and the SHA-512 chip are padded to the template's height.
  A segment that does not fit is refused (`SEGFIT`). The CODE/FUNC roots are then the commitments of
  the padded matrices: the padded height is part of the `code_root`/`func_root` definition (a
  contract-size class, plan §5.0.1.4).
* Commands:
  * `segtemplate <seg_air> <m2_air> (<prep> <K>)+`: the per-table maximum heights over a set of
    calls, and the stacked geometry.
  * `segleaf <seg_air> <m2_air> <prep> <K> <template.json> <out>`: every segment proved at the
    template under one vk. It saves `SEG.vk.json` (the stack's envelope with the domain odd factor),
    `seg-<i>.proof` (the stack's proof codec), `seg-<i>.pubs.json` and `manifest.json` (template,
    parameters, soundness, sha256 of every file, CODE/FUNC roots).
  * `segleafverify <seg_air> <out> <n>`: reloads vk and proofs from disk, checks the vk hash,
    verifies, checks the public values against the saved ones and the boundary chain.
* Script: `run_leaf.sh`; tampers of saved leaves: `leaf_tamper.sh`.

### 3.2 T1 at its template [M] (`logs/t1-leaf-k13.txt`, `t1-template-k13.json`)

* Template `t1-d3tiny-k13`: cut every 13 steps (lane I's default: 2 segments), heights from T1's own
  segments (largest tables BYTE/RANGE16 2^16, SHA-512 chip 2^13; all others ≤ 64), `n_stack` 18,
  `w_stack` 8, `log_blowup` 1, grinding 24.
* WHIR queries **[100, 71, 45, 33]** (seg-v1 at the same geometry: [536, 256, 83, 50]); soundness
  **268.2 bits** (logup 324.4, proximity 295.1, query 268.2).
* **2/2 segments proved at one vk**: 553,355 B and 551,717 B (seg-v1: ≈ 1.33 MB), prove 54 s
  (host shared with two Lean sub-lanes; peak RSS 8.1 GB), verify 40 ms. The boundaries chain.
* **Reloaded from disk**: both verify (27–28 ms), the public values equal the saved ones, and the
  chain holds.
* **Saved-leaf tampers: 11/11 rejected**: a flipped proof byte, a truncated proof, the two proofs
  swapped, seven public values (+1: pc/t/S in, ctx in, mem in, mem out, status), and a vk with a
  query count changed.

* Higher rate: at `log_blowup` 3 the keygen gives 268.3 bits, but the prover was killed inside
  the 22 GB scope. That is 4× lb 1's LDE, and lb 1 peaked at 8.1 GB. A higher-rate leaf needs a
  larger memory budget or a smaller stacked width.

### 3.3 Not yet (item 3)

* **CODE/FUNC roots in-circuit as a SHA-384 Merkle root with per-segment touched-record openings
  (m6 §5b) is not built.** The leaf exposes the cached-commitment roots of the padded CODE/FUNC
  matrices (`manifest.json`). That is the form lane D's `build_seg_leaf` compares in-circuit
  (§5.0.1.4 step 3). PREP (item 4) must then produce the same commitment. See §4 for the cost
  comparison that decides between the two forms.
* The segment public values are lane A's 105 (`PUB_*`); the mapping to lane E's `WasmBnd` fields
  (`B.wasm`, with `gasLeft` per m6 §6) is the leaf wrapper's job and waits for lane E's statement.
* I3 (review-D7): the Wasm segment AIR has no `phase` field; its in-boundary is always an in-call
  state (pc, frame, gas register). The leaf wrapper must set `phase = inCall` and never accept
  `done` as input. The last segment exposes `halted = 1` (`PUB_STATUS`).
* One template per call here. A production menu (a few height classes) is the same machinery:
  `segtemplate` over a corpus sample.

## 4. Item 4: the PREP sub-proof — scope [S] (decision D-3)

**What PREP must prove, per contract (once, not per call):** for the code bytes `c` behind the
state's code hash `h`:
(a) `SHA-256(c) = h`;
(b) `prepare cfg c` (spec `Wasm/Prepare.lean`: decode 407 lines, validate 313, analysis and
    instrumentation limits 550) succeeds;
(c) the committed CODE and FUNC (and DATA, HOSTT) matrices are exactly the records of
    `checkModuleM2 cfg (prepare …)` (`WasmBase/M2Check.lean` over `Check.lean`, about 700 lines),
    padded to the template's contract-size class.
The segment leaves (§3) expose the CODE/FUNC roots. PREP exposes `(h, codeRoot, funcRoot)`, and the
tree checks equality.

**Which root.** Two forms:
* **(R1) Cached commitment (built in §3).** The segment proof's cached CODE/FUNC commitment. PREP is
  then a STARK in the same parameters (`l_skip`, `n_stack`, `log_blowup`, height class) with CODE and
  FUNC as its own cached tables, so equal roots mean equal matrices. There is no in-circuit hashing
  of the code table: the commitment is the prover's, and the leaf compares 2 digests. PREP and every
  segment template of a class must share the commitment parameters of those two tables.
* **(R2) SHA-384 Merkle root over records** (m6 §5b). Each segment opens the records it fetches.
  This is per-segment work (≈ touched records/8 compressions plus multiproof nodes), but it
  decouples PREP's geometry from the segment's.
R1 is cheaper now: T1's segments touch most of d3tiny's 32 records anyway, and R1 costs the leaf
nothing extra. **Recommendation: R1 for M10, R2 only if a height-class menu forces PREP to serve
segments of different geometries.**

**PREP AIR design (certificate style, not a decoder VM):** the prover supplies the decoded module
and the records; the AIR checks local consistency:
1. CODEBYTES (cached): the code bytes, plus the SHA-256 table (lane A already has the SHA-256 AIR,
   `ShaAir.lean`, for `sha256` host calls), which checks `digest = h`. About ⌈(|c|+9)/64⌉
   compressions: **6 for d3tiny (345 B), 88 for d3rich (5,603 B)**.
2. DECODE rows, one per instruction: `(offset, opcode, immediates, len)` read from CODEBYTES by
   lookup. LEB128 is decoded with a byte-row sub-table, and the opcode table is a fixed lookup. Section
   and function boundaries come from the section headers.
3. VALIDATE: the operand-type stack and the control stack as a memory-like bus (the same
   producer/consumer-time argument as the execution AIR); `matchBlocks` (`endOf`/`elseOf`) as a
   bracket bus; locals and type indices by lookup.
4. INSTRUMENT: the per-instruction gas table (`gasTable`, block-level metering), `maxStack` / stack
   charge and the prologue gas as running sums over DECODE rows; the limits of `prepare` (params,
   blocks, operand stack, instrumented size) as range checks.
5. RECORDS: each CODE record is a fixed function of a DECODE row and its gas, end and else entries
   (M2's record layout), sent to the cached CODE table with multiplicity 1. FUNC likewise from the
   function headers.
Lean obligation (lane E's template statement for PREP): `Holds PrepAir ⇒ prepare cfg c = .ok p ∧
CODE = codeRows (checkModuleM2 cfg p …)`, by the same method as the execution AIR (row facts, bus
balance), per spec function.

**Size for d3tiny:** 345 bytes, 32 CODE records, 4 functions, 6 SHA-256 blocks. Every table fits in
2^6–2^9 rows except the fixed lookups, so one small proof.

**Build order:** (1) CODEBYTES + SHA-256 (`h` public) under the template parameters; (2) DECODE +
RECORDS for the MVP subset d3tiny uses, with the cached CODE/FUNC roots equal to T1's leaf roots
(the R1 check, measured); (3) VALIDATE/INSTRUMENT; (4) the Lean statement and its proof;
(5) d3rich. **Not started in this session**: items 1–3 and the T1 blocker took priority.

## 5. Item 5: the Wasm side of the M6 join with lane B [K][M]

Sub-lane JOIN: Lean; the lead: tracer and checks. The build is green (738 jobs).

**Part 1, standalone AIR (`Seg.HostBK.msgM`).**
* The four `reg = 0` bus-210 interactions carry `[ts, wire, dir, ptr + pos, byte]`. The 4th field
  is the linear-memory address, as lane B's `HB(ts, kptr + j, b)` needs: `storage_write` reads two
  buffers in one call.
* The `reg = 1` interaction (REG's register fill) keeps `pos`.
* No downstream proof broke; the statements are generic in the message.
* T1 re-proved at this AIR: 2 template leaves, 553,859 / 551,549 B, 268.2 bits, one new vk
  (`logs/t1-leaf-k13.txt`). Saved-leaf tampers: 11/11 rejected.
* The u128 KAT: 8/8 segments pre-check.

**Part 2, the joined variant `wasmBaseSegAirMPJ`** (`SegAirJ.lean`, `wasmbase-tool airSegMPJ`).
It differs from the MP AIR only in two tables (`segMPJ_same`):
* **HOSTO → `HostOJ`:** + `w`; `mult·(1 − w·(q1−58)(q1−60)) = 0`. The in-trace oracle cannot
  answer `storage_write`/`storage_remove` (`hostOJ_no_storage`).
* **HOSTB → `HostBJ`:** + `stg`, `sw`; `stg = 1 ↔ hid ∈ {58, 60}` (`hostBJ_stg_iff`). HOSTB's own
  receive of request bytes is gated by `1 − stg`, so storage request bytes go to lane B's STB rows.
* Non-vacuity: `decide` on honest `input` and `storage_write` rows; two mutants rejected
  (`JoinCheck`).
* Lane B's obligation `StorageJoinObl` (`Main/HostJoin.lean`):
  * `ans`: `ProducerObl` restricted to the storage calls. HOSTQ/HOSTR (`st`, word = the evicted
    flag, `g_after`), the arm, the registers and the host side.
  * `hb`: the request bytes' addresses are exactly the key and value buffers.
  * `regFill`: the evicted value's register bytes.
  * `producerObl_join`: lane B's part + lane A's oracle part ⇒ `ProducerObl` ⇒ `HostIf`.
* Tracer (J mode): fills `w`/`stg`/`sw`, pads HOSTB with `sw = (58·60)⁻¹`, and gives HOSTO
  `mult = 0` for storage calls.
* **Measured** (`run_j.sh`):
  * `u128kat` (no storage call): 8/8 segments pre-check on the J AIR (`logs/j-u128-segcheck.txt`).
  * T1: pre-check fails with exactly **8 unbalanced messages**: `storage_write`'s HOSTQ (bus 208)
    and HOSTR (209), and its 6 HB request bytes (210: 1 key byte at address 0, 5 value bytes at
    16..20). These are exactly what lane B's rows supply in the joined trace
    (`logs/j-t1-segcheck.txt`).
  * With the oracle still answering, the J AIR rejects the trace (`HOSTO … constraint 0`).

**Open / for lane B:**
* (1) **Wire id.** `storage_write`'s value group goes out on bus 210 under wire
  `58 + 256 = 314` (FIX214 group bits). Lane B's `StbH` constrains `hid ∈ {58, 60}`. Proposal:
  `StbH` accepts wire 314 for the value buffer. The absolute address already separates key and
  value; lane A keeps the group bits, since its group lemmas rely on one wire per group.
* (2) `storage_read` (57) and `storage_has_key` (59) are still oracle-answered; lane B has no rows
  for them yet.
* (3) The evicted value's register fill is still HOSTB's `reg = 1` send to REG (`regFill` is lane
  B's obligation, not a bus balance with lane B).
* (4) The HOSTR answer for 58/60 (evicted flag, `g_after`) is now free only for lane B's rows to
  produce, so lane B must bind it.
* (5) The joined pre-check needs lane B's STB/STW tables in the same trace (one AIR JSON).

## 6. Lane E's `SegSoundWasm` (sub-lane CONN) [K]

The file is `WasmBase/Main/TmplWasm.lean`. The build is green (735 jobs), the axioms are standard,
and `spec/` is unchanged.

* **The leaf predicate.** `wasmHolds Pv d d' tr` combines:
  * `LeafW`, the circuit's checks:
    * `bdigest` of the witnessed `B_in`/`B_out` equals `d`/`d'`; the records are `WF`; phase `inCall`;
    * every non-Wasm field is copied;
    * the Wasm in/out fields equal the publics (pc, sp, 42-byte ctx/mem prefixes, pages, depth);
    * globals/registers digests = the frames digest; promises = `bdigest []`;
    * `fuel_out + (t_out − t_in) = fuel_in`; code/func roots carried; `t_in < t_out`.
  * `SegPremAMP`, `StaticOK`, the in-opening `win`, and the named `CutSeed` and `RestOK`.
* **Theorems:**
  * `wasm_core`, `segSoundWasmRel_of`: the relative form `TmplSoundRel V A Sha384Coll .wasm`.
    Every opening of `d` steps by `CSteps` to an opening of `d'`.
  * `segSoundWasm_of`: lane E's absolute `SegSoundWasm`, given the named `InOpens`.
  * `e2e_sound_t1_wasmRel`: `e2e_sound_t1` with the relative form, so no `InOpens` is needed.
* **Named premises, and why an honest run meets them:**
  * `CutSeed` (`RelW` at the cut, ctx, cid, `RegWF`, σ pin, 48-byte `mem_in`) is **proved from the
    previous segment's `OutSA` + `LinkPubM`** (`cutSeed_of_out`): it is the chain's continuity.
  * `RestOK` (out `stackRem` and `vmCtxDigest`) is proved for the honest record
    (`restOK_honest`). No public binds these two fields.
  * Non-vacuity: `wasmHolds_honest`, for consecutive honest segments.
* **Findings for lane E:**
  * (1) A field-copying leaf cannot meet the absolute `TmplSound`: copied non-Wasm fields are
    unconstrained. Lane F's `rt` has the same issue. **Proposal: adopt `TmplSoundRel`**
    (`e2e_sound_t1_wasmRel` shows it suffices).
  * (2) `mem_in` in the 42-byte record cannot be lifted to the AIR's 48-byte root when no block is
    touched. Fix with a 42-byte `seg_membIn` variant or a 48-byte `memRoot` field.
  * (3) The missing `gasLeft` and `stackRem` publics force `CutSeed.bnd`/`RestOK` (m6 §6).
  * (4) **Completeness:** `wasm_not_complete_pre` shows that `TmplComplete .wasm` fails for the
    instance `pre → pre` (`CSteps.refl`).
    * Lane E's `cm_decomp` uses one `wasm` segment per whole call (`.pre → .fin`).
    * Fixed-height leaves prove `ent → ent` with at least one step.
    * The whole-call meaning must split into entry (§7), mid-call segments, and halt. The honest
      side `WasmSegComplete` is stated, not proved: it is the tracer's completeness, measured by
      `segcheck`.

## 7. The `.pre → .ent` seam: PREP covers exactly `cstep q .pre = preConf q` [S]

The integrator found that lane F's rt-enter ends at `.call I c K q .pre`, while lane A's
segment 0 starts at `.ent p k (.cont s0) n`. In lane E's call machine
(`E2E/CallMachine.lean`), `cstep q .pre = preConf q` is **one** call-machine step, and it is
`runCall`'s whole prefix:
* `prepare cfg code` (decode, validate, analyse, instrument);
* the contract-loading gas;
* `link` and `resolve method`;
* `instantiate` (globals, data segments into memory, the stack budget);
* `adjustSt` (ctx, balance, storage usage, real store);
* the entry (`tailConf`: `.ent p (.start mi | .method) (enter …) fuel`);
* or a `.fin` line on every error branch (prepare error, method not found, gas exceeded, link
  error).
So `MWasm (call I c K q .pre) (call I c K q (preConf q))` is already a Wasm meaning instance.

**Proposal to lane E:** no new `Meaning`. Keep `Tmpl.wasm` and let `A.Tr .wasm` be a sum: segment
traces ⊕ PREP traces. The leaf geometry differs, but lane D's set of template classes already
allows that. If lane E prefers a distinct kind for readability: `Tmpl.prep` with
`MPrep (call I c K q .pre) (call I c K q (preConf q))`, which is contained in `MWasm`, so
`meaning_rsteps` is unchanged.

**PREP's statement** (completing §4). From the boundary digest of `.call I c K q .pre` (which
carries `q`: code hash, method, ctx, store) to that of `preConf q`:
* (a) `SHA-256(code) = h` from the state's code hash;
* (b) `prepare` ok, and the CODE/FUNC roots equal the commitments of `checkModuleM2`'s padded
  records (R1);
* (c) the loading-gas arithmetic;
* (d) `instantiate`: the initial `memRoot`. The data segments are hashed into the memory tree,
  and the zero subtrees are constants, so the cost is about data blocks × depth;
* (e) the entry frame/`pc`/`sp`/`stackRem`;
* (f) `vmCtxDigest` of `blank s0`: the remainder (host side after `adjustSt`) encoded and
  hashed. This is the one field PREP must compute that no Wasm segment does;
* (g) every error branch ends in `.fin` with the spec's line.
For d3tiny, (d) is the data image, `dataEnd` bytes.

## 8. Wasm boundary fields for lane I's boundary digest [M]

`segleaf` now writes, per segment (`seg-<i>.pubs.json` → `wasm_fields`; T1 samples in
`logs/t1-leaf-k13-seg{0,1}.pubs.json`), the `WasmBnd` fields beyond the 105 publics:

| field | status | source |
|---|---|---|
| `codeRoot`, `funcRoot` | **bound** | the proof's cached CODE/FUNC commitments (42 bytes = 5 × u64 + 16 bits; `segleafverify` checks them against the proof) |
| `fuel` | **bound by rule** | `fuel_out = fuel_in − (t_out − t_in)`: one call-machine step per STATE time (`LeafW`); `fuel_in` of segment 0 is the entry's `n` |
| `stackRem` | **honest value, unbound** | the cut's live budget message (`stack_rem_in/out_unbound`; T1: 262,032 at both cuts). It is committed inside the frames digest (`cutMsgs` has `budMsg`), but no public exposes it |
| `vmCtxDigest` | **not available** | `bdigest (encRest (blank s))` moves with `gas.g` at every step. It needs lane E's `gasLeft` (m6 §6) plus the state side's σ at host rows (M6.4) |
| `globalsDigest`, `registersDigest`, `promisesDigest` | by definition | = `framesDigest`, = `framesDigest`, `bdigest []` (`airBnd`) |

**To bind `stackRem` (next AIR change):** SEGB, the boundary table with one row, consumes the in
stream's budget message and produces the out stream's. Today CUTI/CUTO route it through the ctx
digest. Add two public values `rem_in`/`rem_out` and equate them with the budget message's value at
CUTI's and CUTO's space-5 row. A space-5 row needs a selector column `isBud` with
`isBud·(space − 5) = 0`, and the count must force exactly one budget row per stream. Then
`RestOK.stackRem` becomes an AIR fact.

## 9. Milestone A-T2 (2026-11-25): pinned tight heights; PREP stopped at a statement change

### 9.1 Task 1: the Wasm template pins its tight heights [M]

**Finding (lane D, M8):** A-T1's template pinned every table's *log* height but not its *tight*
height (the backend's committed rows = rows up to the last non-zero row). T1's two segments
differed in CODE's common main (16 vs 32 rows) and the SHA-512 chip (7,424 vs 4,992), and other
tables sat below their template height (MEMB 12 of 16 in both), so lane D's leaf, which takes the child's `(log, tight)` heights as program
constants, gave **two WASM leaf programs** for one template.

**Change (`native/wasm-base/src/segcmd.rs`, `segleaf` / `segleafverify`):**
* `segleaf` commits every common main at its full template height
  (`stacked_pcs::set_tight_floor`, the floor lanes B and G use). The floor is set after the cached
  CODE/FUNC commitments are made, so those are unchanged.
* `template_heights` computes the pinned `(log_height, tight_height)` per AIR from the template file
  alone: each JSON table at its template height, the SHA-512 chip at `SHA512` and its table at 128,
  tight = full. `segleaf` asserts that every proof declares exactly these heights, and the
  manifest records them (`pinned_heights`).
* `segleafverify` recomputes them from the manifest's template and refuses any proof that declares
  other heights.
* `SEG_TIGHT_NATURAL=1` restores the old behaviour, for tampers only.
* The vk is unchanged (`b1eed0ca…`): tight heights are proof data, not key data.

**T1 re-proved** (`run_leaf.sh … 13 1 24`, stack backend, base configuration, 8 threads,
`HEAVY_MEM=18G`; `logs/t1-leaf-k13p*.txt`):

| | A-T1 (`at1/leaf-k13c`) | A-T2 (`at2/leaf-k13p`) |
|---|---|---|
| seg 0 / seg 1 proof | 553,859 / 551,549 B | **554,709 / 553,071 B** |
| prove (s), verify (ms), peak RSS | 51 / 53, 44 / 38, 8.1 GB | 25.7 / 28.3, 17 / 17, 8.2 GB |
| queries, soundness | [100, 71, 45, 33], 268.2 bits | same |
| heights, seg 0 vs seg 1 | CODE 16 / 32, SHA-512 7,424 / 4,992 (MEMB 12 / 12 of 16) | **identical**, every table at its template height (`logs/t1-leaf-k13p-heights.txt`) |
| lane D leaf programs (`m8-import`, then the M8 probe) | 2 (`779e31f6…`, `d921c4c2…`; 244,330 / 244,190 rows) | **1** (`59b572a7…`, 238,436 rows, both leaves) |

* **Saved-leaf tampers: 14/14 rejected** (`logs/t1-leaf-k13p-tamper.txt`). These are A-T1's 11 plus
  three new ones:
  * seg 0, and separately seg 1, replaced by the A-T1 proof of the *same* segment under the *same*
    vk at natural tight heights (it verifies under the backend and is refused only by the pinned
    heights rule);
  * the manifest's template `SHA512` height halved.
* **Lane D's format:**
  * `m8-import` verifies both proofs natively; their `INFO.json` `heights` and `vk_sha256` are equal.
  * `m8_spec_real.py` and `M8_CHECK_ONLY` pass: the native chain over the 8 leaves holds and the
    probes are equal.
  * The new `M8_PROGRAMS_ONLY=1` (`pq-chunk-e2e/src/htree.rs`, a measurement aid) prints the
    program root of every leaf at the leaf geometry. It reports one WASM root, and the other
    templates' roots equal `results/zk/m8/t1real`'s (`logs/t1-leaf-k13p-m8.txt`).
  * `e2e/scripts/m8_import_real.sh` now defaults to the A-T2 leaves.
* **Paths:**
  * proofs, vk, pubs, manifest: `/data/illia/nearproof-deps/e2e-laneA/at2/leaf-k13p/leaf/`;
  * lane D's imported form (`TMPL.proof`, `TMPL.vk.json`, `INFO.json`):
    `/data/illia/nearproof-deps/e2e-laneA/at2/m8-tmpl/wasm{0,1}/`.
* **Not done:** lane D's tree-leaf *proofs* of these two children. A full M8 tree run is
  ~6,000 s at 33 GB peak, above this lane's 18 GB share of the slice. The leaf program is fixed (one
  root, measured), so lane D's next `run_m8.sh import|spec|tree` picks them up unchanged.

### 9.2 Task 2: PREP — stopped, it needs a statement change [K][S]

PREP is the `.pre → preConf q` template (§7). It must take the contract code hash to the CODE/FUNC
roots that the Wasm leaves' cached commitments are compared with. Before building its AIR, I
checked what its input and output boundary records can carry. **Under the current boundary
statement, no PREP leaf can bind the code.** Following the stop rule, I built no AIR. The findings:

* **(P1) The `.pre` record has no code field.** For `(q, .pre)`, `WasmView.fbBnd` sets
  `codeRoot = funcRoot = bdigest []`. Its only non-constant field is
  `vmCtxDigest = bdigest (encRest (.other (q, .pre)))`. No `BndRec` field carries the code hash.
  Lane F's enter leaf reads the code hash on `FB`, but its output's Wasm part is this carried
  record: `EnterView` is owed to PREP (`m5t1/lean/M5T1/SegRt.lean`).
* **(P2) The encoder PREP would have to open cannot exist [K]** (`lean/PrepScope.lean`, checked by
  `lake env lean` against the built `WasmBase`; axioms `propext`, `Classical.choice`, `Quot.sound`):
  * `wasmViewParams_empty : WasmViewParams → False`. `encRest_inj` asks for an injective byte
    encoding of `WRest`, which contains `q.real.store : ByteArray → Option ByteArray`. Cantor's
    argument rules that out.
  * Consequence: every theorem over `Pv : WasmViewParams` is vacuous. That includes
    `wasmD_binding`, `viewImpl_hwasm`, `segSoundWasmRel_of`, and the honest non-vacuity results
    (`wasmHolds_honest`, §6). This is a finding against lane A's own §6.
  * `vmD_coll : ∀ V : ViewImpl, Coll V.vmD`. `VmV = List (VmQ × Run)` carries the same store, so
    lane E's `viewImpl_binding_bad` premise `hvm : Coll V.vmD → Bad` holds only with a provable
    `Bad`. Every `V.wasmD` collides as well, because its codomain is countable. That case is not
    formalised.
  * Lane B's `StViewParams.encRest_inj` should be checked for the same pattern.
* **(P3) Where the code hash lives.** In the spec, `q.code = codeOf st h`: `h` is the account's
  code hash and `st` is the hash-keyed recorded store (`TrieRecorder.codeOf`, `TTN.mkStore`). So
  `SHA-256(q.code) = h` is a state-side fact, and the binding starts at lane F's enter leaf.
* **(P4) The output side is unbound too.**
  * `airBnd.codeRoot = Pv.codeRootOf q p` is a free parameter.
  * The Wasm leaf's link from its cached CODE/FUNC matrices to `p` is the named premise
    `CutSeed.ctx`.
  * `vmCtxDigest` at `preConf q` (and the segments' `RestOK`) needs the same impossible encoder.

**Proposed statement change** (owner / integrator; lanes A, E, F; nothing was changed):
* **S1. Take the function-typed store out of the Wasm remainder.**
  * `WRest`/`encRest` should cover `q` with `real.store` dropped. The store is committed by the
    state side (`stRoot`; `RealStore.root` is already in `q.real`).
  * Lane E's `ViewImpl` binding would then be stated modulo equal stores: `Coll V.wasmD` and
    `Coll V.vmD` relative to `q.real.store` (`spec/lean/v3/NearSpecV3/E2E/View.lean`).
  * Alternative: restrict configurations to finitely supported stores (`mkStore values`).
* **S2. The `.pre` record exposes the code hash.** Set `fbBnd (q, .pre)` `codeRoot :=
  SHA-256(q.code) ‖ 0¹⁰` (42 B). Lane F's enter leaf writes it from the `FB` code-hash field it
  already reads. Binding is unchanged, because the fallback record is fixed by `vmCtxDigest` once
  S1 holds.
* **S3. Fix `codeRootOf q p`** as the R1 root of the padded CODE/FUNC matrices of `checkModuleM2`
  at the template's commitment parameters (§4). Add a named commitment-binding event (one
  stacked-PCS root for two matrices). `CutSeed.ctx` then follows from the leaf's in-circuit
  equality *cached root = `B.codeRoot`*.

**What PREP then binds** (the statement to build after S1–S3):
* in: `B_in.wasm.codeRoot` = the code hash, set by RT enter;
* the code `c` with `SHA-256(c)` equal to it (lane A's `ShaAir` SHA-256 table over a CODEBYTES
  table; `HashInputLink` becomes a lookup);
* the `prepare`/`checkModuleM2` certificate of §4;
* out: `B_out.wasm.codeRoot`/`funcRoot` = PREP's own cached CODE/FUNC roots. These are the 2 × 18
  limbs that lane D's M8 record already carries in its W part, next to the segments' cached roots.
* also out: the entry `pc`/`sp`/`stackRem`/`fuel`/`memRoot`/`memPages`/`framesDigest`, and
  `vmCtxDigest` under S1.

**T1 facts that hold today, whatever is decided:** the leaves' cached CODE/FUNC roots equal the
native R1 roots of the records computed in Lean (`statement_ok`, manifest `code_root` /
`func_root`), and `SHA-256(d3tiny) = 8152bed2…` is the account's code hash (lane I).
