# Lane A milestone A-T1: T1's Wasm call end to end

Plan: `docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §4.2 (M10), tracker `docs/zk-formal/E2E-T1-CRITICAL-PATH.md`.
Labels: **[M]** measured, **[K]** kernel-checked Lean (standard axioms, no `sorry`), **[S]** stated / design.

T1 = `/data/illia/nearproof-deps/corpora/d3c8/d3/02-h10196-s3`: one FunctionCall to `d3tiny`
(code `8152bed2…`, 345 B), method `run`, input `again`, 26 Wasm steps, six host calls:
`input`, `register_len`, `read_register`, `storage_write` (existing key), `log_utf8`, `value_return`.

**Update 2026-11-25 (A-T5, §12).**
* The segment AIR's out-boundary exposes `stackRem` (CUTO's budget row) and `gasLeft = s.gas.g`
  (SEGB's gas gadget `g_out + R·(S_out − S_seg) = segb_out`); `airBnd.gasLeft = s.gas.g`, and the
  remainder no longer carries `gas.g`. `WOut` binds both (Lean: `segb_gas_sound`, `cuto_rem_sound`).
* The halting segment's out-record is the fin record `fbBnd (q, .fin r)` (finding I2b-2):
  `TmplWasm.WasmHoldsF`, `wasm_fin_core`, `wasm_relC_fin`, the two-kind system `airsWF`.
* `HashLenLink` is a theorem of `wasmBaseHashAir` (restated: the register branch hashes the
  register's length). The segment AIR has no SHA-256 table, so this does not touch it.
* T1's two Wasm leaves re-proved (557,517 / 556,887 B, 268.2 bits, one lane D program); their in/out
  digests are the chain's `c4 → c5 → c6` (`e90f4a94 → b28bfa13 → b3135387`).

**Update 2026-11-25 (A-T4, §11).**
* PREP decodes the hashed code in-circuit. New tables: `CB` (code bytes, fed to the SHA slots),
  `HDR` (the section walk) and the CODE/FUNC decoder columns. Every byte-determined record field is
  constrained: opcode, indices, constants, offsets, pc and layout.
* T1's PREP leaf is 488,409 B, 268.2 bits, and its roots are unchanged. Mutants: 19/19 rejected,
  and another program's records are now rejected in-circuit.
* Lean: `RecordsCert` is now a theorem (`TmplPrep.recordsCert_of`). It rests on the AIR's
  `DecodeCert`, the named static residual `StaticCert` and the trace-independent `DecFaithfulAt`,
  which is kernel-checked for d3tiny.
* Of `Holds ⇒ DecodeCert`, only the byte-read layer is proved so far.

**Update 2026-11-25 (A-T3, §10).**
* Lane E's soundness fix S1–S3 is adopted on lane A's side. The Wasm view is store-blind,
  `WasmViewParams` is inhabited by T1's real record, and the Wasm template is restated and proved
  against lane E's store-canonical `TmplRelC`.
* PREP is built as a `wasm`-kind leaf and proved for T1 in lane D's format: 469,779 B,
  268.2 bits, pinned heights. Its CODE/FUNC roots equal the segment leaves'. Mutant battery: §10.3.
* PREP does not yet bind the records to the code in-circuit (the decoder certificate, §10.4).

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

## 10. Milestone A-T3 (2026-11-25): S1–S3 adopted; PREP as a `wasm`-kind leaf

Lane E adopted A-T2's S1–S3 as a soundness fix (`spec/lean/v3/NearSpecV3/E2E/StoreBlind.lean`,
`TreeM8C.lean`; plan §3.5 M11i). This milestone does lane A's part. `S`, `claimDigest` and the
checker are unchanged, and nothing here needs them changed (stop rule not triggered). Lean: the
`WasmBase` package builds (762 jobs, with `wasmbase-tool`) with standard axioms only, and there is no `sorry`,
`native_decide` or `axiom`.

### 10.1 The store-blind Wasm view and T1's parameter record [K]

**`WasmView.lean` §7–8 (restated in place):**
* `WasmViewParams` now asks for `encRest_blind` (`encRest (setW t a) = encRest a`: stores are not
  encoded) and `encRest_inj` modulo stores (`encRest a = encRest b → stripW a = stripW b`). It also
  asks for `ctxOf_blind`.
* S2: the fallback record at `.pre` has `codeRoot = preCodeRoot q = SHA-256(q.code) ‖ 0^10`
  (`fbCode`).
* S3: `codeRootOf P q p k = codeC.root (codeRecs hCode X)` and
  `funcRootOf P q p k = funcC.root (funcRecs hFunc X)`. Here `X = ctxOf q p k`, and `codeRecs` /
  `funcRecs` are the entry module's records padded to the template height by repeating the last
  row (`padRep`, as `seg.rs` `pad_rep`). The roots now take the entry `k`, because the checked
  closure depends on the entry function.
* `wasmBnd_set` / **`wasmD_set`**: the component ignores stores.
* `wasmBnd_binding`: equal records give equal components up to stores, or `Sha384Coll`.
* **`wasmD_binding : CollOn WStripped (wasmD P) → Sha384Coll`**, and `viewImpl_hwasm` (the Wasm
  premise of lane E's `SB.e2e_sound_t1_relC_bind`).

**`WasmViewT1.lean` (new): the explicit instance, so that the Cantor problem cannot recur.**
* `ctxM2` is the real static context: the entry kind's function (`start`, or the resolved method),
  then `checkModuleM2 cfg p (fi − |imports|)`, packed by `M2Ctx.toCtx`. `ctxM2_ok` proves `CtxOK`.
* `encRestT1` encodes the remainder through lane E's store-blind serialisers (`argsN`, `stN`,
  `confN`), tagged by constructor (`encRestT1_blind`, `encRestT1_inj`).
* `ccT1` is a `CodeCommit` stand-in (`bdigest ∘ Ser.enc`). The circuit's root is the stacked-PCS
  commitment, which has no Lean model.
* T1's heights are CODE 32 and FUNC 4.
* **`wasmViewParams_nonempty : Nonempty WasmViewParams`.**
* `vT1` is lane E's store-blind view `SB.vSB` with lane A's Wasm component. It satisfies
  `vT1_blind` (`StoreBlind`), `vT1_clear` (`ClearCall`) and `vT1_wasm` (the restricted Wasm
  binding, with `Bad = Sha384Coll`).
* `a-t1/lean/PrepScope.lean` keeps the finding as `encRest_total_empty`: no injective encoder of a
  store-carrying remainder exists. It now also checks `wasmViewParams_nonempty`.

### 10.2 The Wasm template against `TmplRelC` [K]

**`SegStore.lean` (new):** a Wasm segment never writes the trie store function.
* `step_resOK` covers one step. A non-storage step commutes with the store map (`Logged.W.E_step`).
  A storage host call keeps the store (`callHostL_spec`, with a byte-list store `gOf σ` that agrees
  with `σ`, `gOf_agrees`).
* **`seg_setSt`** extends this to a segment, and `enter_setSt` to a function entry.

**`TmplWasm.lean` (restated):**
* `wasm_core` now returns the successor explicitly.
* `open_in` opens the in-digest only up to stores, because the record cannot see stores.
* New named premise **`GhostC sf V tr`**: there is a ghost intake `I` whose context digest is the
  in-record's `ctxRoot`, and the ghost query and state carry `I`'s canonical store `sf I`. It is
  needed because the AIR's σ-thread pins the ghost state's store: storage reads run against it.
  The record carries no store (it is a function), but `ctxRoot` pins `I`, and `I` pins the store.
* **`wasm_relC`** / **`segSoundWasmRelC_of`** prove `SB.TmplRelC sf V A (Sha384Coll ∨ Coll V.ctxD)
  .wasm` for `A.Holds .wasm = wasmHoldsC sf V Pv` (`WasmHolds ∧ GhostC`). A canonical opening `x`
  of `d` steps by `MWasm` to a canonical opening of `d'`; the output is canonical by `seg_setSt`.
* `airsWC` / `segSoundWasmRelC_airsWC` give the system `Airs`.
* Non-vacuity: `ghostC_honest`, and `wasmHoldsC_honest` (`wasmHolds_honest` plus canonicity).
* The non-canonical `segSoundWasmRel_of` / `wasm_rel` are removed. Over a store-sensitive opening
  they are not provable: the ghost's store and the opening's store can differ.

**What the Wasm leaf's soundness still rests on** (each is a named premise, and each holds on an
honest run):
1. `SegPremAMP`, lane A's per-segment premises. These include `CodeOK`/`FuncOK`: the CODE/FUNC
   rows are records of `X`. Under S3 these should follow from the leaf's in-circuit equality
   *cached root = `B.codeRoot`* and `CodeCommit` binding (the matrix is `codeRecs hCode X`, and
   `padRep` repeats a record). **Not formalised.**
2. `CutSeed`, proved from the previous segment (`cutSeed_of_out`).
3. `RestOK`: `stackRem` and `vmCtxDigest` of the out-record. No public binds them (§8).
4. `win`, the ghost in-opening, and `GhostC`.

### 10.3 PREP: AIR, T1 leaf, mutants [K][M]

**AIR (`WasmBase/PrepAir.lean`, `wasmbase-tool airPrep`):** 4 tables and 33 public values (the 32
hash bytes, then the length).
* `PHDR` has one active row. It sends the hash-call summary and receives
  `[0, 53, 1, len, h_0 … h_31]` on bus 211.
* `SHA256` is lane A's SHA-256 table (the classical `ZkFormal.Sha.Table` constraints) plus
  `Dmult ∈ {0,1}`. Its digest row sends `[ts, hid] ++` the classical digest message
  `[Id, Nd, digest bytes]`, embedded by `toW`.
* `CODE` and `FUNC` are the segment AIR's `Chips.Code.table` / `Chips.Func.table`, verbatim
  (`prep_code_verbatim`, `prep_func_verbatim`).

**Soundness of the hash part (`WasmBase/PrepSound.lean`) [K]:**
* **`prep_sha_sound`**: from `Holds prepAir pub tr` (SHA table height a power of two in
  `[2, 2^22]`) there is a message `m` with `pub[32] = |m|` and `pub[0..32) = SHA-256(m)`.
  * PHDR's first row is active (`act_val`). Every count on bus 211 is a bit (`dmult_bit`), so the
    balance is exact.
  * The only 36-field sender on bus 211 is a SHA digest row (`occ211`).
  * That row's message is `[Id, |m|] ++ sha256 m`, by the classical
    `sha_digest_contract_closed` through `eval_z`.
* `prep_hash_of_holds`: the 32 bytes the wrapper reads (`hashOf pub`) are `SHA-256(m)`.

**The PREP template (`WasmBase/Main/TmplPrep.lean`) [K]:**
* `prepHolds sf V Pv` is the circuit's checks (`PrepCirc`) plus the named premises (`PrepNamed`).
  * `PrepCirc`: the record digests, WF, phase, the copy rule, `B_in.codeRoot = hash ‖ 0^10`, the
    out roots = `codeC.root cm`, `funcC.root fm`, and `sha256 code = hash`. The last is a theorem
    of the AIR: `prepCirc_sha_of_air`.
  * `PrepNamed`: `win`, `ghost`, **`cert`** (`RecordsCert`, the decoder certificate), `ent` (the
    success path) and `rest` (the entry record's other fields).
* `preConf_canon`: `preConf` keeps a canonical query canonical (`adjustSt`, `enter_setSt`).
* **`prep_relC`**: every canonical opening of `d` (necessarily `call I c K q .pre`) steps by one
  `cstep` to the canonical `call I c K q (preConf q)` with digest `d'`. Otherwise there is a
  `Sha384Coll`, a `Coll V.ctxD`, or a `Sha256Coll` (the circuit's bytes and `q.code` hash
  equally).
* **`segSoundWasmPrepRelC_of`**: the Wasm kind over both leaf types (`airsWP`: `WTr ⊕ PTr`, lane
  E's decision) meets `SB.TmplRelC … (Sha384Coll ∨ Coll V.ctxD ∨ Sha256Coll) .wasm`.
* `prepNamed_honest` proves `win`, `ghost` and `rest` for the honest records.

**T1's PREP leaf [M]** (`run_prep.sh`; prover = the segment prover against the stack backend,
`build_stack.sh`):

| | |
|---|---|
| template | the segment template's commitment parameters (`n_stack` 18, `w_stack` 8, `log_blowup` 1, 24 grinding bits, DKT certificates); heights PHDR 4, SHA256 128 (103 live rows: 6 blocks), CODE 32, FUNC 4 |
| pinned heights | `[(2, 4), (7, 128), (5, 32), (2, 4)]` (`set_tight_floor`, as `segleaf`); `prepleafverify` refuses any other |
| proof | **469,779 B**, prove 31.1 s, verify 13–14 ms, peak RSS 7.7 GB, **268.2 bits** (logup 324.4, proximity 295.1, query 268.2), WHIR queries [100, 71, 45, 33] |
| public values | `8152bed2…36bf9` (the account's code hash) and 345 |
| R1 | PREP's cached CODE / FUNC commitments = the canonical `code_root` / `func_root` = **both A-T2 segment leaves' cached roots** (`prepleafverify` against `at2/leaf-k13p/leaf`), and in lane D's format the 18-limb `cached` cells of `INFO.json` are equal to `wasm0`'s and `wasm1`'s |
| lane D format | `m8-import` (pq-e2e-m8 drv2) verifies it natively: `M8_TEMPLATE_PROVED wasm_prep bytes=469779 … bits=268.2` |

**Mutant battery (`preptamper`): 14/14 rejected** (`logs/t1-prep-tamper.txt`):

| mutant | rejected by |
|---|---|
| wrong code byte (byte 100 flipped, public hash kept) | bus 211 unbalanced: the prover fails (`LogupZerocheck(NonZeroRootSum)`) |
| wrong hash (public byte 0 + 1) | the same |
| wrong length (public length + 1) | the same (`Nd` is in the digest message; see the finding below) |
| wrong func record (FUNC row 0 charge + 1) | R1: PREP's FUNC root ≠ the segments' FUNC root |
| wrong code record (CODE row 3 op + 1) | R1: CODE root |
| code records out of pc order | R1: CODE root |
| swapped code root (CODE committed with the FUNC records, FUNC with CODE's) | R1: CODE root |
| natural tight heights | pinned-heights rule |
| saved proof byte flipped | the verifier (`WhirError(MerkleVerify)`) |
| published code / func roots swapped | published root ≠ the proof's cached commitment |
| `in_code_root` of another contract | ≠ the public hash |
| a public hash byte edited | the public values |
| vk query count edited | vk hash |
| the segment leaves of another code (their CODE root edited) | R1 |

The record mutants (func record, code record, order, swap) are rejected **only** by the R1
comparison with the segment leaves. PREP itself accepts any CODE/FUNC matrix: nothing in the AIR
yet ties the records to the hashed bytes (§10.4).

**Finding: `Chips.Sha`'s `sh_len` is not tied to `Nd`.** A first PREP AIR took the length from
the summary (`sh_len`), and the "wrong length" mutant was accepted. In the segment AIR, a
`sha256` host call's summary therefore does not bind the message length. This is inside the
stated `HashInputLink` obligation (`ShaAir.lean`), but the fix is cheap: carry `Nd` in the digest
message, as PREP now does.

### 10.4 Open

* **The decoder certificate (`TmplPrep.RecordsCert`)**: the CODE/FUNC matrices are
  `checkModuleM2 cfg (prepare cfg m)`'s records for the hashed bytes `m`. These are steps 2–5 of
  §4 (DECODE rows with LEB128 and an opcode lookup over a CODEBYTES table byte-linked to the SHA
  rows; VALIDATE; INSTRUMENT; RECORDS sent on `busFetch`/`busFunc` to the `mult` columns PREP's
  CODE/FUNC already have). Until it exists, a prover may pair a contract's hash with records of a
  different program, provided its segment leaves use the same records. The R1 comparison binds
  PREP to the segments, not to the code. **This is the main gap of the Wasm side.**
* `PrepRest` (§7 (c)–(f)): the entry record's pc, sp, stackRem, fuel, memory root and pages, the
  frames digest and `vmCtxDigest`, all at `preConf q`. `PrepNamed.ent` covers the success path
  only; the error branches of `runCall`'s prefix need a second PREP shape.
* `CodeOK`/`FuncOK` from S3 (§10.2 item 1).
* Lane D: put the PREP leaf into the tree spec, between RT `enter` and WASM segment 0. This needs
  the W-part mapping and a normaliser from PREP's 32 hash bytes to `B_in.wasm.codeRoot`; then lane D
  can report its leaf program root. The leaf is ready in lane D's format:
  `/data/illia/nearproof-deps/e2e-laneA/at3/prep/m8-tmpl/prep/`.
* The `gasLeft`/`stackRem` publics (m6 §6, §8) for `RestOK`.

**Paths:** PREP leaf (`PREP.vk.json`, `prep.proof`, `prep.pubs.json`, `manifest.json`) at
`/data/illia/nearproof-deps/e2e-laneA/at3/prep/leaf/`; lane D's import at `…/at3/prep/m8-tmpl/prep/`;
logs `logs/t1-prep-*.txt`.

## 11. Milestone A-T4 (2026-11-25): the decoder certificate (`RecordsCert`)

**Goal.** Close the gap of §10.4: PREP must prove that its cached CODE / FUNC matrices are the
records `checkModuleM2 (prepare c)` produces for the bytes `c` it hashes. Before A-T4 a prover could
pair d3tiny's hash with another program's records, provided its segment leaves used the same
records. `S`, `claimDigest` and the checker are unchanged, and nothing here needs them changed
(stop rule not triggered).

### 11.1 Design: an in-circuit decoder, with the static analysis left as a named residual [S]

I compared the two options of the task.

* **(a) A full in-circuit `prepare` + `checkModuleM2`.** This means decode, validate (operand-type
  and control stacks), finite-wasm block metering (`gasTable`: loop pre/post re-kinding, two merge
  passes), the operand-stack maximum in bytes, the closure BFS, method resolution through the
  export names, and the host-name table. Each of these is an AIR *and* a Lean equivalence proof
  against ~1,300 lines of spec. That is several milestones of work.
* **(b) A certificate.** The circuit checks a witness cheaply. But a record has two kinds of field:
  * fields the instruction's **bytes** fix: the opcode, local / global / label / function
    indices, constants, memory offsets, the pc, the function layout;
  * fields only the **static analysis** fixes: the stack height `h`, the block fee, control
    targets, the halt/next choice of `end` / `br`, and call targets / host ids.

  A certificate for the first kind is a byte-level decoder that is local and cheap. For the second
  kind, a certificate still needs the analysis's invariants to be checked in-circuit (height
  transitions with a label stack, block-fee sums), which is most of (a).

**Chosen: (b) for the byte-determined fields, fully in-circuit, from byte 8 of the hashed code.**
The static-analysis fields go to a narrower named residual. Concretely:

* **Byte link.** A new `CB` table holds the code bytes (row `i` = byte `i`, live rows exactly
  `i < len`). It feeds the SHA-256 table's 16 byte slots on `busCB`, using the classical frame's own
  byte interactions. It answers every byte read on `busLB`, live rows only. So every byte the
  decoder reads is a byte of the message whose SHA-256 is the public code hash.
* **Coverage: the section walk (`HDR`, one row per item).** The walk starts at byte 8. Section
  headers are id + size LEB; every section other than the code section (id 10, detected by an
  inverse gadget) is skipped by its size. Then come the code section's count, each body's size
  LEB, its local-group count and the local groups (count LEB + type byte). The number of groups is
  tracked by a zero-tested register. At the end of a body's local groups the row *emits*
  `(k, iS, bE)`: the body index, its first instruction byte and its end. Every transition is
  forced by the bytes (`PrepDec.hrow` is a function). The prover can only stop early, which leaves
  later bodies unemitted.
* **Records: the CODE table's common columns decode.** Each live CODE row decodes one instruction.
  It has a pointer `ptr`, an 11-byte window (8 bit columns per byte) and a class one-hot. The class
  is an *indicator polynomial* of the opcode byte's bits, degree 8, 13 classes (the M2 subset with
  record immediates; any other byte makes the trace unsatisfiable). Two LEB chains (continuation
  bits, termination, exactness of the high groups) compute the immediate, and the immediate's bits
  give the record limbs: unsigned 21-bit indices, the 28-bit memory offset split into 16-bit
  halves, and `i32`/`i64` constants as 16-bit two's-complement limbs with the sign of the last
  group. The row then constrains the cached record:
  * the pc is the row index;
  * the opcode (`= byte`, or the class constant: `next`, `if`, `else → jump`, `return → halt`,
    `memory.size`/`grow`);
  * every immediate field and every field that is 0 for the class.
* **Coverage: the layout.**
  * Inside a function, `ptr` steps by the instruction length.
  * A function's last row ends exactly at `bE`, after `fsz` rows.
  * Function starts are a permutation (`busFn`) of the live FUNC rows `[off, k, iS, bE, size]`.
  * FUNC's offsets are prefix sums from 0.
  * Each FUNC row looks its body up among the walk's emissions (`busBody`).
  * Padding rows (CODE and FUNC) repeat the last record, which is `padRep`.

  The cached CODE / FUNC columns are unchanged (first 8 columns, same names, height and
  commitment parameters), so R1 still holds.
* **Not in-circuit (the residual `StaticCert`, named):**
  * which bodies the FUNC rows list, in closure order (`ks = X.M.fns`);
  * CODE fields `h`, `fee`, the opcode of `end`/`br`/`br_if`/`call`, `x0` of
    `if`/`else`/`br`/`br_if`/`call`, `x1`/`x2` of `call`;
  * FUNC fields 1–7.
* **Not in-circuit, but trace-independent (`DecFaithfulAt cfg c`, a `Bool` check).** If `prepare`
  accepts `c`, every body the walk emits for a defined function decodes, by the reference decoder,
  to that function's instructions. The adversary cannot choose its truth after the fact: it is a
  property of the code, decided by evaluation per code, here by the kernel for d3tiny.

Cost on T1: see §11.3. The decoder adds 4 tables. CB is 512 rows × 4 columns, HDR is 16 × 77, and
the CODE / FUNC common mains grow to 133 / 5 columns.

### 11.2 What is proved [K]

Standard axioms only. No `sorry`, `native_decide` or `axiom`.

* **`PrepDec.lean`.** The reference: `lebBytes`/`lebU`/`lebS`, `clsOf`, `decInstr`/`decBody`,
  `hrow`/`walk`/`emits`, `dimg` (spec `Instr` → decoded `(byte, imm)`), `fieldsOf`/`decFields`,
  `Agree`, `DecFaithfulAt`, and **`DecodeCert`**, the AIR's claim about its cached matrices.
* **`PrepCert.lean`.** `recordAtM2_agree`: every record `recordAtM2` produces agrees with
  `decFields (off + pc) (dimg ins)`, case by case over `Instr`. `checkModuleM2_agree` lifts this to
  each checked function of a module. This is the *spec side*: the fields the AIR decodes are the
  fields `checkModuleM2` writes.
* **`TmplPrep.recordsCert_of`.** It proves `RecordsCert` from four premises:
  * `CtxOK`;
  * `CtxIsM2` (the context is `checkModuleM2`'s);
  * `DecodeCert`;
  * `StaticCert` and `DecFaithfulAt`.

  The proof uses `preConf_ent` (the entry's `p` is `prepare q.code`), the prefix-sum layout of
  `checkModuleM2` (`checkModuleM2_shape`, `layout_locate`), `agree_eq` (two records agreeing on
  the fixed fields and equal on the free ones are equal) and `padRep_of`.
* **`TmplPrep` restated.**
  * `PrepCirc` gains `dec : DecodeCert …`.
  * `PrepNamed.cert` (the whole `RecordsCert`) is replaced by `stat : StaticCert …` and
    `df : DecFaithfulAt …`.
  * `prep_relC` and `segSoundWasmPrepRelC_of` take `CtxIsM2`.
  * `PTr` carries the FUNC body indices `ks`.
* **`PrepT1Ctx.ctxM2_isM2`.** T1's context satisfies `CtxIsM2`.
* **`PrepT1.decFaithful_d3tiny`.** `DecFaithfulAt pv86 d3tiny`, by `decide +kernel`: the kernel
  runs `prepare`, the walk and the decoder on the 345 bytes. `decFaithful_d3tiny_cfgs` covers every configuration
  that differs from `pv86` in `floats`, `curveHosts` or `globalActions`. The check is on demand,
  outside the default build: 43 s under a 12 GB cap
  (`HEAVY_MEM=12G … lake build WasmBase.Main.PrepT1`). It does not fit a 4 GB job.
* **`PrepDecSound`.** The AIR obligation `PrepDecodeSound` (`Holds prepAir ⇒ DecodeCert` of the
  SHA message) is **stated**. Its byte-read layer is proved:
  * CB's `pos` is the row index (`cb_pos`), and its live rows are exactly `r < len`
    (`cb_live_of_lt`, `cb_live_lt`, `cb_last`, `cb_drop`);
  * **`lb_read_sound`**: every byte read on `busLB` with count 1 carries `[r, byte_r]` of a live CB
    row `r < len`. It goes through `occLB` and `lookup_sound`; the read counts are boolean columns
    `u_i`, added for this.
* `PrepSound.prep_sha_sound` is re-proved for the 6-table AIR (`occ211`, with `bus_ne_of_all` for
  the decoder tables).

### 11.3 T1's PREP leaf [M]

`run_prep.sh` with the A-T4 AIR (`wasmbase-tool airPrep`) and prover (`build_stack.sh`); the
template adds `CB` 512 and `HDR` 16 (`PREP_CB`, `PREP_HDR`); 8 threads, `HEAVY_MEM=12G`. Logs:
`logs/t1-prep-at4-*.txt`.

| | A-T3 (§10.3) | A-T4 |
|---|---|---|
| tables | 4 | **6** (`CB`, `HDR` added; CODE / FUNC common mains 1 → 133 / 1 → 5 columns) |
| pinned heights | `[(2,4),(7,128),(5,32),(2,4)]` | `[(2,4),(7,128),(9,512),(4,16),(5,32),(2,4)]` |
| proof | 469,779 B | **488,409 B** (+18,630 B) |
| prove, verify, peak RSS | 31.1 s, 13–14 ms, 7.7 GB | **26.1 s, 12 ms, 7.7 GB** |
| soundness | 268.2 bits | **268.2 bits** (logup 324.4, proximity 295.1, query 268.2) |
| pre-check of the honest trace | – | every constraint of every table and every bus balanced |
| cached CODE / FUNC roots | = both A-T2 segment leaves' | **unchanged**: = A-T3's = both segment leaves' (`prepleafverify` R1) |
| lane D format | `m8-import` OK | `m8-import` OK: `M8_TEMPLATE_PROVED wasm_prep bytes=488409 … bits=268.2`; the 18-limb `cached` cells = `wasm0`'s and `wasm1`'s |

* vk sha256 `1cd98087…486d36`; lane D's `INFO.json` vk sha256 `7c2a48e1…579467`.
* The AIR JSON the prover ran is the one `wasmbase-tool airPrep` prints from the final Lean
  (byte-identical).
* Paths: `/data/illia/nearproof-deps/e2e-laneA/at4/prep/` (`leaf/`, `m8-tmpl/prep/`,
  `airPrep.json`, `prep-template.json`).

### 11.4 Mutant battery

**`preptamper`: 19/19 rejected** (`logs/t1-prep-at4-tamper.txt`). The battery is A-T3's 14, plus
five A-T4 mutants that must be rejected **in-circuit**: the pre-check fails, and the proof fails in
the prover or verifier, not at R1.

| mutant | rejected by |
|---|---|
| **another program's records: `progB`** (d3tiny with `i64.gt_u` → `i64.lt_u`; records from `wasmbase-tool prepM2`, eligible) with d3tiny's bytes | **in-circuit**: CODE row 7, `op = byte` (0x54 ≠ 0x56) |
| **another program's records: `progC`** (the constant 60000 → 60001) | **in-circuit**: CODE row 6, `x0 = limb 0` of the decoded `i64.const` |
| the `i64.const` immediate of CODE row 6 + 1 | **in-circuit** (same constraint) |
| the FUNC row-0 offset + 1 | **in-circuit**: `off₀ = 0` |
| a CODE padding row ≠ the last record | **in-circuit**: the `padRep` copy constraint |
| code records out of pc order (A-T3: R1 only) | now **in-circuit**: the pc / decode constraints |
| swapped code root (A-T3: R1 only) | now **in-circuit** |
| wrong FUNC charge (A-T3: R1 only) | now in-circuit, but through the FUNC padding copy: the charge itself is a `StaticCert` field |
| wrong code record: CODE row 3's op + 1 (row 3 is a `call`) | **R1 only**: a call's opcode (host / internal / unchipped) is a `StaticCert` field. This is the residual, shown on purpose |
| wrong code byte, wrong hash, wrong length | bus 211 / `CB`'s `len` (pre-check and prover) |
| natural tight heights, saved-file mutants, another code's segment leaves | as in A-T3 |

The two `progB` / `progC` preps are at `/data/illia/nearproof-deps/e2e-laneA/at4/other/`
(`run_prep.sh` passes them via `PREP_OTHER`).

### 11.5 The `sh_len` finding, stated

`ShaAir.HashLenLink tr t` is the precise obligation: on every digest row with `Dmult = 1`,
`sh_len = Nd`. It is part of `HashInputLink`: the consumed bytes are the call's input, and there
are `len` of them. The AIR fix is to carry `Nd` in `callMsg` next to `sh_len`, as PREP's digest
message does. That changes the segment AIR's vk and lane D's WASM leaf program (`59b572a7…`), so it
is **not done here**. It belongs to the next segment-AIR revision.

### 11.6 Open

* **`PrepDecodeSound` beyond the byte-read layer.** Not yet proved: the `busCB` permutation with
  the SHA byte slots (CB row `i` holds `m[i]`, from the classical frame contract); the HDR induction (HDR row `r` = `walk m r`); the CODE window decode (= `decInstr`); and the layout. All
  are row facts and bus balances of the kind `prep_sha_sound` uses. The AIR they are about runs on
  T1 (§11.3). This is the largest remaining Lean item of PREP.
* **`StaticCert`.** The static analysis in-circuit: heights from the operand-stack transitions
  and a label stack; block fees from `gasTable`'s metering; control targets from block matching;
  call targets and host ids from the closure and import names; FUNC's `np`/`nl`/charge/prologue/
  mask. With it, `RecordsCert` would rest on the AIR and `DecFaithfulAt` alone.
* **`DecFaithfulAt` for all codes.** A general proof that the reference walk/decoder agree with
  the spec's parser on accepted modules. Today it is decided per code (d3tiny). The decoder's
  completeness limits: the AIR rejects LEBs whose high groups are non-zero (indices ≥ 2^21, sizes and
  offsets ≥ 2^28), multi-byte alignment LEBs, and instructions outside the 13 classes (`nop`,
  `br_table`, `call_indirect`, floats, bulk memory).
* `PrepRest`, PREP's error branches, `CodeOK`/`FuncOK` from S3, and lane D's tree-spec insertion are
  unchanged from §10.4.


## 12. Milestone A-T5 (2026-11-25): the next segment-AIR revision

Lane I's I-2b chain (`docs/zk-formal/E2E-T1-CRITICAL-PATH.md` §2) left lane A three items: the
halting segment's out-record (finding I2b-2), `gasLeft` (M11i) and the stack budget as bound
fields, and the `sha256` length link. All three are done. `S`, `claimDigest` and the checker are
unchanged, and nothing here needs them changed (stop rule not triggered). Lean: `WasmBase
wasmbase-tool` builds (769 jobs) and `spec/lean/v3` builds (459 jobs) after merging main
(`38c3262cc`, lane G G-5). Standard axioms only; no `sorry`, `native_decide` or `axiom`.

### 12.1 The AIR change [K][M]

**Public values 108–116** (`Seg.numPub` 105 → 117; 105–107 stay `wasmBaseSegAirG`'s):

| publics | meaning | constraint |
|---|---|---|
| 108, 109 `rem_lo`, `rem_hi` | the out-cut's stack budget `[rem mod 2^16, rem / 2^16]` | `CUTO`: `k5·(F₃ − rem_lo)`, `k5·(F₄ − rem_hi)` on the (one) space-5 row |
| 110–113 `g_out` | the spec's gas register `s.gas.g` at the out-cut, four 16-bit limbs | `SEGB`'s gas gadget |
| 114–116 `R` | the bytes of `regularOpCost` | the wrapper pins them to the template's constant (T1: 822,756) |

**SEGB's gas gadget** (`SegAir.lean`, `Seg.Segb.gas*`): 30 bit columns for `d = S_out − S_seg,out`
(bytes `δ₀ δ₁ δ₂`, 6-bit `δ₃`, so `d < 2^30 < P`), 33 bit columns for three 11-bit carries, and per
16-bit limb `k`: `gₖ + Uₖ + c_{k−1} = Bₖ + 2^16·cₖ`, where `Uₖ` collects the byte products `ρᵢδₘ`
of weight `2^{16k}` and `2^{16k+8}`. Every side of a limb equation is `< 2^28`, so the equations hold
over the naturals and sum to `g_out + R·d = segb_out`. All four `SEGB` rows repeat the gadget's
columns, so the 68 new constraints need no selector and have degree 2. SEGB grows from 4 to 67
columns; no table gains an interaction.

**Lean [K] (`Main/SegGasRem.lean`):**
* `segb_gas_sound`: from `HoldsXS` and the wrapper's range checks `GasPubOK` (limbs `< 2^16`, bytes
  `< 2^8`) and `S_seg,out ≤ S_out`: `gOutN + ropN·(S_out − S_seg,out) = gbOutN`.
* `cuto_rem_sound`: if CUTO's hashed list is `cutView X s`, then `remN pub = s.stackRem`. The view
  has exactly one space-5 message (`budMsg s.stackRem`); its CUTO row has `k5 = 1`
  (`cuto_k5_of_five`, through `cuto_kL_lookupS`).
* `Cuti.seg_cutoView_AMP`: a cut segment's CUTO list is the view of its successor state.

### 12.2 `gasLeft` in the view and the mid-call template [K]

* `WasmView.airBnd.gasLeft := s.gas.g`. `blank` now zeroes `gas.g` (m6 §6.2), so the remainder
  digest `vmCtxDigest` no longer moves with the gas register. `InDom.lt64` gains `s.gas.g < 2^64`
  (from `RelW`: `g ≤ segb < 2^64`, `SegDom.seg_inDom`). `blank_inj` and `wasmBnd_binding` take
  `gas.g` from `gasLeft`.
* `TmplWasm.WOut`: `gas : w.gasLeft = gOutN pub` (was the interim `= 0`), `gok : GasPubOK pub`,
  `rem : w.stackRem = remN pub`.
* `RestOK` is now only the remainder digest plus the **gas-thread pin**
  `sg (t_out + 1) = (S_seg,out, segb_out)`. Why the pin stays named: the AIR binds the public out
  gas register to the channel's last space-7 message (SEGB's receive; segtamper "S_seg_out+1 with
  the gadget re-solved" is rejected by the CH bus), but `RelW` does not interpret space-7 messages,
  so the ghost thread `sg` is not tied to them.
* New `WasmHolds.rop : ropN pub = X.R` (named, static): the wrapper checks the `R` bytes against the
  template constant; the template applies to calls with that `regularOpCost`.
* `wasm_core` derives `wo.stackRem = sN.stackRem` and `wo.gasLeft = sN.gas.g` from the AIR. The
  non-vacuity results (`leafW_honest`, `restOK_honest`, `wasmHolds_honest`, `wasmHoldsC_honest`)
  take the honest publics as hypotheses.

### 12.3 The halting segment: the fin out-record (finding I2b-2) [K]

The configuration after the last segment is not an AIR state. `.ent p .method r m`, with `r` the
terminal result, takes one `cstep` to `.fin (afterMethod (entPost r))`, whose record is
`fbBnd (q, .fin r')`: every counter is 0 and every digest is `bdigest []`, except `vmCtxDigest`.
Lane F's resume leaf reads exactly this record.

* `LeafWF`: the halting wrapper. Its in-checks are `WIn` and `n ≤ fuel_in`; it checks the status
  `halted ∈ {1, 2}`; the out-record is `WOutFin` (the fin record's constant fields).
* `WasmHoldsF` = `LeafWF` ∧ `SegPremHMP` (the halting segment's premises, `SegCallSigma`) ∧
  `StaticOK` ∧ `meth : k = .method` ∧ `win` ∧ `CutSeed` ∧ `FinRest`. `FinRest` is the named
  `vmCtxDigest` of the call's result, the analogue of `RestOK`'s.
* **`wasm_fin_core`**: an opened in-record steps by `CSteps` to
  `.fin (afterMethod (entPost (step s')))` at digest `d'`. The steps are the segment's `n − 1`
  steps, the terminal step (`seg_sound_haltσ_mp`) and the exit (`csteps_exit`).
* **`wasm_relC_fin`** / `segSoundWasmFinRelC_of`: lane E's store-canonical `TmplRelC`. The result
  is canonical (`afterMethod_setRun`, `entPost_setSt`, `sync_setSt`: lane E's `join/CanonH2.lean`
  lemmas, restated in the default build).
* `airsWF` (`WTr ⊕ WTr`) with `segSoundWasmRelC_airsWF` gives cut and halting leaves in one Wasm
  kind. Non-vacuity: `leafWF_honest`, `finRest_honest`.
* Natively, `segleaf` writes `wasm_fields.out_record = "fin"` for the halting segment. It also writes
  `stack_rem_out`, `gas_left_out` and `regular_op_cost`. `segleafverify` checks that only the last
  segment halts and that the record kind matches.

### 12.4 `HashLenLink` [K][M]

The segment AIR has no SHA-256 table: a `sha256` call there is answered through the σ-pinned host
contract. A-T4 §11.5 said otherwise, and that was wrong. The link belongs to `wasmBaseHashAir`:

* `Sha.callMsgL = [ts, hid, sh_len, ptr, reg, Nd, 0, 0]` is received on the digest row.
* `HOSTO` sends `[ts, hid, a0, a1, a2, elen, 0, 0]`, with the new witness `elen` constrained by
  `(a0 − (2^64 − 1))·(elen − a0) = 0`.
* `Dmult` is a bit (`cDmultB`).
* **Finding:** A-T4's `HashLenLink` (`sh_len = Nd`) is false for honest traces on `memOrRegH`'s
  register branch (`len = u64Bound − 1`): the KAT `sharegkat` failed the bus pre-check. It is
  restated as `sh_len = Nd ∨ sh_len = 2^64 − 1`. Binding the register's length is the join
  obligation (stated).
* **`ShaLenSound.hashLenLink_of_holds`**: `Holds (wasmBaseHashAir nloc ngl) → HashLenLink tr 26`.
  The proof goes through the bus-211 occurrences (`occ211`), the bit counts, the balance, and the
  constraint on the `HOSTO` sender row.
* KAT: 98/98 (`run_kat.sh`: Python reference = Lean spec = Rust trace + AIR pre-check), including
  the SHA programs.

### 12.5 T1's two Wasm leaves re-proved [M]

Run as `run_leaf.sh … 13 1 24`: stack prover, base configuration, 8 threads, in a 12 GB capped
scope (§12.7). Logs: `logs/t1-leaf-at5*.txt`, `logs/t1-segtamper-at5-seg{0,1}.txt`.

| | A-T2 (§9.1) | A-T5 |
|---|---|---|
| seg 0 / seg 1 proof | 554,709 / 553,071 B | **557,517 / 556,887 B** |
| prove, verify, peak RSS | 25.7 / 28.3 s, 17 / 17 ms, 8.2 GB | 26.9 / 25.6 s, 18 / 17 ms, 8.2 GB |
| soundness, queries | 268.2 bits, [100, 71, 45, 33] | same |
| publics | 105 | 117 |
| vk sha256 | `b1eed0ca…` | `4e469b45…b7b9d2` (lane D `INFO.json`: `0f88f4ad…8518ec72`) |
| heights | pinned, equal across segments | pinned, equal (lane D `m8-import`: equal heights and vk, so one WASM leaf program) |
| `segcheck` K = 1 … 26 | 26/26 | 26/26 |

**Against lane I's chain** (`t1/chain.py plan`, `leaf_table`, SAVED → A-T5 leaves): **every Wasm
field equal, every digest equal.**
* seg 0: `h(c4) = e90f4a94…` → `h(c5) = b28bfa13…`. The `gasLeft` public is 53,990,571,634,314 and
  `stackRem` is 262,032.
* seg 1: `b28bfa13…` → `h(c6) = b3135387…`. The out-record is the fin record.
* `vmCtxDigest` and `fuel` are still placeholders shared with the chain.
* PREP (A-T4, unchanged): its CODE/FUNC roots are still the segments' (R1).

**Mutants.**
* `leaf_tamper.sh`: **21/21 rejected**. That is A-T2's 14 plus the publics 108, 109, 110, 113 and
  114 edited, and the out-record kind swapped on either segment.
* `segtamper` (in-circuit; each case proved and verified): seg 0 **57/57 rejected**. The new cases
  are `g_out` limbs, an `R` byte, `S_seg,out`, `rem_lo` / `rem_hi`, the gadget bits `gd0` / `gc0`,
  and the gas register forged with the gadget re-solved (rejected by the CH bus).
* seg 1: **56/57**. The accepted case is "`R` byte + 1, rows honest": in the halting segment
  `d = S_out − S_seg,out = 0` (the last host call re-synchronised the register), so `R` does not
  enter the gadget. The wrapper's check `ropN = R_t` rejects it (`leaf_tamper` "[114] + 1").

Paths: `/data/illia/nearproof-deps/e2e-laneA/at5/leaf-k13/leaf/` (proofs, vk, pubs, manifest) and
lane D's imported form `/data/illia/nearproof-deps/e2e-laneA/at5/m8-tmpl/wasm{0,1}/`.

### 12.6 Not done

* **PREP's `.pre` / `.ent` records (c3 → c4), item 4:** not cheap. The `.ent` record's
  `framesDigest` / `memRoot` of the entry state would need PREP to hash the entry view (a CUTO-like
  stream plus a Merkle root), and `B_in` / `B_out` as whole records need in-circuit `BndRec`
  hashing. PREP stays as in A-T4: the code hash and the CODE/FUNC roots.
* `vmCtxDigest` and `fuel` as publics; the 42-B packing of the CODE/FUNC commitment; lane D's tree
  run over the A-T5 leaves (the leaf program root was not re-measured).
* The gas-thread pin (§12.2) and `FinRest` are named.

### 12.7 Operations

Lane D's M8 tree (~29 GB) and a lane G Lean job (~14.5 GB) kept `zkbuild.slice` above its
`MemoryHigh` (40 GB) for this whole milestone: memory-pressure stall ~75 %, every job in the slice at
~5 % CPU, lane D included. A one-second Lean module did not finish in 30 minutes. So this
milestone's jobs ran in their own capped scopes outside the slice
(`systemd-run --user --scope -p MemoryMax=… -p MemorySwapMax=0`, OOM-first). Caps: Lean and cargo
at 5 GB, the two leaf proofs and the mutant battery at 12 GB (8 threads). The host had ≥ 60 GB
available throughout.
