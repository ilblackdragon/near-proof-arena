# Lane A milestone A-T1: T1's Wasm call end to end

Plan: `docs/zk-formal/E2E-GENERAL-CHUNK-PLAN.md` §4.2 (M10), tracker `docs/zk-formal/E2E-T1-CRITICAL-PATH.md`.
Labels: **[M]** measured, **[K]** kernel-checked Lean (standard axioms, no `sorry`), **[S]** stated / design.

T1 = `/data/illia/nearproof-deps/corpora/d3c8/d3/02-h10196-s3`: one FunctionCall to `d3tiny`
(code `8152bed2…`, 345 B), method `run`, input `again`, 26 Wasm steps, six host calls:
`input`, `register_len`, `read_register`, `storage_write` (existing key), `log_utf8`, `value_return`.

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

## 5. Item 5: HOST rows in lane B's bus shape — scope [S]

Lane B (m5a README §M5b) consumes `SREQ [ts, pr, seg, klen, kptr, vlen, vptr]` and
`HB [ts, pos, byte]`, with `pos` the **absolute** linear-memory address. Lane A's bus 210 today
carries `[ts, wire, dir, pos, byte]`, with `pos` relative to the group's `ptr`. The changes needed:
* HOSTB's state-side half (the `busHostB` interactions HOSTB keeps for `reg = 0`): send
  `HB [ts, ptr + pos, byte]` (`HostB.memAddr`, already a column expression) for request bytes. This
  also makes the **address** visible to the producer. Today the HOSTB `ptr` columns are not tied to
  the HOST row's pointer argument anywhere in the AIR, so read and write coverage (`HostAnsCov`,
  `ProducerObl.resp`) rest on the producer. With absolute addresses on the bus, lane B's STB rows
  check `base = kptr` (they already do on T1's tape: `HB (ts, base + j, b)`).
* HOST rows for `storage_write`/`storage_remove`: send `SREQ` with `pr` from `hid` (58 → 1,
  `storage_remove` → 0), `seg` from a public value, and the four argument words from the HOST
  argument limbs.
* The `HOSTO` stand-in and HOSTB's self-cancelling halves are dropped in the joined template. They
  stay in the standalone Wasm template.
To do: the Lean AIR (a new `Seg.HostBJ` variant, so the standalone template is unchanged), the
tracer, and a joined pre-check on T1 with lane B's STB/STW tables.
