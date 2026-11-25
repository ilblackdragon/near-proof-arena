# T1 critical path to M10 (single tracker)

Status: **lane I, milestone I-2, 2026-11-21**, measured on main `1461c97f6` (lane E M11h merged).
Plan: [`E2E-GENERAL-CHUNK-PLAN.md`](E2E-GENERAL-CHUNK-PLAN.md) §3 (interface; §3.4.1 canonical `S`,
§3.4.2 accepted mutants, §3.5 per-template obligations), §4 (M10), §5.0.1 (wrap interface, leaf
requirements). Driver: `research/near-compression/e2e-general/t1/` (`run_t1.sh`, `t1.py`,
`stmt.py`, `bndrec.py`, `lean/StmtEval.lean`, `test_t1.py`). Labels: **[M]** measured by the I-2
driver this session (run `e2e-t1/run4`), **[L]** measured by the owning lane (cited), **[K]**
kernel-checked by lane E, **[S]** design only. Nothing under `spec/` changed (checker sha256
`644495ff…a9ae3`).

**M10 exit test.** T1 = `d3c8/d3/02-h10196-s3`: one ZK proof whose verifier, given only the public
statement `S` (chunk-header outputs + trusted facts; section B private, D-2), accepts T1 and
rejects ≥ 50 statement mutants.

## 1. T1 as the driver sees it [M]

| item | value |
|---|---|
| Lean checker `--tier allFeatures` | `accept`; self-check 4/4; **FinalOut: 14/14 header output fields equal the run's outputs** (`finalout.json`) |
| statement `S` | lane E's canonical encoding (plan §3.4.1, `E2E/StmtEnc.lean`): `S = stmtPre ‖ 00 00 00 00 ‖ stmtPost` = **1,007 B** (stmtPre 416 B, stmtPost 587 B); section B **4,967 B** private (2 blocks); `claimDigest = bdigest(S)` = `bb5aad11ba6ba32d…9e4e299f2f01`. **Byte for byte equal** to a Lean evaluation of `PublicStmt.encode` / `claimDigest` / `stmtPre` / `stmtPost` on T1's claim bytes (`lean/StmtEval.lean`, `lake env lean --run`; Lean also reports `wf`, `encode_splice` and `decode ∘ encode` true on the input) and to the kernel-evaluated `t1_S_len` / `t1_claimDigest` [K]. I-1's `040290778c…` (1,003 B, no vector count) is retired |
| `BndRec` codec | `bndrec.py` = Lean `BndRec.encode` / `bdigest` / `decode` **byte for byte** on all 9 records of the plan below (408 B out of a call, 784 B in a call) and on the self-test records (`bndrec.lean_check`: generated Lean literals, evaluated with lane E's definitions) |
| run | 2 receipt outcomes (s5a00, gas 568,551,750,000; s5k210.s2a00 FunctionCall, gas 1,009,188,008,301); `gasUsed` 1,577,739,758,301 = Σ outcomes; 4 outgoing receipts; 10 state changes; `balanceBurnt` 0; no transactions |
| Wasm | 1 call: `d3tiny` (`8152bed2…`, 345 B) `run("again")`, 54 Tgas prepaid, **26 steps**, burnt 121,110,620,829; host calls `input`, `register_len`, `read_register`, `storage_write` (evicted: returns 1, old value into register 1), `log_utf8`, `value_return`. Lean tape and clean-room checker agree |
| mutants (`t1.py mutants`) | 92 distinct statements (+41 witness-consistent runs). **59 false** (rejected with T1's section B and witness); **33 true** — explained field by field in **plan §3.4.2** (unread by the relation, as in nearcore, or read only on paths T1 does not take; `height_created` is the owner finding). Binding negatives only, §3. Every decodable mutant's `S`/`claimDigest` equals the Lean evaluation |

## 2. The segment plan: lane I's 7 segments on `Templates.lean`

Lane E's T1 system (`E2E/Templates.lean`, plan §3.5) has five templates. Every `CM` run factors
into them (`cm_decomp`): `INIT`, then per engine step either one `state` segment (no VM call) or
`rt` enter, `wasm` per call, `rt` next / resume, then `final`. T1's honest chain (`t1_honest_chain`)
is therefore **INIT, STATE, rt(enter), WASM, rt(resume), STATE, FINAL**. I-1's plan maps onto it:

| I-1 segment | template (lane, Lean premise) | T1 content |
|---|---|---|
| INTAKE | **INIT** (G, `SegSoundInit`) | `init cb wb → eng I start` (one `CM.step`) |
| STATE(r0) | **STATE** (B, `SegSoundState`) | every VM-free engine step up to receipt 1's step (incl. receipt 0, s5a00) |
| STATE(r1 up to VM call) | **RT enter** (F, `SegSoundRt`) | `eng I c → call I c [] q .pre` |
| WASM(0,13], WASM(13,26] | **WASM** (A, `SegSoundWasm`) | `CSteps` of the call; cuts anywhere (`MWasm`), so the driver's k = 13 gives 2 WASM leaves (k = 26: one) |
| STATE(r1 resume) | **RT resume** (F) | the whole receipt step with the VM answered from the tape (actions, gas, refund, outcome) |
| (folded into FINAL in I-1) | **STATE** (B) | VM-free engine steps after receipt 1, to `eng I ⟨done out⟩` |
| FINAL | **FINAL** (G, `SegSoundFinal`) | `eng done → fin → done H o`, `headerOk` |

At k = 13 the driver's plan is 8 segments (`plan.json`): INIT / STATE / RT enter / WASM / WASM /
RT resume / STATE / FINAL; the digest chain `d_out(k) = d_in(k+1)` holds. **Owner change from I-1:**
INIT and FINAL are lane G's (Templates.lean), the receipt step is lane F's, STATE is lane B's.

**Which `BndRec` fields are real today** (`plan.json` `provenance`):

| field | source | status |
|---|---|---|
| `claimDigest` | `bdigest(S)`, Lean-checked | **real** |
| `phase`, `receiptIdx`, `inCall`, `gasUsed`, `gasBurnt`, `compute`, `rPrepaid`, `rBurnt`, `rUsed` | the Lean run's outcomes (clear fields) | **real** |
| `t` | lane A's in-call clock from the segment publics | **real** in a call |
| `wasm.pc, sp, framesDigest, globalsDigest, registersDigest, memRoot, memPages, promisesDigest` | lane A segment public values through `WasmView.airBnd` (`ctxDigest[:42]`, `memRoot[:42]`, `nblk/64`, `bdigest []`) | **real** at every WASM cut |
| `wasm.stackRem, fuel, vmCtxDigest, codeRoot, funcRoot` | not in lane A's public values (`codeRoot/funcRoot` are the proof's CODE/FUNC commitments; A-T3: the PREP leaf produces the same roots from the code hash, and `.pre`'s `codeRoot = SHA-256(code) ‖ 0^10`) | placeholder (`codeRoot/funcRoot`: produced by PREP, decoder certificate open) |
| `stRoot` | lane B's `StCommit` circuit form with M5b's public `trie` (= prev_state_root) and `wsLen`; `ws` (RCH root) and `rest` are not public | **partial** |
| `ctxRoot`, `outcomeAcc`, `outRcptAcc`, `proposalsAcc`, `bwAcc`, `vmAcc`, `balanceBurnt`, `blockIdx`, `actionIdx` | no component (F, G, A/E) | placeholder 0^42 |

**Clear-field convention (lane E M12, plan §3.5 "M12"; supersedes the provenance column for the
clear fields).** `ViewE.clearE`: `receiptIdx = |outcomes|`, `gasUsed = gasBurnt = rs.gas`,
`balanceBurnt = rs.txBurnt`, `compute = rs.compute` at engine cuts (those of the starting engine
state inside a call, plus `rPrepaid = prepaid gas`); at `done`: `gasUsed`, `balanceBurnt` from the
header, the rest `0`; `claimDigest = bdigest []`, `blockIdx = actionIdx = t = rBurnt = rUsed = 0`
everywhere. The driver's current `claimDigest` (real digest), in-call `t` (lane A's clock) and
resume-output `rBurnt`/`rUsed`/`receiptIdx` must follow it.

Consequence: the two STATE segments and RT resume → STATE have equal in/out digests today (the
fields that change there are placeholders). **Seam found:** RT enter ends at `call … .pre`, whose
`wasmD` is lane A's fallback record (`fbBnd`); lane A's segment 0 starts at the entry state
(`airBnd`). The `.pre → .ent` step (PREP, C7) is in no template's AIR; the plan puts segment 0's
entry boundary at the RT enter cut.

## 3. Components: status, interface, owner

Status: **PASS** = proves/verifies on T1 today and its public boundary equals the Lean run's;
**BLOCKED** = exists, fails on T1; **MISSING** = no code.

| # | component | owner | status on T1 | interface it must expose |
|---|---|---|---|---|
| C0 | **statement** `S`, `claimDigest`, `B_0 = Init(claimDigest)` | E (codec, done [K]) + D (wrap) + I | **PASS** [M]: canonical `S` (§3.4.1) = Lean evaluation = kernel values; `BndRec` = Lean on all cuts | wrap: `D_wrap = H(tag_wrap, SHA-384(S))`; `WrapInitSound`: `B_0` = digest of `init (assemble s.ci secB s.secC) w` |
| C1 | **INIT** (claim + witness decode, intake record, receipts) | **G** | **MISSING** | `SegSoundInit`: `B_0` (phase 0) → `eng I start` (phase 1), `ctxRoot = ctxD(I)`; witness `S` hashed in-circuit to `claimDigest` |
| C2 | **receipt step** (RT enter / next / resume) | **F** | **PASS as leaves** [L] (lane F F-3, M11i record shape: `engF` 450 B / `callF` 834 B): enter **87,739 B** (S2 `codeRoot = code hash ‖ 0^10`, lane A's `.pre` record), resume **430,143 B**, lane D's base configuration, both imported by lane D's `m8-import`; mutants 10/10 + 11/11. Digests ≠ this driver's run4 plan (pre-M11i: the plan needs the singleton `outRcptAcc`, `gasLeft`, and the `.pre` record at the enter cut, PREP after it). Lean [K]: **enter discharged** in lane E's relative store-canonical form from the circuit (`EnterC.enter_relC`, non-vacuity on T1's leaf `T1Enter.t1_enter_nonvac`), under view laws + named checks (README §F-3); resume not (F3-1: carried `stRoot`/accumulators — needs the lane B split, accumulator appends, `estepO` composition); F3-2 clear-field convention open | `SegRelRt` / `TmplSoundRel8C .rt`: `enter` (start `q` at a non-final `eng I c`), `resume` (`estepO (strictO (K ++ [(q, r)]))`): actions, gas/compute, refund, outcome, `vmAcc` |
| C3 | **Wasm segments** `wasmBaseSegAirMP` for `d3tiny.run` | A | **PASS** [M] (was BLOCKED in I-1): lane A's M6 bus-214 multi-group fix (`da5844114`) fixed the HOSTB 314 vs key 58 failure. `segcheck` at k = 13 (2 segments) and k = 26 (1): every pre-check OK, chained. **Boundary = Lean run 16/16** (entry pc, `t`, `S`/`sb`/`cid` = 0, gas `g0` = Lean prep, memory size / `nblk` / depth, entry `memRoot` = Merkle root of the Lean prep image, `t_out` per cut, `halted` only last, chain, final gas = Lean `gFinal` = last host call's `gAfter`, final `memRoot` = image + the Lean tape's `read_register` write). **Lean `HoldsX ∧ ChipIf` SATISFIED** on both dumped segments (`wasmbase-tool holds`, `checkSeg_sound`). Proofs (k = 13, `segprove`, statement check incl. CODE/FUNC roots): 1,328,433 B + 1,334,481 B, 268.2-bit, prove 47.4 + 45.8 s, verify 58 / 91 ms (8 threads, host load ~33; 37.9 + 46.4 s on a quieter run) | 105 public values → `WasmBnd` by `WasmView.airBnd` (§2); missing: `stackRem`, `fuel`, `vmCtxDigest`, `codeRoot/funcRoot` as public values; HOSTO still an oracle (C4); `.pre → .ent` (C7) |
| C3' | Wasm whole call (`wasmBaseM2Air`, no boundary) | A | **PASS** [M]: return `again`, log `tiny`, final gas equal; proof 1,474,032 B, 268.2-bit, prove 30.8 s under load (15.7 s in I-1), verify 42 ms. Reference only | – |
| C4 | **host ↔ state join (M6)** | A + B | **MISSING; message-level join measured** (lane B B-T2: lane A's 8 `storage_write` messages fed into `m5tSegH` — HOSTR and the 5 value bytes (wire 314) balance, the key does not: lane A sends the contract key `t`, the state rows hash the trie key `0x09‖receiver‖,‖t` (finding B2-4; control with the trie key balances). Remaining: `STBH` prefix run from the call context, one prover for both AIRs, HOSTR answer (`EVK`), reads; lane A: `HostIf`, `seg_sound_hostIf_air` [L]) | STATE rows answer `HOSTQ`/`HOSTR`/`HOSTB` in the WASM segment (T1: `storage_write` evicted value → register 1, `input`, `log_utf8`, `value_return`); HOSTO removed; σ in `vmCtxDigest` |
| C5 | **state**: working set, trie, FINAL MPT root (M5b) | B | **Lean (B-T2) [K]:** lane B's half of the STATE / RT split (`StHalfC.stHalf_inst'`, `split_sound_relC_rel`; `ApplyFaithful` replaced by the relational form, finding B2-1), `ws_moves_seg` (circuit tree = view tree), position check `rtPos`; view leaf-digest fix B2-2; T1 non-vacuity in the kernel (`t1_ws_nonvac`: view root of T1's leaves = the leaf's public `R_in`/`R_out`); `stRoot` interface for lane F's resume (`STMQ`/`STMA`, `STC` not built). **PASS as one proof** [M]: post root = Lean `stateRoot` = header `1db48e38…`; **public boundary 6/6**: `pubs` prev_state_root = TAPE `(0, root)`, TAPE `(10, root)` = Lean `stateRoot` and Lean's 10 state changes, prev_state_root and `wsLen` 17 = clean-room checker (Lean prints neither); proof 1,476,227 B, 268.2-bit, prove 110 s under host load ~33 (58 s in I-1). Not split into STATE leaves; host requests from the public `HTAPE` | split at the template cuts into STATE leaves (`SegSoundState`, VM-free engine steps) exposing `stRoot = stD(StV)` (`StCommit`: `ws` = RCH root, `trie`, `wsLen`, `idx`, `rest`) as public values; INIT/FINAL parts handed to G |
| C6 | **FINAL / FinalOut** (outcome root, outgoing receipts root, congestion, bandwidth requests, RS encoding, tx root, gas, balance, proposals) | **G** | **MISSING** (reference: `finalout.json`, 14/14) | `SegSoundFinal`: from `eng I ⟨done out⟩` to `done H o`; `WrapFinalSound`: `FinalOutPub s`; consumes the accumulators; state root from C5 |
| C7 | **PREP** (`.pre → .ent`): code hash → CODE/FUNC | A | **PASS as a leaf, records not yet bound** (lane A A-T3, `a-t1/README.md` §10, after lane E's S1–S3). `prepAir` (PHDR + SHA-256 over the code bytes + the segment AIR's CODE/FUNC tables): T1 leaf 469,779 B, 268.2 bits, 31 s, pinned heights, lane D `m8-import` OK; cached CODE/FUNC roots = both segment leaves' [M]; mutants 14/14 rejected. Lean: `PrepSound.prep_sha_sound` (public hash = SHA-256 of the hashed bytes), `TmplPrep.segSoundWasmPrepRelC_of` (`TmplRelC`, Wasm kind = segments ⊕ PREP) [K]. **Open:** the decoder certificate (`RecordsCert`: records = `checkModuleM2 (prepare code)`; today only the R1 comparison binds PREP to the segments, not to the code), the entry record (`PrepRest`), the tree-spec insertion (D) | per code (T1: 1 blob, 345 B): SHA-256(code) = the account's code hash, `checkModuleM2`, CODE/FUNC roots = `wasm.codeRoot/funcRoot` |
| C8 | **leaf templates with pinned shapes** | A, B, F, G + D | **Lane A done** (A-T2: log *and* tight heights pinned; T1's two Wasm leaves give one lane D leaf program, `59b572a7…` [L]); lane B, F done as leaves; G open; leaf statement `[phase, h(B)]` fixed (§3.4.1) | per template: one parameter set, height classes, proof + vk saved, `build_seg_leaf` → `H9(...)` |
| C9 | **heterogeneous aggregation (M8)** | D | **MISSING for T1** (D0a base templates only [L]) | anchors over T1's 5 templates; 8 leaves → arity 4, depth 2 |
| C10 | **ZK wrap (M9)** | D | **MISSING for T1** (D0a wraps 328.8–330.4 KB [L]) | `[LEVEL_WRAP, D_wrap(S)]`, V_d from `S` alone; `WrapInitSound`, `WrapFinalSound` |
| C11 | **Lean `e2e_sound_t1`** | E | **stated, conditional** [K] (M12: clear-field convention F3-2 implemented, `ViewE.clearE`; split-leaf glue `E2E/Glue.lean`: STATE `state_sound_relC` from lane F's engine half + lane B's state half and `ApplyFaithfulS`, INIT `init_glue`, FINAL `final_glue`; per-lane table in plan §3.5 "M12"; **D-a – D-d** (plan §3.5 "Lane E D-a – D-d"): `R_0` committed at `start`, the finalize step a STATE leaf with IF-FINAL (`FinalizeAgree` proved in its precise form), the relational split with `W` = `stRoot` (`StateW.state_sound_stRoot`), an incremental `rest` (`RestI.encRestI`, binding), (H2) `CanonH2.cstep_canon`): `e2e_sound_t1` from `NvFaithfulE2E` + `WrapInitSound`/`WrapFinalSound` + the five `SegSound*`; **M11 non-vacuity on T1 done** (`t1_rel`, `t1_e2e_stmt`, `t1_honest_chain`; 27.1 GB kernel run) | per lane: discharge its `SegSound*` premise (A: `SegSoundWasm`, B: `SegSoundState`, F: `SegSoundRt`, G: `SegSoundInit`/`SegSoundFinal`), D: the wrap premises |

## 4. Statement mutants [M]

`t1.py mutants` changes one public field per mutant (sections A and C; section B never), re-splices
the original section B (`assemble_splice`), and runs the pinned Lean checker on every mutant claim.
Each `chunk_inner` mutant runs twice: with the original witness and with the witness's own copy of
the header patched ("+w"), so the rejection must come from the relation's checks.

* **92 distinct statements** (sha256 of the canonical `S` pairwise distinct, none equal to T1's);
  every decodable one's `S`/`claimDigest` equals the Lean `StmtEnc` evaluation.
* **59 false statements** (no variant accepted), covering every header output field and every
  trusted fact T1's run reads (`InvalidStateRoot`, `InvalidOutcomesProof`, `InvalidReceiptsProof`,
  `InvalidGasUsed`, `InvalidBalanceBurnt`, `InvalidGasLimit`, `InvalidCongestionInfo`,
  `InvalidBandwidthRequests`, `InvalidValidatorProposals`, `InvalidChunkEncodedMerkleRoot`,
  `InvalidChunkEncodedLength`, `InvalidTxRoot`, `InvalidChunkHeaderShardSplit`, `shard_id`,
  `prev_block_hash`; trusted facts: epoch id, epoch table, RS parameters, `epoch_start_after`,
  `tx_valid`, `genesis_chunk_extra`, `validator_update`, protocol version). M10's soundness
  negatives.
* **33 true statements** (accepted with T1's section B and witness): `chain_id`; the epoch
  record's height, layout byte, validator accounts and stakes, dropping a validator;
  `minimum_stake`; `chunk_inner.height_created` with the witness's header copy patched. **Plan
  §3.4.2** checks each against the spec and nearcore 2.13.4: none is a soundness gap for T1 (unread
  by the relation as in nearcore — `height_created`, the layout version byte — or read only on paths
  T1 does not take; section C is trusted). For M10 they are **binding negatives**: T1's proof must
  fail on them because `D_wrap` binds `S`. `height_created > height(prev block)` is an owner
  decision (checker change), not taken.

## 5. Blocking order

0. ~~C0 canonical `S` and leaf statement~~ (**done**: lane E §3.4.1 [K], driver = Lean [M]).
1. ~~C3 bus-214 fix~~ (**done**: lane A `da5844114`; T1's segments chain, prove and match the
   Lean run [M]).
2. **In parallel:**
   * C1 INIT + C6 FINAL (G): T1's intake and 14 FinalOut fields.
   * C2 receipt step (F): RT enter / resume for receipt 1.
   * C5 split into STATE leaves exposing `stRoot` (B).
   * C7 PREP for `d3tiny` (the `.pre → .ent` seam): leaf done (A-T3); decoder certificate open.
   * C3 public values (A): `stackRem`, `fuel`, `vmCtxDigest`, `codeRoot/funcRoot`.
3. **C4 M6 join** (A + B). Needs C2's rows and C5's `SREQ`/`HB`; replaces HOSTO and `HTAPE`.
4. **C8 pinned shapes and saved proofs** per template, base WHIR configuration.
5. **C9 + C10** (D). Leaf wrappers, a tree over T1's 8 leaves, a wrap with V_d over `S`.
6. **M10** (I). `run_t1.sh` fills every `BndRec` field from its component (today: §2's real
   fields) and checks every cut. Exit: `FinalVerify` accepts T1 and rejects the 59 false
   statements and the 33 binding negatives.
7. **C11** (E + each lane's `SegSound*`) alongside 2–6.

Critical path: 2 (G, F are new lanes, the longest items) → 3 → 4 → 5 → 6.

## 6. Reproduce

```sh
PROVE=1 MUTANTS=1 research/near-compression/e2e-general/t1/run_t1.sh /data/illia/nearproof-deps/e2e-t1/run4
python3 -m pytest -q research/near-compression/e2e-general/t1/test_t1.py
```

* Builds the lane A and lane B provers fresh from this tree into
  `/data/illia/nearproof-deps/e2e-t1/target-{wb,m5a}` (`NOBUILD=1` skips).
* Uses the main checkout's Lean tools (checker, `wasmbase-tool`, `m5a-tool`) and its v3 package's
  built oleans for the Lean evaluations (`lake env lean --run`, no build; scratch files
  `lean/StmtEval.lean` and the generated `OUT/lean-bnd/BndEval.lean` are outside every build).
* `wasmbase-tape` is not built on this host: T1's tape is read from lane A's cached M3 corpus tape
  and cross-checked against the clean-room checker.
* **Fails loudly**: every disagreement between a component's public boundary (or the driver's
  encodings) and the Lean run is printed as `MISMATCH [...]` on stderr, listed in `report.md`, and
  `run_t1.sh` exits 1 (`test_t1.py` checks this path).
* Writes `report.{md,json}`, `plan.json` (records, digests, provenance, seams), `statement.json`,
  `finalout.json`, `mutants.json`, per-component logs.
