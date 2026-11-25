# T1 critical path to M10 (single tracker)

Status: **lane I, milestone I-2, 2026-11-21; §2 regenerated 2026-11-25** (I-2b: the leaf chain
under lane E's M11i / M12 / M13 conventions, on main `5917c569c`: lanes A A-T4, B B-T3, E M13,
F F-4, G G-4 merged). Plan: [`E2E-GENERAL-CHUNK-PLAN.md`](E2E-GENERAL-CHUNK-PLAN.md) §3 (interface;
§3.4.1 canonical `S`, §3.4.2 accepted mutants, §3.5 per-template obligations), §4 (M10), §5.0.1
(wrap interface, leaf requirements). Driver: `research/near-compression/e2e-general/t1/`
(`run_t1.sh`, `t1.py`, `chain.py`, `stmt.py`, `bndrec.py`, `data/t1-inputs.json`,
`lean/StmtEval.lean`, `test_t1.py`). Labels: **[M]** measured by the I-2 driver (run
`e2e-t1/run4`; §2 from `chain.py plan`), **[L]** measured by the owning lane (cited), **[K]**
kernel-checked by lane E, **[S]** design only. Nothing under `spec/` changed (checker sha256
`644495ff…a9ae3`); nothing here changes `S`, `claimDigest` or the checker.

**M10 exit test.** T1 = `d3c8/d3/02-h10196-s3`: one ZK proof whose verifier, given only the public
statement `S` (chunk-header outputs + trusted facts; section B private, D-2), accepts T1 and
rejects ≥ 50 statement mutants.

## 1. T1 as the driver sees it [M]

| item | value |
|---|---|
| Lean checker `--tier allFeatures` | `accept`; self-check 4/4; **FinalOut: 14/14 header output fields equal the run's outputs** (`finalout.json`) |
| statement `S` | lane E's canonical encoding (plan §3.4.1, `E2E/StmtEnc.lean`): `S = stmtPre ‖ 00 00 00 00 ‖ stmtPost` = **1,007 B** (stmtPre 416 B, stmtPost 587 B); section B **4,967 B** private (2 blocks); `claimDigest = bdigest(S)` = `bb5aad11ba6ba32d…9e4e299f2f01`. **Byte for byte equal** to a Lean evaluation of `PublicStmt.encode` / `claimDigest` / `stmtPre` / `stmtPost` on T1's claim bytes (`lean/StmtEval.lean`, `lake env lean --run`; Lean also reports `wf`, `encode_splice` and `decode ∘ encode` true on the input) and to the kernel-evaluated `t1_S_len` / `t1_claimDigest` [K]. I-1's `040290778c…` (1,003 B, no vector count) is retired |
| `BndRec` codec | `bndrec.py` = Lean `BndRec.encode` / `bdigest` / `decode` **byte for byte** on all 11 cuts of §2 (408 B at `init` / `done`, 450 B engine, 834 B in a call; I-2: 9 records, pre-M11i) and on the self-test records (`bndrec.lean_check`: generated Lean literals, evaluated with lane E's definitions) |
| run | 2 receipt outcomes (s5a00, gas 568,551,750,000; s5k210.s2a00 FunctionCall, gas 1,009,188,008,301); `gasUsed` 1,577,739,758,301 = Σ outcomes; 4 outgoing receipts; 10 state changes; `balanceBurnt` 0; no transactions |
| Wasm | 1 call: `d3tiny` (`8152bed2…`, 345 B) `run("again")`, 54 Tgas prepaid, **26 steps**, burnt 121,110,620,829; host calls `input`, `register_len`, `read_register`, `storage_write` (evicted: returns 1, old value into register 1), `log_utf8`, `value_return`. Lean tape and clean-room checker agree |
| mutants (`t1.py mutants`) | 92 distinct statements (+41 witness-consistent runs). **59 false** (rejected with T1's section B and witness); **33 true** — explained field by field in **plan §3.4.2** (unread by the relation, as in nearcore, or read only on paths T1 does not take; `height_created` is the owner finding). Binding negatives only, §3. Every decodable mutant's `S`/`claimDigest` equals the Lean evaluation |

## 2. The leaf chain under the current boundary conventions (I-2b, 2026-11-25) [M]

`chain.py plan` (also step 5 of `t1.py run`) builds T1's cut records `c0 … c10` as lane E's view
`ViewE.viewE` defines them (`View.split`, `clearE`, `ctxDE`, `outDE`, `vmDE`; lane B's `stD`;
lane A's `wasmD`), with every convention adopted since I-2:

* **M11i**: `WasmBnd.gasLeft` (u64 after `fuel`); `outRcptAcc` = one chain (`[chainD enc rs]` in
  an engine / call state, `[]` at `init` / `done`); `B_0`: `ctxRoot = ctxD(.raw cb wb)` =
  `bdigest (0 ‖ u32 ℓ_B ‖ u32 |cb| ‖ cb ‖ wb)`, `stRoot = stD .none`, `outD .none = (bdigest [],
  [], bdigest [], bdigest [0])`, `vmAcc = bdigest []`, counters 0.
* **M12** (`clearE`): `claimDigest = bdigest []`, `blockIdx = actionIdx = t = 0` at every cut;
  counters carried (`start`: all 0); `rPrepaid` only inside the call; resume outputs
  `receiptIdx + 1`, `rPrepaid = rBurnt = rUsed = 0`; `done H o` carries `o.gasUsed` /
  `o.balanceBurnt`, the rest 0.
* **M13** (D-a – D-d): the `start` cut commits lane B's `R_0` (`stRoot` = `StCommit` with
  `ws = R_0`, tag 1); the finalize step is its own STATE leaf (`yields _ _ 0 → eng I ⟨done out⟩`,
  `stD` tag 3); `W` = the whole `stRoot`. **`rest`: lane E's `encRestI` is not adopted** by lane
  B's default instance or lane F's leaves (`STMQ`/`STMA` metas are stand-ins), so the driver keeps
  the current encoder with `rest = 0^42`.
* **S2 / A-T3**: the enter output is lane A's `.pre` record (`fbBnd`: counters 0, digests
  `bdigest []`, `codeRoot = SHA-256(code) ‖ 0^10`); **PREP after enter** (`.pre → .ent`); the
  call's last cut is lane A's `fbBnd (q, .fin r)`.
* **F-4**: accumulators are the Lean run's `chainD Ser.enc` (lane F's `m5t1-tool dump`, frozen in
  `data/t1-inputs.json`): one SHA-384 append per outcome / outgoing receipt.

**Cross-checks [M].** All 11 records = Lean `BndRec.encode` / `bdigest` / `decode` byte for byte
(`bndrec.lean_check`); the view constants = Lean evaluations of lane E's own definitions
(`chain.lean_consts`: `ViewE.rawPre` on T1's 5,970 + 8,764 bytes, `ViewE.u32` (big-endian),
`chainD id` of the 4 accumulator states, `bdigest []`, `bdigest [0/1/2]`); 0 convention violations
(`chain.check_conventions`); header `gasUsed` / `computeUsage` equal.

| cut | configuration | phase | receiptIdx | gasUsed | compute | rPrepaid | `h(B)` |
|---|---|---|---|---|---|---|---|
| c0 | `init cb wb` (`B_0`) | 0 | 0 | 0 | 0 | 0 | `ac01792e46679f5f…` |
| c1 | `eng I start` (commits `R_0`) | 1 | 0 | 0 | 0 | 0 | `4ae97236e9279de7…` |
| c2 | `eng I c` at receipt 1's step | 1 | 1 | 568,551,750,000 | 568,551,750,000 | 0 | `5da6ab41d6bb0112…` |
| c3 | `call I c [] q .pre` | 6 | 1 | 568,551,750,000 | 568,551,750,000 | 54 T | `adf08591c9b9994f…` |
| c4 | `call … (preConf q)` (`.ent`) | 6 | 1 | ″ | ″ | 54 T | `e90f4a94653ebfae…` |
| c5 | `call …` at t = 13 | 6 | 1 | ″ | ″ | 54 T | `b28bfa132ef88018…` |
| c6 | `call … (.fin r)` | 6 | 1 | ″ | ″ | 54 T | `b31353870481c2b5…` |
| c7 | `eng I c'` after receipt 1 | 1 | 2 | 1,577,739,758,301 | 1,732,463,022,301 | 0 | `afe47194b7e4566c…` |
| c8 | `eng I ⟨yields _ _ 0⟩` | 1 | 2 | ″ | ″ | 0 | `afe47194b7e4566c…` (= c7: the position is only in `rest`) |
| c9 | `eng I ⟨done out⟩` | 1 | 2 | ″ | ″ | 0 | `f7c8b2b65dc38957…` |
| c10 | `done H o` | 4 | 0 | 1,577,739,758,301 | 0 | 0 | `d15c24388312dbb7…` |

| # | leaf | lanes | in → out | `d_in` → `d_out` |
|---|---|---|---|---|
| 1 | INIT ⊕ IF (split leaf, joined by the `CLM` bytes and `PSR`) | G ⊕ B | c0 → c1 | `ac01792e` → `4ae97236` |
| 2 | STATE seg A (receipt 0, the 3 forwards; 8 of 10 changes) | B ⊕ F | c1 → c2 | `4ae97236` → `5da6ab41` |
| 3 | RT enter | F | c2 → c3 | `5da6ab41` → `adf08591` |
| 4 | PREP | A | c3 → c4 | `adf08591` → `e90f4a94` |
| 5 | WASM seg 0 (steps (0, 13]) | A | c4 → c5 | `e90f4a94` → `b28bfa13` |
| 6 | WASM seg 1 (steps (13, 26], halts) | A | c5 → c6 | `b28bfa13` → `b3135387` |
| 7 | RT resume (`STMQ`/`STMA` to lane B's `STC`, `ACC`) | F ⊕ B | c6 → c7 | `b3135387` → `afe47194` |
| 8 | STATE seg B (VM-free steps to `yields _ _ 0`; may be empty) | B ⊕ F | c7 → c8 | `afe47194` → `afe47194` |
| 9 | finalize (IF-FINAL, D-b) | B ⊕ F | c8 → c9 | `afe47194` → `f7c8b2b6` |
| 10 | FINAL | G ⊕ B | c9 → c10 | `f7c8b2b6` → `d15c2438` |

Every adjacent pair chains digest for digest (`chain.chain_ok`). **The records are the view's
wherever a component computes the field; the rest are `0^42` placeholders** (`chain.PLACEHOLDERS`):
`stD .none` (B), `stRoot.rest` everywhere and `stRoot.ws` at c2 (B, F, E), `ctxD (.intake I)` at
every engine / call cut (E: `Ser Intake`; G), `ctxD (.header H)` and `bdigest (Ser.enc o)` at done
(E: `Ser ChunkInner` / `Ser Outputs`; G), `wasm.vmCtxDigest` and `wasm.fuel` (A), the 42-B packing
of the cached CODE / FUNC commitment (A; the driver packs 5 × u64be + u16be). A placeholder is
the same at every cut where the view's value is a constant, so it hides no step; it hides the
fields listed.

### 2.1 Saved leaves against the chain [M] (`chain.leaf_table`)

Only the two `rt` leaves expose whole `BndRec`s (their public values are the encoded bytes); the
others expose components that lane D assembles into records (prototype regions, `tmp-laneD/m9b`).

| leaf (saved proof) | exposes | in / out vs the chain | why | who re-proves what |
|---|---|---|---|---|
| INIT, **G-5** (`e2e-m5d/g5/tmpl/init`) | `claimDigest` (leaf `ctx`), `ctxRoot(B_0)`, `prev_state_root` | **in ✓**: `ctxRoot` = `60498d85…` (big-endian), assembled `B_0` = **`h(c0)`** `ac01792e…`; out: not exposed (lane B's half) | I2b-1 resolved (G-5: `INI` hashes big-endian `u32`); `prev_state_root` = IF's ✓ | **B**: `B_1` (c1: `ctxD (.intake I)`, `R_0`) is INTAKE's half of the joined leaf (E: `Ser Intake`) |
| IF, B-T1b (`laneB-t1/t1b/T1S/if/out`) | prev / post roots, `wsLen`, `R_0`, `R_n`, #changes | ws parts ✓ (`R_0 = ca91c86e…`, `R_n = 2d2e132a…`, post = header, 17, 10) | no `stRoot` (tag, idx, `rest` not opened) | **B**: `STC` on the IF halves — the INTAKE half's `R_0` commitment (c1, D-a) and the FINAL half as the finalize leaf (D-b) |
| RT enter, F-3 (`e2e-m5t1/f3/enter-proof`) | `B_in` 450 B, `B_out` 834 B | `b850f1e5 → c320b92b` vs `5da6ab41 → adf08591`: **✗ / ✗** | pre-M12 record: real `claimDigest`; `outcomeAcc`, `outRcptAcc`, `proposalsAcc`, `bwAcc`, `vmAcc` = `0^42` (view: chains, `bdigest []`, `bdigest [1]`) | **F** re-proves enter from `plan.json` (2.4 s leaf). `stRoot` / `ctxRoot` placeholders shared with the chain |
| PREP, A-T4 (`e2e-laneA/at4/prep/leaf`) | code hash, `|code|`, cached CODE / FUNC | `.pre` `codeRoot` cells ✓; CODE / FUNC = both segments' (R1) ✓ | `B_in` / `B_out` not public: the rest of the `.pre` and `.ent` records is free | **A**: PREP's records (`PrepRest`), root packing; **D**: PREP between enter and WASM 0 (m9b has the older A-T3 PREP) |
| WASM seg 0, **A-T5** (`e2e-laneA/at5/leaf-k13/leaf/seg-0`) | 117 publics (A-T5: `stackRem` halves, `g_out` limbs, `R` bytes) + cached CODE / FUNC | **✓ / ✓**: `h(c4) = e90f4a94` → `h(c5) = b28bfa13`, digest for digest | `gasLeft` = the public `g_out` (SEGB's gas gadget), `stackRem` public (CUTO's budget row) | **A**: `vmCtxDigest`, `fuel` not public (placeholders shared with the chain); the 42-B packing |
| WASM seg 1, **A-T5** (`…/seg-1`) | same; out-record = the fin record | **✓ / ✓**: `b28bfa13` → `h(c6) = b3135387` | **I2b-2 closed (A-T5):** the halting leaf emits `fbBnd (q, .fin r)` (`TmplWasm.WasmHoldsF`, `wasm_fin_core`), the record lane F's resume reads | **A**: as seg 0 |
| RT resume, F-4 (`e2e-m5t1/f4/resume-proof`) | `B_in` 834 B, `B_out` 450 B | `3a3862e9 → 50500c19` vs `b3135387 → afe47194`: **✗ / ✗** | counters, `receiptIdx + 1`, accumulators, `vmAcc` ✓; but `claimDigest` real, **`t = 26`** (run4's in-call clock; M12: 0), `proposalsAcc` / `bwAcc` `0^42`, `B_in.wasm` = run4's halted `airBnd` (view: fin record), `stRoot` out = the `STC` stand-in | **F** re-proves resume from `plan.json`; **B**: `STC` answers `stRoot` |
| STATE seg, B-T1b (`laneB-t1/t1b/T1S/seg0/out`) | prev root, `wsLen`, `R_in`, `R_out` | `R_in = R_0` ✓, `R_out = R_n` ✓ | one segment over all 10 changes spans c1 → c9 across the call; no `stRoot` | **B**: split at the `rt` cuts (seg A ends after 8 changes, seg B starts after 10) and prove `m5tSegC` (`STC`, B-T3, not re-proved); **F**: STATE engine rows (none) |
| finalize | — | missing | no leaf | **B** (IF-FINAL half with `STC`) + **F** (engine rows `yields → done`) |
| FINAL, **G-5** (`e2e-m5d/g5/tmpl/final`) | `claimDigest`, `finInDigest`, n, L, `ctxD (.header H)`, `outD (.done o).1`, `gasUsed`, `balanceBurnt` | in: not exposed (lane B's half); **out ✓**: assembled `B_out` = **`h(c10)`** `bd9c8344…` | G-5: `ViewSer`'s fixed-width `Ser ChunkInner` / `Ser Outputs` (E ∧ G), FINAL recomputes `bdigest (3 ‖ Ser.enc H)`, `bdigest (Ser.enc o)`; the M12 counters are public values 58..82 | **B**: c9 (`B_in`, FINAL half; `finInDigest` is a join value) |

Lane D's M9 prototype tree (`tmp-laneD/m9b`, running) imports lane F's **F-2b** `rt` leaves (not
F-3 / F-4), lane A's **A-T3** PREP (not A-T4), G-4 INIT, G-3 FINAL, B-T1b IF / seg0; it has no
STATE leaf between IF and RT enter and no finalize leaf, and binds prototype regions, not `BndRec`
digests (its `spec.edges` list the free cells).

### 2.2 Remaining to "T1 tree over real leaves with real `BndRec` on every edge"

1. **E** (view data only): decide the `u32` byte order of `ctxD (.raw)` (I2b-1); `Ser Intake`,
   `Ser ChunkInner`, `Ser Outputs` closures (`ctxD (.intake I)`, `ctxD (.header H)`,
   `outD (.done o)`); adopt `encRestI` in lane B's default instance (D-d) and fix the per-position
   `rest` contents lane F's metas carry.
2. **B**: `stD .none` constant; `STC` on IF-INTAKE (c1's `R_0` commitment) and IF-FINAL (the
   finalize leaf, c8 → c9); split the STATE segment at the `rt` cuts (c1 → c2, c7 → c8) and prove
   `m5tSegC`; `rest` per position.
3. **F**: re-prove RT enter and RT resume from the regenerated `plan.json` (`rtbnd.pair` reads it
   unchanged: template names `RT enter` / `RT resume`, `B_0`, `B_out`); STATE engine rows for
   seg A / seg B / finalize (`EngHalfRC`); the `STMQ`/`STMA` metas with real `rest`.
4. **A** — A-T5 done: `gasLeft = s.gas.g` in `airBnd` and public (`g_out`), `stackRem` public, the
   last segment ends at `fbBnd (q, .fin r)` (I2b-2); both Wasm leaves re-proved, digests = c4 → c5 →
   c6. Left: `vmCtxDigest`, `fuel` as public values; PREP exposes / checks its `.pre` and `.ent`
   records (`PrepRest`); the 42-B packing of the CODE / FUNC commitment; **D** imports the A-T5
   leaves (`e2e-laneA/at5/m8-tmpl/wasm{0,1}`, one program: equal heights and vk).
5. **G** — G-5 done: INIT's `ctxD (.raw)` big-endian (= c0), FINAL with `ViewE`'s `ctxD (.header H)` / `outD (.done o)` (`ViewSer` fixed-width serialisers, E ∧ G) and the M12 counters (= c10), both re-proved and `m8-import`ed (`e2e-m5d/g5/tmpl`). Left: `B_1`'s `ctxD (.intake I)` (with E's `Ser Intake`) and `B_in` = c9 are lane B's halves of the joined INIT ⊕ IF / FINAL ⊕ IF leaves.
   agreed `ctxD (.raw)`; FINAL with `ViewE`'s `ctxD (.header H)` / `outD (.done o)` and `B_in` = c9
   (joint with lane B's FINAL half).
6. **D**: a tree spec with the 11 leaves of the table above (INIT ⊕ IF, STATE A, enter, PREP,
   WASM 0/1, resume, STATE B, finalize, FINAL), each edge the 42-B `h(B)` — not prototype regions —
   and the current saved leaves (F-3 / F-4 or their re-proofs, A-T4 PREP).
7. **I**: rerun `chain.py plan` after each landing; a leaf row turns ✓ when its exposed values
   equal the chain's; the placeholders list shrinks to empty.

## 3. Components: status, interface, owner

Status: **PASS** = proves/verifies on T1 today and its public boundary equals the Lean run's;
**BLOCKED** = exists, fails on T1; **MISSING** = no code.

| # | component | owner | status on T1 | interface it must expose |
|---|---|---|---|---|
| C0 | **statement** `S`, `claimDigest`, `B_0 = Init(claimDigest)` | E (codec, done [K]) + D (wrap) + I | **PASS** [M]: canonical `S` (§3.4.1) = Lean evaluation = kernel values; `BndRec` = Lean on all cuts | wrap: `D_wrap = H(tag_wrap, SHA-384(S))`; `WrapInitSound`: `B_0` = digest of `init (assemble s.ci secB s.secC) w` |
| C1 | **INIT** (claim + witness decode, intake record, receipts) | **G** (+ B: INTAKE) | **PASS as a leaf for `B_0`** [M] (G-5: 356,405 B, 268.2-bit, 21.6 s, `m8-import`ed, 13/13 mutants; main-slot selection in-circuit; assembled `B_0` = chain `h(c0)`); Lean [K]: `Leaf.init_sound8` (`SegSoundInit8` from lane G's half `init_g_half` + lane B's INTAKE `InitBOut`), `InitBus.init_main_index` (G-4's bus premises from `Holds`), non-vacuity `T1G5.t1_init_c0`; open: `InitDig` (G), `B_1` = c1 (B: INTAKE) | `SegSoundInit`: `B_0` (phase 0) → `eng I start` (phase 1), `ctxRoot = ctxD(I)`; witness `S` hashed in-circuit to `claimDigest` |
| C2 | **receipt step** (RT enter / next / resume) | **F** | **PASS as leaves** [L] (lane F F-3, M11i record shape: `engF` 450 B / `callF` 834 B): enter **87,739 B** (S2 `codeRoot = code hash ‖ 0^10`, lane A's `.pre` record), resume **430,143 B**, lane D's base configuration, both imported by lane D's `m8-import`; mutants 10/10 + 11/11. Digests ≠ this driver's run4 plan (pre-M11i: the plan needs the singleton `outRcptAcc`, `gasLeft`, and the `.pre` record at the enter cut, PREP after it). Lean [K]: **enter discharged** in lane E's relative store-canonical form from the circuit (`EnterC.enter_relC`, non-vacuity on T1's leaf `T1Enter.t1_enter_nonvac`), under view laws + named checks (README §F-3). **F-4: resume as a split leaf** — AIR `RB` (M12 clear fields, `vmAcc` reset) + `STMQ`/`STMA` + `ACC` (SHA-384 appends on the native SHA-512 chip): T1 resume **468,680 B**, 19/19 mutants, `m8-import`ed; Lean `ResumeC.resume_relC8` (engine half from the circuit ∧ lane B's `stHalf_inst`) and `rt_relC8_full`, named `RsStep` (the `estepO` composition, lane A's `fin` record, `Ser.enc` items), `RsJoint` (`STC`), `ChipOK`; non-vacuity `T1Resume` | `SegRelRt` / `TmplSoundRel8C .rt`: `enter` (start `q` at a non-final `eng I c`), `resume` (`estepO (strictO (K ++ [(q, r)]))`): actions, gas/compute, refund, outcome, `vmAcc` |
| C3 | **Wasm segments** `wasmBaseSegAirMP` for `d3tiny.run` | A | **PASS** [M] (was BLOCKED in I-1): lane A's M6 bus-214 multi-group fix (`da5844114`) fixed the HOSTB 314 vs key 58 failure. `segcheck` at k = 13 (2 segments) and k = 26 (1): every pre-check OK, chained. **Boundary = Lean run 16/16** (entry pc, `t`, `S`/`sb`/`cid` = 0, gas `g0` = Lean prep, memory size / `nblk` / depth, entry `memRoot` = Merkle root of the Lean prep image, `t_out` per cut, `halted` only last, chain, final gas = Lean `gFinal` = last host call's `gAfter`, final `memRoot` = image + the Lean tape's `read_register` write). **Lean `HoldsX ∧ ChipIf` SATISFIED** on both dumped segments (`wasmbase-tool holds`, `checkSeg_sound`). Proofs (k = 13, `segprove`, statement check incl. CODE/FUNC roots): 1,328,433 B + 1,334,481 B, 268.2-bit, prove 47.4 + 45.8 s, verify 58 / 91 ms (8 threads, host load ~33; 37.9 + 46.4 s on a quieter run) | 117 public values → `WasmBnd` by `WasmView.airBnd` (§2; A-T5: `stackRem`, `gasLeft = s.gas.g` public, the halting segment's out-record = `fbBnd (q, .fin r)`, leaves re-proved 557,517 / 556,887 B, digests = c4 → c5 → c6); missing: `fuel`, `vmCtxDigest`, the `codeRoot/funcRoot` packing; HOSTO still an oracle (C4); `.pre → .ent` (C7) |
| C3' | Wasm whole call (`wasmBaseM2Air`, no boundary) | A | **PASS** [M]: return `again`, log `tiny`, final gas equal; proof 1,474,032 B, 268.2-bit, prove 30.8 s under load (15.7 s in I-1), verify 42 ms. Reference only | – |
| C4 | **host ↔ state join (M6)** | A + B | **MISSING as one proof; message-level join balances** (lane B B-T3: B2-4 fixed — `STBH`'s key run is `0x09 ‖ receiver ‖ 0x2c ‖ key` with the receiver from the call context (`CTXB` 215 / `CTXL` 216, proposed), `HOSTQ` `key_len = klen − pl`; lane A's 8 T1 `storage_write` messages verbatim in `m5tSegH`: **pre-check OK, no control hack**; `StHostPfx.prefix_run` [K]; B2-4 mutants 4/4 rejected. Remaining: the context provider (A/F), one prover for both AIRs, HOSTR answer (`EVK`), reads; lane A: `HostIf`, `seg_sound_hostIf_air` [L]) | STATE rows answer `HOSTQ`/`HOSTR`/`HOSTB` in the WASM segment (T1: `storage_write` evicted value → register 1, `input`, `log_utf8`, `value_return`); HOSTO removed; σ in `vmCtxDigest` |
| C5 | **state**: working set, trie, FINAL MPT root (M5b) | B | **Lean (B-T3) [K]:** the `STC` table built (`Stc.m5tSegC`: opens / closes the 42-B `stRoot`, `STMQ` 211 / `STMA` 212, `wsLen ≤ 2^D` in-circuit) and **`StcOK` from `Holds`** (`StcSound.stc_holds`, `stc_seg`, `holdsSt_seg` = lane E M13's `HoldsSt` premise); T1 pre-check OK, STC mutants 8/8 [M]; finding B3-1 (`SegLeaves` too strong → `SegLeavesN`, reduced to the leaf content `LastNew`/`Untouched`, open). **Lean (B-T2) [K]:** lane B's half of the STATE / RT split (`StHalfC.stHalf_inst'`, `split_sound_relC_rel`; `ApplyFaithful` replaced by the relational form, finding B2-1), `ws_moves_seg` (circuit tree = view tree), position check `rtPos`; view leaf-digest fix B2-2; T1 non-vacuity in the kernel (`t1_ws_nonvac`: view root of T1's leaves = the leaf's public `R_in`/`R_out`); `stRoot` interface for lane F's resume (`STMQ`/`STMA`, `STC` not built). **PASS as one proof** [M]: post root = Lean `stateRoot` = header `1db48e38…`; **public boundary 6/6**: `pubs` prev_state_root = TAPE `(0, root)`, TAPE `(10, root)` = Lean `stateRoot` and Lean's 10 state changes, prev_state_root and `wsLen` 17 = clean-room checker (Lean prints neither); proof 1,476,227 B, 268.2-bit, prove 110 s under host load ~33 (58 s in I-1). Not split into STATE leaves; host requests from the public `HTAPE` | split at the template cuts into STATE leaves (`SegSoundState`, VM-free engine steps) exposing `stRoot = stD(StV)` (`StCommit`: `ws` = RCH root, `trie`, `wsLen`, `idx`, `rest`) as public values; INIT/FINAL parts handed to G |
| C6 | **FINAL / FinalOut** (outcome root, outgoing receipts root, congestion, bandwidth requests, RS encoding, tx root, gas, balance, proposals) | **G** (+ B: FINAL half) | **PASS as a leaf for `B_out`** [M] (G-5: 486,168 B, 268.2-bit, 22.9 s, `m8-import`ed, 38/38 mutants; `B_out` in `ViewE`'s encodings with the M12 counters = chain `h(c10)`); Lean [K]: `Leaf.final_soundRel8C` (`TmplSoundRel8C .final` from lane G's half `fin_g_half` + lane B's `FinPre`), `fin_clear`, non-vacuity `T1G5.t1_final_c10`, `t1_fin_dig`; open: `FinDig`, `Computed` (G), c9 + header link (B) | `SegSoundFinal`: from `eng I ⟨done out⟩` to `done H o`; `WrapFinalSound`: `FinalOutPub s`; consumes the accumulators; state root from C5 |
| C7 | **PREP** (`.pre → .ent`): code hash → CODE/FUNC | A | **PASS as a leaf; records bound in-circuit for the byte-determined fields** (lane A A-T4, `a-t1/README.md` §11). `prepAir` now has 6 tables: PHDR, SHA-256 with its byte slots fed by `CB`; `HDR` (section walk); CODE/FUNC with decoder columns. T1 leaf 488,409 B, 268.2 bits, 26 s, pinned heights, CODE/FUNC roots unchanged (= both segment leaves'), lane D `m8-import` OK [M]. Mutants 19/19; another program's records are rejected in-circuit [M]. Lean [K]: `TmplPrep.recordsCert_of` (`RecordsCert` from the AIR's `DecodeCert` + named `StaticCert` + trace-independent `DecFaithfulAt`); `PrepCert.recordAtM2_agree`; `PrepT1.decFaithful_d3tiny` (kernel); `PrepDecSound.lb_read_sound`. **Open:** `PrepDecodeSound` beyond the byte-read layer; `StaticCert` (heights, fees, control targets, call fields, FUNC 1–7: the static analysis in-circuit); `DecFaithfulAt` for all codes; `PrepRest`; the tree-spec insertion (D) | per code (T1: 1 blob, 345 B): SHA-256(code) = the account's code hash, `checkModuleM2`, CODE/FUNC roots = `wasm.codeRoot/funcRoot` |
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
   * C7 PREP for `d3tiny` (the `.pre → .ent` seam): leaf done (A-T3). The decoder certificate
     binds the byte-determined fields in-circuit (A-T4). Open: the static-analysis residual
     `StaticCert`, and the Lean proof `PrepDecodeSound` beyond the byte reads.
   * C3 public values (A): `stackRem`, `fuel`, `vmCtxDigest`, `codeRoot/funcRoot`.
3. **C4 M6 join** (A + B). Needs C2's rows and C5's `SREQ`/`HB`; replaces HOSTO and `HTAPE`.
4. **C8 pinned shapes and saved proofs** per template, base WHIR configuration.
5. **C9 + C10** (D). Leaf wrappers, a tree over T1's 11 leaves (§2), a wrap with V_d over `S`.
6. **M10** (I). `run_t1.sh` fills every `BndRec` field from its component (today: §2's records,
   placeholders listed there; remaining work by lane in §2.2) and checks every cut. Exit: `FinalVerify` accepts T1 and rejects the 59 false
   statements and the 33 binding negatives.
7. **C11** (E + each lane's `SegSound*`) alongside 2–6.

Critical path: 2 (G, F are new lanes, the longest items) → 3 → 4 → 5 → 6.

## 6. Reproduce

```sh
PROVE=1 MUTANTS=1 research/near-compression/e2e-general/t1/run_t1.sh /data/illia/nearproof-deps/e2e-t1/run4
python3 -m pytest -q research/near-compression/e2e-general/t1/test_t1.py
# §2 only, from the frozen inputs (no provers): chain, Lean cross-check, saved-leaf table
python3 research/near-compression/e2e-general/t1/chain.py plan OUT
# refresh the frozen inputs from a run + lane F's Lean engine dump (LEAN_RUN)
python3 research/near-compression/e2e-general/t1/chain.py inputs /data/illia/nearproof-deps/e2e-t1/run4
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
