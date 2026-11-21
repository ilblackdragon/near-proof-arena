# T1 critical path to M10 (single tracker)

Status: **lane I, milestone I-1, 2026-11-21**, measured on main `7358a938d`. Plan:
[`E2E-GENERAL-CHUNK-PLAN.md`](E2E-GENERAL-CHUNK-PLAN.md) §3 (interface), §4 (M10), §5.0.1 (wrap
interface, leaf requirements). Driver: `research/near-compression/e2e-general/t1/` (`run_t1.sh`,
`t1.py`, `stmt.py`, `bndrec.py`). Labels: **[M]** measured by the I-1 driver this session,
**[L]** measured by the owning lane (cited), **[S]** design only. Nothing under `spec/` changed
(checker sha256 `644495ff…a9ae3`).

**M10 exit test.** T1 = `d3c8/d3/02-h10196-s3`: one ZK proof whose verifier, given only the public
statement `S` (chunk-header outputs + trusted facts; section B private, D-2), accepts T1 and
rejects ≥ 50 statement mutants.

## 1. T1 as the driver sees it [M]

| item | value |
|---|---|
| Lean checker `--tier allFeatures` | `accept`; self-check 4/4; **FinalOut: 14/14 header output fields equal the run's outputs** (`finalout.json`) |
| statement | `S` = claim minus section B: **1,003 B** public; section B **4,967 B** private (2 blocks); `claimDigest` = `bdigest(S)` = `040290778c850dde…` (I-1 encoding, §4 item 0) |
| run | 2 receipt outcomes (s5a00 forward, gas 568,551,750,000; s5k210.s2a00 FunctionCall, gas 1,009,188,008,301); `gasUsed` 1,577,739,758,301 = Σ outcomes; 4 outgoing receipts; 10 state changes; `balanceBurnt` 0; no transactions |
| Wasm | 1 call: `d3tiny` (`8152bed2…`, 345 B) `run("again")`, 54 Tgas prepaid, **26 steps**, burnt 121,110,620,829; host calls `input`, `register_len`, `read_register`, `storage_write` (evicted path: returns 1, old value into register 1), `log_utf8`, `value_return`. Lean tape and clean-room checker agree on code, method and burnt gas |
| segment plan (`plan.json`, cut every 13 Wasm steps) | **7 segments**: `INTAKE → STATE(r0) → STATE(r1 up to VM call) → WASM(0,13] → WASM(13,26] → STATE(r1 resume) → FINAL`; each cut encoded as lane E's `BndRec` (`bndrec.py`), digest chain `d_out(k) = d_in(k+1)` holds; clear fields real (phase, receipt index, Σ gas/compute = header), **every digest field is still a 0^42 placeholder** |
| mutants (`t1.py mutants`) | 92 distinct statements (+41 witness-consistent runs). **59 false** (the checker rejects with T1's section B and witness; every header output field and every trusted fact the T1 run reads); **33 true** (trusted facts T1's relation never reads, and `height_created`) — binding negatives only, see §3 |

## 2. Components: status, interface, owner

Status: **PASS** = proves/verifies on T1 today; **BLOCKED** = exists, fails on T1; **MISSING** = no
code. "Interface" is what the component must expose for the tree (plan §3.2 `BndRec`, §5.0.1 (4)
leaf statement `H9(ctx, a, a+1, [phase, h(B_in)], [phase, h(B_out)])`).

| # | component | owner | status on T1 | interface it must expose |
|---|---|---|---|---|
| C0 | **INIT / statement**: `S` encoding, `claimDigest = bdigest(S)`, `B_0 = Init(claimDigest)` | E (codec) + D (wrap) + I | **P** [M]: `S` = claim minus section B (I-1 working encoding), `BndRec` codec transcribed in Python (round trip only; not cross-checked against a Lean evaluation) | canonical `S` bytes and tag (wrap §5.0.1 1(b)7, `D_wrap = H(tag_wrap, SHA-384(S))`); `Init`: phase 0, indices/clock/counters 0, accumulators empty, `claimDigest` = ctx |
| C1 | **receipt intake** (claim + witness decode, incoming/delayed/buffered receipts, INTAKE leaf) | **F (new)** | **MISSING** | in `B_0` (phase 0) → out phase 1 (`eng start`), `ctxRoot = ctxD(I)` (intake record: claim, witness, walk, env, receipts), witness `S` hashed in-circuit to `claimDigest`; receipts handed to STATE rows on a bus |
| C2 | **runtime** (receipt/action rows: T1's forward receipt, FunctionCall, refund, outcome, gas/compute) | **F (new)** | **MISSING** | STATE template: `receiptIdx`, `actionIdx`, `gasUsed/gasBurnt/compute`, `rPrepaid/rBurnt/rUsed`, `outcomeAcc`/`outRcptAcc[shard]` (`chainD` items), enter/leave `inCall` (phase 1 ↔ 6), `vmAcc` (answered VM queries `K`) |
| C3 | **Wasm segments** for `d3tiny.run` (`wasmBaseSegAirMP`) | A | **BLOCKED** [M]: `segcheck` fails at every cut size (k = 1, 5, 9, 13, 20, 26): `1 unbalanced message on bus 214 [ts=18, hid=314] from HOSTB`. HOSTB's `storage_write` value group carries wire id `hid + 256` = 314 (M1-b), HOST offers its call key `[ts, hid = 58]` only (M4c). So **no call with a `storage_write` value can be cut today**; T1's single call is one | public values (105 today) mapped into `WasmBnd`: `pc, sp, stackRem, fuel`, `ctxDigest` (frames/globals/registers), `memRoot`, `memPages`, `vmCtxDigest` (host side σ, M6), `promisesDigest`, `codeRoot/funcRoot` (= PREP's, not recomputed natively); buses HOSTQ/HOSTR/HOSTB/214/REG-C local to the segment; I3: reject `B_in.phase = done` |
| C3' | Wasm whole call (`wasmBaseM2Air`, no boundary) | A | **PASS** [M]: tape trace pre-checks, return `again` / log `tiny` / final gas equal the chunk's; proof 1,474,032 B, 268.2-bit, prove 15.4–15.7 s, verify 28 ms (8 threads). Not a template: no cut, HOSTO oracle, CODE root recomputed natively | – (reference only) |
| C4 | **host ↔ state join (M6)** | A + B | **MISSING** (lane A: `HostIf` scope, σ-pinned restatements [L]; lane B: M5b `SREQ`/`HB` design, `HostReqs` from the public tape [L]) | STATE rows in the WASM segment's trace answer `HOSTQ [ts, hid, S, args…]` / `HOSTR [ts, status, result, g_after]` / `HOSTB [ts, pos, byte]` (T1: `storage_write` with evicted value → register 1, `input`, `log_utf8`, `value_return`), HOSTO removed; σ carried in `vmCtxDigest` across cuts |
| C5 | **state**: working set, trie, FINAL MPT root (M5a/M5b) | B | **PASS as one proof** [M]: M5b AIR (INTAKE trie + working set + STATE write rows + FINAL root), spec-oracle root = Lean `stateRoot` = header `1db48e38…`; proof 1,476,227 B, 268.2-bit, prove 58–59 s, verify 95 ms. Not split into leaves; host requests from the public `HTAPE` (not lane A's HOST rows) | split at `RCH` cuts into INTAKE / STATE / FINAL leaves; `stRoot = stD(StV)` with `encStV` (lane E `StViewE`, M11f) instead of the bare `RCH`/`TCH` pair; `TAPE`/`HTAPE` public tapes become in-circuit (M6) |
| C6 | **outputs / FinalOut** (outcome root, outgoing receipts root, congestion, bandwidth requests, RS `encoded_merkle_root`/`encoded_length`, tx root, gas used, balance burnt, proposals) | **G (new)** | **MISSING** (reference values: `finalout.json`, 14/14 equal) | FINAL template (recommendation 1(b)(ii)): in phase 1/2 → out phase 4 `done`; witnesses `S`, checks `SHA-384(S) = claimDigest` and `headerOk(H, o)` field by field; consumes `outcomeAcc`, `outRcptAcc`, `proposalsAcc`, `bwAcc`; state root from C5 |
| C7 | **PREP**: code hash → CODE/FUNC | **unassigned** | **MISSING**: lane A's V_d recomputes the CODE root natively from the code bytes [M] (not ZK) | per distinct code (T1: 1 blob, 345 B): SHA-256(code) = the account's code hash (read from the working set), `checkModuleM2` + instrumentation, emits cached CODE/FUNC/HOSTT with the pinned padding; exposes `codeRoot/funcRoot` that C3 equates in-circuit |
| C8 | **leaf templates with pinned shapes** | A, B, F, G + D | **MISSING** for T1 (blockers 4, 5, 8 of plan §5.0.1.3); D0a base-template leaves exist [L] | per template: one parameter set (n_stack, w_stack, log_blowup; base configuration, 24 grinding bits), height classes, proof + vk saved, verifier-backend vk hashing; leaf wrapper `build_seg_leaf` → `H9(...)` |
| C9 | **heterogeneous aggregation (M8)** | D | **MISSING for T1** (built for D0a base templates: arity 4, `P_2`/`P_*`, `PAD_L`/`PAD_N`, one setup over classes S/M/L [L]) | anchor set `{C_t}` over T1's templates; 7 leaves → arity 4, depth 2 (16 slots, PAD) |
| C10 | **ZK wrap (M9)** | D | **MISSING for T1** (D0a tree wraps: 328.8–330.4 KB, verify 49–86 ms, ZK classical ROM [L]) | `[LEVEL_WRAP, D_wrap(S)]`; V_d from `S` alone (no hint, no `u`, no class); packet `S ‖ FINAL` |
| C11 | **Lean `e2e_sound`** | E | conditional [L]: obligation 3 proved (`cm_iff`, `rcm_iff`); 1, 2, 4 reduce to `NodeExec`/`WrapExec`, per-template `SegSoundR`, `ViewImpl` binding, `WitnessExtraction` | per template `k` of C1–C7: `Holds SegAir_k (B, B') → RSteps (abs B) (abs B') ∨ Bad`; `ViewImpl` instances `ctxD` (F/B), `stD` (B), `outD` (G), `vmD` (A/E), `wasmD` (A, done: `wasmD_binding`) |

## 3. Statement mutants [M]

`t1.py mutants` changes one public field per mutant (sections A and C; section B never), re-splices
the original section B, and runs the pinned Lean checker on every mutant claim. Each `chunk_inner`
mutant runs twice: with the original witness (rejected by `w.innerBytes == c.chunkInner`) and with
the witness's own copy of the header patched ("+w"), so that the rejection must come from the
relation's checks.

* **92 distinct statements** (sha256 of `S` pairwise distinct, none equal to T1's).
* **59 false statements** (no variant accepted), covering every header output field and every
  trusted fact T1's run reads. With a patched witness they are rejected by `InvalidStateRoot`,
  `InvalidOutcomesProof`, `InvalidReceiptsProof`, `InvalidGasUsed`, `InvalidBalanceBurnt`,
  `InvalidGasLimit`, `InvalidCongestionInfo`, `InvalidBandwidthRequests`,
  `InvalidValidatorProposals`, `InvalidChunkEncodedMerkleRoot`, `InvalidChunkEncodedLength`,
  `InvalidTxRoot`, `InvalidChunkHeaderShardSplit`, `receipt proof to_shard_id` (`shard_id`), and
  `segment does not start at prev_block_hash`. Trusted facts: epoch id, the epoch table, RS
  parameters, `epoch_start_after`, `tx_valid`, `genesis_chunk_extra`, `validator_update`, and
  protocol version (`out_of_domain`). These are M10's soundness negatives.
* **33 true statements** (the checker accepts them with T1's section B and witness): `chain_id`;
  the epoch record's height, layout byte, validator accounts and stakes, and dropping a validator;
  `minimum_stake`; and **`chunk_inner.height_created`** once the witness's header copy matches.
  These fields are not read by T1's relation (no epoch switch, no validator update), so a sound
  system may prove them. For M10 they are **binding negatives** only: T1's proof must fail on them,
  because `D_wrap` binds `S`. That `height_created` is unconstrained is a spec observation for
  lane E and the spec owner. It is not a checker change.

## 4. Blocking order

0. **C0: canonical `S` and leaf statement** (E + D, with I). This fixes `claimDigest` and
   `s = [phase, h(B)]` (blocker 5), and every leaf exposes them. I-1 uses `S` = claim minus
   section B.
1. **C3 bus-214 fix** (A, small). The key lookup must match `hid + 256` value groups (or HOSTB
   carries the real `hid` plus a group flag). Exit: `run_t1.sh` gives C3 PASS with 2 chained
   segments.
2. **In parallel:**
   * C1 + C2 (F): T1's two receipts as INTAKE + STATE rows.
   * C5 split into leaves (B).
   * C6 (G): T1's 14 FinalOut fields.
   * C7 PREP for `d3tiny`.
3. **C4 M6 join** (A + B). Needs 1, the C2 rows and C5's `SREQ`/`HB`. The STATE rows replace
   HOSTO and `HTAPE`. Exit: the T1 WASM segments with no oracle, and a tampered host answer
   rejected.
4. **C8 pinned shapes and saved proofs** per template (A, B, F, G), at the base WHIR
   configuration.
5. **C9 + C10** (D). Leaf wrappers for C1–C7, a tree over T1's 7 leaves, and a wrap with V_d over
   `S`.
6. **M10** (I). `run_t1.sh` fills each `BndRec` digest from its component and checks equality at
   all 6 cuts. Exit: `FinalVerify` accepts T1 and rejects the 59 false statements and the
   33 binding negatives.
7. **C11** (E) runs alongside steps 1–6. It blocks the `e2e_sound` claim, not the measured run.

Critical path: 0 → 1 → 3 → 4 → 5 → 6. Lane F (C1, C2) and lane G (C6) are new, and the longest
items in step 2.

## 5. Reproduce

```sh
PROVE=1 MUTANTS=1 research/near-compression/e2e-general/t1/run_t1.sh /data/illia/nearproof-deps/e2e-t1/run
```

* Builds the lane A and lane B provers fresh from this tree into
  `/data/illia/nearproof-deps/e2e-t1/target-{wb,m5a}`.
* Uses the Lean tools of the main checkout: the checker, `wasmbase-tool` and `m5a-tool`.
* `wasmbase-tape` is not built on this host. The driver then reads T1's tape from lane A's cached
  M3 corpus tape (`e2e-laneA/m3/tape.jsonl`, produced by the same checker build). It
  cross-checks the tape against the clean-room checker.
* Writes `report.{md,json}`, `plan.json`, `finalout.json`, `mutants.json` and per-component logs.
