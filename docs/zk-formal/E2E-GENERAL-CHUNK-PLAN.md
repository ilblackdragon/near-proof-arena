# End-to-end ZK proof of general NEAR chunk validation: build plan

Status: **plan, 2026-10-31**; milestone 1 done, M3 (host tape) done, M2 corpus coverage 25,918 / 26,731 method calls equal (§5, 2026-11-03). No Lean spec, checker or signed
challenge file is changed by this document or by the milestone-1 code.

Labels: **[M]** measured (in this repo, cited), **[K]** kernel-checked Lean, **[S]** stated only
(a `Prop` or a design), **[E]** estimate, **PROPOSAL** = needs an owner decision.

## Target (owner, 2026-10-31)

| | target |
|---|---|
| relation | `NearSpecV3.Successor.Tier.rel .allFeatures c w` (`spec/lean/v3/NearSpecV3/Successor/Config.lean:456`); contract execution included |
| hardware / latency | 8 H200; ≤ 3 s after the chunk for chunks up to ~100 Tgas; ~10 s at 1 Pgas |
| hash / security | SHA-384 throughout (42-B digests, U-10), proven soundness bounds, no elliptic curves |
| privacy | zero-knowledge; public = chunk-header outputs + trusted facts |
| size / verify | ~400 KB proof; verify < 200 ms |
| architecture | streaming segment proofs, 8-ary aggregation, one ZK wrap; architecture (b) of `research/near-compression/prover-budget/README.md`: multilinear zerocheck + LogUp-GKR + stacked WHIR on BabyBear |

The prover-budget model puts architecture (b) at 105 Tgas worst case in 3 s, 10.6 s at 1 Pgas,
and a 392,867 B ZK proof [E, from M anchors]. Those are the relaxed targets, so they leave no
margin. Two items are on the critical path for feasibility as well as for correctness: Wasm chip
cost per gas, and recursion-node cost.

The main stack is OpenVM `stark-backend` v2.0.1 (`d667af5929d0`) plus research patches
(`research/near-compression/native/patches/`, `recursion/patches/`): the "unified SWIRL" backend,
BabyBear with a degree-12 extension, SHA-384 MMCS with 42-B digests, and stacked WHIR. All PQ-stack
measurements below are on it.

---

## 1. Inventory: what exists proof-side on main today

Columns:
* **Status:** **B** = built and tested, **P** = partial, **–** = missing.
* **Lean link:** **proved** = closed theorem, standard axioms only. **cond.** = proved under named
  open premises. **–** = none.

"D0a" is the transfer-only tier whose chain produced the 299,967 B packet. "WB" is the direct-Wasm
AIR: `research/near-compression/wasm-base-lean/WasmBase` (Lean, the single source of truth) and
`research/near-compression/native/wasm-base` (Rust, which replays the Lean-exported AIR). "R" is
`research/near-compression/results`.

### 1.1 State side

| component | where | status | measured cost | Lean link |
|---|---|---|---|---|
| claim decoding | classical: `examples/np-udr-stark-v2/source/src/v3/{prep,d0,hint}.rs`, `zk-formal/ZkFormal/NearV3/Assembly/HintCodec.lean` | **B for D0a**, but done natively by the verifier (`prepD0`), not in the AIR. **Incompatible with ZK**: the verifier will not see the witness (§2) | – | proved for D0a (`nearV3_admission_final`, `Assembly/AdmissionV3.lean`) |
| witness decoding | the D0a hint (`Hint.decode_encode`); D1: `NearV3/D1/PrepD1.lean` | **P**: D0/D1 shapes only; no general borsh witness decoder in-circuit | – | proved for D0a; D1 conditional (`ExtractD1StmtT`) |
| trie authentication and update | D0a tables `nodeA7, head, valA7, walk, uniq, upsA7, sizeA7`; PQ port `research/near-compression/native/pq-state-port`; ContractData walk `zk-formal/ZkFormal/PQ/CdStorage/Link.lean` | **B for D0a keys** (account, access key, queue); **P for contract data**: upsert hard-coded to the `[0,15]` path, no D3 render | `nodeA7` 188 cols / 480 constraints / 23 interactions (`R/pq-d1-envelope/envelope-d0a.csv`) | D0a proved (`extractV3`, `factorSound`); PQ `pq_d0a_rel` conditional on `SwirlRel`/`VdChecks`; CD: `RealStoreMatchesTables`, `CdKeynibFromHostB`, `UpsV3AppliesLog` are stated, not proved |
| transactions (signature, nonce, conversion to receipt) | D1: `nearAirV3D1`, 33 tables (`NearV3/D1/NearAirD1Defs.lean`), transfer transactions only | **P**: D1 transfers; signature check is native/claim-side; no Ed25519 or ML-DSA chip | – | conditional (`pq_d1_rel`, `ExtractD1StmtT` open) |
| receipts and actions | D0a `rcptV3` (transfer receipts); promise bookkeeping `PBC`, `zk-formal/ZkFormal/PQ/Receipt/*` | **B** transfer; **–** CreateAccount, FunctionCall, AddKey/DeleteKey, Stake, Deploy, DeleteAccount, Delegate, global/gas-key actions, data receipts and yields. There is **no D2/D3 chunk AIR** (`nearAirV3D2` = 0 hits) | `PBC` 49 cols, 51 constraints, 29 interactions (`R/pq-receipt-air/README.md`) | encodings proved (`remaining_eleven_closed`, `promise_encodings_cover`); `RIDS/SRC/RCL`, `newReceipts`, `FCPlanIsTrace` open |
| queues (delayed, buffered, outgoing, yield, bandwidth scheduler, congestion) | D0a: `qvV3` (table 22), scheduler tables 11–15, ChaCha 8–10 | **B for D0a's shapes**; D2's design keeps queue arithmetic **native** (P-D2-2), which ZK rules out (§2) | `qv` is the degree-6 table | D0a proved |
| gas, fees, balances, refunds | D0a refund codec and `acct` | **B** transfer refunds; **–** function-call gas (burnt/used, prepaid, weights distribution, gas price, receiver reward) | – | D0a proved |
| outputs and roots | D0a `mrk` (maxLog 19), `sort`, `upsA7`/`sizeA7` post-state, public header segments | **B for D0a** (state, outcome and outgoing roots); **–** in-circuit Reed–Solomon `encoded_merkle_root`/`encoded_length`, validator proposals, congestion info, bandwidth requests for the general case | – | D0a proved |

### 1.2 Wasm side (WB, on the main PQ stack)

| component | where | status | measured cost | Lean link |
|---|---|---|---|---|
| prepare (decode, validate, finite-wasm instrumentation, stack limit) | native decidable checker `WasmBase.checkModuleIfH` + cached `CODE`/`FUNC`/`HOSTT` tables bound by `code_root`/`func_root` (`R/pq-wasm-base/README.md` §9.1, §13.1) | **P**: the roots are recomputed **by the verifier from the code bytes**, which ZK does not allow for private contracts. No PREP AIR; no in-circuit SHA-256(code) = code hash | – | `CodeOK`/`FuncOK` are hypotheses of `wasm_base_sound`; `runCall_done_prepare_ok` (`zk-formal/ZkFormal/PQ/Join/PrepareLink.lean`), converse false |
| integer ALU (i32/i64 add…rotr, compare, const, div/rem with traps) | `WasmBase/Chips.lean`, `Local/*`, `Main/Row*.lean` | **B** | 28.5 committed cells, 12.6 fractions per op ⇒ 349 cell-eq/op at E=12 (529 padded) [M, `R/pq-wasm-base/README.md` §6]; SHIFT 886, MUL 799 | proved: `WasmBase.wasm_base_sound` (`Main/Final.lean`) against `NearSpecV3.Wasm.run`, std axioms, explicit domain conditions |
| locals, globals, operand stack (channel argument) | `Channel.lean`, LOCAL, globals family §12 | **B**, under the **no-discard-branch** domain condition (D3) | CH traffic 3–5 fractions per binop | proved (`Channel.lean`) under D3 |
| linear memory: load/store | family 2 (§11), running producer/consumer channel space 3 | **B** for integer loads/stores within the initial pages | – | proved |
| `memory.grow` / `memory.size`, bulk memory, `call_indirect`, discarding branches, floats | `WasmBase/M2Check.lean` | **P**: `memory.grow`/`memory.size` are admitted without a chip (a run executing one is not provable: 385 `d3rich` calls); the others do not occur in d3c7–d3c10 and are **–** (they block compiled Rust contracts, T3). Wrap/extend (CONV), `unreachable` (UNREACH) and `if` with a result are **B** (`wasmBaseM2Air`, 2026-11-03) | – | CONV/UNREACH row lemmas (`Main/M2Link.lean`) |
| control flow: block/loop/br/br_if/return, `if`/`else` | CTRL, IF chip (`IfCheck.lean`, `docs/logs/pq-if-air-2026-10-22.md`) | **B** | IF: 14 cols, 2 constraints | `if_rowfacts` proved; the full IF checker soundness is open |
| calls (defined functions) | family 4, FUNC table (§13.1) | **B** | – | proved (`step_call`, `call_rowfacts`) |
| gas (instruction units `S`, `R·S ≤ g0`) | in every chip; per-segment invariant `WasmBase/Main/SegExec.lean`, `R/pq-host-gas` | **B** Wasm-internal; host resynchronisation (`g := remaining`) is **P** | – | Wasm-only proved; `H0`/`HoldRow` open |
| segmentation of one call | spec: `NearSpecV3/Wasm/Segment.lean` `run_foldSegments` [K]; `wasmBaseSegAir` (`WasmBase/SegAir.lean`, E2E M4) | **B** (2026-11-03): mid-call cuts with SHA-384 `ctxDigest` + `memRoot` boundary; 1.13 M-step call proved as 5 chained segments | boundary per written 1 KiB block 50 SHA-512 compressions (`D = 16`); M4b multiproof (`wasmBaseSegAirMP`): 680 per 32-block segment, boundary 43 % | `exec_of_rows_cut`, `cuts_csteps` [K]; M4b: `seg_sound`, `wasmD_binding` [K]; M4c: `seg_chain_mem`/`seg_chain_k` (chained segments → `CSteps` or `Sha384Coll`; memory roots, CUTI side, halting, MP AIR default) [K]; host relies vacuous on host traces until M6's σ pinning |

### 1.3 Host functions (HOST/HOSTO/HOSTT/HOSTB/REG chips, `WasmBase/HostChip.lean`)

| family | status | Lean link |
|---|---|---|
| registers (`read_register`, `register_len`, `write_register`) and `input` | **B** (`RegChip.lean`, KAT 81/81 [M]) | conditional (MEMIO: `HostBLinked.linked/unique`, `BufOK`) |
| context getters (19 functions: block index, timestamp, account ids, prepaid/used gas, balances, …) | **B** at the Wasm side: answers come from the HOSTO oracle table; no state-side producer | arity [K]; the answer itself is unproven |
| logs, `value_return`, `panic*`, `abort` | **B** byte movement over HOSTB (MEMIO, log 86/86 and register 101/101 tampers rejected [M]) | conditional (MEMIO) |
| storage (`storage_write/read/remove/has_key`) | **P**: Wasm side and byte bus built; contract-data trie update (CD) partial | CD stated Props open |
| storage iterators | out of domain for PV86 (`spec`), nothing to build | – |
| promises (`promise_create/then/and/batch_*`, `promise_return`, `promise_results`, yield/resume) | **P**: `PBC` built; `promise_yield_resume*` result-tag mismatch (`results/pq-host-promise/DESIGN.md` §3) | encodings proved; receipt production open |
| math/hash hosts (`sha256`, `keccak256/512`, `ripemd160`, `ed25519_verify`) | **P**: the chips below exist; no HOST ↔ hash-chip binding (`Sha.HashInputLink` stated) | see crypto |
| curve hosts (`alt_bn128_*`, `bls12381_*`, `ecrecover`), ML-DSA | **–** | – |
| `validator_stake`, `validator_total_stake`, `epoch_height` | **P**: oracle-answered; trusted facts T7/T8 must feed the producer | – |

### 1.4 Cryptography

| primitive | where | status | cost [M] | Lean link |
|---|---|---|---|---|
| SHA-256 | `zk-formal/ZkFormal/Sha` (classical), `WasmBase/ShaAir.lean` (PQ) | **B** | 17 rows, 9,333 cells/block (`R/pq-hash-air/README.md`) | `sha_digest_is_spec` proved; `HashInputLink` stated |
| SHA-512/384 (state boundary digests, Ed25519, recursion) | `research/near-compression/native/sha384-air`, NV `Sha512Air` (patch) | **B** as a recursion chip | 10,624 cells/compression (`R/pq-ed25519-air/CENSUS.md`); ≈ 29 k cells per SHA-384 compression inside the NV verifier circuit | partial |
| Keccak-f[1600] | `WasmBase/KeccakAir.lean`, `ChiAir.lean` | **P**: `chi` only | 118,582 cells/perm [E] | `chi_sound` |
| RIPEMD-160 | `WasmBase/RipemdAir/Round/Sound.lean` | **P**: row AIR; `round_agrees` (`bl'`/`br'`), feed-forward, digest bus and message binding open | 1,608 cols × 80 rows = 128,640 cells/block | partial; the file header says so |
| Ed25519 (tx signatures, `ed25519_verify`) | `R/pq-ed25519-air/FpChip.lean` | **P**: F_p multiply prototype only | ≈ 1.51 M cells/sig at N=149, worst 1.96 M [E from M] | `value_of_chain` only |
| secp256k1 (`ecrecover`, secp keys), p256, BN254, BLS12-381 | – (spec semantics only, `spec/lean/v3/NearSpecV3`) | **–** | sketches ±2× (prover-budget `WORKLOAD.md`) | – |
| ML-DSA-65 (keys) | – (spec: `nearspec-v3-mldsa-check`) | **–** | sketch | – |

"No elliptic curves" binds the *proof system*. Curve hosts and Ed25519 are application semantics
and must be arithmetised as non-native-field chips.

### 1.5 Proof composition

| component | where | status | cost [M] | Lean link |
|---|---|---|---|---|
| segment leaves | – | **–**: no real D3 segment leaf exists. Tree tests use the Fibonacci `SegAir` | – | – |
| boundary model | `research/near-compression/NearCompression/{Segments,Boundary}.lean` | **P** (model) | – | `certified_run_or_hash_collision` proved |
| aggregation (NV nodes) | `zk-formal/ZkFormal/PQ/Aggregation/*`, NV circuit in `native/recursion/patches/openvm-recursion-*.patch` | **B** at production parameters for 2–8 identical children | depth 2 (4 leaves) 315,913 B / 700 s / 18.8 GB; depth 3 (8 leaves) 322,027 B / 752 s / 21.5 GB (`docs/logs/pq-agg-depth2-legal-2026-10-24.md`) | `d3Stmt_tree_sound`, `certified_root` take `NodeOK` as input; `nvFaithful_of_obligations`: 1 of 6 obligations proved; no Lean model of the NV AIR |
| D0a end to end | `research/near-compression/native/pq-chunk-e2e` | **B**: one 25-table base proof → 5-level linear NV chain → FINAL; 299,967 B, 52 min, 1.6–2.1 s verify (`VALIDATION.md`) | 33 B margin, not structural (300,765 B on a replay) | `pq_d0a_rel` for the base; NV levels and FINAL unlinked |
| final ZK wrap | modelled (HVZK-WHIR, +92.9 KB [E]); **a sibling agent is building it for D0a now** | **–** on main | – | – |
| succinct D3 | none. `examples/reexec-v3-d3` is witness re-execution | – | – | `check_iff` → `RelD3` (artifact-bound, not succinct) |

### 1.6 Summary

* **Proof-side, only D0a (transfers) is end to end.** Its verifier does native preparation work
  over private data and is not ZK.
* **The Wasm side is the most advanced part for general chunks.** It is a 27-table AIR on the main
  stack, base-faithful to the Lean `Wasm.run` for its families, and two unmodified corpus contracts
  (`d3tiny`, `d3hostx`) are in its domain.
  M1 (§5) found that this holds for the public statement only: host → memory writes are not
  modelled, so the proved trace's return bytes are wrong.
* **What is missing:**
  * every non-transfer action;
  * function-call gas and outcomes;
  * contract-data state;
  * the host ↔ state join;
  * preparation in-circuit;
  * Wasm `memory.grow`/`call_indirect`/discarding branches/floats;
  * Ed25519 and every curve primitive;
  * segment leaves with boundaries;
  * the ZK wrap;
  * the Lean join from a final proof to `Tier.rel .allFeatures`.

---

## 2. The old bounded-tier proposals (P-D2-1…6, P-D3-1…5)

They were written (2026-10-23) for a different architecture. That architecture had one
fixed-height AIR per tier, checked by a **native verifier that sees the claim and a hint**
(`prepD2 cb (decodeHint2 hintBytes)`) and admitted by the 4-hour Lean judge. Two of its premises
no longer hold:

1. **ZK removes the verifier's view of the witness.** Anything the old design ran natively over
   receipts, queue values or code bytes (`prepD0`/`prepD1`/`prepD2`, `code_root` recomputation)
   must move into the circuit. The verifier may compute only over public data: the header outputs
   and the trusted facts.
2. **Segments plus aggregation remove the global table height.** Each segment has a fixed shape,
   and the number of segments grows with the chunk (an 8-ary tree adds levels logarithmically).
   Soundness never needed a size bound. Completeness up to a size is a property of the *prover*
   and is stated about the prover, not inside the relation.

| proposal | was | recommendation | reason |
|---|---|---|---|
| **P-D2-1** `RelD2a` bounded tier (amendments + `NT2`, `DR2`) | a bounded statement so a fixed-height AIR can be complete | **Supersede.** Prove `Tier.rel .allFeatures` itself | No relation-level bound is needed once heights are per segment. The amendments `a2/a7/a9/a10/a12/canon0f` existed to make the native hint single-valued or to give tables a height. With everything in-circuit the relation's own determinism does that work |
| **P-D2-2** queue arithmetic native (`D2-N`) | verifier runs `groupsPushBack`… natively | **Supersede: in-circuit** | Queue state is private under ZK. Queue values are trie values, so they come through the same authenticated state reads as any other value |
| **P-D2-3 / P-D2-4** `NT2 = DR2 = 8,192` | domain bounds on receipts and delayed pops | **Supersede as relation bounds; keep as per-segment sizing parameters** | Each becomes the number of receipt rows a segment template holds. A long chunk uses more segments |
| **P-D2-5** corpus distributions before AIR | measure receipt counts, congestion and pops | **Keep, retargeted** | Needed to size segment templates and to pick the realistic mix for the latency model; use the shard-13 window and W13 |
| **P-D2-6** `prepD2` candidate-side | native prep location | **Supersede** | Same as P-D2-2: no native prep over private data |
| D2 §5.3 judge-budget wall (4 h) | split, coarsen or native-extract | **Owner decision D-6** | Native extraction is no longer available. Use a generic chip framework (one `Holds` → step lemma per chip, reused across segments) and measure it |
| **P-D3-1** `RelD3a` bounded tier | as P-D2-1, plus `T3` | **Supersede** | as P-D2-1 |
| **P-D3-2** D2 AIR before D3 | no D3 AIR without D2 | **Supersede with parallel lanes.** The Wasm leaf (M1–M4) and the state machine (M5) are built against the fixed host-bus interface (§3.3) and joined in M6 | The interface is now specified, so the halves no longer serialise. Both are needed for any E2E proof |
| **P-D3-3** keep re-execution `D3a` admitted, never call it succinct | – | **Keep** | Still true |
| **P-D3-4** `T3: Σ ops ≤ 2²²` derived from `G_α` | operator bound for the EXEC table height | **Supersede** | `G_α ≈ 3.45 Tgas` is 30× below 100 Tgas and 290× below 1 Pgas. `.allFeatures` has `gasCap := none` |
| **P-D3-5** join on `Read.check` (artifact acceptance) | `check_iff` premise strictly stronger than `RelD3` | **Supersede by §3.4's theorem; keep the method** | Under ZK the witness is not an artifact the verifier holds, so the join is on the final verifier's acceptance. Keep the lesson: test every join by asking whether its premise is its conclusion |

### 2.1 Owner decisions (all recommended answers ADOPTED by the owner, 2026-11-03)

D-1 (unbounded `allFeatures`), D-2 (section B private), D-3 (PREP sub-proof) with D-7 (non-native chips), and D-4/D-5/D-6 were all accepted as recommended. The superseded proposals in §2 are therefore retired for the PQ E2E track.

| id | question | recommended answer |
|---|---|---|
| **D-1** | Target relation | `Tier.rel .allFeatures`, unbounded. Completeness is a separate, measured prover-capacity claim ("every chunk with ≤ X gas and ≤ Y witness bytes is proved within T"). No new tier rank, so `Tier.rank` governance is not touched |
| **D-2** | Public statement | Public = `chunk_inner` (header incl. all outputs) + trusted section C + `epoch_id`, `protocol_version`, `chain_id` (claim-v3 §2.4, T1–T14). Claim section B (block headers, authenticated by `chunk_inner.prev_block_hash`, A2) becomes **private**. Statement: `∃ secB w, Tier.rel .allFeatures (assemble chunk_inner secB secC) w`. This is a statement-shape change (PROPOSAL), not a checker change. Alternative: keep section B public (no ZK loss beyond those headers, a larger statement) |
| **D-3** | Contract preparation under ZK | Prove it in-circuit as a **PREP sub-proof** per distinct code blob: SHA-256(code) = code hash, decode and validate, emit the instrumented `CODE`/`FUNC`/`HOSTT` tables (P-PERF-8, early PREP). Lean link: `PREP holds ⇒ tables = records(checkModuleIfH (prepare code))`. The alternative, a public registry of prepared-code roots signed by validators, changes the trust base; not recommended |
| **D-4** | Cross-segment state binding | **Explicit SHA-384 boundary digests** (§3.2, no global challenge), so segments stream. A two-phase global LogUp challenge is a later, measured optimisation only |
| **D-5** | Extension field | Stay on BabyBear Ext12 (the measured, NV-verifiable stack). The model's Ext8 saves ≈ 1.2× and needs its own soundness recalculation; revisit after M8 |
| **D-6** | Formal admission budget | The 4 h judge limit was set for one-statement certificates. Recommend measuring M11's generic framework first and deciding then. Do not pre-split the statement |
| **D-7** | Curve, Ed25519 and ML-DSA hosts | Arithmetised in-circuit as non-native chips (application semantics, not proof-system curves). First E2E targets avoid them; coverage lanes M7b–M7f |

---

## 3. The segment interface

### 3.1 What one segment proves

The chunk check is re-expressed as a **small-step machine** `CM` whose configurations are the
boundaries below. Its step relation is the spec's own pipeline order:
1. claim and witness intake;
2. per applied block: transactions → local receipts → delayed → incoming → yield timeouts;
3. per receipt: actions;
4. per FunctionCall: the Wasm instructions;
5. finalize (balance checks, outcome and outgoing roots, congestion and bandwidth, the encoded
   chunk).

A segment proof is a proof of

```
Seg(B_in, B_out)  :≡  ∃ trace tr, Holds SegAir (B_in, B_out) tr
```

and its Lean meaning (M11) is `CM.steps* (abs B_in) (abs B_out)`. A segment may cut anywhere, **including in the
middle of a Wasm call**: a 300 Tgas call is ~10⁸ instructions, more than one 2²³-row segment
holds. Segments are heterogeneous by phase but come from a fixed menu of templates, so each
template has one verifying key.
Templates: `INTAKE`, `STATE` (receipt and action rows plus trie overlay), `WASM` (WB chips plus host
bus), `PREP`, `CRYPTO-x` (hash and signature batches), `FINAL`.

Within a segment every bus (STATE, CH, FETCH, HOSTQ/HOSTR/HOSTB, trie value buses, hash-call
buses) is balanced locally, with the segment's own Fiat–Shamir challenges. **Nothing crosses a
segment except `B`.**

### 3.2 The public boundary `B`

Every field is a fixed-width vector of BabyBear limbs. Digests are 42-B SHA-384 (U-10).

| group | fields | notes |
|---|---|---|
| chunk constants | `claimDigest` = SHA-384 of the public statement | identical in every segment; the root checks it once |
| position | phase tag, block index, receipt index, action index, `inCall` flag | the program counter of `CM` |
| clock | global step `t` (u64) | segment-local timestamps are `t − t_in` < 2²⁴, so the BabyBear channel time checks stay sound |
| state | `stRoot`: SHA-384 Merkle root of the **working set**, a key-sorted indexed Merkle tree over `(trieKey → current value digest, pre-value digest, touched flag)` | `INTAKE` builds it from the authenticated partial trie (pre-state root proved against `prev_state_root`). `FINAL` folds it into the new MPT root (SHA-256 nodes). Updates cost one SHA-384 path per write, priced by storage gas |
| queues | none separately | delayed, buffered, outgoing, yield and congestion state are trie values, so they live in `stRoot` |
| gas and balance | chunk `gasUsed`, `gasBurnt`, `balanceBurnt` (u128), compute, per-shard outgoing gas, plus the in-flight receipt's `prepaid/burnt/used` | the u128 sums are limb vectors with range checks |
| outputs so far | `outcomeAcc` (running list commitment of outcome hashes), `outRcptAcc[shard]` (outgoing receipts), `proposalsAcc`, `bwAcc` | `FINAL` turns them into the Merkle roots the header carries |
| Wasm (when `inCall`) | `pc`, `S`, `stackRem`, frame-chain digest, `memRoot` (SHA-384 Merkle over 1 KiB memory blocks, plus `memPages`), globals digest, registers digest, VMContext digest, promises-so-far digest, `codeRoot`/`funcRoot` of the running contract | in-segment memory stays the channel argument. At a cut, only touched blocks are re-hashed |

A cut costs SHA-384 work proportional to the blocks and keys touched in that segment. The
prover-budget model already counts in-circuit SHA-384 as the dominant recursion cost; M4 measures
the boundary term.

### 3.3 The Wasm ↔ state join inside a segment

The buses are the ones fixed in `R/pq-wasm-base/README.md` §14.2: `HOSTQ [ts, hid, S, args…]`,
`HOSTR [ts, status, result, g_after]` and `HOSTB [ts, pos, byte]`. Today `HOSTO` answers them
inside the Wasm trace as a free oracle. In the E2E design the producer is the state template's
host-semantics rows: storage via the working set, context from the VMContext digest, promises
into the receipt rows, gas from the receipt's counters. A WASM segment and the STATE rows serving
it share one trace, so these buses balance locally. When a call spans segments, the in-flight
host context is carried in `B`.

### 3.4 Chaining, the root, and the final public inputs

* **Node** (fan-in 8): verifies children `π_1..π_8` (any templates) and checks
  `B_out(π_j) = B_in(π_{j+1})`. Its own public values are `(B_in(π_1), B_out(π_8))`.
* **Root**: the top node's `(B_0, B_N)`.
* **Wrap** (ZK, HVZK-WHIR): verifies the root and checks:
  * `B_0 = Init(claimDigest)`: position 0, empty accumulators, and `stRoot` = the working-set root
    `INTAKE` committed (`INTAKE` is the first segment and proves it from `prev_state_root` in the
    statement);
  * `B_N.phase = done`;
  * `FinalOut(B_N) = header outputs`: `prev_state_root` of the next chunk = state root,
    outcome root, gas used, balance burnt, outgoing receipts root, validator proposals, congestion
    info, bandwidth requests, encoded Merkle root and length, tx root.

  Its only public input is the statement of D-2. No boundary leaves the tree.

### 3.5 The Lean theorem that closes it

```
theorem e2e_sound (stmt : PublicStmt) (π : Proof) :
    FinalVerify vk stmt π = true →
    (∃ secB w, Tier.rel .allFeatures (assemble stmt secB) w) ∨ HashCollision ∨ FSBad
```

It decomposes into four obligations, none of whose premises is its conclusion:

1. **NV/wrap faithfulness:** acceptance yields a tree of satisfied segment instances with chained
   boundaries. This is `NvFaithful` (5 of 6 obligations open) plus `NodeOK` and the QROM bound.
   Shared with the D0a chain.
2. **Segment soundness**, one per template: `Holds SegAir_k (B, B') tr → CM.steps* (abs B) (abs B')`.
   WASM reuses `wasm_base_sound`'s row lemmas and `run_foldSegments`. STATE reuses the D0a table
   lemmas.
3. **Small-step factorisation of the checker** (spec-side theorem, no semantic change):
   `checkSuccessor (Tier.cfg .allFeatures) c w = .ok () ↔ ∃ n, CM.run n (init c w) = done (out c w) ∧ out c w ⊨ c`.
   `run_foldSegments` is the Wasm instance. The pipeline-level instance is new and large.
4. **Witness extraction:** the `INTAKE` segment's authenticated nodes and code blobs determine `w`
   as `encodeWitness`, and the relation reads `w` only through them (decode ∘ encode = id).

This has the same shape as `certified_run_or_hash_collision`, already proved for the Boundary
model.

**Status (lane E, 2026-11-03) [K].** In `spec/lean/v3/NearSpecV3/E2E/` (`Engine`, `Machine`, `Statement` in
`defaultTargets`; `RealChunk` on demand). Only `propext`/`Classical.choice`/`Quot.sound`; no `sorry`;
no checker semantics changed. Log: [`docs/logs/e2e-lean-join-2026-11-03.md`](../logs/e2e-lean-join-2026-11-03.md).

* **Obligation 3 is proved.** `cm_iff : Tier.rel .allFeatures cb wb ↔ CMAccepts cb wb`. `CM.step`
  runs verbatim slices of the checker: `INTAKE` = the prefix of `checkReshardCoreObs`
  (`checkReshardCoreObs_split` is `rfl`); engine steps = slices of `StorageExecution.applyNewChunkD2`
  (`applyNewChunkD2_split` is `rfl`; `den_step`, `engine_run_ok_iff`); `FINAL` = implicit
  transitions and the computed `Outputs`; `FinalOut` = `headerOk H o`. Chaining:
  `steps_of_chain`, `stepsN_of_chain` (the clock adds up). `cm_done_header`: the `H` of a reached
  `done H o` is the claim's own decoded `chunk_inner`.
* **Statement.** `assemble ci secB secC`, `E2EStmt s := ∃ secB w, Tier.rel .allFeatures (assemble …) w`,
  `e2e_statement_iff` (for a well-formed assembled claim: a `CM` run to a configuration passing
  `FinalOutPub`, the comparison with the **public** `chunk_inner`).
* **`e2e_sound` is proved from the obligations as hypotheses:** `NvFaithfulE2E` + `WrapFinalFaithful`
  (obligation 1), `SegSound` (2), `WitnessExtraction` (4), over a parametric `SegSystem`/`WrapCheck`.
  None of them mentions `Tier.rel` or `checkSuccessor`. Non-vacuity: the re-execution system
  `reexec` proves obligations 1, 2, 4 from `CM.step` alone and reaches `Tier.rel` only through
  `cm_iff` (`reexec_sound`, `reexec_complete`, `reexec_rejects_zero_steps`); on a real chunk,
  `cm_run_06_h10006_s0` (`d3c7/d3/06-h10006-s0`, non-genesis, via the kernel-checked
  `relAllFeatures_06_h10006_s0`).
* **Granularity gaps.** (a) *Closed by M11b (below)*: mid-call cuts. (b) *Closed by M11c
  (below)*: a segment that contains a genesis block is no longer one atomic `CM` step. (c) *Closed
  by M11b/M11c up to the per-component commitments*: the concrete §3.2 boundary encoding, `abs`,
  and what each configuration commits to (`View.lean`); the commitments themselves are lanes A/B's.

**M11b (lane E, 2026-11-03) [K].** New modules, all in `defaultTargets`, standard axioms only, no
checker definition changed. Log: [`docs/logs/e2e-lean-m11b-2026-11-03.md`](../logs/e2e-lean-m11b-2026-11-03.md).

* **Mid-call cut (`CallMachine`, `CutW`, `Refined`).** One VM call is a small-step machine
  (`CallConf`: `pre | ent p k r n | fin r`). One step is one Wasm instruction (`Wasm.step`) inside
  the `start` or method entry; the `inCall` boundary is `ent p k (.cont s) n`, the whole `St` with
  the fuel left. Its prefix is `runCall` verbatim (`runCall_eq_G`, `rfl`). `csteps_fin_iff`: the
  call machine reaches `fin r` iff `r` is the call's result. `csteps_seg` and `csteps_foldSegments`
  show a Wasm segment is a call-machine run, and `cden_foldSegments` is `Wasm.run_foldSegments`
  lifted to the call machine. The receipt chain down to the VM call is copied verbatim with each
  callee as a parameter (`CutW`: `pwO_std`, `rfl`/induction). Every layer is monotone in its
  callee (`pwO_mono`, a walk over the copied bodies). The refined machine `RCM` adds
  `RConf.call I c K q cc`. The steps are `base` (a `CM` step), `enter` (start VM call `q`),
  `wasm` (one call-machine step), `next` (record `(q, r)` in `K`, start the next call) and
  `resume` (finish the receipt step with the VM answered **only** from `K`, `strictO`). So the
  STATE template never runs Wasm.
  **`rcm_iff : Tier.rel .allFeatures cb wb ↔ RCMAccepts cb wb`** (through `rsteps_sound` /
  `rsteps_of_steps`, `estepO_sound`). `rsteps_foldSegments` makes a list of Wasm segments an `RCM`
  run between `inCall` boundaries. The cut is not vacuous (`rsteps_through_calls`): a receipt step
  completed by the answers of calls `q₁…q_m` is reached through every Wasm instruction of every
  call. `e2e_sound_r` is `e2e_sound` with obligation 2 against `RSteps` (`SegSoundR`), so segments
  may begin and end mid-call.
* **Concrete boundary (`Boundary`).** `BndRec` holds the §3.2 fields plus `vmAcc` (the digest of
  `K`) and the Wasm part. `BndRec.codec` is fixed-width (u64/u128 big-endian, 42-B digests,
  counted lists, a presence byte). Its round trip is `BndRec.decode_encode` and
  `BndRec.encode_inj` follows. `sha384` is FIPS 180-4 §6.5 over the existing SHA-512
  compression, with `sha384_length` and the kernel-checked `sha384_abc`. `bdigest` is its 42-B
  truncation (U-10). For a commitment `view : RConf → BndRec` (a parameter: the working-set root
  and accumulators are lanes A/B's), `absD view` opens a digest by choice. Then
  `absD_bndOf` gives `abs (bndOf x) = some x ∨ BndCollision view`, and `bndCollision_split` gives
  a collision as a SHA-384 collision or a `view` collision. `segSoundR_digest`: segments
  whose rows open both digests to `RSteps`-connected configurations satisfy `SegSoundR` at the
  digest boundary with `Bad := BndCollision view`.
* **Obligation 1 from `NvFaithful` (`zk-formal/ZkFormal/PQ/E2EBridge.lean`).** `ZkFormal`
  requires `NearSpecV3`, so the link lives on the `zk-formal` side; the v3 package cannot import
  it without a cycle. The link is `nvFaithfulE2E_of_nv`: `NvFaithful Pin D V` for the node
  circuit, plus `NodeOK` (an accepting node verification accepts each child and chains their
  boundaries), `Extract` (knowledge soundness / QROM: an accepted proof is a satisfied leaf, or a
  node trace satisfying the node AIR with lower children, or `Bad`) and `WrapOK`, together imply
  `NvFaithfulE2E`. `e2e_sound_of_nv` is the composition. The file is on demand (like
  `NvFaithful.lean`, not in `ZkFormal.lean`).
  Build: `cd zk-formal && lake env lean ZkFormal/PQ/E2EBridge.lean`.

**M11c (lane E, 2026-11-03) [K].** Standard axioms only, no `sorry`, no checker definition changed.
Log: [`docs/logs/e2e-lean-m11c-2026-11-03.md`](../logs/e2e-lean-m11c-2026-11-03.md).

* **`NodeOK`/`WrapOK` from the pinned aggregation program (`zk-formal/ZkFormal/PQ/E2EAgg.lean`).**
  `aggNodeV` is the native meaning of `build_agg` (`openvm-recursion-agg.patch`): `k ≥ 2` children,
  each accepted by its own native verifier, and `Stmt.compose` (the Lean `RangeStmt::compose`) of
  their range statements is `some out` with `D(out)` the exposed tag-9 digest. `nodeOK_agg` proves
  that acceptance gives accepted children chaining from `out.s_a` to `out.s_e` (`compose_chain`).
  `aggWrapV` (verify the root against its preimage statement, `ctx` = claim digest, `InitOK`,
  `FinalOK`) gives `wrapOK_agg` from `NvFaithful` of the wrap circuit and the wrap's extraction.
  `ExtractWG` states the WHIR / LogUp-GKR straight-line extractor per key (leaf template `k`:
  `HoldsLogUp (segAir k)` at `segPub π` decoding to the statement; node: `HoldsLogUp Pin.air` with
  `D.stmt = D(st)` and lower-level children), with the bad events `hashColl`, `whirBad`, `gkrBad`,
  `rangeColl` (`BadEvents`; their QROM bounds are recorded, not Lean theorems).
  `nvFaithfulE2E_of_agg`/`e2e_sound_of_agg`: obligation 1 and the E2E statement from `NvFaithful`
  of the node and wrap circuits, `ExtractWG`, `ExtractW`, `LeafHolds` (the definition of `S.Holds`
  for the circuit's segment system) and `RangeBinding`, with `Bad := BE.Any`.
* **Genesis segments are cut (`Intake.lean`, `Machine.lean`).** `checkD2CoreGWith` is sliced
  verbatim (`checkD2CoreGWith_split`, `gRest_eq`, `checkD2CoreWithObs_split`, all `rfl`). If the
  main block is not genesis, `INTAKE` is the prefix plus `checkD2CoreWithObs`'s intake
  (`d2IntakeK`), producing an `Intake` with `d2 = some ⟨b2i, sched⟩`; the **same engine steps**
  follow (so receipts and mid-call Wasm cuts apply), and `FINAL` is `finD2K`/`tailD2New`
  (`finStep` dispatches on `d2`). If it is genesis, `INTAKE` (`genAK`) ends in the new
  configuration `gfin G` and `FINAL` (`genB`: implicit transitions and the header comparison)
  steps to `doneG`. `cm_iff_gen` proves both paths against `checkD2CoreGWith`; `cm_iff`, `rcm_iff`
  and `e2e_sound_r` are unchanged in statement.
* **The commitment view (`View.lean`).** `split : RConf → Parts` (tag, `CtxV`, `StV`, `OutV`,
  `VmV`, `WmV`) is injective (`unsplit_split`, `split_inj`). `ViewImpl` (what lanes A/B
  implement) gives one commitment per component: `ctxD` → the new `BndRec.ctxRoot`, `stD` →
  `stRoot`, `outD` → the four accumulators, `vmD` → `vmAcc`, `wasmD` → `wasm`/`inCall`; the tag is
  `phase` (`gfin` is tag 3). `viewImpl_binding`: a boundary collision is a SHA-384 (42-B)
  collision or a collision of one component commitment; `viewImpl_binding_bad` closes it with the
  lanes' per-component reductions. `chainD`/`chainD_binding`: a running list commitment over an
  injective item encoding is binding modulo `bdigest` collisions.

**M11d (lane E, 2026-11-03) [K].** Standard axioms only, no `sorry`, no checker definition changed
(sha256 `644495ff…a9ae3`), `make pin-check` ok, full v3 build 447 jobs. Log:
[`docs/logs/e2e-lean-m11d-2026-11-03.md`](../logs/e2e-lean-m11d-2026-11-03.md).

* **`NvFaithful` composition fixed and proved for the node and wrap
  (`zk-formal/ZkFormal/PQ/E2ENode.lean`).**
  * *The statement was wrong.* `NvCompositionAt` (sub-obligation 6) had no `HoldsLogUp` premise,
    so it forced acceptance on non-satisfying traces. It is refuted by any verifier that rejects
    something (`nvCompositionOld_false`). It is now amended, and `nvFaithful_of_obligations` is
    unchanged in form.
  * `build_agg` is transcribed cell by cell (`NodeRead`, `ContAsserts` with the Rust `zip` loop,
    `outCell`). `compose_of_asserts`: the continuity asserts on fixed-shape cells compute
    `RangeStmt::compose`. `zipEq_short` shows the fixed shape is load-bearing.
  * `node_composition`, `nvComposition_node` (in the generic slots), `wrap_composition`.
  * `nvFaithful_node` / `nvFaithful_wrap` take `NodeExec` / `WrapExec`: the NvAir executes the
    program's hash jobs (1), inner verifiers (2 + 4), tape (3) and asserts (4). These are the open
    remainder, generic to NV, and not provable without a Lean NvAir model.
* **`LeafHolds` proved** (`leafHolds_circ` over the circuit segment system `circSeg`: a segment
  instance is `Holds (segAir k)` at public values whose statement has its boundaries).
* **`RangeBinding` reduced to CR** (`rmsg_inj`: the pinned `range_values` message is injective;
  `rangeBinding_of`; `hColl_bdigest`: a collision is a 42-B SHA-384 collision).
  `e2e_sound_of_exec` is the E2E statement from `NodeExec`, `WrapExec`, the extractors and
  obligations 1b, 2 and 4.
* **The honest call tape (`spec/lean/v3/NearSpecV3/E2E/Tape.lean`, `defaultTargets`).**
  * A finite-use walk over the `CutW`/`Refined` copies: `TLe`, `pwO_tle`.
  * `estepO_complete`.
  * `honestK P c` has entries `(q, callResult q)`. The query list is chosen classically from
    completeness; there is no constructive recorder.
  * `estepO_honest : estepO (strictO (honestK P c)) P c = .ok c' ↔ estep P c = .ok c'`.
  * `rsteps_honest`: `RCM` reaches the next engine configuration through the honest calls.
* **Soundness budget for `BadEvents`** ([`E2E-SOUNDNESS-BUDGET.md`](E2E-SOUNDNESS-BUDGET.md)).
  * At Q = 2^64: ROM ≈ 204 bits; QROM with one-database accounting ≈ 140 bits (constants 1) or
    134.7 bits (historical constants).
  * The QROM per-proof union drops below 128 bits for deep trees: 121.8 bits at fan-in 8, depth 6.
  * The dominant term is `whirBad`.
  * The wrap has no parameters pinned at the 268-bit per-round target.

**The interface the circuit lanes must meet.** A template `k` proves `Holds SegAir_k (B, B') tr`;
obligation 2 requires `abs B = some c`, `abs B' = some c'` and `Steps c c'` with `Steps` the
closure of `CM.step : Conf → Except String Conf`, where `Conf` is `init cb wb | eng I ⟨pos, st⟩ |
fin I out | done H o | doneG`, `pos : EPos` is `start | txs rest acc rs | locals rest rs |
delayed fuel rs | incoming rest rs | yields yf yn fuel i k rs | done out`, `rs : RS` (overlay =
working set, `dq`, `bufIdx`, `metas`, `limits`, `cong`, gas/compute/burnt totals, outcomes,
outgoing, proposals, instant/locals queues, deployed/attempted code, `wasmGas`) and
`st : Recording` (recorder, cache, pipeline schedule, soft limit). `I : Intake` is fixed from
`INTAKE` on (claim, witness, walk, env, pre-state trie, receipts, txs). The wrap checks
`InitOK` (`B_0` abstracts to `init (assemble ci secB secC) w`, obligation 4) and `FinalOK`
(`B_N` abstracts to an accepting configuration, `headerOk` against the public `chunk_inner`).

---

## 4. Milestones to a first general-chunk E2E proof

### 4.1 First targets (all pinned corpus cases, cold nearcore `ok`, `expected_rel` true)

| id | case | why |
|---|---|---|
| **T1** | `d3c8/d3/02-h10196-s3` | 1 incoming receipt, 1 FunctionCall to pre-state `d3tiny` (`run`, input `again`). It writes existing storage (evicted path), logs, returns, and refunds. No transactions, so no signatures. Witness 8,382 B |
| **T2** | `d3c9/d3/00-h10018-s0` | 14 receipts; CreateAccount + Deploy + FunctionCall in one receipt, a postponed call, local receipts from transactions (Ed25519), promises, yield queue, 4 `d3rich` calls (`memory.grow`/`loop`) |
| **T3** | a shard-13 mainnet chunk with a contract call (`/data/illia/nearproof-deps/mainnet-w13/replay-cases`) | compiled Rust contracts (`call_indirect`, bulk memory, discarding branches) |

### 4.2 Milestones

Sizes are agent-effort estimates [E]: S ≤ 1 week, M 1–3 weeks, L 1–2 months, XL > 2 months.
"Lane" marks the work that can run in parallel; the critical path to T1 is
**M1 → M3 → M5-T1 → M6 → M8 → M9 → M10**.

| # | milestone | deliverable | exit test | size | lane |
|---|---|---|---|---|---|
| **M1** | Wasm leaf on a real corpus call | the call extracted from a corpus chunk by the independent clean-room checker; its spec trace proved on the main stack; outputs compared | the proof verifies; `value_return`/log bytes and gas equal the chunk's outcome; mutants rejected | S | A (Wasm) |
| **M2** | Wasm coverage for compiled contracts | `memory.grow`/`memory.size`; lift no-discard (kill rows); `call_indirect` with a cached TABLE; bulk memory; floats (`d3float`); SHIFT/CMP degree reduction | every FunctionCall in `d3c7–d3c10` (9 contracts) is eligible; ≥ 1 proved per contract; tamper suites; Lean row lemmas, std axioms | L | A |
| **M3** | real host tape | the trace generator takes the host answers from the chunk's checker run (Lean `allFeatures` host log), not the default context; all host families used in the corpus | every corpus call replays with the chunk's own answers; gas burnt equals the outcome (T1's evicted `storage_write` is the first case) | M | A |
| **M4** | Wasm segment cuts | `memRoot`/frame/register digests at cuts (SHA-384 chip in the WASM template); `run_foldSegments` ↔ AIR | a 10⁶-step call proved as 2²⁰-row segments chained by hand; a forged boundary rejected; boundary cost measured | L | A |
| **M5** | state machine in-circuit (general runtime) | M5a working-set tree + INTAKE (authenticated partial trie) + FINAL MPT root; M5b receipts and all actions + function-call gas, refunds, outcomes; M5c queues, congestion, bandwidth scheduler, yields; M5d outputs incl. Reed–Solomon `encoded_merkle_root`. Built by porting and generalising the D0a/D1 PQ tables | **M5-T1**: T1's non-Wasm part proved against its claim. Then all d2corpus shapes | XL (4 sub-lanes) | B (state), parallel to A |
| **M6** | join | STATE rows produce HOSTQ/HOSTR/HOSTB for a WASM segment in one trace; PREP sub-proof (SHA-256(code) = hash, decode/validate/instrument → `CODE`/`FUNC`) | T1 single-segment trace with no `HOSTO` oracle; tamper on a host answer rejected; PREP proof of `d3tiny` and `d3rich` | L | A+B |
| **M7** | crypto chips | 7a Ed25519 + SHA-512 (needed for T2 transactions); 7b Keccak full; 7c RIPEMD closure; 7d secp256k1; 7e p256/BN254/BLS12-381; 7f ML-DSA-65 | each: KAT vs spec, tamper, host binding (`HashInputLink`), Lean chip lemma | XL total (7a L) | C (one sub-lane per primitive) |
| **M8** | heterogeneous 8-ary aggregation | NV node over mixed templates + boundary-equality check; production params (rate 1/4–1/16 nodes, fan-in 8, ≤ 3 levels) | 8 real T2 segments aggregated; swapped or forged-boundary child rejected; node time and size measured | L | D (recursion) |
| **M9** | ZK wrap + public-input reduction | integrate the sibling D0a ZK wrap; `Init`/`FinalOut` checks against the statement | proof ≤ ~400 KB, verify < 200 ms (single core, profiled), hiding test (simulated transcript indistinguishable at the field level) | M | D (after the sibling lands) |
| **M10** | first E2E | T1 end to end: public statement only; mutants on every header output and trusted fact rejected; then T2, then T3 | `FinalVerify` accepts T1/T2/T3, rejects ≥ 50 statement mutants each | M | integration |
| **M11** | Lean join | §3.5 obligations 1–4: `NvFaithful` closure, per-template segment soundness, the `CM` small-step factorisation of `checkSuccessor`, witness extraction | `e2e_sound` with std axioms, non-vacuity on T1 (a kernel or `decide` instance of the premise) | XL | E (formal), from day 1 |
| **M12** | performance | GPU kernels for the main stack; segment-template tuning; RIPEMD/SHIFT re-layout; prover-budget experiments 2–6 | the measured 100 Tgas worst case in ≤ 3 s on 8 H200; 1 Pgas ≤ ~10 s | XL | F (needs hardware) |

Parallel lanes at once: **A** (Wasm), **B** (state; four sub-lanes), **C** (crypto; one per
primitive), **D** (recursion and ZK, after the sibling), **E** (Lean join), **F** (GPU, once
hardware is available). M2 does not block T1, so it runs beside M3.

---

## 5. Milestone 1: status

**M11 (lane E, 2026-11-03):** obligation 3 (`cm_iff`), statement assembly (`e2e_statement_iff`) and
the composition `e2e_sound` are kernel-checked; obligations 1, 2, 4 are stated `Prop`s; see §3.5
status.

**M11b (lane E, 2026-11-03) [K]:** see §3.5. Done:
* mid-call `inCall` cuts, with `rcm_iff` and `e2e_sound_r`;
* the concrete §3.2 boundary codec with its round trip, SHA-384, and the digest `abs` under a
  collision `Bad`;
* obligation 1 derived from `ZkFormal.PQ.NvFaithful` plus `NodeOK`/`Extract`/`WrapOK`
  (`E2EBridge.lean`).

**M11c (lane E, 2026-11-03) [K]:** see §3.5. Done:
* `NodeOK` and `WrapOK` proved for the pinned aggregation node/wrap programs (`E2EAgg.lean`);
  `Extract` stated against the WHIR / LogUp-GKR extractor with named bad events;
* genesis segments cut (`gfin`, delegated engine path, `cm_iff_gen`);
* the commitment view: injective component split, `ViewImpl`, the binding lemma.

**M11d (lane E, 2026-11-03) [K]:** see §3.5. Done:
* `NvFaithful` composition (sub-obligation 6) amended and proved for the node and wrap programs;
  `NvFaithful` of both reduces to `NodeExec`/`WrapExec`;
* `LeafHolds` proved; `RangeBinding` reduced to SHA-384 CR;
* the honest call tape `honestK`, with `estepO_honest` (completeness) and `rsteps_honest`;
* the `BadEvents` soundness budget document.

Open for lane E:
1. A constructive recorder for `honestQ` (the honest tape is now a Lean function, by classical
   choice; lane A's `wasmbase-tape` computes it).
2. `NodeExec`/`WrapExec`: the NvAir executes the node/wrap program (generic NV sub-obligations
   1–4; they need a Lean NvAir model or an exporter for the NV crate). The QROM bound behind
   `ExtractWG`/`ExtractW` is not expressible in this library; its budget is written out in
   `E2E-SOUNDNESS-BUDGET.md`. Per that doc, deep trees need either the single-database QROM
   theorem (GAPS S-19) or a larger per-round target, and the wrap needs pinned parameters.
3. The per-component binding lemmas `Coll stD → …`, `Coll outD → …` (lane B: `StateM5a` `Ws`
   Merkle root, accumulators), `Coll wasmD → …` (lane A), and instances of `ViewImpl` with `WF`
   records.

See `research/near-compression/e2e-general/m1/README.md` for commands, logs and numbers.

**Done [M]:**
* **Call extraction.** `extract_calls.py` takes the FunctionCall invocations of a whole corpus
  chunk from the independent clean-room checker: code, method, prepaid gas, input, outcome.
* **First real-chunk proof on the main stack.** `d3tiny.run("hello")` from T2
  (`d3c9/d3/00-h10018-s0`) was run by the freshly built Lean `prepIf`, checked (`CHECK OK`), proved
  and natively verified on the main stack: 1,469,458 B base proof, 268.2-bit calculator,
  35.6 s prove, 30 ms verify on 12 threads. Mutants: 92/93 rejected; the accepted one is the known arity-0 `pub.result` gap. The status and the log bytes match the chunk.
* **The comparison exposed two gaps that the earlier KAT-style checks could not see.**
  * *(a) No host → memory writes.* `read_register` writes nothing to linear memory and `input`
    carries a placeholder payload, so the proved trace returns `0000000000` where the chunk returns
    `hello`. There is no AIR on main with both `IF` and `REG`. The earlier "`d3tiny` in domain"
    claims therefore overclaim: they hold for the public statement only.
  * *(b) Wrong host gas.* Host gas comes from the default context. T2 differs from the chunk by
    exactly 5 × `read_cached_trie_node` (11.4 Ggas), T1 by 28.1 Ggas (evicted path).

**Done 2026-11-03 (lane A) [M]** (`research/near-compression/e2e-general/m1/README.md` update, `../m3/README.md`):

* **M1-a.** `wasmBaseIfRegAir` (`WasmBase/RegMem.lean`) is the first AIR with both `IF` and the
  register table.
  * **Memory write.** A `read_register` group writes the register bytes into linear memory at
    `ptr + pos` (STORE's shape: consume the old byte at `mtp`, produce the new one at `ts`).
  * **Binding.** Bus 211 ties each write group to a successful `read_register` HOST row; HOST'
    carries an `rr = [hid = 49]` selector.
  * **Forged register bytes.** Every register read must consume. This closes a hole in REG, where a
    read row could forge register bytes.
  * **Arity-0 gap closed.** The public result is 0 unless returned.
  * **Result.** `d3tiny.run("hello")` (T2) proves with `value_return = 68656c6c6f`:
    1,474,766 B, 268.2-bit, prove 18.1 s, verify 29 ms.
  * **Mutants.** 136/136 rejected. One documented oracle gap is reported, not counted: a consistent
    HOST + HOSTO `g_after` change (M6).
  * **Lean** (`WasmBase/Main/RegMemLink.lean`, standard axioms): `read_register_run` (the spec's
    post-state is `writeBytes s4 ptr d`), `heap_read_register`, `regw_write_msgs`,
    `read_register_rows_heap`, `regw_pub_result`.
  * **Named open.** The REG' group walk at index 27, and R16-backed `mtp < ts` (`regw_time_lt` is
    the algebraic step).
* **M1-b.** The key bytes of `storage_read/write/remove/has_key` and the value bytes of
  `storage_write` are on HOSTB with the MEMIO link. The value group's wire id is `hid + 256`.
* **M3.**
  * **Tape.** `wasmbase-tape` records each Wasm call's host answers from the unmodified
    `allFeatures` checker run: a link-time wrapper of the compiled call entry returns the real
    result and replays the call from the checker's own context and trie-backed store.
  * **Corpus.** Over d3c7–d3c10 (19,007 cases, 27,197 calls) every call the AIR covers equals the
    chunk's outcome when traced with its own answers: status, burnt gas, logs and return value.
    That is **3,414 / 3,414** calls, including all **1,755** `d3tiny` calls, T1 and T2. There are
    0 differences and 0 trace failures.
  * **T1 proof.** T1 (evicted `storage_write`, register-1 fill) proves with its chunk tape
    (1,476,278 B).

**Done 2026-11-03, second session (lane A): M2 corpus coverage** (`research/near-compression/e2e-general/m2/README.md`):

* **Census** (`wasmbase-tool census`). The 23,317 uncovered calls need wrap/extend, `if` with a
  result, `unreachable`, `ed25519_verify`, and (`d3rich` only) `memory.grow`, `abort` (`i32`
  parameters) and `promise_yield_resume` (`i32` result). **No discarding branch, `call_indirect`,
  bulk memory or float occurs in d3c7–d3c10**; those are T3 (compiled Rust) work.
* **`checkModuleM2` + `wasmBaseM2Air`** (tables 0–26 of `wasmBaseIfRegAir`, REG-C 27, CONV 28,
  UNREACH 29). `memory.grow`/`memory.size` and hosts the HOST row cannot type are admitted with
  opcodes no chip can fetch: sound, and a run that executes one is not provable.
* **Register refill.** REG-C's clear group consumes a live register before a refill (and is bound
  to the following fill); the generator no longer refuses refills.
* **Sweep at `wasmBaseM2Air`** (19,007 cases, 27,197 calls, 0 replay mismatches, **0 different**):
  **21,438 equal** (status, burnt gas, logs, return) + **4,480 equal-abort** (status, logs, trace
  final budget = spec's) = 25,918 of the 26,731 calls that run a method; every call of `d3tiny`,
  `3b1ad423`, `e1fe4f9c`, `d3ed`, `d3hostx`; 17,409 / 18,222 `d3rich` calls. Remainder (813, all
  `d3rich.run`): `memory.grow` 385, `abort` 120, `promise_yield_resume` 58 (no chip); stack-budget
  trap 124, address `≥ 2^27` 89, out-of-gas at a Wasm instruction 37 (generator domain).
* **Mutants**: CONV/UNREACH/REG-C 37 / 37 rejected on three corpus calls; the full battery at
  `wasmBaseM2Air` on a refill call 211 / 211 (the HOSTO `g_after` gap reported, not counted).
* **Lean** (standard axioms): `Main/M2Link.lean` (`conv_row_spec`, `step_conv`, `execNum_conv`,
  `unreach_row`, `regc_clear_cancels`, `regc_clear_next`); `Main/RegWalkG.lean`: the REG group
  walk and `RegLenAgree` for any AIR with REG's constraints at an index, instantiated at index 27 of
  `wasmBaseIfRegAir` and `wasmBaseM2Air`.

**Done 2026-11-03, third session (lane A): M4 segment cuts, M2 gaps, coverage**
(`research/near-compression/e2e-general/m4/README.md`; m2 README updates; log
`docs/logs/e2e-laneA-wasm-2026-11-03.md`):

* **M4 [M].** `wasmBaseSegAir` (`WasmBase/SegAir.lean`): M2's chips unchanged + `SEGB` (STATE and
  gas register from public values), `CUTI`/`CUTO` (SHA-384 `ctxDigest` of the sorted live
  non-memory channel messages, activation ids relabelled to depths, `CIDMAP`), `DROP` (dead locals of
  tombstoned activations; RET sends the tombstone), `MEMB`/`MPATH` (SHA-384 Merkle `memRoot` over
  1 KiB blocks: touched blocks produced at `t_in`, consumed and re-hashed at the end, old and new
  paths, root chain), HOST with the gas register `(S_seg, segb)`, and the native SHA-512 chip v4 on
  bus 103. **A 1,128,011-step call proved as 5 segments of 2^18 steps (≈ 2^20 trace rows each),
  one verifying key, chained by hand** (`B_out(k) = B_in(k+1)`): 1.73–1.75 MB per segment proof, prove 596–823 s each (8 threads, shared host), verify 63–223 ms, 268.2-bit calculator. A corpus call
  with host calls and a register refill (`3b1ad423.run`) proves as 4 segments. **Tampers:**
  54 / 54 rejected (forged public boundary fields, CUT/MEMB/MPATH/DROP/SEGB/gas-register cells) on two segments of the refill call; a Lean audit found two unsound range checks in the new tables (MEMB split, CUT padding length), both fixed. **Boundary cost:** per touched block 18 leaf + 2·D path compressions (`D = 16`
  for NEAR's 64 MiB initial memory: 50 compressions ≈ 0.53 M cells per written block); 59 % of a
  2^18-step segment's cells in the memory-heavy benchmark (fixed per cut).
* **M4 [K]** (sub-lanes): `exec_of_rows_cut` (rows from an arbitrary related boundary to a cut or
  halt, global time, host gas segments), `cuts_foldSegments`/`cuts_halt`/**`cuts_csteps`** (onto lane
  E's call machine), `RelW.relabel`/`Bnd.relabel`, `cutView` + `cutDigest_binds`, MEMB/CUT/DROP row
  lemmas, `mpath_block` + `rch_chain`. A Lean counterexample (`memb_split_counterexample`) found an
  unsound MEMB split check, fixed in the AIR. Open: `cutView` = the relabelled live list (needs
  `RelW` register clause, spaces 1/7–15, `fns` Nodup, field bounds), leaf = SHA-384 of the
  block bytes, a Lean model of the SHA-512 chip, lane E's `wasmD` instance (this AIR has one
  `ctxDigest`). Done besides: `leaf_link`, `seg_hsend_r16`, touched blocks distinct, an R16 audit
  of every AIR (`R16Audit.lean`).
* **M2 gaps [K].** R16 send bound for `wasmBaseIfRegAir`/`wasmBaseM2Air` (`m2_hsend_r16`), so the
  REG walk and `mtp < ts` are theorems about `Holds` (`m2_regw_mtp_lt_ts`, with `ts, mtp < 2^29`
  explicit). `Ctx` split (`ModFacts`; `M2Ctx.toCtx`), successor facts derived from `checkModuleM2`,
  base row lemmas on constraints only (`HoldsC`) and for every `Ctx` (the `else` arm in CTRL),
  `m2_hsend_fetch`, and **`m2_rowfacts`**: `RowFacts2` for every active non-HOST instruction row
  of a `wasmBaseM2Air` trace (tables 1–14, IF 26, CONV 28, UNREACH 29) from `Holds`, `M2Ctx`,
  `PubOK`, `CodeOK`, `FuncOK`. Not yet: the STATE/CH bus split over the M2 tables (REG-C's space-6
  messages need a `RegCLinked`-style link), then `wasm_base_sound_m2` with `HoldRow`/HOSTO named.
* **Absent-register header [M][K]** (`wasmBaseM2rAir`): `RINIT` + REG-A force a clear before a
  refill; the double fill verifies at `wasmBaseM2Air` and is rejected at `wasmBaseM2rAir`
  (25/25 tampers). Open: the bus-level one-header-per-register count.
* **Coverage [M]** (`wasmBaseM3Air`): i32 host tags (`abort`, `promise_yield_resume`),
  `memory.grow`/`memory.size` (size message, MEMG/MSZ/GINIT): **555 of the 813 M2 remainder calls
  now equal, 0 different**; remainder 258, all pre-existing generator limits (129 stack-budget
  traps, 91 addresses `≥ 2^27`, 38 out-of-gas at an instruction).

**Done 2026-11-03, fourth session (lane A): M4b** (`m4/README.md` §8; log
`docs/logs/e2e-laneA-wasm-2026-11-03.md`):

* **Soundness findings, fixed [K][M].** `Holds (wasmBaseSegAir …)` was unsatisfiable (the native
  chip's bus 103; `seg_holds_false`), so the M4 Lean results were vacuous: everything is restated
  over `HoldsX` with the chip as the named contract `ChipIf` (lane B's `Sha512IfContract`, reused).
  CUTO's filler row was not forced to zero (`cuto_filler_counterexample`): fixed by gating the
  message words with `act`.
* **Tampers [M].** Final `wasmBaseSegAir` (after `r16 gl`, and again after the filler fix):
  54/54 rejected; the filler-fixed AIR re-checks the 1.13 M-step benchmark (5 segments, chained)
  and proves the refill call's 4 segments.
* **Segment soundness as one theorem [K]: `seg_sound`** (cut case): from `HoldsX` + `ChipIf`, the
  `CutSeg` built from the trace, `seg n s0 = .cont sN`, the extended relation `BndC` (register and
  space clauses; `fns` Nodup proved for both checkers; field bounds from CUTO) at the out cut, and
  the public `ctx_out` = SHA-384 of `cutView X sN`. MEMB leaf = `sha384` of the block bytes and
  MPATH node = `sha384 (l ‖ r)` under `ChipIf`. Named: host-chip relies (M6), `HostBLinked`,
  `RegCLinked`, `CodeOK`/`FuncOK`, `TombDead`, the in-boundary `Nodup`; not yet conjuncts: memory
  root, CUTI side, halting segments.
* **`ViewImpl.wasmD` [K]:** concrete instance (single ctxDigest as frames/globals/registers digest,
  SHA-384 memory Merkle root), `wasmD_binding : Coll wasmD → Sha384Coll`, `viewImpl_hwasm`. No
  `BndRec` change needed; optional proposal to lane E: `WasmBnd.gasLeft`.
* **`wasm_base_sound_m2` [K]** with the M2 STATE/CH split (`RegCLinked` named).
* **Boundary cost [M]:** `wasmBaseSegAirMP`, MPATH as a batched Merkle multiproof (`mp_tree` [K]):
  1,610 → 680 compressions per 2^18-step segment, chip 2^18 → 2^17, cells 38.86 M → 27.91 M (−28 %),
  boundary 59 % → 43 %, peak RSS 19.4 → 17.2 GB; proof size/time unchanged on the current shape;
  85/85 tampers rejected.

**Done 2026-11-03, fifth session (lane A): M4c** (`m4/README.md` §9; M6 scope `m6/README.md`):

* **Finding [K/S].** The HOST-row premises (`HoldRowS`, `HostRegRely`, `HostRely.wf`) quantify over
  every related pre-state, but `RelW` does not pin the host-side state (`gas.remaining`, `ctx`, …;
  `relW_sigma` [K]). On any segment with a continuing host call they cannot hold, so the segment
  theorems (and `wasm_base_sound_m2`) are **vacuous on host traces**. Host-free segments are
  unaffected.
  * The counterexample is mechanised (`HostVacuity.lean`).
  * σ-pinned restatements are proved: `seg_sound_σ`/`_cσ`/`_σ_mp` and `seg_chain_σ`, with the
    thread being the host side plus registers.
  * Open: that an honest run satisfies `HoldRowSσ`. This is argued, and needs the two-run
    `callHost` footprint (M6.2).
* **Segment soundness [K]:**
  * `TombDead` discharged (`seg_tombDead`); `InDom` at the out-boundary (`seg_inDom`, `seg_wasmD`).
  * Halting segments (`seg_sound_halt`/`seg_sound_any`).
  * CUTI side (`cuti_view`: `ctx_in` = digest of a canonical list ⇒ CUTI = that list or
    `Sha384Coll`), `initS_nodup`, re-entry (`seg_reentry`).
  * Memory roots and memory frame (`seg_membIn`, `seg_mem_frame`, `seg_memRootOut`).
  * **The chained-segments theorem** `seg_chain_mem` / `seg_chain_k`: `Sha384Coll` or a `CSteps`
    run of lane E's call machine from `s0` to `sN`, with only ChipIf, CodeOK/FuncOK
    (→ `CodeIs`/`FuncIs`), host relies (M6), size bounds and the first segment's in-boundary named.
  * Everything is also proved for `wasmBaseSegAirMP` via a generic `HoldsXS` layer; **MP is now the
    default segment AIR**.
* **AIR change [M][K]:** call-key bus 214 (HOST `nk` offer; HOSTB/REG-C lookups) makes
  `HostBLinked`/`RegCLinked` theorems (`seg_hostBLinkedL`, `seg_regCLinked`). Re-proved the refill
  call (4 segments); tampers MP 45/45 and M4 32/32 rejected; the benchmark re-checks.
* **`memory.grow` segments [M]:** `wasmBaseSegAirG` (MEMG, SEGG size message + depth-lift root,
  MEMBG grown blocks, MEMBH above 64 MiB). A 7-segment grow call chains, two segments prove, and
  49/49 tampers are rejected. `memRootOf` is unchanged by grows except `nodeH root Z_16` at the
  one possible 16 → 17 lift [K]. Its `seg_sound` is open (needs a size clause).
* **Non-vacuity [K][M]:** sound executable checkers for `Holds`/`HoldsX`/`ChipIf` and the
  trace-level premises. Honest dumps satisfy every relation the live theorems use.
  `wasm_base_exec_host_holds` (pre-M2) looks vacuous on host traces.
* **M6 [S][K]:** scope (`m6/README.md`). `HostRely.sp` is a theorem; the host footprint is proved
  for all 89 arms (`callHost_hinv`); `RegWF` is preserved by every step.

**Next (lane A):**
* M6: the σ-pinned host-row premises, then `HostIf ⇒ HoldRowS ∧ HostRely` (M6.2) and the
  noninterference half of the footprint (M6.1).
* One combined chain statement (memory + key bus + MP); the first segment's `h0` from `enter`.
* `seg_sound` for `wasmBaseSegAirG`; the corpus grow calls.
* The generator limits (stack-budget trap row, out-of-gas row,
  `≥ 2^27` addresses).
* **Distinguish the storage key and value bytes in-circuit** when the state side consumes bus 210
  (the `hid + 256` wire convention, M6).
* **M6.** Replace HOSTO so the tape is bound inside the proof.

The milestone-1 exit test (return bytes, logs and gas equal the chunk's outcome on T1 and T2, with
mutants rejected) is met. The gas equality holds outside the proof (the tape) until M6. The
`lake build WasmBase` breakage reported on 2026-10-31 was fixed on main (`6a1739cd7`), and the build
is green with the new files.

### 5.0 Lane D (ZK wrap for M9): status, 2026-11-03 (milestone D-4)

See `research/near-compression/e2e/README.md` §0 (§0a for D-3, §0b for D-2) and
`research/near-compression/e2e/ZK-ARGUMENT.md`. The log is
`docs/logs/e2e-zk-lane-d-2026-11-03.md`.

**Done (D-4):**
* **Obligation H is closed** (the owner decision was adopted).
  * The setup pins the FINAL heights (`Setup::final_heights`).
  * V_d checks equality before any other work, and rejects a zk vk with no pinned heights.
  * The prover pads to the pinned heights.
  * Setups without ZK are byte-identical.
* **Re-run on the 3 D0a chunks.**
  * Packets: 325,709 / 323,958 / 325,247 B.
  * Verify: 38.8–54.4 ms on one core.
  * Negatives: 26/26 per chunk, including 4 height negatives (each must hit the pinned-height
    check) and a re-pinned control.
  * Distinguisher: 0/287 for both witnesses.
  * A fixed-setup second proof gives a byte-identical setup.
* **`zero_knowledge_established = true`**, scoped to:
  * statistical ZK, classical programmable ROM, ε_ZK ≤ 2^-184.4;
  * the statement (claim, hint, setup), relative to the per-chunk setup's shape class.

  It is not a QROM claim.
* **Q (QROM) is partly closed.**
  * FINAL part: 2^-121.0, via AHU19 O2H Thm 3 and GHHM21 Thm 1, both checked against the
    papers.
  * The base point `u` is open: the D0a base commits only 2–4 columns.
  * Two closures, both owner decisions: base `zk = 2` (2^-103) or a base salt (about 2^-120).
    Neither reaches 128 bits.
* **Size option:** one EF stacking mask column is proved impossible for any number of τ chains.
  Not built.
* **Review-zk6 N1–N4 folded in.**
  * N1: joint-list text, minus 3 bits on PIOP terms (minimum 318.9); the floor is unchanged.
  * N2: mask-count assert.
  * N3: layout step bound.
  * N4: no thread-locals.
  * The fuzzer is adopted.
* **M9 wrap interface:** §5.0.1 below.

**Open (D-4):**
* **Owner decision on `u` in the QROM:** base `zk = 2` or a base salt. Either needs a chain
  re-run. Check: `R` (FS jobs) is estimated at ≤ 2^12, not yet counted.
* A shape-independent setup for the general wrap (§5.0.1, blockers 2 and 6).
* An independent review of D-4: §6.5 QROM composition, `check_pinned_heights`, the padding
  path.

#### D-3 status (superseded by D-4 above)

**Done (D-3):**
* **`zk = 6` built** (FINAL, `NEARPROOF_ZK_FINAL=6`).
  * No stacked opening is sent. WHIR batches with `μ^j + ν c_j` (the stacking coefficients),
    and `B = Σ μ^j q̂_j(u)` is sent after `μ`.
  * The stacking Libra masks are extension-field columns, 12 base columns each, so there are 37
    mask columns.
* **Soundness re-derived** (ZK-ARGUMENT §5, in the per-move form of E2E-SOUNDNESS-BUDGET §3.1).
  * The μ move is unchanged, at 283.6 bits.
  * The new ν move is `E_1/|F| + ℓ₀/|F|`, at 295.6 bits.
  * FINAL minimum: 268.2 bits at the 268 target, 274.0 at 274.
* **Lemmas D and E are proved.** D is Lemmas D1 + D2; E is Lemma V, which is exact.
  * Simulator and hybrids are complete.
  * **ε_ZK ≤ 2^-184.4** (ROM), for the statement (claim, setup, heights).
* **Measured on the 3 D0a chunks.**
  * Packets: 325,751 / 325,722 / 325,247 B. That is +6 KB against `zk = 5`: the price of the
    provable masks.
  * At 274 bits: 330,485 B.
  * Verify: 41–67 ms on one core.
  * Negatives: 21/21 per chunk.
  * Distinguisher: 0/287 for both the right and the wrong witness.
  * `zk-diff`: clean.
* **Independent review: fixes landed.** #1 (verifier hang), #2 (panic), #5, #6, #7 and #8 are
  fixed, with regression tests.

**Open:**
* `zero_knowledge_established=false` because of **obligation H**. The FINAL trace heights are
  public, but V_d does not pin them (review #4). The fix is to record them in the setup, have
  V_d check equality, and have the prover pad. It changes the setup content, so it is an owner
  decision.
* **Q:** the ZK proof is in the classical ROM. A QROM-programming lemma is needed for the PQ
  claim. Lane E's QROM work covers soundness only.
* Independent review of the D-3 verifier changes (`WhirBatch::Deferred`,
  `stacking_final_coeffs`).
* Size lever: one extension-field mask column with three τ chains would save about 4.4 KB, but
  it needs a new rank lemma.

#### D-2 status (superseded by D-3 above)

See `research/near-compression/e2e/README.md` §0 and `research/near-compression/e2e/ZK-ARGUMENT.md`.
The log is `docs/logs/e2e-zk-lane-d-2026-11-03.md`.

**Done:**
* **PIOP masking of the FINAL layer is built.** It is the `WhirLevers::zk = 5` mode,
  `native/recursion/patches/zk-piop.patch`.
  * Masked GKR: a root sumcheck replaces the half-sum and `q_0` messages, plus off-cube level
    masks and Libra masks.
  * Masked batch sumcheck: a Libra mask, last-variable column masks, and no per-AIR LogUp terms.
  * Masked stacking reduction: sparse mask claims and a committed-column Libra mask.
  * The public program columns stay unmasked, because V_d checks them.
* A self-test on toy AIRs in the FINAL configuration rejects every tampered zk field.
* **Measured on the 3 D0a chunks (FINAL only, `zk = 5`).**
  * Packets are 319,695 / 320,464 / 319,779 B.
  * Fresh-process verify takes 40–50 ms on one core, of which the FINAL check is 24–26 ms.
  * 21/21 negatives pass per chunk, and the minimum is 268.2 bits per round.
* **Split packing (`zk = 3/5`) is fixed.** The FINAL layout is 68 columns, against 98 without
  splitting. All packing loss from the reserved rows is gone.
* **Verify is in-process** (sub-agent). `statepublic` is a library call, and the TAPE
  evaluation is folded. The non-ZK-PIOP packets verify in 32–34 ms on one core.
* The simulator and the hiding error are written down in ZK-ARGUMENT.md §6. The witness-guessing
  distinguisher and the two-witness test have been run.

**Open:**
* `zero_knowledge_established=false`. Lemma D (the stacking mask's joint rank) and Lemma E
  (per-column absorption of opened rows plus stacked openings) are argued but not proved.
* The fix for both is a protocol change: batch WHIR with the stacking coefficients so that no
  individual stacked opening is sent, and use an EF-valued stacking mask. It would also save
  about 5 KB.
* An independent review of the masked verifier is still needed.

#### 5.0.1 M9 wrap interface (lane D draft, 2026-11-03)

This section defines what the M9 wrap consumes from M8 (the heterogeneous 8-ary aggregation)
and what it requires of the lanes below it. Tags used:
* **[main]**: on main.
* **[patch]**: on main only as a patch file, not rebased onto the current recursion tree.
* **[D-4]**: lane D milestone D-4 (this branch).
* **[plan]**: not built.

**Reference point: the D0a chain [main].** It is
`base (zk=1) → L1..L4 NV (zk=0) → FINAL (zk=6, final domain)`. V_d (`nv/vd.rs::verify_final_claim`)
checks five things:
* the pinned `vk_final`;
* `pvs[0] == level`;
* `check_height_caps`;
* the FINAL program columns against the pinned program (`check_final_program_at`, at the batch
  point from `verify_with_point`);
* `pvs[1..19] == digest_cells(StatementClaim::digest())`.

`StatementClaim::digest()` is the tag-8 SHA-384 of the base proof's public values. Cached roots
are folded in by `node`, or, with tape-eval, `node(G1, tape_eval_digest(u, openings))`.

The packet is `hint ‖ u ‖ FINAL`. The setup (`main.rs::Setup`) is
`{air_sha256, base_params, final_vk, program, level}`. D-4 adds `final_heights` [D-4].

**The setup is per chunk today.** The NV program is straight-line and specialised to the
child's vk and committed heights. The three D0a chunks have three setups (program lengths
142,654 / 143,132 / 144,468; ZK-ARGUMENT §7; README §7 item 3).

##### 1. What the wrap consumes

**(a) One proof: the root node `π_root`.** It is an NV proof over the node AIR set (NvAir, SHA
compress, table, byte). Its public values are `[level, D]`.

The [patch] statement is `RangeStmt` (`openvm-recursion-agg.patch`, `nv/agg.rs`):

```
D = SHA-384(tag 9 = TAG_RANGE, [n_ctx, n_state, ctx.., a, e, s_a.., s_e..])
```

with:
* `ctx` = `claimDigest` (identical in every child; the node asserts it);
* `[a, e)` = the segment index range;
* `s_a` = `B_0`, `s_e` = `B_N`.

A node takes its children's preimages as witness, hashes them in-circuit, and asserts:
* `ctx_i = ctx_0`;
* `a_{i+1} = e_i`;
* `s_a(i+1) = s_e(i)`.

The Lean counterpart is `nodeOK_agg` / `Stmt.compose` (`ZkFormal/PQ/E2EAgg.lean`).

**(b) The wrap program [plan]. Its wrap-specific asserts are all in-circuit.** It is one NV
program, run under the final domain (`ShaTranscript::new_layer(true)`, `Sha384CpuEngine::new_final`).
It does the following:
1. Verifies `π_root` (`build_verifier`, `child_nv`).
2. Binds the root's program: its cached program root equals a pinned constant `C_node` (see 1d).
3. Witnesses the root preimage `(ctx, a, e, B_0, B_N)`, hashes it with tag 9, and compares the
   result with the root's `D` (as `ChildKind::Node` does).
4. Asserts `a = 0`. `e = N` stays a witness and is never exposed.
5. Asserts **Init**: `B_0.phase = init`, position, clock and accumulators zero, and
   `B_0.claimDigest = ctx`. The witness-commitment part of `B_0` stays free. Lean `InitOK` has
   `secB` and `w` existential, so only the public-derived fields are checked.
6. Asserts **done**: `B_N.phase = done`.
7. Asserts **FinalOut**, in one of two ways:
   * **(i) in the wrap:** witness the public-statement bytes `S` (`chunk_inner` + section C +
     `epoch_id`/`protocol_version`/`chain_id`, decision D-2), check `SHA-384(S) = ctx`, and
     compare the header fields with `FinalOut(B_N)`.
   * **(ii) in the `FINAL` template (lane B, M5d):** the template takes `S` as a witness hashed
     to `B.claimDigest` and checks `headerOk`, so `phase = done` already implies FinalOut.

   **Recommendation: (ii).** It keeps the wrap template-agnostic and the same size as the D0a
   FINAL, and it matches lane E's `cm_done_header` / `FinalOutPub`.
8. Exposes `[LEVEL_WRAP, D_wrap]`, with `LEVEL_WRAP` a setup constant and `D_wrap` the
   `claimDigest` under a wrap-only tag (domain-separated from tags 8 and 9). The root's own level
   is **not** re-exposed, because it would reveal the tree depth.

Nothing else leaves the tree. `B_0`, `B_N`, `N`, the per-segment boundaries and every segment or
node FS value stay witness. This matches plan §3.4 ("No boundary leaves the tree") and lane E's
`aggWrapV`. **Verified:** no field of §3.2 `B` is needed natively once FinalOut is in-circuit.

**(c) Native V_d [plan], a variant of today's.** The pinned vk, `LEVEL_WRAP`, the pinned heights
(D-4 equality), the pinned wrap program (public program columns), and
`pvs[1..19] == digest_cells(H(tag_wrap, SHA-384(S)))`. V_d computes this from the public
statement alone:
* no hint, no `prepD*`, no `statepublic` over private data (D-2);
* no `u`, no `base_params`, no `air_sha256` of a base AIR.

The packet is `S ‖ FINAL`.

**(d) The setup must pin one setup for all chunks:**
* `vk_wrap`, `program_wrap`, `LEVEL_WRAP`, `heights_wrap` (D-4 form);
* the constants embedded in those programs, for audit only (V_d does not read them):
  * per template `t`: `(vk_t, fixed per-AIR log and tight heights_t, C_t)`;
  * the node vk and pinned node heights;
  * `C_node`;
  * `d_min` and arity 8.

`program_wrap` is a function only of the root's vk, its heights, and `C_node`. So a single wrap
setup exists **iff every possible root has the same vk, the same committed heights, and the same
program commitment, independent of N and of the template mix.** Today that holds for none of the
three. The requirements:

* **Leaf heterogeneity.** A level-1 node's program unrolls each child's vk and heights, so a node
  over 8 mixed templates has up to `T^8` programs. Two options:
  * **(A) per-template normaliser [plan].** A one-child NV over each template leaf, with program
    `P_t` and the template's vk as a constant. It maps the template's raw public values (lane A's
    `wasmBaseSegAirMP` has 108, M5a's are different) into a canonical tag-9 `RangeStmt`. Every
    normaliser proof shares the NV vk and pinned heights. Level-1 nodes check that the child
    program root is in `{C_t}`, using a pinned constant set and a witness selector. This costs one
    extra NV proof per segment.
  * **(B) one universal leaf verifier with the vk as witness.** It does not exist. The NV builder
    is straight-line per vk.
* **Fixed template shape.** Each template's per-AIR heights (log and tight) must be fixed, by
  padding to `heights_t`, or `P_t` varies per segment. The D0a chain needed `tight_floor` for the
  same reason. Lane A's segments are about 2^20 rows each, but the per-table heights are not
  pinned.
* **Node uniformity (program self-reference).** NV binds a child's program either to a constant
  of an earlier program (anchor `(M, C_M)`) or to its own program (BIND). So a fixpoint program
  `P*` across levels needs uniform children:
  * one arity, 8, at every node;
  * `d ≥ d_min` so that the root is a converged level (`> M`);
  * node heights pinned (`tight_floor`, as in D0a).

  The D0a chain's levels have byte-identical vks, and the program converges by about L4 (agg-tail
  log: only L4 and L5 are admissible children of FINAL). Mixed arities would need a set of node
  programs that refer to each other, which is circular unless the program commitment is moved
  into the statement (a design change, lane D).
* **Measured caveat [patch].** Two sibling production depth-2 nodes over different leaves had
  different program lengths (232,318 vs 232,702 rows; `docs/logs/pq-agg-depth2-legal-2026-10-24.md`
  §5.5). The log attributes it to the different leaves each node covers; the mechanism (most likely the children's committed heights) was not isolated. It must be removed before BIND across siblings can be relied
  on.

##### 2. ZK requirements on the lower layers

| item | requirement | status |
|---|---|---|
| masking | only the wrap is masked (`zk = 6`). Every leaf, normaliser and node is `zk = 0`. The NV generator asserts unmasked children (review #7), and ZK at an inner level is impossible because the parent recomputes the RO in-circuit (ZK-ARGUMENT §1) | [main] for the chain; the same holds for the tree |
| transcript domains | leaves and nodes use the non-final domain. The wrap alone uses `new_layer(true)`, so programming the RO at the wrap's points stays consistent with every in-circuit evaluation. Node children each start a fresh transcript (`restart_transcript`) | [patch] for nodes |
| PCS hiding at segments (`zk = 1` analogue) | **not needed** if no FS-derived segment value leaves the tree. D0a needs it only because `u` is in the packet (tape-eval). In the general design, `u` (if any template keeps a tape-eval cached table) and the cached roots stay inside the node and normaliser statements. **Condition:** no `StatementClaim::tape_point` or cached root may reach V_d | holds by the design of 1(b); must be kept |
| private "public tapes" | lane A's HOSTO host tape (until M6) and M5a's `WRITE`/`TCH` public tape are segment public values today. In the tree they are hidden by the wrap, but they must not be needed natively. M6 and M5b bind them in-circuit. The cached CODE/FUNC roots that lane A's segment check verifies natively (`check_code_root`) must instead be compared in-circuit with `B.codeRoot`/`funcRoot` (from PREP) by the normaliser or node | [plan] (M6, M5b, M8) |
| unsalted digests of private data | `B_0`, `B_N`, `stRoot`, `memRoot`, `ctxDigest` and the accumulators are deterministic digests of private data. Publishing any of them would allow witness guessing. 1(b) keeps them in-circuit | holds by design |
| heights (obligation H analogue) | the wrap's heights are a function of its program, which is a function of the root's shape. **If N changes the depth or the top arity, the root's vk, heights and program change, and `level` changes, so the depth (⌈log₈ N⌉) and the arity leak.** ZK for `(claim, setup)` needs a chunk-independent root shape: fixed arity 8, depth `≥ d_min`, the root level not exposed, and the root and wrap heights pinned. N must then be padded to `8^d` for the chosen `d`, with **PAD leaves**: an identity template `B_out = B_in`, admissible only when `B_in.phase = done` (a PAD template is not in plan §3.1's menu). Alternatively, depth classes can be published as setup variants, with ZK for `(claim, setup, d)`; `gasUsed` is already public, so this leaks a size class (owner decision). The plan provides neither padding nor PAD; §2 says "the number of segments grows with the chunk" | **open** |
| wrap parameters | the wrap must meet the 268-bit per-round target with pinned params (E2E-SOUNDNESS-BUDGET §1 item 1). D0a's `zk = 6` FINAL meets 268.2 / 274.0 | [main] for D0a; must be re-pinned for a root child |

Size: the D0a wrap over L4 is 325.2–325.8 KB [main]. The production agg roots, not ZK, are
316 KB (depth 2) and 322 KB (depth 3) [patch]. A wrap over an agg root has not been measured
(agg log §4 item 2). It should be close to D0a's if the root's geometry equals L4's (both are
NV children, the same verifier program shape).

##### 3. Blockers and open questions, in order

| # | item | owner |
|---|---|---|
| 1 | **Rebase the agg overlay** (`agg.rs`, `build_agg`, `RangeStmt`, per-child BIND, `restart_transcript`) onto the current stack: `e2e-verify` + `zk-pcs` + `zk-piop` + tape-eval + D-4. Today it exists only as `openvm-recursion-agg.patch` on `f08bf28`. The d4h tree has no `nv/agg.rs` and no `TAG_RANGE` | D (M8) |
| 2 | **A chunk-independent root shape:** fixed arity 8, `d_min`, pinned node heights, the `P*` fixpoint across levels and siblings (find the cause of the 232,318 vs 232,702 row difference), and the root level not exposed. Without this, `setup` is per chunk (D0a README §7.3) | D (M8) |
| 3 | **Template heterogeneity:** the per-template normaliser with `{C_t}` set binding (option A), or a design change that moves the program commitment into the statement | D (M8) |
| 4 | **Fixed shape per template** (pinned per-AIR log and tight heights, prover pads) | A (WASM), B (INTAKE/STATE/FINAL), C (CRYPTO), with A+B for PREP |
| 5 | **Canonical boundary statement:** every template exposes, or its normaliser derives, `(claimDigest, h(B_in), h(B_out))` with `h = bdigest ∘ BndRec.codec` (lane E M11b). This replaces lane A's 108 raw fields and M5a's `(RCH, TCH, change index)`. Hashing inside the AIR is cheap, because the SHA-512 chip is in every template | A, B; E for the codec |
| 6 | **Padding policy for N:** PAD template plus `8^d` padding, or published depth classes. This is an owner decision, because it changes the ZK statement or the prover cost (up to 8× leaves at a class boundary) | owner; then B (PAD template), D |
| 7 | **Init and FinalOut placement:** recommendation 1(b)(ii), with `headerOk` in the FINAL template and Init in INTAKE. There is also an ambiguity in plan §3.4: "`B_0 = Init(claimDigest)` … `stRoot` = the working-set root INTAKE committed" is circular if INTAKE is the first segment. Proposed fix: `B_0` is the pre-INTAKE configuration (`init`, with the witness commitment free) | B (M5d), E (`InitOK`/`FinalOK` wording) |
| 8 | **In-circuit cached-root binding:** CODE/FUNC (lane A `check_code_root`, today native) and any tape-eval cached table bound to `B` fields inside the normaliser or node; no cached root or `u` in the wrap statement | A, D |
| 9 | **M6/M5b:** HOSTO tape and M5a public `WRITE` tape replaced by in-circuit producers. Not a ZK leak inside the tree, but needed for soundness without native checks | A, B |
| 10 | **Wrap ZK obligations carried over:** H is closed for D0a in D-4 (`final_heights` in the setup, V_d equality check first, prover pads); Q (QROM hiding, ZK-ARGUMENT §6.5); the review of the D-3 verifier changes. With #2, H becomes "the root shape is a setup constant" | D |
| 11 | **Soundness budget:** the wrap is pinned at 268 bits per round. The QROM union fails at depth 6 (121.8 bits). If padding fixes `d`, pick `d ≤ 3`; 137 leaves at 1 Pgas gives depth 3 | E, D |
| 12 | **Lean:** `aggWrapV` has no `a = 0` check and no wrap tag. Align it with 1(b), and add PAD-leaf soundness to `SegSound` (identity at `done`) | E |

### 5.1 M5a (state lane B): status, 2026-11-03

See `research/near-compression/e2e-general/m5a/README.md` (commands, logs, cost census).

**Done [M]:**
* **INTAKE + working-set tree + FINAL proves on T1** (`d3c8/d3/02-h10196-s3`) on the main stack:
  17 working-set keys, 10 committed changes (7 upserts, 3 deletes), taken from the clean-room
  checker and cross-checked against the Lean `allFeatures --emit-full` write log. 156 trie-node
  rows, 270 SHA-512 compressions; 1,243,380 B, 268.2-bit, prove 193 s (8 threads), verify 93 ms.
* **Root equality:** the circuit's post-state root = the Lean run's `stateRoot` = the header's
  (`1db48e38…`).
* **Mutants 4/4 rejected:** tampered trie node (hash link), wrong pre-value (INTAKE answer),
  omitted write (write log + root chain), wrong post-root (closing root).
* The AIR (`KEY`, `BR`, `SN`, `KCMP`, `WSB`, `WSN`, `WSA` + the unchanged SHA-256 table + the
  native SHA-512 chip) is a Lean `ZkFormal.Air` value interpreted unchanged by the prover. The trie
  side walks the spec's own recursions (`findRef`, `upsert`, `del` with `squashBranch` /
  `extendChild`); the working set is a SHA-384 tree of `(sha256 key, pre, cur, written)` leaves,
  key-sorted by `KCMP`, with one Merkle-path row per write access and a root chain (`RCH`) a
  segment boundary can carry.
* **Cost:** 32.5 k cells per trie-node row (branch 42.0 k, short node 17.2 k, SHA-256 dominated),
  129.5 k per INTAKE find, 286.1 k per FINAL change, 53.5 k per working-set key (key + order +
  leaf digests), 149.3 k per write access at depth 5.

**Lean [K]** (`StateM5a/`, std axioms, no `sorry`): every `BR`/`SN` op is one step of
`PTrie.findRef`/`upsert`/`del` (`Steps`); the branch bitmap / children block and `hexPrefix` equal
the rows' layout formulas (`Layout`); `KCMP` ⇒ `bytesLt` (`Order`); one write access updates
exactly one leaf of the working set (`Merkle.write_access_sound`, collision-free hash); field-level
`KEY` row lemma (`KeyField`). Open: field-level lemmas for the wide tables, the walk composition
over the witness trie (needs `del` refinement and the no-collision identification), and the
SHA-512 chip's interface in Lean.

**Second session (same day): T2 [M].** The menu now covers every spec case of T2
(`d3c9/d3/00-h10018-s0`, 52 keys / 42 changes): absent finds and deletes at a leaf / extension
(a mismatch witness: matching prefix, then another nibble with an inverse, or a key end), a find
ending at a branch value, `splitLeaf`/`splitExt` upserts (new branch `BR.oSL`, `wrapExt` row,
re-keyed extension), absent deletes (result kind `SAME`, root repeated on `TCH`), the delete whose
child is a kept branch (`extendChild k (branch …)`), and node keys past one row's capacity
(`SNC` continuation rows, 64 nibbles each; the 90-nibble key). Nibbles no key lookup covers are
range-checked by a new 256-row `RNG` table. **T2 proves and verifies** on the main stack:
1,533,468 B, 268.2-bit, verify 158 ms; post-state root `61f5330a…` = the Lean run's `stateRoot`.
(Prove 4,392 s on 8 threads while the shared build slice was memory-throttled; T2 is 47.3 M cells,
3.3× T1.) T1 still prechecks with the same rows. Mutants **12/12 rejected**: the four
statement-level ones plus one tampered row per new row type (README, `logs/T2-mutants.txt`).

**FINAL batching [M, model]:** hashing each touched node once in nearcore's order (which is the
spec's: `upsert`/`del` never hash, `rootHash` hashes the final trie once) cuts FINAL's SHA-256 work
by 46.7 % on T1 and 81.9 % on T2 (74.7 % / 89.4 % reusing INTAKE's digests of the pre-state nodes);
on T2 that is ~12 M of 34.2 M used cells. Not yet in the AIR: it needs an offline-memory node store
(timestamped `NODE(nid, t, record)` messages) in place of hash-addressed node versions (README,
next steps).

**Lean [K], second session:** `StepsT2` (one spec step per new row: absent finds/deletes from the
mismatch witness `k[jm]? ≠ key[jm]?`, `br_findValue`, `ext_del_branch`, `leaf_split`, `ext_split`,
`kids2_at`), `Layout.hpAt_chunk` (continuation rows' `hexPrefix` bytes); **field level from the
tables' constraints** (`FieldRows`): `KCMP` order, `SN` mismatch, `BR` keep condition, and the
16-bit memory chains as exact 64-bit equations; **walk composition** (`Walk`): chains of row steps
(`FChain`/`UChain`/`DChain`, one constructor per row op) are `findRef`/`upsert`/`del`/`applyChange`
on the rows' trie, and for finds and upserts the same answer / new root hash on any trie the rows'
trie refines (`PTrie.upsert_refinedBy`); `refinedBy_of_hash` takes `Sha256CR` and `NodeSerInj` as
named premises (no axioms). Open: `NodeSerInj` (decode ∘ encode of the node preimage), the
refinement of the whole rows' trie along a chain, `del_refinedBy`, the `SN` key layout / `BR`
children block / `SNC` / `WS*` at field level, and the bus-level step from `DOWN`/`UP` balance to the
chain constructors. Std axioms only, no `sorry`; the Lean spec and checker are unchanged.

**Boundary:** the state side carries `(RCH working-set root, TCH trie root, change index)`; it
maps to §3.2's `stRoot` and will follow lane E's `CM` boundary record when §3.5 publishes it.

**M5a-2 (third session, 2026-11-03) [M][K]:** log
[`docs/logs/e2e-m5a2-state-2026-11-03.md`](../logs/e2e-m5a2-state-2026-11-03.md).
* **Batched FINAL in the AIR.** Each trie node is hashed once: a pre-state node by its first
  reader, published on a new `VER` bus under its digest for every other reader (INTAKE is batched
  too); a node a later change rewrites is published under a version id (the producing row's id)
  and never hashed; a final node is hashed by its row. Child slots, `DOWN`/`UP` and `TCH` carry
  refs (digest | version id); the public `TCH` ends are digests. Immutable records with unique ids
  make `VER` a persistent store: no timestamps.
* **T1 / T2 re-proved**, roots = the Lean runs' `stateRoot` and the Lean spec oracle
  (`m5a-tool apply`: `revealTrie` → `applyChanges` → `rootHash`): T1 1,258,042 B, prove 260 s;
  T2 1,296,042 B (was 1,533,468), prove 478 s, 2.7 GB (was 16.4 GB); 268.2-bit. Trie-row SHA-256
  cells −67 % / −86 %; T2 committed cells 47.3 M → 16.2 M (the SHA-512 working-set chip is now
  the largest term). Mutants: T2 17/17, T1 9/9, synthetic 7/7 rejected (5 new ones for the
  version store).
* **Completeness:** branch values (`BR.oUV`/`oDV`/`oDZ`), proved on a synthetic NEAR-shaped case.
* **Lean:** `Store.batched_changes` (through every upsert and delete the post root is
  `rootHash (applyChanges …)` on the witness; premises `Sha256CR` and `KeepsFW`, a spec property),
  `FieldVer`, `StepsBV`; `NodeSerInj` **proved** (`SerInj`), `del_refinedBy` (general `del`),
  `rows_refinedBy`, `sn_hexPrefix`, `br_sel`.
* **Open:** the bus-level step (row traffic ⇒ reveal / chain / store expansion); `KeepsFW`;
  squash after a value delete / onto a non-leaf sibling, splits where a key ends at the branch,
  mismatch past 63 nibbles, the empty trie.

**M5a-3 (fourth session, 2026-11-03) [K][M]:** log
[`docs/logs/e2e-m5a3-state-2026-11-03.md`](../logs/e2e-m5a3-state-2026-11-03.md).
* **Bus-level step [K].** `Bus.holds_perm` (`Holds` ⇒ every bus's sent list is a permutation of
  its received list); `Traffic.walk_unique` (one active row per walk position — needed since `UP`
  does not repeat the ref), `walk_sem`, `tch_chain`, `ver_recv`, `reqresp`; `BusWalk.ver_store`
  (the store from `VER`), 23 row-local steps, and **`bus_batched_changes`**: walk shape +
  `DOWN`/`UP`/`TCH` balance + every row's local step ⇒ `rootHash (applyChanges …)` =
  `post_state_root` on the witness, premise `Sha256CR` only. `FieldWalk.br_gdn_gold`: a `BR` `DOWN`
  sender is active (the `SN` analogue is open). `KeepsFW` is false (`not_keepsFW`); replaced by `keepsFWRows` /
  `batched_changes'`; chain constructors for `oUV`/`oDV`/`oDZ`.
* **Working-set cost [M].** One SHA-512 compression per leaf; per-write paths replaced by a
  memory-checked `WM` bus and one batched path update per segment (`RCH` kept). T2 committed
  cells 16.18 M → 10.73 M, 1,264,466 B, prove 149 s; T1 5.15 M, 1,238,300 B; synthetic 1.99 M;
  roots unchanged; mutants 52/52 rejected (7 new). `WRITE` is now `(seg, t, kd, value)`.
* **Open:** field-level decoding of the walk / store / working-set messages and the per-row
  facts the steps take; steps for the split ops, `oDL`, `oD1`; the `WM`/`PT` bus step; the
  SHA-512 chip interface; the completeness gaps of M5a-2.

**M5a-4 (fifth session, 2026-11-03) [K]:** log
[`docs/logs/e2e-m5a4-state-2026-11-03.md`](../logs/e2e-m5a4-state-2026-11-03.md). Lean only, no
circuit change.
* **From `Holds` of the AIR the prover runs** (`m5aAir D` + tables not on `DOWN`/`UP`): for any
  field decoder, `DecodeM5a.walk_traffic` gives the record-level `DOWN`/`UP` permutations of the
  decoded `BR`/`SN` rows and `WSB` roots (interactions pinned by `filter` lemmas against the
  exported tables); `DecodeShape.walk_rootUniq` (one root per walk id, from `Holds` alone),
  `walk_deeper` (premises: depth `< P − 64`, short `SN` keys), and **`air_batched_changesS`**:
  `rootHash (applyChanges …) = post_state_root` from `Holds`, `Sha256CR`, the depth bounds, each
  decoded row's `LocalOK`, `TCH` and the writing roots. `FieldWalk2.sn_gdn_walk` (the `SN` descend
  fact, staged), `FieldWsb.wsb_index`.
* **All ops have row-local steps**: `oLX`, `oEX`, `oDL`, `oD1` + responders `oSL`/`oEP`/`oEM`/
  `oLM`/`oLS` through `Traffic.reqresp` (`BusSplit`, `BusSplit2`); `oEX` needs `SemUS` (the spec
  equation in place of `UChain`), `bus_batched_changesS`.
* **Working set** (`WsBus`): `WM` chain (`wm_chain`), `RCH` link, `PT` uniqueness and the
  segment's `Merkle.Upd` rebuilt from the rows (`seg_root`); **SHA-512 chip interface** (`Sha512If`:
  `IF384` contract, `comp_node`, `wsp_hashes`).
* **`ViewImpl` state component** (`StateView`, imports `NearSpecV3.E2E.View`): `stD`,
  `stD_binding : Coll stD → Sha384Coll ∨ Sha256Coll ∨ LeafColl`, `viewImpl_hst` (the `hst`
  argument of `viewImpl_binding_bad`); parameters `proj_inj`, `encRest_inj`, `trie_ok` (lane E must
  commit the full trie expansion), `leafBlock_inj`.
* **Open:** per-row decoded facts → `LocalOK` (`VER`/`SHA`/`NIB`/`KLEN` decoding, a concrete
  decoder), the depth bounds (`KEY` index + `NIB` membership; `SNC` `rl` bound), `TCH`/public tape
  in Lean, working-set field decoding and segment composition, the `ViewImpl` parameters, the
  completeness gaps of M5a-2.

**M5a-5 (sixth session, 2026-11-03) [M][K]:** log
[`docs/logs/e2e-m5a5-state-2026-11-03.md`](../logs/e2e-m5a5-state-2026-11-03.md).
* **AIR**: `wsLen` = public value 16 (`WSB` `real ↔ i < wsLen`, `WSL` `i < wsLen`), kept in the
  state commitment. Five soundness fixes from the per-row decoding and an audit of the whole AIR
  for field wrap-around / unranged bytes / truncated spec subtraction: `BR` `oUV` length
  `nvl₃ = 0` and `SN` new-leaf memory `nmem₃ ∈ {0,1}` (both real holes: a value `+ P` passed),
  `BR` `oDH`/`oDL` `om ≤ mem`, `BR` old length `vl₃ = 0`, `RNG` on version-published value
  bytes. T1/T2/synthetic/T2-seg3x5 re-proved (roots = Lean oracle), all mutants rejected
  (6 new). Open for M5b: range-check `WSA` times once they are prover-chosen.
* **Lean**: one upsert semantics (`UChain.extSplit`; `SemS = Sem`); keys / `NIB` / `KLEN` / `KDIG`
  / `ORD` decoded, depth bounds, `SNC` chain, the public tape as a Lean table, writing roots in
  key order — `FinalOrder.air_final_sorted` (`applyChanges (sortKV committed)` reaches
  `post_state_root`); concrete decoder, all 14 `BR` ops and 12 `SN` walk ops `LocalOK`, `BR`
  records from `VER` and SHA-256, `MATR`/`SIBA` answers — `SnResp.air_final_sorted_sn2`; working
  set from `Holds` (`ws_entries`: FINAL leaves = INTAKE entries with their latest writes);
  `StViewParams` for lane B (`stD_binding_B`), lane E's obligations as `StViewE`; non-vacuity
  (`ChipStub`: `Holds` of the prover's AIR is satisfiable with a stub `IF384` sender; no theorem
  vacuous).
* **Open:** `SN` splits (`oLX`/`oEX` via the split buses), continued keys, `SN` records from
  `VER`/SHA and limb ranges, `BR` `OslApart`; `committed ~ cs` (M5b); lane E `StViewE`;
  completeness gaps.

**Next:** the remaining `SN` premises (splits, continued keys, `SN` records), then M5b (STATE
rows produce the writes now on the public tape; range-check `WSA` times).
