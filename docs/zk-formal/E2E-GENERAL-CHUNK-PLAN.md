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
| segmentation of one call | spec: `NearSpecV3/Wasm/Segment.lean` `run_foldSegments` [K]; `wasmBaseSegAir` (`WasmBase/SegAir.lean`, E2E M4) | **B** (2026-11-03): mid-call cuts with SHA-384 `ctxDigest` + `memRoot` boundary; 1.13 M-step call proved as 5 chained segments | boundary per written 1 KiB block 50 SHA-512 compressions (`D = 16`) | `exec_of_rows_cut`, `cuts_csteps` [K]; full segment soundness open |

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
* **Granularity gaps.** (a) *Closed by M11b (below)*: mid-call cuts. (b) *Open*: a segment that
  contains a genesis block is one atomic `CM` step (`init → doneG`, exact but uncut). (c) *Closed
  by M11b up to the commitment*: the concrete §3.2 boundary encoding and `abs`; what each
  configuration commits to (`view`) is the circuit lanes' part.

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

Open for lane E:
1. Cut the genesis path like the reshard path (`checkD2CoreGWith` → intake/final split).
2. The commitment `view` (working-set root, accumulators, Wasm digests) and its binding, with
   lanes A/B.
3. The honest prover's `K` (the call tape) as a function of the step. It exists by computation
   (lane A's `wasmbase-tape`); it is not a Lean theorem.
4. Instantiate `NodeOK`/`Extract` against the pinned NV circuit (with `pq-nv-faithful`).

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

**Next (lane A):**
* Segment soundness as one theorem (the `cutView` equality and the LEAF link above), and lane E's
  `ViewImpl.wasmD` with `Coll wasmD → SHA-384 collision`.
* Boundary cost levers (tree depth from used pages, write-only leaf re-hash, 4-ary nodes) and
  segments with `memory.grow` (`wasmBaseM3Air` chips in the segment AIR; `D` changes).
* `wasm_base_sound_m2` dispatch; the generator limits (stack-budget trap row, out-of-gas row,
  `≥ 2^27` addresses).
* **Distinguish the storage key and value bytes in-circuit** when the state side consumes bus 210
  (the `hid + 256` wire convention, M6).
* **M6.** Replace HOSTO so the tape is bound inside the proof.

The milestone-1 exit test (return bytes, logs and gas equal the chunk's outcome on T1 and T2, with
mutants rejected) is met. The gas equality holds outside the proof (the tape) until M6. The
`lake build WasmBase` breakage reported on 2026-10-31 was fixed on main (`6a1739cd7`), and the build
is green with the new files.

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

**Next:** the bus-level step, then M5b (STATE rows produce the writes now on the public tape).
