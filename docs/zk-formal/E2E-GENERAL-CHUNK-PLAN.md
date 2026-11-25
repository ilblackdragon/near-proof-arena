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
| outputs and roots | D0a `mrk` (maxLog 19), `sort`, `upsA7`/`sizeA7` post-state, public header segments; general: M5d FINAL template `research/near-compression/e2e-general/m5d` (§5.2) | **B for D0a** (state, outcome and outgoing roots); **B for class F1 / T1** (M5d, 2026-11-21): all 13 `headerOk` comparisons in-circuit incl. Reed–Solomon `encoded_merkle_root`/`encoded_length`; **–** proposals, bandwidth requests, split, transactions (other classes) | FINAL T1 989,626 B; Reed–Solomon + part hashing ≈ 500 cells / body byte | FIN row ⇒ `headerOk` proved (`final_template_sound`, named `Computed`/`FinInOK` premises) |

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
| segmentation of one call | spec: `NearSpecV3/Wasm/Segment.lean` `run_foldSegments` [K]; `wasmBaseSegAir` (`WasmBase/SegAir.lean`, E2E M4) | **B** (2026-11-03): mid-call cuts with SHA-384 `ctxDigest` + `memRoot` boundary; 1.13 M-step call proved as 5 chained segments | boundary per written 1 KiB block 50 SHA-512 compressions (`D = 16`); M4b multiproof (`wasmBaseSegAirMP`): 680 per 32-block segment, boundary 43 % | `exec_of_rows_cut`, `cuts_csteps` [K]; M4b: `seg_sound`, `wasmD_binding` [K]; M4c: `seg_chain_mem`/`seg_chain_k` (chained segments → `CSteps` or `Sha384Coll`; memory roots, CUTI side, halting, MP AIR default) [K]; host relies vacuous on host traces until M6's σ pinning; M6: σ-pinned `seg_chain_all_mp` and honest host premises (`callHost_two_run`, `seg_sound_hostIf_air`) relative to the producer contract `HostIf` [K] |

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

#### 3.4.1 The canonical statement bytes `S` and `claimDigest` (lane E, M11h) [K]

Fixed in Lean, `spec/lean/v3/NearSpecV3/E2E/StmtEnc.lean` (in `defaultTargets`); lanes D and I
implement exactly this.

* **`S = PublicStmt.encode s`** = the claim-v3 encoding (`spec/claim-v3.md` §2, `Claim.encode`) of
  the claim with an **empty section B**: every field in claim order, the block vector replaced by
  its empty encoding `u32 0` = `00 00 00 00`. Byte layout:
  `S = stmtPre ‖ 00 00 00 00 ‖ stmtPost`, `stmtPre` = claim tag, statement id, `protocol_version`
  (u32), `chain_id` (bytes), `epoch_id` (32 B), `chunk_inner` (bytes); `stmtPost` =
  `rs_data_parts`, `rs_total_parts` (u16), `epochs`, `epoch_start_after`, `apply_facts`,
  `tx_valid`, `genesis_chunk_extra` (all as in claim-v3). The claim the relation checks is the
  same bytes with the private block vector (count included) in place of the four zero bytes:
  `assemble ci secB secC = stmtPre ‖ encList BlockRec.encode secB ‖ stmtPost`
  (`assemble_splice`, `encode_splice`).
* **Canonical and injective.** `PublicStmt.decode` = the strict claim decoder (`decodeClaim`) then
  `blocks = []`; `PublicStmt.decode_encode` on well-formed statements (`PublicStmt.wf` =
  `Claim.wf` of the empty-B claim: field widths), hence `PublicStmt.encode_inj`. `assemble_wf`: a
  well-formed assembled claim has a well-formed statement.
* **`claimDigest s = bdigest S`** (SHA-384 truncated to 42 B, U-10). `claimDigest_binding`: equal
  digests of well-formed statements are equal statements or a SHA-384 collision. Every
  boundary's `claimDigest` field is this value; the wrap's `D_wrap = H(tag_wrap, SHA-384(S))`
  (§5.0.1) hashes the same `S`.
* **T1** (kernel-evaluated in `E2E/RealChunkT1.lean`): `|S| = 1,007 B` (`t1_S_len`; lane I's I-1
  working encoding, the claim with the block vector *and its count* cut out, is these bytes
  without the four zero bytes: 1,003 B, checked byte-for-byte against `e2e-t1/run3/S.bin`),
  `claimDigest = bb5aad11ba6ba32d91739f13a2dbd544f2420d770bcd2c3fde9ddc0e1c02710caee28e5e9e4e299f2f01`
  (`t1_claimDigest`; equals Python `hashlib.sha384(S)[:42]`). Lane I's `040290778c…` digest is of
  the 1,003-B working encoding and must be replaced.
* **Leaf statement.** A boundary is exposed as `bndOf V.bnd x = bdigest (BndRec.encode (V.bnd x))`
  (`Boundary.lean`; `BndRec.codec` is fixed-width big-endian, §3.2) with the clear `phase` tag
  (`View.split`: `init` 0, `eng` 1, `fin` 2, `gfin` 3, `done` 4, `doneG` 5, `inCall` 6), i.e.
  lane D's `s = [phase, h(B)]` with `h(B) = bdigest (BndRec.encode B)`; the T1 system
  (`Templates.lean`) is stated over exactly these digests.

#### 3.4.2 Public fields the relation does not constrain (lane I's 33 accepted mutants) [M + spec]

Lane I's T1 mutants (`t1.py mutants`, run `e2e-t1/run3/mutants.txt`): 33 one-field changes of
`S` are **true statements** (the checker accepts them with T1's section B and witness). Checked
against the spec and nearcore 2.13.4 (`/data/illia/nearproof-deps/nearcore`, `44f7ae6`):

| field (mutants) | read by | why T1 accepts | verdict |
|---|---|---|---|
| `chunk_inner.height_created` (±1, with the witness's header copy patched) | nothing in the relation: decoded (`Wire.lean`, `heightCreated`) and only compared as part of the witness's header copy | nearcore's witness validation never reads it: `validate_chunk_state_witness_impl` (`chain/chain/src/stateless_validation/chunk_validation.rs:565`) uses it only as a log/span field; it is consumed by the consensus layer — chunk-producer selection and signature (`ChunkProductionKey`, `partial_witness_actor.rs:430–440`), the relevance window against the node's **local** head (`client/src/stateless_validation/validate.rs:253–320`, node state, not a validity predicate), and block inclusion. Already recorded as spec finding (1) in `spec/near-chunk-validation-v0.md` §(findings): nearcore accepts the same mutants | **unconstrained by design** (mirrors nearcore). Finding for the owner: an intrinsic constraint every honest chunk satisfies is `height_created > height(prev block)` (the prev block header is in section B); nearcore enforces it only through block inclusion. Adding it is a checker change (owner decision); not done. For M10 these are binding negatives (`D_wrap` binds `S`) |
| `chain_id` | `Env.chainId`: ETH-implicit wallet hash (`D2/Actions.lean` `ethWalletHash`), global-contract resolution (`StorageExecutionOrig.lean:70`), the VM context | T1 has no ETH-implicit account, no global contract | constrained when read; unread by T1 |
| `epochs[0].height` | host `epoch_height` (`Wasm/Host.lean:716`), epoch-switch rewards | `d3tiny.run` does not call `epoch_height`; no epoch switch | constrained when read |
| `epochs[0].layout` (last byte) | `decodeLayout` (`Layout.lean:58`): T1's layout is V2 (tag 2, 293 B); its last byte is the high byte of the trailing `version: u32` (T1: `03 00 00 00`), parsed and discarded | nearcore uses `ShardLayout::version` only in `ShardUId` (DB key prefixes), never in a state root or receipt routing | unconstrained by design (semantically irrelevant); any change to boundaries / shard ids is rejected |
| `epochs[0].validators[*]` (account, stake ±1, drop) | host `validator_stake` / `validator_total_stake`, epoch-switch validator updates | no such host call, no epoch switch, no validator update in T1 | constrained when read |
| `apply_facts[0].minimum_stake` | the `Stake` action (`D2/Actions.lean:301`: `stake < env.minStake` fails), via `envOf` (`ChunkValidationD2.lean:228/250`) | T1 has no stake action | constrained when read |

So no accepted mutant is a soundness gap of the relation for T1: each field is either never read
by the chunk-validity relation (as in nearcore) or read only by paths T1 does not take, and section
C is a **trusted** input (its correctness is the statement's premise, not proved). Lane I's doc
(`E2E-T1-CRITICAL-PATH.md` §3) can cite this table.

  **M5d coordination note (lane G, 2026-11-21; details and owners in
  `research/near-compression/e2e-general/m5d/LEAF-TEMPLATE-SPEC.md`).** Proposals:
  (1) `claimDigest` is lane E's canonical §3.4.1 value `bdigest(stmtPre ‖ u32 0 ‖ stmtPost)`;
  INIT and FINAL hash exactly these bytes in-circuit (T1: 1,007 B, `bb5aad11…9f2f01`). (2) *lane B:* `ctxD (.raw cb wb) =
  bdigest(0x00 ‖ u32 ℓ_B ‖ u32 |cb| ‖ cb ‖ wb)` (INIT computes it); INTAKE must check that the
  decoded block list spans `ℓ_B` bytes (else section C could be re-read from shifted bytes).
  (3) *lanes B/E:* FINAL starts after `finK`; join it to lane B's FINAL / M5c in one segment with
  the `FinIn` record on a bus (recommended), or split `CM`'s `fin → done` step at `finK`.
  (4) *lane E:* the M5d accumulators are `chainD` over outcome leaves and over
  `u64 routedShard ‖ u32 ℓ ‖ Rcpt.encode r`; `outD(.none) = (bdigest [], [bdigest []], bdigest [],
  bdigest [])`.

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

**M11e (lane E, 2026-11-03/04) [K + D].** Standard axioms only, no `sorry`, checker sha256
`644495ff…a9ae3` unchanged, `make pin-check` ok, full v3 build 447 jobs. Log:
[`docs/logs/e2e-lean-m11e-2026-11-03.md`](../logs/e2e-lean-m11e-2026-11-03.md).

* **The one-database QROM argument for the tree does not go through** (budget doc §9). Inner
  proofs are checked in-circuit with the concrete SHA-384, so they are not H-transcripts. Theorem
  O rules out a query-only bound. No published QROM PCD theorem exists: CGSY24 is classical, and
  CDHZ proves single-step extraction.
* **What can be claimed.** The wrap alone reaches 2^−130.2 (CDHZ Thm 11.3), plus a named
  InnerSound assumption per inner level.
* **Per-proof union at depth 6.** It needs ε_rbr ≤ 2^−274.19 (+4/+6/+5 queries and a second OOD
  sample, ≈ +6.3 KB) at constants 1, or 2^−282.73 at CDHZ constants (not reachable by
  parameters). This is an owner decision; nothing was changed.
* **Lane D's D-5 tree transcribed** (`zk-formal/ZkFormal/PQ/E2ETree.lean`): `node_bind`
  (child program binding: anchor set or shared root + BIND), `one_template` (normaliser + PADs ⇒
  exactly one template, `init → done`) and `wrapT_composition` (`D_wrap`).
  * The old overlay's binding was dead code (`else if false`). M11d's `NodeInner` therefore
    failed for the old node, but the M11d theorems stand.
* **`honestQ`/`honestK` are now computable** (`recordK`, `Tape.lean`).
* **Not done.**
  * No NvAir exporter run and no Lean NvAir model: the draft exporter in `nv-export/` targets
    the historical overlay. No `NodeExec` sub-obligation is proved.

**M11f (lane E, 2026-11-04) [K + D].** Standard axioms only, no `sorry`, checker sha256
`644495ff…a9ae3` unchanged, `make pin-check` ok, full v3 build green; lanes A (`WasmBase`, 695
jobs) and B (`StateM5a`, 379 jobs) build green against the changed `View`. Log:
[`docs/logs/e2e-lean-m11f-2026-11-04.md`](../logs/e2e-lean-m11f-2026-11-04.md).

* **The chunk's key list is in `StV`.** `StV.eng p ⟨st, keys⟩` (`EngSt`); `ViewImpl.keys :
  Intake → List Bytes` fills it (`split κ`, `stOfK`); `keysOf`. `split_inj` holds for every `κ`.
  `stOf` (empty key list) is kept only for lane B's `FitsReach`, which must move to `stOfK`.
* **Lane B's `StViewE` is supplied** (`e2e-general/join/StViewE.lean`): `encStV` (prefix-free
  serialiser of all of `StV`, `StEnc.lean`; `encStV_inj` on every `StV`), `keysOf`, `idxOf = 0`
  (timestamps restart per segment; lane B to confirm), `depth = 24`. `stD_binding_E` and
  `viewImpl_hst_E` have no open field. `FitsReachK` reduces to the engine invariant `EngOvlInv`
  (open).
* **NvAir exported and `NodeTape` proved from it** (`NvAirExport.lean`, `NvTape.lean`): the
  exporter ran on the e2e-tree stack (4,518 nodes, 548 constraints, 49 interactions); `y_row`,
  one-hot selectors, `mem_slots`, the LogUp `hit`, `pvd_cells`, `nodeTape_of_pvd`. Premise left:
  `PvdAt` (program binding + op decode). Vacuity guard: the bus closure of NvAir is exactly
  {NvAir, Sha512Air4, TableAir4, ByteAir} (`nv_closure`); bus 3 is NvAir's alone.
* **Finding: `ZkFormal.Air.Interaction` cannot express NvAir's merged field-valued counts**
  (`−ka·mult + kb`), so `HoldsLogUp Pin.air` over a `ZkFormal.Air` transcription is not the
  circuit's predicate; `NodeExec` should be restated over the field-count semantics
  (`NvConstr` + per-bus `MemBalance`-style balances).
* **Budget refreshed for D-8** (§10 of the budget doc): wrap pinned at 268.2 (masked protocol);
  1 Pgas at arity 4 is N = 222 charged proofs, 132.5 bits (constants 1) / 129.5 (CMS19) under the
  per-proof union; depth 6 at arity 4 fails 128. Claim stated per level. Finding: `seg-v1` at 32
  grinding bits is 266.9 bits (< 268).

**M11g (lane E, 2026-11-04/05) [K].** Standard axioms only, no `sorry`, checker sha256 unchanged.
Log: [`docs/logs/e2e-lean-m11g-2026-11-04.md`](../logs/e2e-lean-m11g-2026-11-04.md).

* **`NodeExec` restated over the circuit's own predicate.** `NvField.NvHold`: the four pinned
  tables, **all exported** (`nv_export_all`: Sha512Air4, TableAir4, ByteAir added), constraints on
  every row and the field LogUp balance (signed, merged counts) on every bus. The E2EAgg/E2ENode/
  E2ETree composition is re-derived over a trace-predicate parameter (`E2EHold.lean`;
  `e2e_sound_of_execH`, `wrapT_ofH`; the old statements are the `HoldsLogUp` instance).
  `NodeExecV = NodeExecH NvHold`. Vacuity guard kept and grounded in the export
  (`busUsers_exported`).
* **Non-vacuity on an honest NV trace.** `nv_export_trace`: a small program run by the circuit's
  own `nv_trace`, proved and verified by the backend, exported (4,096 rows, 792 used). Proved on it:
  all 548 constraints on all rows (kernel DAG evaluation, `NvDagEval`), `MemBalance`, `PvdAt` at
  both `PvD` rows, `ProgBound`, the `assert_eq` pair, and the tape lemma's conclusion. Not
  exhibited: `NvHold` as a whole (the other tables' traces are not exported).
* **`PvdAt` and the asserts proved from `NvHold`** (`NvProg.lean`): program binding (premise
  `ProgBound`) → ALU role (`(1 − ka)·P1`) → op decode (constraint 1799, all 40 cases, partial
  evaluation `NvAff`) → byte range (ByteAir's keys are byte pairs from its 9 exported constraints;
  bus-11 field LogUp; premise `GlueByteBool` for four GLUE-row counts) → `op = 8b + a`.
  `pvdAt_of`, `tapeAt_of`, `wrapTape_of_prog`, `asserted_eq` (every `assert_eq` of the bound
  program holds on the memory cells), `contAsserts_of`, `nodeExecV_of_prog`.
* **Left for `NodeExec`:** `ProgBound` (BIND/anchor/V_d binding of the program columns),
  `GlueByteBool`, `NodeLink` (decode-level), `NodeSha`, `NodeInner`.
* **`EngOvlInv`** (item 3): proved for the engine's accepting runs
  (`OvlInv.lean`, `StViewE.engOvlInv_of`): the overlay trie is never modified after
  `Ovl.ofTrie` and committed keys stay distinct (`reach_trie_nodup`), committed keys only grow
  (`reach_covered`), over every overlay operation of the logged store and recorder programs.
  Hypotheses (`IntakeOk`): key count ≤ 2^24, intake trie `wf`, revealed pre-state values < 2^24
  bytes, `κ` covers the accepting run's output keys (true for the canonical `κRun`), and **`cur`:
  committed values < 2^24 bytes — open** (the engine caps Wasm writes at 4 MiB; the pass through
  the host and receipt limits is not done). Non-vacuity only for the conditions (no accepting-run
  example).

**M11h (lane E, 2026-11-21) [K].** T1-first. Standard axioms only, no `sorry`, no checker
definition changed. Log: [`docs/logs/e2e-lean-m11h-2026-11-21.md`](../logs/e2e-lean-m11h-2026-11-21.md).

* **The T1 segment system and the per-lane obligations** (`E2E/Templates.lean`, `defaultTargets`;
  namespace `NearSpecV3.E2E.T1`). Templates `init | state | rt | wasm | final`, each with a meaning
  on `RCM` configurations (all inside `RSteps`, `meaning_rsteps`):

  | template | lane | Lean premise | the rows must open their two boundary digests to `x`, `x'` with |
  |---|---|---|---|
  | INTAKE | G | `SegSoundInit V A Bad` | `MInit`: `x = init cb wb`, `CM.step (init cb wb) = .ok c`, `x' = c` |
  | STATE | B | `SegSoundState V A Bad` | `MState`: `eng I c →* eng I c'` by engine steps that make **no VM call** (`estepO (strictO [])`) |
  | receipt step | F | `SegSoundRt V A Bad` | `MRt`: `enter` (start call `q` at a non-final `eng I c`), `next` (record `(q, r)`, start `q'`), `resume` (`estepO (strictO (K ++ [(q, r)])) I.prog c = .ok c'`: the whole receipt step — actions, gas, refunds, outcomes — with the VM answered only from the tape) |
  | WASM | A | `SegSoundWasm V A Bad` | `MWasm`: `call I c K q cc → call I c K q cc'` with `CSteps q cc cc'` (cuts anywhere in a call) |
  | FINAL | G | `SegSoundFinal V A Bad` | `MFinal`: a `CM` run from `eng I ⟨.done out, _⟩`, `fin I out` or `gfin G` (to `done` / `doneG`) |

  Each premise is `TmplSound V A Bad k := ∀ d d' tr, A.Holds k d d' tr → Bad ∨ ∃ x x',
  bndOf V.bnd x = d ∧ bndOf V.bnd x' = d' ∧ Meaning k x x'`, where `A : Airs` is the lanes' trace
  type and AIR predicate per template and `bndOf V.bnd x` the 42-B digest of the boundary record
  (§3.4.1). The wrap gets `WrapInitSound` (`B_0` = digest of `init (assemble s.ci secB s.secC) w`)
  and `WrapFinalSound` (`B_N` = digest of a configuration passing `FinalOutPub s`).
  **`e2e_sound_t1`**: `NvFaithfulE2E` (lane D) + the two wrap obligations + the five template
  obligations ⇒ `E2EStmt s ∨ Bad ∨ BndCollision V.bnd`; `e2e_sound_t1_bind` splits the collision
  (SHA-384 or a component commitment, `viewImpl_binding`).
  Honest side: `TmplComplete V A k` (each lane's completeness), **`cm_decomp`** (every `CM` run
  factors into these templates: per engine step one `state` segment when the honest tape is empty,
  else `rt` enter, per call `wasm` + `rt` next/resume), `honest_chain`, `mstate_trans` (STATE
  segments merge), `cut_roundtrip`.
* **M11 exit criterion: non-vacuity on T1** (`E2E/T1Run.lean`, `E2E/RealChunkT1.lean`, on
  demand). The monolithic `decide +kernel` of the checker on T1 is OOM-killed at the 34 GB cap; the
  run is checked in two kernel pieces: `INTAKE` against an oracle-printed literal intake (kernel
  `Eq.refl`), then the other 12 `CM` steps (incl. the `d3tiny` call in the spec's Wasm
  interpreter and `FINAL`) by `decide +kernel` — 27.1 GB, 192–318 s. Proved: `t1_accepts` (13
  steps), `t1_rel : Tier.rel .allFeatures T1`, `cm_run_t1` (`headerOk`), `t1_e2e_stmt`, and
  **`t1_honest_chain`**: for any view and lane AIRs meeting the completeness obligations, T1's run
  is a valid chain of the T1 system whose roots pass the wrap checks for T1's public statement.
  T1's `S` is 1,007 B and its `claimDigest` is kernel-evaluated (§3.4.1).
* **Canonical statement encoding** (`E2E/StmtEnc.lean`, §3.4.1) and the **33 accepted statement
  mutants** checked against spec and nearcore (§3.4.2: unconstrained by design; `height_created`
  finding for the owner).
* **`EngOvlInv.cur` narrowed, not closed** (`E2E/OvlVal.lean`, `join/StViewE.lean`, sub-agent):
  fixed-size writes and the Wasm write-back (under the class `VmWritesShort`) proved `< 2^24` B;
  `cur` → `curHard` (keys of account, code, access-key, received-data, receipt-queue, contract-data,
  yield, buffer, bandwidth and global-code columns). **Finding:** the spec admits incoming
  receipts > 2^24 B (`validReceipt false` has no size check, as nearcore's Existing mode), which are
  stored verbatim as postponed/delayed receipts, and unbounded global-contract code; nearcore
  bounds them at creation (chain history). `cur` needs an intake-side receipt-size hypothesis.
* Not attempted: `NodeSha`, `NodeLink` (done in M11i, below).

**M11i (lane E, 2026-11-21) [K].** Standard axioms only, no `sorry`, no checker definition changed.
Log: [`docs/logs/e2e-lean-m11i-2026-11-21.md`](../logs/e2e-lean-m11i-2026-11-21.md).

* **Soundness fix S1–S3 (lane A's A-T2 finding; `E2E/StoreBlind.lean`, `defaultTargets`).**
  *The defect:* `TTN.RealStore.store` is a function, carried in call configurations (the query
  `q`, the tape `K`, the Wasm states), so no `vmD`/Wasm remainder is injective (`no_ser_store`,
  lane A's `vmD_coll`, `wasmViewParams_empty`). Hence **`BndCollision V.bnd` holds for every view**
  and the conclusions `E2EStmt ∨ Bad ∨ BndCollision` of `e2e_sound_t1`, `e2e_sound_t1_rel`,
  `e2e_sound_m8(_rel)`, `e2e_sound_of_tree8` are vacuous as they stand. `S`, `claimDigest` and
  the checker are untouched by the fix (it changes only views and the soundness statement's
  collision event), so no stop was needed.
  *The fix (S1):* `setR s` overwrites every store, `stripR = setR blankStore`; a view is
  **`StoreBlind`** if its record ignores stores; **`Canon sf x`**: every store in `x` is `sf I`
  (the store the context determines — in the honest run `CutW`'s `fun hb => (env.codeOf (ofBA
  hb)).map toBA`); `canon_strip_inj`: stripping is injective on canonical configurations;
  **`bnd_eq_canon`**: for a store-blind well-formed view, equal digests of canonical
  configurations are equal configurations, a 42-B SHA-384 collision, or a component collision with
  the tape / Wasm components restricted to stripped values (`CollOn VStripped vmD`,
  `CollOn WStripped wasmD`). **The per-template obligation becomes `TmplRelC sf V A Bad k`**
  (every *canonical* opening of the input digest steps to a *canonical* opening of the output):
  **`e2e_sound_t1_relC`** concludes `E2EStmt ∨ Bad ∨ BndCollisionOn (Canon sf) V.bnd`, and
  **`e2e_sound_t1_relC_bind`** splits that into SHA-384 and component collisions — real bad
  events. Non-vacuity: **`vSB`** is an explicit store-blind view (`vSB_blind`) whose tape and Wasm
  commitments are binding on stripped values (`vmSB_bind`, `wasmSB_bind`: `→ Sha384Coll`). *S2:*
  `preCodeRoot q = SHA-256(q.code) ‖ 0^10` (42 B), the `.pre` record's `codeRoot`, written by lane
  F's enter leaf. *S3:* `CodeCommit` (the cached-commitment root of the padded CODE/FUNC records)
  with its collision event `CodeCommit.Coll`. **What the lanes do:** lane A — `encRest_inj` modulo
  stores (`encRest a = encRest b → stripW a = stripW b`, with `ViewSer.argsN`/`confN`/`stN`),
  `fbBnd (q, .pre)`'s `codeRoot := preCodeRoot q`, `codeRootOf := CodeCommit.root` of the padded
  records, and its binding lemmas restated as `CollOn WStripped`; lane F — the `enter`/`next`
  leaves produce canonical `x'` (the engine's query, store `sf I`) and write `preCodeRoot`; all
  lanes — target `TmplRelC` (the M11i `TmplRel` is the special case where openings are
  canonical). **Lane B's state view checked:** `StV` contains no function-typed component
  (`StEnc.encStV_inj` holds for every `StV`), and `join/StViewE.stViewE` is an explicit
  `StViewE` instance — not affected. **M8 fixed too** (`E2E/TreeM8C.lean`, `defaultTargets`): `TmplSoundRel8C`,
  **`e2e_sound_m8_relC`** (collision restricted to canonical configurations) and
  **`e2e_sound_m8_relC_bind`** (split into real bad events); lane D's `e2e_sound_of_tree8`
  composes with it the same way (`treeFaithful_of_aggH` is unchanged). **Open (lane E, M12):** the
  honest side for `Canon` (the engine's queries carry `sf I` for `sf I := fun hb =>
  (I.env.codeOf …)`, or the per-block env); `View.lean`/`Boundary.lean` themselves are unchanged
  (the fix is a new module, so that the v3 / lane A / lane B / zk-formal chains need no rebuild;
  moving it into `View.lean` is mechanical).
* **The official per-template obligation is now the relative form** (`Templates.lean`,
  replacing M11h's absolute `TmplSound` as the lanes' target; lanes A and F found independently
  that no segment circuit can meet the absolute form, `M5T1.Obl.tmplSound_image`,
  `TmplWasm` §4). **`TmplRel V A Bad k := ∀ d d' tr x, A.Holds k d d' tr → bndOf V.bnd x = d →
  Bad ∨ ∃ x', bndOf V.bnd x' = d' ∧ Meaning k x x'`** (definitionally lane F's
  `TmplSoundFrom`), one definition for all five templates, abbreviations **`SegRelInit` (G),
  `SegRelState` (B ∧ F, split below), `SegRelRt` (F), `SegRelWasm` (A), `SegRelFinal` (G)**.
  **`e2e_sound_t1_rel`**: `NvFaithfulE2E` + `WrapInitSound` + `WrapFinalSound` + the five
  relative premises ⇒ `E2EStmt s ∨ Bad ∨ BndCollision` (`chain_rel`: the wrap opens `B_0`, each
  segment carries the opening forward). `tmplRel_of_sound` (absolute ⇒ relative, mod collision)
  and `e2e_sound_t1_of_abs` keep the M11h statements as a special case; `TmplSound`,
  `SegSound*`, `e2e_sound_t1` stay for source compatibility. In the M11h table above read
  `SegSoundX` as `SegRelX` with "the rows open their two boundary digests to `x`, `x'`" replaced
  by "**if the input digest opens to `x`, the output digest opens to some `x'`** with". The M8
  counterpart is `TreeM8.TmplSoundRel8` / `e2e_sound_m8_rel` (there INIT stays absolute, since
  the tree's wrap sees only the phase cell; INIT computes its whole input record from the bytes).
* **`NodeSha` and `NodeLink` from the circuit** (`zk-formal/ZkFormal/PQ/{NvOps,NvShaNative,NvSha,NvNode}.lean`,
  on demand). `NvOps` (sub-agent): per-op ALU row semantics from the exported NvAir by partial
  evaluation (`add_sem`, `const_sem`, `unit1_sem`, `job_sem`, `dig_sem`, and over all 40 ops
  `alu_slot_job`/`alu_job_job`: a nonzero SHA-unit or job-bus entry carries `P2`). `NvSha`: the
  **SHA contract** `ShaContract` (named premise = FAITHFUL-v4 C1–C8, FAITHFUL.md §2(c) C9, §2(d)
  R.3.1, at the ALU interface: an exactly offered job's received digest pairs are its SHA-384, pair
  2 truncated with the `lo6` shift), `offer_of_job` (a `hash_range` job laid out as `build_agg`
  emits it is exactly offered), **`range_cells`** (its two `Dig` cells are the native range
  digest cells `rangeLimbs pre vals`, i.e. `digest_cells(range_digest(…))`). `NvNode`:
  **`nodeSha_of`**, **`nodeLink_app`** (`e = Add(a, Const 1)`), **`nodeLink_node`** (the asserted
  digest/packed cells, with the premise `PackOK`), **`nodeExecV_of_contracts`**: `NodeExecV` over
  `NvHold` from `ProgFull`, `GlueByteBool`, `ShaContract`, `TailCanon`, `PackOK` (node children),
  `NodeInner` (the extractor) and decidable program-layout facts (incl. `RangeJob.OK.excl`: no
  other program row has `P2 = j`). **Finding:** ALU jobs are `tr = 1` jobs, so GLUE sends word 5's
  limb 2 as `s5 − lo6` with only `4·lo6` byte-checked; FAITHFUL.md C9.8 pins it through canonical
  consumers (`node`, `merkle_path`), but `hash_range`'s consumers (`assert_eq` with packed public
  values, `PvD`) are not canonical: every internal range digest's last limb is malleable by
  `δ ∈ {v/4}` (binding still ≈ 2^-334, not an attack; but `kidDig = rdigest st` needs the pin).
  `tail_pin` proves a canonical consumer suffices; **fix for lane D**: pin `lo6` in GLUE or add a
  tail byte-pair lookup to range-job `Dig` rows (`TailCanon`).
* **The M8 heterogeneous tree** (`E2E/TreeM8.lean`, `defaultTargets`; `zk-formal/ZkFormal/PQ/E2ETree8.lean`,
  on demand). Leaf kinds `tmpl k | pad` over the five T1 templates; a leaf statement is
  `(ctx, b, b')` with `b = lbOf V x = ((V.bnd x).phase, bndOf V.bnd x)` (lane D's
  `s = [phase, h(B)]`, phase codes of `View.split`: init 0, eng 1, fin 2, gfin 3, done 4, doneG 5,
  call 6). The per-template obligation `TmplSound8` adds a **context link** to M11h's
  `TmplSound`: INIT opens its input to `init (assemble s.ci secB s.secC) w` for a well-formed `s`
  with `claimDigest s = ctx`; FINAL, if its output is `done H o`, gives `FinalOutPub s` for such an
  `s`. `PadSound8`: `b' = b`, phase done/doneG. **`e2e_sound_m8`**: `TreeFaithful` (the accepted
  tree is a boundary-chained leaf list at `ctx = claimDigest s`, first phase init, last phase
  done/doneG) + the five obligations + PAD ⇒ `E2EStmt s ∨ Bad ∨ BndCollision ∨ Sha384Coll`. The
  wrap needs only `ctx` and the two phase cells: the first leaf is forced to be INIT
  (`phase_zero`, `meaning_init_src`), the last template leaf before a `done` boundary is FINAL
  (`meaning_done_tgt`, via `init_step_shape`: INTAKE ends in `eng` or `gfin`). **Connection to
  M11h:** `wrapInitSound_m8` / `wrapFinalSound_m8` prove `e2e_sound_t1`'s `WrapInitSound` /
  `WrapFinalSound` for the wrap check `wrap8` (an INIT leaf at `claimDigest s` starts at `d`; `d`
  is a done/doneG end of a FINAL leaf) from the INIT/FINAL obligations, modulo a collision. Honest
  side: `honest_tree` (an accepting run of an assembled claim is a valid PAD-free leaf chain passing
  the phase checks, from per-template completeness `TmplComplete8`; `mchain_links` shows the
  context links hold on `cm_decomp`'s chain). zk-formal: `compose_ctx` (the node's
  `ctx_i = ctx_0` asserts carry the root context to every leaf), `leaves_of_acc_tree8`,
  **`treeFaithful_of_aggH`** (obligation 1 for the tree from `build_agg` / wrap faithfulness over
  `Hold`, the extractors and range binding; leaf keys mapped to kinds by `kindOf`, so a template
  may have several leaf keys — height classes, families), `e2e_sound_of_tree8`.
* **Lane E's view components** (`E2E/ViewE.lean`, `defaultTargets`): `ctxDE` (lane G's raw
  context `bdigest(0 ‖ u32 ℓ_B ‖ u32 |cb| ‖ cb ‖ wb)` for `|cb| < 2^32`; intake / genesis / header
  as `bdigest(tag ‖ Ser.enc ·)`), `outDE` (running list commitments `chainD` of the outcome,
  outgoing-receipt and proposal lists; the final `Outputs`; a constructor tag in the fourth field),
  `vmDE` (`chainD` of the call tape, `vmDE_snoc`: `next` is one SHA-384), constant clear fields,
  `viewE` and `viewE_binding` (a boundary collision is a SHA-384 collision or a collision of lane
  B's `stD` / lane A's `wasmD`). **Finding:** lane G's proposals (2) and (4) as written are not
  injective (`outD .none = outD (.eng ([], [], []))`; a `u32` length wraps for `|cb| ≥ 2^32`), so
  `Coll outD → Bad` / `Coll ctxD → Bad` would be unsatisfiable; `ViewE` keeps their circuit
  formulas and adds the domain separation. The serialisers of `Intake`, `GFin`, `ChunkInner`,
  `Outputs`, `CallArgs`, `Run` (and lane A's `encRest`) are instance arguments: `ViewSer.lean`
  (sub-agent, see the log) supplies them.

* **Serialisers (`E2E/ViewSer.lean`, `defaultTargets`; sub-agent).** `Ser` instances for the
  closure of `Intake`, `GFin`, `ChunkInner`, `Outputs`, `Prepared`, `EntK` (≈ 60 types: claim,
  witness, block, layout, walk, env, Wasm module/frame/gas/value types); resolved encoders
  `ctxDEc`, `outDEc` with `coll_ctxDEc`, `coll_outDEc` (a collision is a SHA-384 collision): lanes
  G and F can use `ctxDE .header`, `ctxDE .intake`, `outDE .done` now.
  **Finding (owner decision needed, not implemented): the call tape and the Wasm component cannot
  be committed injectively.** `TTN.RealStore.store : ByteArray → Option ByteArray` is a
  *function* field, and it occurs in `CallArgs` (= `VmQ`), `St`, `Res`, `Run`, `CallConf`;
  `no_ser_store : Ser TTN.Store → False` (Cantor). So **no** `vmD : VmV → Bytes` and no lane-A
  remainder encoder `encRest` is injective, and `Coll V.vmD → Bad` / `Coll V.wasmD → Bad`
  (premises of `viewImpl_binding_bad`) are unsatisfiable for every view: the M11c binding
  argument does not close for `call` configurations. In honest runs the store is a function of
  the context (`CutW.lean:101`: `store := fun hb => (env.codeOf (ofBA hb)).map toBA`, with
  `env.store : HStore` serialisable). Options: **(a)** a spec/machine change — `RealStore` carries
  first-order data (the `HStore`) instead of the function; **(b)** a view change — commit the tape
  and the Wasm remainder with the stores blanked (`ViewSer`'s `argsN`, `runN`, `confN`, `encQRN`,
  injective modulo stores: `encQRN_pf_mod`, `confN_eq`) plus a template obligation that
  `q.real.store` is the context `Env`'s lookup. Recommendation: (a) (it removes a non-first-order
  value from a boundary-carried type; the checker's semantics is unchanged if the function is
  rebuilt from the data at use). Lanes A/F: until then, `vmDE` and lane A's `encRest` exist only
  in the stores-blanked form.

##### How to discharge `SegSound*` (per lane, M11i)

All boundaries are under `viewE lB κ stD wasmD` (`ViewE.lean`) with lane B's `stD`
(`StateM5a.StateView` with `join/StViewE.stViewE`) and lane A's `wasmD P` (`WasmView`). A leaf
exposes `ctx` (the 18 limbs of `claimDigest s`, §3.4.1) and `s_in = [phase, h(B_in)]`,
`s_out = [phase, h(B_out)]` with `h(B) = bdigest (BndRec.encode B)` (`bndOf`); it witnesses the
two records, hashes them in-circuit, and copies every field it does not change. The Lean premise
is the **relative** obligation: T1 form `SegRelX V A Bad` (`Templates.lean`, `e2e_sound_t1_rel`),
M8 form `TmplSoundRel8 V A8 Bad k` over the circuit's leaf AIRs `circAirs8` (`E2ETree8.lean`,
`e2e_sound_m8_rel`; INIT absolute, `SegSoundInit8`) — "if `b` opens to `x`, then `b'` opens to an
`x'` with the edge below (and the context link)".

| lane / premise | edge (`Meaning k`) | fields that change (`V.bnd`) | context link | Lean tools |
|---|---|---|---|---|
| A `SegRelWasm` (T1) / `TmplSoundRel8 .wasm` (M8) | `call I c K q cc → call I c K q cc'`, `CSteps q cc cc'` | `wasm = wasmD P (some (q, cc))` only (AIR branch `airBnd` inside a call, `wasmD_air`); phase 6, `ctxRoot`, `stRoot`, accumulators, `vmAcc` copied | none | `csteps_seg`, `csteps_foldSegments`, `rsteps_foldSegments`, `wasmD_binding` |
| B ∧ F `SegRelState` / `TmplSoundRel8 .state` (split: `split_sound`) | `eng I c →* eng I c'` by `VFSteps` (engine steps whose honest tape is empty) | `stRoot = stD (stOfK (κ I) c)`; `outDE (.eng (eposAcc c.pos))` (append: `acc' = bdigest (acc ‖ Ser.enc item)`); phase 1, `ctxRoot`, `vmAcc = bdigest []` copied | none | `stViewE`, `stD_binding_E`, `vfsteps_rsteps`, `mstate_trans` |
| F `SegRelRt` / `TmplSoundRel8 .rt` | enter `eng I c → call I c [] q .pre`; next `call I c K q (.fin r) → call I c (K ++ [(q, r)]) q' .pre`; resume `call I c K q (.fin r) → eng I c'` with `estepO (strictO (K ++ [(q, r)])) I.prog c = .ok c'` | enter: phase 1 → 6, `wasm = wasmD P (some (q, .pre))` (fallback `fbBnd`), `vmAcc = bdigest []`; next: `vmAcc' = bdigest (vmAcc ‖ Ser.enc (q, r))` (`vmDE_snoc`), `wasm` → `(q', .pre)`; resume: phase 6 → 1, `vmAcc → bdigest []`, `wasm → none`, `stRoot`/accumulators of `c'` (the receipt step's effects, lane B's commitments); the circuit opens `vmAcc` by recomputing `chainD` over the answers it consumes | none | `vmDE_snoc`, `estepO_honest`, `strictO`, `rsteps_through_calls` |
| G `SegRelInit` (T1) / `SegSoundInit8` (M8, absolute) | `init cb wb → c`, `CM.step (init cb wb) = .ok c` (`c = eng I ⟨start, initRec⟩` or `gfin G`, `init_step_shape`) | `B_in`: phase 0, `ctxRoot = bdigest (0 ‖ u32 ℓ_B ‖ u32 \|cb\| ‖ cb ‖ wb)`, `stD .none`, `outDE .none`, `vmAcc = bdigest []`; `B_out`: phase 1 / 3, `ctxRoot = bdigest (1 ‖ Ser.enc I)` / `bdigest (2 ‖ Ser.enc G)`, `stD (stOfK (κ I) …)` / `stD .none`, `outDE (.eng ([], [], []))` / `outDE .none` | `∃ s secB w, s.wf ∧ claimDigest s = ctx ∧ cb = assemble s.ci secB s.secC` (INIT hashes `S` = `cb` with section B replaced by `u32 0`: `assemble_splice`, `encode_splice`) | `claimDigest_binding`, `assemble_wf`, `PublicStmt.decode_encode` |
| G `SegRelFinal` / `TmplSoundRel8 .final` | a `CM` run from `eng I ⟨.done out, _⟩`, `fin I out` or `gfin G` to `done H o` / `doneG` | `B_out`: phase 4 / 5, `ctxRoot = bdigest (3 ‖ Ser.enc H)`, `outDE (.done o) = (bdigest (Ser.enc o), [], bdigest [], bdigest [2])`, `stD .none` | for `done H o`: `∃ s, s.wf ∧ claimDigest s = ctx ∧ decodeChunkInner s.ci.chunkInner = .ok H ∧ headerOk H o` (M5d `final_template_sound`) | `cm_done_header`, `fin_accepts_iff`, `final_header_public` |
| D `TreeFaithful`, `PadSound8` | tree / PAD (`b' = b`, phase 4 or 5) | — | wrap: `cx (ctxOf s) = claimDigest s`, `B_0.phase = 0`, `B_N.phase ∈ {4, 5}` (**the `View.split` codes, not D-5's placeholder 1 / 2**) | `treeFaithful_of_aggH`, `compose_ctx`, `NodeExecV` (item 1 below) |

**Lane F status (F-3, 2026-11-25):** enter discharged in the canonical form from the circuit
(`m5t1/lean/M5T1/EnterC.enter_relC`, `enter_relC8`; non-vacuity on T1: `T1Enter`) under the view
laws `RtView` and the named checks `EntChecks` (README §F-3 lists them by owner); resume and the
STATE engine half are not (F3-1, no STATE engine rows); split leaves in the relative canonical form:
`SplitC.split_sound_relC`.


Notes for the lanes:
* **INIT must commit to the decoded intake** (`bdigest (1 ‖ Ser.enc I)`): every engine and call
  boundary carries it. `Ser.enc I` includes the revealed pre-state trie, so this is
  witness-sized hashing. A cheaper commitment by the source bytes `(cb, wb)` is binding only if
  `Intake` carries them (a change of the E2E machine's `Intake` record and a re-check of T1's
  run); not done, lane E proposal.
* **FINAL (M5d note (3))**: `MFinal` is a `CM` run, so the FINAL leaf covers `fin → done`, i.e.
  `finK` (storage bound, gas cap, post-state root, implicit transitions) as well as `tailNew`.
  Lane G's FINAL starts after `finK`: either join it with lane B's post-state root in one leaf, or
  lane E splits the `CM` step `fin → done` at `finK` (a new configuration; changes `cm_iff`'s
  proof and T1's 13-step run). Proposal, not done.
* **Phase cell**: the leaf must expose the record's own `phase` (the in-circuit hash covers it),
  and a template must reject `B_in.phase ∈ {4, 5}` (review-D7 I3) — automatic from the meanings,
  which never start at `done`/`doneG` (`meaning_not_done_src` for `done`; `doneG` is not a `FinStart`).

##### Split leaves: STATE = lane F ∧ lane B; INIT / FINAL = lane G ∧ lane B's IF proof (decision, M11i)

Lane B's B-T1 note (`m5a/README` "Lane E's T1 template system") is right: `m5tSeg` moves only the
working-set root `R_in → R_out`; *which* storage requests a VM-free engine step makes, and every
other boundary field (position, queues, gas, accumulators, the `rest` part of `stD`), come from
lane F's engine rows. **Decision:** a STATE leaf is one leaf proof whose trace is the **join** of
lane F's engine rows and lane B's `m5tSeg` rows, balanced on the shared request bus
(`SREQ`/`HB`); likewise an INIT (FINAL) leaf joins lane G's rows with the INTAKE (FINAL) half of
lane B's `m5tIF` proof through the public roots `R_0` (`R_n`, `post_state_root`). The Lean
obligation stays one per template (`TmplSound8`), and is **split** by `TreeM8.split_sound`
(`defaultTargets`, std axioms):

* `SplitAir A k`: the leaf's predicate gives an engine half `HoldsE ctx b b' q r r'` and a state
  half `HoldsS q r r'` sharing the bus traffic `q` and the state pair `(r, r')` (the leaf AIR's
  bus balance / equal public values — a property of the joined AIR, lane D / the integrator).
* `SplitSem`: `wIn x` / `wOut x` (the state value a configuration carries in / out), `qOf x x'`
  (the bus traffic of a meaning instance), `apply q r` (lane B's function).
* **`EngHalf` (lane F for STATE; lane G for INIT, FINAL)**: the rows open `b` to `x` with
  `wIn x = r`, `q = qOf x x'`, `Meaning k x x'`, `CtxLink k ctx x x'`, and *if* `wOut x' = r'` then
  `b' = lbOf V x'` (the engine half fixes every field of `B_out` except the state value, which
  it takes from the bus).
* **`StHalf` (lane B)**: `HoldsS q r r' → Bad ∨ r' = apply q r` (the restated `m5tSeg` /
  `m5tIF` soundness: `StSound.write_sent`, `WsBus.seg_root`, `chain_sound`, `m5b_final`).
* **`SplitGlue` (lane E)**: `Meaning k x x' → wOut x' = apply (qOf x x') (wIn x)`.
* `split_sound`: `EngHalf ∧ StHalf ∧ SplitGlue ⇒ TmplSound8 V A Bad k`.

Instances (what each lane states):

| leaf | `wIn` / `wOut` | `q` | `apply` (lane B) | glue (lane E, open) |
|---|---|---|---|---|
| STATE | the depth-24 working-set root of `stD (stOfK (κ I) c)` (`StateView.StCommit.ws`) | the run's storage requests (`SREQ`/`HB` messages: key, old / new value, presence) | `m5tSeg`: apply the requests to the working-set tree | the overlay after `VFSteps I c c'` is the overlay before with the run's requests applied (`Ovl` operations of the logged store; `OvlInv.lean` already walks them) |
| INIT | — / the root `R_0` of `stD (stOfK (κ I) ⟨start, …⟩)` | the revealed pre-state trie and `prev_state_root` | IF-INTAKE: `R_0` from the authenticated partial trie | `Ovl.ofTrie` of the intake trie has working-set root `R_0` |
| FINAL | the root `R_n` of the last engine state / `post_state_root` in `done H o` | the committed change list (`n`) | IF-FINAL (`m5b_final`): `applyChanges … = some T'`, `rootHash T' = post` | `finK`'s post-state root is `Ovl.finalize` of the overlay (`m5b_final`'s statement is the checker's fold) |

* The **IF proof may be checked by both the INIT and the FINAL leaf**: its two halves are
  independent statements linked to the rest only through the public roots, so each leaf can verify
  the same IF proof and use its half; nothing requires the two uses to be the same instance
  (soundness is per leaf). The double verification costs one extra IF verification per chunk.
* RT (`resume`) is the same split as STATE (lane F's receipt rows + lane B's rows for the
  receipt's storage requests); WASM's host storage calls join lane A's rows with lane B's on the
  HOST buses (lane B item 3), with `wIn`/`wOut` the working-set root inside `B.wasm`'s host state.
* Lane E owes the three glue lemmas (not done in M11i).

##### Lane G's G-3 boundary gaps (decisions, M11i; `m5d/README` §G-3)

All three follow from `ViewE.viewE` (the concrete view; lane B's `stD`, lane A's `wasmD`):

1. **`B_0` (INIT input, `init cb wb`, phase 0).** Fixed: `ctxRoot = ctxDE (.raw cb wb)` =
   **lane G's encoding adopted** `bdigest (0 ‖ u32 ℓ_B ‖ u32 |cb| ‖ cb ‖ wb)` for `|cb| < 2^32` (the
   only branch a real claim takes; the `≥ 2^32` branch `bdigest (5 ‖ Ser.enc (cb, wb))` only makes
   the function injective); `stRoot = stD .none` (lane B's `StateView.stD` at `.none`, a constant);
   accumulators `outDE .none = (bdigest [], [], bdigest [], bdigest [0])` — **not** lane G's
   proposed `(bdigest [], [bdigest []], bdigest [], bdigest [])`, which equals `outD (.eng ([], [],
   []))` and breaks `Coll outD → Bad`; `vmAcc = vmDE [] = bdigest []`; `wasm = none`,
   `inCall = false`; clear fields `clearE` = constants (`claimDigest = bdigest []`, all counters 0:
   the chunk context travels in the leaf statement's `ctx`, not in the record).
2. **INIT output / FINAL input.** There is no leaf ending at `B_0`: `INIT` is one `CM` step
   `init cb wb → eng I start` (or `gfin G`), so its leaf is the **join** INIT (lane G, `InitGPart`)
   ∧ INTAKE (lane B, `InitBPart`), composed by `TreeM8.split_sound` (§ "Split leaves"); its `B_out`
   is the full record of `eng I ⟨start, …⟩` (`ctxDE (.intake I)`, `stD (stOfK (κ I) …)`,
   `outDE (.eng ([], [], []))`, `vmDE []`, `clearE`). Likewise FINAL's input is the full record of
   `eng I ⟨done out, _⟩` / `fin I out`; **`finInDigest` and `prev_state_root` are join values**
   (on the bus between the two halves), not boundary fields. **`outRcptAcc` shape:** in an engine
   state it is the singleton `[chainD enc rs]` over the *unrouted* outgoing list (`AccV`'s
   `List Rcpt`; the shard routing is `finK`'s output, so it cannot be in an engine-state
   accumulator); FINAL opens it (witnesses the list, recomputes the chain), then builds its own
   routed `u64 shard ‖ u32 ℓ ‖ enc r` chain internally. **Item encodings:** `ViewE` uses the
   prefix-free `Ser.enc` (`OutD1`, `Rcpt`, `Proposal`), whose injectivity is proved; lane G's
   `OutD1.leaf` and `u32 ℓ ‖ Rcpt.encode r` may replace them once their injectivity is proved
   (lane E, M12 — open); until then a leaf computing a different item encoding does not meet the
   view.
3. **FINAL output `done H o` (phase 4).** Clear fields: **constants** (`clearE`); no pass-through
   leaf is needed — the outputs that matter are in `o`, which `outDE (.done o)` commits to.
   `outDE (.done o) = (bdigest (Ser.enc o), [], bdigest [], bdigest [2])` (the first field commits to
   the whole `Outputs`, the last is the constructor tag); `ctxRoot = ctxDE (.header H) =
   bdigest (3 ‖ Ser.enc H)` (`ViewSer` supplies `Ser ChunkInner`, `Ser Outputs`); `stRoot = stD
   .none`; `vmAcc = bdigest []`. Lane G's current `ctxD(.header H)` / `outD(.done o).1` values must
   be recomputed with these formulas. Lane I's plan to carry `gasUsed`/`gasBurnt`/`compute`/
   `receiptIdx` into `done` is dropped.
* **Open (lane G):** slot selection (`walkSegment`) is not in-circuit; the `psr_slot` mutant is
  rejected only by the statement check — a FINAL/INIT soundness gap to close in-circuit (it is part
  of `SegRelInit`'s / `SegRelFinal`'s meaning, `CM.step`).
* No checker or spec definition changed for these; `ViewE`/`ViewSer` are E2E-layer definitions.

##### Lane A's A-T1 points (decisions, M11i)

1. **Relative obligation adopted.** A field-copying leaf cannot open its input digest by itself
   (`TmplWasm.lean` §4); lane A's `segSoundWasmRel_of` / `e2e_sound_t1_wasmRel` (T1 form) are
   accepted as the T1-level statement (they stay in lane A's file: adding the same name to
   `Templates.lean` would clash with lane A's `open NearSpecV3.E2E.T1`). M8 form, in
   `TreeM8.lean`: `TmplSoundRel8` (every opening of `b` steps to an opening of `b'`, with the
   context link), `tmplSoundRel8_of` (absolute ⇒ relative mod collision), `NotInitIn` (a non-INIT
   leaf rejects a phase-0 input — lane A's leaf already asserts phase 6; lanes F/B/G add the
   check), and **`e2e_sound_m8_rel`**: absolute `SegSoundInit8` (INIT computes its whole input
   record from the bytes, so it opens `B_0`), relative `state`/`rt`/`wasm`/`final`, PAD ⇒ the E2E
   statement. Lanes F, B, G may prove the relative form for their copying leaves too.
2. **Whole-call completeness fixed.** `cm_decomp`'s `wasm` elements are whole calls; the M8 honest
   side now refines them (`refine_chain`, `csteps_fine`) into single call-machine steps from
   non-final configurations (`MWasm1`), so completeness is needed only there
   (`TmplCompleteFine`, **`honest_tree_fine`**). Lane A's leaf may merge consecutive steps
   (`CSteps.trans`, `WasmSegComplete`).
3. **The `.pre → .ent` seam** is the single step `cstep q .pre = preConf q`, an `MWasm1` instance:
   PREP proves exactly it as a `wasm`-kind leaf (kind map `kindOf` in `E2ETree8`); no new kind.
4. **`gasLeft` added** to `WasmBnd` (`Boundary.lean`, lane A's m6 README §6.1 diff verbatim:
   after `fuel`, `u64` in the codec), with **default `0`** so lane A's record literals
   (`airBnd`, `fbBnd`) build unchanged (two positional proofs in `WasmView.lean` — `wasmBnd_ok`'s
   anonymous constructor and one `WasmBnd.mk.injEq` destructuring — were shifted by one field in
   this branch; lane A's `WasmBase WasmBase-tool` builds, 727 jobs); lane A then sets it per §6.2 (`s.gas.g` on the AIR branch)
   and drops `gas.g` from `blank`. Every v3 `E2E` module downstream of `Boundary` and the zk-formal
   E2E/Nv chain are rebuilt. **On merge with lane A's A-T1:** `TmplWasm.wb_ext` (`cases a; cases
   b; simp_all` over 13 field equalities) needs a 14th hypothesis `a.gasLeft = b.gasLeft` (its
   callers have both records from `airBnd`, where it is `rfl` with the default), and any other
   positional `WasmBnd.mk.injEq` pattern in A-T1 / lane F / lane G files gains one `-`.
5. **Lane A's side of S1–S3 is done (A-T3, 2026-11-25; `a-t1/README.md` §10) [K].**
   * `WasmView` is store-blind. `wasmD_binding` is the restricted `CollOn WStripped` form that
     `SB.bnd_eq_canon` needs. S2 is `fbCode`, and S3 is `codeRootOf` via `CodeCommit`.
   * `WasmViewParams` is inhabited (`WasmViewT1.wasmViewParams_nonempty`, T1's real context).
   * The Wasm template targets `TmplRelC`: `TmplWasm.segSoundWasmRelC_of`, with `Bad =
     Sha384Coll ∨ Coll V.ctxD`, plus the named, honest-proved `GhostC`.
   * PREP is a `wasm`-kind leaf: `TmplPrep.segSoundWasmPrepRelC_of` covers segments ⊕ PREP and
     adds `Sha256Coll` to `Bad`.
   * In the per-lane table, read lane A's row as: Lean tools `segSoundWasmRelC_of`,
     `segSoundWasmPrepRelC_of`, `wasmD_binding` (restricted), `seg_setSt`, `preConf_canon`.

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

**M11e (lane E, 2026-11-03/04):** see §3.5. Done:
* the one-database QROM verdict, with per-round targets (budget doc §9);
* the D-5 tree transcription (`E2ETree.lean`);
* the computable `honestQ`;
* the binding-defect correction for M11d.

**M11f (lane E, 2026-11-04):** see §3.5. Done:
* the chunk key list carried in `StV` (`EngSt`, `ViewImpl.keys`) and lane B's `StViewE`
  supplied (`encStV_inj`, `keysOf`, `idxOf`, `depth`); `FitsReachK` reduced to `EngOvlInv`;
* the NvAir exporter run on the e2e-tree stack and `NodeTape` proved from the export (memory
  consistency + `PvD`), with the bus-closure vacuity guard;
* the soundness budget refreshed for D-8, with the claim stated per level.

**M11g (lane E, 2026-11-04/05):** see §3.5. Done: `NodeExec` over the circuit's own predicate
(all four tables exported), honest-trace non-vacuity, `PvdAt` and the program's asserts from
program binding + op decode over the byte bus, and `EngOvlInv` for accepting runs (value bound `cur` still a hypothesis).

**M11h (lane E, 2026-11-21) [K]:** see §3.5. Done: the T1 segment system with one named
soundness premise per template (`E2E/Templates.lean`: `SegSoundInit` (G), `SegSoundState` (B),
`SegSoundRt` (F), `SegSoundWasm` (A), `SegSoundFinal` (G), `WrapInitSound`/`WrapFinalSound`) and
`e2e_sound_t1`; every `CM` run factors into the templates (`cm_decomp`); **M11 exit criterion met**:
T1's accepting run kernel-checked under 34 GB (`T1Run`, 27.1 GB) with `t1_e2e_stmt` and
`t1_honest_chain`; canonical `S`/`claimDigest` (§3.4.1); the 33 accepted statement mutants
explained (§3.4.2); `cur` narrowed to `curHard` + `VmWritesShort`, with the spec/nearcore
receipt-size finding.

**M11i (lane E, 2026-11-21…25) [K]:** see §3.5. Done: the **relative per-template obligation
made official** (`TmplRel`, `SegRel*`, `e2e_sound_t1_rel`); the M8 heterogeneous tree
(`TreeM8`: `e2e_sound_m8`, `e2e_sound_m8_rel`, wrap connection, `split_sound` for STATE = F ∧ B and
INIT/FINAL = G ∧ IF, `honest_tree_fine`; zk-formal `treeFaithful_of_aggH`); lane E's view
components (`ViewE`, `ViewSer`); `WasmBnd.gasLeft`; `NodeSha` and `NodeLink` from the circuit
(`NvOps`, `NvSha.range_cells`, `NvNode.nodeExecV_of_contracts`). Findings: the range-digest tail is
not pinned (`TailCanon`, lane D), `RealStore.store` is a function so the call tape and Wasm
remainder have no injective commitment (owner decision (a)/(b)), lane G's view proposals needed
domain separation.

Next for lane E (M12), in order:
1. Owner: `RealStore` (a)/(b); `height_created`; the intake-side receipt-size hypothesis (`cur`).
2. The three split-glue lemmas (`SplitGlue` for STATE, INIT, FINAL: overlay semantics).
3. `PackOK` (the ALU's Ext12 `Mul`/`Add` chain of `pack`, basis cells from `ce`), then
   `ProgBound` (BIND/anchor) and `GlueByteBool` (GLUE phase-bit induction); `NodeInner` is the
   extractor's.
4. The zk-formal Nv chain rebuilt against the `gasLeft` boundary (see the M11i log: the rebuild is
   ≈ 2 h / 28 GB for `NvOps` alone on a quiet host).

Previous list (M11h → M11i):
1. Lanes F/A/B/G: discharge their `SegSound*` premise for their T1 leaf (and `TmplComplete` for
   the honest side). Lane D: `WrapInitSound`/`WrapFinalSound` from the wrap's checks on the opened
   record (`claimDigest` of §3.4.1, `phase`, `headerOk`).
2. `cur`: owner decision on an intake-side receipt-size hypothesis (incoming receipts satisfy the
   New-mode 4 MiB limit), then a receipt-size pass for the remaining `Hard` columns;
   `VmWritesShort` from the host (`storage_write` 4 MiB check).
3. `ProgBound` from BIND/anchor and `GlueByteBool`; then `NodeSha` (Sha512Air4 exported), `NodeLink`.
4. A full-circuit honest trace to exhibit `NvHold` itself.
5. Lane B: move `FitsReach` to `stOfK`; confirm `idxOf = 0` (lane B M5a-9: per-boundary restarts
   check).

M11d's open list, updated:
1. ~~A constructive recorder for `honestQ`~~ (M11e: `recordK`).
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

**Done 2026-11-21, sixth session (lane A): M6, lane-A side** (`m6/README.md` §5; log
`docs/logs/e2e-laneA-wasm-2026-11-03.md`). The build is green (727 jobs, on main `7358a938d`) with
standard axioms, `pin-check` passes, and `spec/` is unchanged.

* **Honest host premises [K].**
  * The two-run footprint `callHost_two_run` holds for all 75 + 14 arms. Low-equivalent states on
    the arm's read set give one `HostEff` applied to both.
  * A spec-level non-vacuity check (`pinned_cont_g`, `Vacuity2.twin_witness`) would have caught
    HostVacuity.
  * `rel_twin_post` and the page count on the thread (`SigP`) lead to `seg_sound_hostIf_air`:
    segment soundness with every HOST-row premise discharged except the named ones —
    * the producer contract `HostIf` + `HostAnsCov`;
    * `HostWritesCovT` (the AIR gap below);
    * `HostProdNodup`;
    * `HostCallsNotLinear`.
* **One chain [K].**
  * `seg_chain_all_mp` (+ `_csteps`) carries the σ pin, the memory root and the key bus.
  * Entry: the decidable `EntryPub` and `entry_inSA_mp`.
  * Exit: `callResult_of_segments_mp` (M6.5 shape).
  * `wasm_base_sound_m2σ`.
* **Host answers ↔ tape [K][M].**
  * The `HostIf` contract is indexed by host-call rank. `SigKeep`, the in/out pins and the bus
    messages ↔ the thread's arm run are proved.
  * `callResult_of_chainσ`.
  * Lane B's obligations are stated as `ProducerObl`.
  * Answer functions are proved for `register_len`, `input`, `read_register`.
  * Corpus host frequency: `m6/host-freq.md`.
* **Grow [K][M].**
  * `M3Ctx`, size clause `SzC`, all MEMG rows, and `seg_sound_g`, the last relative to a named
    non-MEMG action layer `SegGLayer`.
  * Corpus `d3rich` grow calls: 1,309/1,309 segments pre-check; 215 + 25 grow segments proved and
    verified (median 1.43 MB, 53 s); tampers 65/65.
* **AIR fix [M][K]: bus 214, multi-group HOSTB.** HOSTB group bits; `hid` = base id. Before it,
  every segment with a `storage_write` value group failed pre-check, also on the default MP AIR.
  Re-proved, re-checked, and all tamper batteries rejected.
* **Found, open:** the write-coverage AIR gap. Five `setU128H` hosts write memory with no
  space-3 message: `account_balance`, `account_locked_balance`, `attached_deposit`,
  `validator_stake`, `validator_total_stake`. All five are imported by `d3rich`. The proposed HOSTB
  old-byte write pair is in `m6/README.md` §5.5.
* **Proposed to lane E (route via integrator):** `WasmBnd.gasLeft` and the register-id order via
  `registersDigest`. The diff is in `m6/README.md` §6.

**Next (lane A):**
* The write-coverage AIR change (HOSTB `ob` column and the space-3 write pair), with re-proof and
  tampers.
* Grow:
  * `SegGLayer` (base-row FETCH under `CodeOK3`, MEMBG pairing, the CUT link);
  * the grow memory root, halting case and chain;
  * the fee bound on failed grows.
* Answer functions for `storage_write`, `log_utf8`, `value_return`, `ed25519_verify`; `EntrySeed`.
* With lane B: discharge `HostIf` from the state rows (M6.4, `ProducerObl`); pin the HOSTB group
  index when the state side consumes wire ids.
* The generator limits (i32 host signatures in segment AIRs, stack-budget trap row, out-of-gas row,
  `≥ 2^27` addresses).
* **Next milestone, the aggregation-tree leaf (lane D §5.0.1.4; `m6/README.md` §5b):**
  * fixed per-template heights;
  * in-circuit CODE/FUNC roots, with touched-record multiproofs per segment;
  * proof + vk on disk.

The milestone-1 exit test (return bytes, logs and gas equal the chunk's outcome on T1 and T2, with
mutants rejected) is met. The gas equality holds outside the proof (the tape) until M6. The
`lake build WasmBase` breakage reported on 2026-10-31 was fixed on main (`6a1739cd7`), and the build
is green with the new files.

**Done 2026-11-21, seventh session (lane A): milestone A-T1** (`e2e-general/a-t1/README.md`; log
`docs/logs/e2e-laneA-wasm-2026-11-03.md`). `lake build WasmBase wasmbase-tool` is green (741 jobs)
with standard axioms and no `sorry`, `pin-check` passes, and `spec/` is unchanged. Sub-lanes: WCOV,
ANS, CONN, JOIN.

* **T1 blocker (lane I) [M]:** at lane A's head, T1 pre-checks and chains at every cut size
  1–26. It proves at K = 8 and K = 26, and `t1/run_t1.sh` passes. The failure came from binaries
  older than FIX214.
* **Item 1, write coverage [M][K]:**
  * HOSTB `ob` and the space-3 write pair (`act·dir·(1−reg)`).
  * The old AIR proves a run that ignores `setU128H` writes (KAT); the new one gives 8/8 proved and
    54/54 tampers rejected.
  * `HostWritesCovT` is derived; `seg_sound_hostIf_airW` has no write premise (producer clause
    `HostNoTouch`, with non-vacuity).
  * Failed-grow fee: analysed, open.
* **Item 2, answer functions [K]:**
  * `storage_write` (both backends), `log_utf8`, `value_return`; `ansT1` for all six T1 hosts.
  * `specU_T1`. Finding: `ProducerObl.spec` cannot express host-side updates, so it is restated as
    `SpecU`.
  * `decide` checks on T1's calls match the tape's gas.
  * Open: the bridge `hostPost_of_answer` to `HostIf.ans`.
* **Item 3, T1 as pinned-shape leaves [M]:**
  * The prover runs on the stack's backend with the base configuration (first-order
    certificates, m = 64, 24 grinding bits), at pinned template heights
    (`segtemplate`/`segleaf`/`segleafverify`).
  * T1 gives 2 leaves, about 553 KB each, 268.2 bits, queries [100, 71, 45, 33], one vk on disk.
    The leaves are reloaded and verified; 11/11 tampers rejected.
  * CODE/FUNC roots are published as cached commitments (R1).
* **Lane E's template [K]:** `TmplWasm.lean`: `segSoundWasmRel_of` (relative), `segSoundWasm_of`
  (absolute, with `InOpens`), `e2e_sound_t1_wasmRel`.
  * Findings: the absolute `TmplSound` needs an opening premise for any field-copying leaf (adopt
    `TmplSoundRel`); `TmplComplete .wasm` fails for `pre → pre`; the whole-call meaning must split.
  * The `.pre → .ent` seam is `cstep q .pre = preConf q`, and PREP covers exactly it (statement in
    the a-t1 README §7). No new `Meaning` is needed.
* **Item 5, M6 join [K][M]:**
  * HOSTB bus 210 carries the absolute address.
  * `wasmBaseSegAirMPJ`: the oracle cannot answer 58/60; storage request bytes go to lane B.
  * Lane B's `StorageJoinObl`.
  * T1 on the J AIR lacks exactly `storage_write`'s HOSTQ, HOSTR and 6 HB messages.
  * Wire-id mismatch with lane B's `StbH`: the value group is wire 314.
* **Item 4 PREP [S]:** scoped (R1 roots; certificate-style AIR; d3tiny 6 SHA-256 blocks,
  32 records). Not built.

**Next (lane A):**
* PREP for d3tiny: CODEBYTES + SHA-256 first, which needs `HashRegisterLink`.
* `hostPost_of_answer`.
* Bind `stackRem` as a public (SEGB/CUTI design in the README §8). `vmCtxDigest` waits for lane E's
  `gasLeft`.
* The joined pre-check with lane B's tables; storage read/has_key rows.
* The failed-grow fee bound.
* A height-class menu over a corpus sample.

**Done 2026-11-25, eighth session (lane A): milestone A-T2** (`e2e-general/a-t1/README.md` §9; log
`docs/logs/e2e-laneA-wasm-2026-11-03.md`). `spec/` is unchanged; no Lean definition of the repo
changed.
* **Pinned tight heights [M]:**
  * `segleaf` commits every common main at its template height (`set_tight_floor`, as lanes B and
    G do).
  * `template_heights` gives the pinned `(log, tight)` per AIR from the template file alone.
    `segleaf` asserts it, and `segleafverify` refuses any other heights. The vk is unchanged
    (`b1eed0ca…`).
  * T1 re-proved: 554,709 / 553,071 B, 268.2 bits, prove 25.7 / 28.3 s, verify 17 ms, 8.2 GB.
    Both segments now declare identical heights.
  * Lane D's `m8-import` gives equal `INFO.json` heights, and the leaf program is **one WASM
    program** (`59b572a7…`, 238,436 rows; it was two). Measured with the new `M8_PROGRAMS_ONLY=1`;
    the other templates' roots are unchanged.
  * Saved-leaf tampers: 14/14 rejected. New cases: the A-T1 proof of the same segment under the
    same vk at natural tight heights, and a changed template height.
  * Proofs: `/data/illia/nearproof-deps/e2e-laneA/at2/leaf-k13p/leaf/`; `m8_import_real.sh`
    defaults to them.
  * Lane D's tree-leaf proofs of the two children are not run (~33 GB).
* **PREP stopped: it needs a statement change [K][S].**
  * (P1) The `.pre` record (`fbBnd`) has no code field. The code is reachable only through
    `vmCtxDigest = bdigest (encRest (.other (q, .pre)))`, and no `BndRec` field carries the code
    hash.
  * (P2) **`WasmViewParams` is uninhabited** (`a-t1/lean/PrepScope.lean`, `wasmViewParams_empty`,
    standard axioms). `encRest_inj` would inject `q.real.store : ByteArray → Option ByteArray`
    into `Bytes`, which Cantor's argument rules out. So every lane A theorem over `Pv` is vacuous
    (`wasmD_binding`, `segSoundWasmRel_of`, `wasmHolds_honest`).
  * (P2, lane E side) `vmD_coll : ∀ V, Coll V.vmD` is proved, so lane E's `hvm` premise holds only
    with a provable `Bad`; `Coll V.wasmD` likewise, not formalised.
  * (P4) `codeRootOf` is a free parameter, and `CutSeed.ctx` is a named premise.
  * Proposal (lanes A, E, F; owner):
    * S1: the Wasm and VM remainders exclude the function-typed store (committed by `stRoot`),
      and lane E's component bindings become modulo the store (`E2E/View.lean`).
    * S2: `fbBnd (q, .pre).codeRoot := SHA-256(q.code) ‖ 0¹⁰`, written by lane F's enter leaf from
      `FB`.
    * S3: `codeRootOf` = the R1 root, plus a named commitment-binding event.
  * PREP's AIR then reads `B_in.wasm.codeRoot` and writes `B_out.wasm.codeRoot/funcRoot`, the cells
    lane D's record already carries. No AIR was built.

**Done 2026-11-25, ninth session (lane A): milestone A-T3** (`e2e-general/a-t1/README.md` §10; log
`docs/logs/e2e-laneA-wasm-2026-11-03.md`). `S`, `claimDigest` and the checker are unchanged.
* **S1–S3 adopted on lane A's side [K]:**
  * `WasmView` is store-blind. `encRest_blind` and `encRest_inj` hold modulo stores, and
    `ctxOf_blind` holds.
  * S2: `.pre`'s `codeRoot = preCodeRoot q`.
  * S3: `codeRootOf`/`funcRootOf` are `CodeCommit` roots of the padded records.
  * `wasmD_binding : CollOn WStripped (wasmD P) → Sha384Coll`, and `wasmD_set` (the component is
    store-blind).
  * **`WasmViewT1.wasmViewParams_nonempty`**: T1's record uses the real `checkModuleM2` context
    `ctxM2` and lane E's store-blind serialisers. `vT1` (lane E's `vSB` with lane A's component)
    is `StoreBlind` and `ClearCall`.
  * `SegStore.seg_setSt`: a segment keeps the store function.
  * **`TmplWasm.segSoundWasmRelC_of`** proves `SB.TmplRelC sf V A (Sha384Coll ∨ Coll V.ctxD)
    .wasm`. It adds one named premise, `GhostC`: the ghost carries the canonical store of the
    intake pinned by `ctxRoot`. `GhostC` is honest-proved.
* **PREP as a `wasm`-kind leaf [K][M]:**
  * `PrepAir`: PHDR, SHA-256 over the code bytes, and the segment AIR's CODE/FUNC tables verbatim.
  * **`PrepSound.prep_sha_sound`**: from `Holds prepAir`, the 32 public hash bytes are SHA-256 of
    the SHA table's message, and the public length is its length.
  * **`TmplPrep.segSoundWasmPrepRelC_of`**: the Wasm kind over segments ⊕ PREP meets `TmplRelC`
    with `Bad = Sha384Coll ∨ Coll V.ctxD ∨ Sha256Coll`. It relies on `preConf_canon` and the named
    premises `RecordsCert`, `PrepRest` and `ent`.
  * T1's PREP leaf: **469,779 B, 268.2 bits**, prove 31 s, verify 13 ms, 7.7 GB, pinned heights.
    Its cached CODE/FUNC roots equal both A-T2 segment leaves' roots (natively and in lane D's
    `INFO.json` cells). `m8-import` verifies it.
  * Mutants: 14/14 rejected. The record mutants are rejected only by the R1 comparison with
    the segments.
  * Finding: `Chips.Sha.sh_len` is not tied to `Nd`, so the segment `sha256` summary does not bind
    the length.
* **Open:**
  * The decoder certificate `RecordsCert`. PREP does not yet tie the records to the code bytes;
    this is the main Wasm-side gap.
  * `PrepRest` (the entry record), and PREP's error branches.
  * `CodeOK`/`FuncOK` from S3.
  * Lane D: insert the PREP leaf into the tree spec, between RT `enter` and WASM 0, with a
    normaliser from the hash bytes to `B_in.codeRoot`.

**Next (lane A):** the decoder certificate (README §4 steps 2–5) for d3tiny's subset; the
`stackRem`/`gasLeft` publics (`RestOK`); `CodeOK`/`FuncOK` from S3; `Nd` in the segment `sha256`
summary.

### 5.0 Lane D: status, 2026-11-21 (milestone M8, heterogeneous tree; prototype)

**Where to read:** `research/near-compression/e2e/README.md` §0 (M8; D-9 is now §0.9),
ZK-ARGUMENT §10.5, log `docs/logs/e2e-zk-lane-d-2026-11-21-m8.md`.

**Done (M8):**
* **Generic template leaf** (`nv/htree.rs`): a template is a declared layout (`TemplateSpec`:
  phases; input / output boundary-record cells from child public values, cached-commitment limbs,
  statement cells, pass-throughs, constants; `ctx` source; public-value equality / pins). Leaf
  generation is refused unless every public value and cached commitment of the child is bound. The
  leaf exposes `H9(ctx, a, a+1, [phase, h(B_in)], [phase, h(B_out)])`. Template set binding
  (option A) over several kinds: `P_2`'s one-hot set holds every template's leaf program.
* **Chaining rules in-circuit:** boundary equality (phase + digest), index continuity, one `ctx`,
  INIT at the left edge and DONE at the right edge (wrap), no DONE input for any template (I3), PAD
  only after DONE. Constraint-level negatives on the Fib fixture (template swap, boundary mismatch,
  reordering, PAD misuse, foreign `ctx`, forged preimage, no FINAL).
* **`ctx` = `claimDigest = bdigest(S)`** of §3.4.1 (14 three-byte limbs + 4 zeros, lane G's
  exposed form); packet `S ‖ wrap`; V_d recomputes it from `S` alone. T1: `bb5aad11…9f2f01`.
* **T1 prototype over the lanes' saved leaves:** stub INIT · lane B IF · lane A seg 0, seg 1 · lane
  B seg · stub FINAL (+ PAD), arity 4 depth 2, one wrap (README §0 table).
* D0a unchanged (`regress_m8_d9.sh`); depth-0 one-template D0a tree (code only).

**Open (M8):**
* Lane G's INIT / FINAL as real leaves: their proofs must be saved on the stack backend
  (`CtxMode::Src(pv 0..14)` and the record of LEAF-TEMPLATE-SPEC §3 / §4 are ready to declare).
* ~~Lane A: pin the tight heights (two T1 segments give two leaf programs today).~~ Done by lane A
  A-T2 (2026-11-25). The leaves are at `e2e-laneA/at2/leaf-k13p/leaf` and give one WASM program
  `59b572a7…`. `m8_import_real.sh` defaults to them.
* Lane E's `BndRec` digests in place of the prototype record (the templates expose
  `bdigest(BndRec)`; the leaf's record is then those 14 limbs).
* Lane F's `rt` leaf; a run-independent setup (pinned template shapes); cheaper PAD_L / PAD_N;
  the 6 D0a sample trees; the owner decisions (`u`, 268 vs 274).

### 5.0-D9 Lane D (ZK wrap for M9): status, 2026-11-05 (milestone D-9)

**Where to read**
* `research/near-compression/e2e/README.md`: §0 is D-9; §0a is D-8, §0b D-7, §0c D-6, §0d D-5, …
* `research/near-compression/e2e/ZK-ARGUMENT.md`: §10.1 tree wrap, §10.2 D-7, §10.3 D-8, §10.4 D-9.
* Logs:
  * `docs/logs/e2e-zk-lane-d-2026-11-05-d9.md` (D-9);
  * `docs/logs/e2e-zk-lane-d-2026-11-04-d8.md` (D-8) and `…-d7.md` (D-7);
  * `docs/logs/e2e-zk-lane-d-2026-11-04.md` (D-6);
  * `docs/logs/e2e-zk-lane-d-2026-11-03.md`.

**Done (D-9):**
* **One leaf geometry per family, one wrap setup.** Each class's leaf is proved at the smallest
  geometry that holds it. S and M form one family (NvAir 2^19); L forms another (2^20). Each family
  has its own `PAD_L` and `P_2`. All `P_2` are proved at one node geometry, and the wrap anchors the
  set `{C_2^f}`. The setup is version 6.
  * An L chunk reproduces the setup made by an S chunk byte for byte, including L's `C_2`, which
    the setup computed from a probe.
  * Cost: the leaf is −14 % time and −15 % memory at equal threads. That is only ≈ 4–5 % of an S/M
    chunk's tree proving, because the leaf's SHA AIR stays at 2^21 rows. The larger D0a-specific
    cost is elsewhere: in a one-template chunk, 3 of the 4 leaves are `PAD_L` proved at the full
    family heights.
* **Review-D8 M1 / M2 fixed.** Every class's base vk is rebuilt from the declared AIR, its TAPE pad
  and the calibration for its shape, in both `tree-prove` and `tree-audit`, and compared byte for
  byte.
  * The pad is validated. `validate-base` uses the pad, and the chain path refuses a padded base
    (I4).
  * The reviewer's three tamper fixtures are rejected.
  * `tree-audit` regenerates every setup constant except the other families' `C_2`, which needs a
    run of each family (L1).
  * ZK-ARGUMENT §10.3 is corrected (L3 / I1).
* **Every layer at 274 bits per round, one S chunk** (`NEARPROOF_RBR_ALL=274`; measurement only).
  The packet grows by 6,130 B (329,357 → 335,487 B), confirming lane E's +6.3 KB estimate. Verify
  time is unchanged (≈ 69 ms). Tree proving is +12 % (loaded host). Base: see README §0.
* **Throughput sample, partial** (stopped on the M10 re-prioritisation).
  * 10 random corpus chunks (6 S, 2 M, 2 L): all dumped and base-proved.
  * 4 S chunks tree-proved under the production setup. Each reproduced the setup byte for byte.
    Packets 328,866–330,591 B; tree 1,870–2,021 s; verify 48–55 ms.
  * No failures. Something outside lane D's scripts deleted the driver binary mid-run; it was
    rebuilt and the run resumed.
* **Tidy.** Every run script fails on error, and every results directory carries `SHA256SUMS`
  (`scripts/sha256sums.sh`).
* **Oversize policy (review-D8 L2).**
  * A chunk that no class admits is rejected by the prover: `class-admits` fails, and no base is
    proved.
  * For production, add a larger class. It is a new family and a new `P_2` in the same setup; this
    is free while that `P_2` fits the node geometry, and needs `h_N` re-derived otherwise.
  * Alternatively, segment the chunk (lanes A/B boundaries).
  * The 7 TAPE pad keys are corpus-derived. Deriving them from the AIR's public buses is open.

**Open (D-9):**
* Base-point `u` (QROM): pending an owner decision.
* The per-round target (274 vs 268): owner decision, now with measured numbers.
* Lanes A/B templates (blockers 4, 5, 8, 9) and their segment parameters (I5: seg-v1 at 32
  grinding bits is 266.9 bits).
* `PAD_L` cost in one-template trees.
* TAPE keys from the AIR.
* An independent review of D-9.

#### D-8 status (superseded by D-9 above)

**Done (D-8):**
* **Production base-class set.** A heights census of all 1,311 D0a-compatible honest chunks of the
  d1/d2/d3 corpora (`statedump --heights-only`); three nested classes chosen over it with 25 %
  headroom (`classes_d8.py`): **S** (83.4 %), **M** (13.1 %), **L** (3.4 %, the tail: base at
  `n_stack` 22, lb 2). Every census chunk is assigned a class; coverage is checked chunk by chunk
  (re-cut at the class, every classical constraint re-checked, then the base prover's precheck:
  every constraint and bus). The TAPE is pinned per class (`TapePad`: log + the corpus's 7 public
  keys, built identically by prover and V_d), so it no longer splits classes. The generator now
  grows any table past its render (zero rows, cyclic byte window, row-counter padding; the
  ill-founded 2-row progression fixed). Two chunks per class proved (6 bases) and tree-wrapped
  against **one setup** for all three classes (README §0).
* **Arity 4 is the default** (`tree-prove … - DEPTH`, `run_tree.sh TAG -`); node margin per arity
  `max(1.10, 1.01 + 0.04 (arity − 1))` = 1.13 at 4.
* **Leaf cost.** Re-measured: the segment leaf's size depends on the segment's WHIR parameters, not
  only its height — at the stack's base configuration (first-order certificates, list decoding
  m = 64) a 2^22-row lb-1 segment needs [97, 69, 41, 31] queries (5,192 query·depth units), the
  lanes' seg-v1 parameters [536, 256, 83, 50, 36] (21,789), D-7's model law 610 per round. A leaf
  over an `n_stack`-22 base was measured (class L). **Implemented lever: leaves at their own
  rate** (`ns20lb2`, setup constant): leaf proof −39 % CPU time and memory at equal threads, `P_2`
  +15 % (more queries per child). Projection (model): 1 Pgas 21.2 → 14.2 s, 100 Tgas 7.8 → 5.6 s
  after execution with the leaf lever + segments at the base configuration (lanes A/B).
* **Review-D7 folded:** L1 (`sha_cap_log` in the shape pin; static child-height check in
  `build_verifier`), L2 (confirmations distinct by chunk), L3 (class vks shipped with the setup,
  `tree-audit`), L4 (PAD_N text), L5 (anonymity sets ≥ 45 chunks), I4 (codec inside
  `catch_unwind`), the reviewer's forged test in the repo tests; I3 noted for lanes A/B (§5.0.1 (4)).

**Open (D-8):** QROM `u` (owner); lanes A/B templates (blockers 4, 5, 8, 9) — and their segment
parameters (adopt the base configuration at 24 grinding bits: −75 % in-circuit hashing per segment leaf); one leaf geometry per
setup (class L's leaf sets every class's leaf heights in a shared setup: a production setup per
leaf-geometry family, or L chunks split into S-size segments; *done in D-9: families in one
setup*); an independent review of D-8 (*done: no Critical/High; M1/M2 fixed in D-9*).

#### D-7 status (superseded by D-8 above)

**Done (D-7):**
* **Base shape classes (review-D6 F1).** A template class is now a pinned per-AIR `(log, tight)`
  base shape that several chunks share: the dump is re-cut at the class logs by the generator
  (`statedump --class`, re-checked) and the base committed at the class tight heights
  (`NEARPROOF_BASE_CLASS`). Two classes over real d1 chunks (A: 2 members, B: 5 members; 4 bases
  proved); each class's leaf program is the same for both proved members, and a class-B member that
  did not define the class reproduces the setup byte for byte. The D-6 claim is reworded: the D-6
  setup accepted exactly its three defining chunks.
* **Two node shapes + PAD at any level** (`P_2` over leaves at their own heights, `P_*` above,
  `PAD_N` with a witness level; `Builder::sibling_alt`), **multi-instance SHA AIRs** (up to 4,
  disjoint compression-id ranges), arity 2 depth 3 on real chunks with one setup over two classes
  (packets 326,903 / 328,349 B, 22/22 negatives each, ZK flag set, `A = 8`), constraint-level tests
  of every new binding rule.
* **Base-template leaf is the default** (statement and soundness link: ZK-ARGUMENT §10.2); the
  chain L1..L4 leaves the tree path.
* **Review-D5 open items closed** (verifier-path errors, structural last-used-row check) and
  **review-D6 F2–F7 folded** (no chunk names in the setup, base vk hashes, soundness of tree setups
  recorded, base-leaf constraint negatives, base-mode ZK flag by check, text).
* **Arity re-measured on real chunks** (README §0): `P_2` proved at arity 2, 3, 4 (2 SHA instances)
  and 8 (3 SHA instances, NvAir 2^22, 39.6 GB peak), each wrapped and verified; `P_*` measured at
  arity 2 and probed at 4 and 8 (+12 % / +27 % NvAir over `P_2`: children at the node heights cost
  more). **Recommendation: arity 4** (lowest CPU work up to ≈ 100 leaves and lowest projected GPU
  work at 1 Pgas; fits this host). **Projection** (model only, 8 H200, streaming): 1 Pgas ≈ 20.8 s
  (arity 4) to 23.9 s, 100 Tgas ≈ 6.7–9.1 s after execution; throughput-bound, dominated by base
  segments and their leaves (the leaf of a 2^22-row segment costs more than the segment proof).

**Open (D-7):** QROM `u` (owner); a production class set (pinned shapes with headroom chosen over
the corpus; some tables can be re-cut only up to their classical render height); lanes A/B
templates (blockers 4, 5, 8, 9); an independent review of D-7.

#### D-6 status (superseded by D-7)

**Done (D-6):**
* **The tree-wrap packets are ZK in the classical ROM** (`zero_knowledge_established = true`,
  ZK-ARGUMENT §10.1): the argument was re-read for the wrap program (statement
  `(claim, hint, class, setup)`, same AIRs and public columns as the D0a FINAL, 60 + 37 stacked
  columns, every §6.4 term carries over, aborts `A·2^-192`). The flag is gated on wrap `zk = 6`,
  base `zk ≥ 1` and shape-floored template chains.
* **All three D0a classes have shape-floored chains** (chunks 2 and 3 re-proved; D0a packets
  326,077 / 326,468 / 325,825 B), so every setup and template constant is a function of the class
  shape. **One tree setup for all three chunks** (arity 2, depth 1; `SETUP.json` 4,531,396 B,
  chunks 2 and 3 reproduce chunk 1's byte for byte); a **fresh chain's template set equals it**.
  Packets 327,911 / 327,630 / 327,365 B, verify 42–46 ms one core, 18/18 negatives each.
* **Depth 2 on real chunks** (4 leaves incl. 3 PAD, 2 + 1 nodes): chunks 2 and 3, one setup,
  byte-identical; packets 329,268 / 327,029 B; every node runs `C_node`.
* **Arity:** per-child node cost measured (334K NvAir, 1.16M SHA rows, 172K program rows); a
  3-ary node proved (421 KB, 547 s, 21.3 GB); 8-ary does not fit: 3 SHA instances, and a node's
  NvAir height must equal its children's (BIND), so every tree proof would move to NvAir 2^22.
  Comparison for 1 Pgas in README §0 (`scripts/tree_arity_model.py`).
* **Lanes A/B leaves planned** (§5.0.1.4) and the wrapper prototyped on the D0a base
  (`build_base_leaf`: a standalone non-NV STARK with cached tables verified directly by the leaf;
  packet 327,449 B; the chain L1..L4 leaves the tree path).
* **Review-D5 folded in** (D5-1 constraint-level tests adopted + depth-2 / mixed-level negatives,
  D5-2, D5-5).

**Open (D-6), all addressed in D-7 except QROM and lanes A/B:** QROM `u` (owner); two node shapes + PAD at any level (needed before 8-ary pays
off); an 8-ary node (3 SHA instances, NvAir 2^22, ≈ 30–70 GB); lanes A/B blockers 4, 5, 8, 9
(§5.0.1.4); verifier-path panics → errors before library use; an independent review of D-6
(done 2026-11-04: no Critical/High; F1–F7 folded in D-7).

#### D-5 status (superseded by D-6 above)

**Done (D-5):**
* **An aggregation tree feeds the ZK wrap, end to end** (`tree-prove` / `tree-verify`, deps tree
  `pq-e2e-d5` = D-4 stack + `native/recursion/patches/e2e-tree.patch`). Run: arity 2, depth 1;
  leaves = the D0a template leaf (normaliser of the chunk's `L4`) + one PAD leaf; one node; the
  wrap (`zk = 6`, final domain). Packets 328,331 / 327,407 B (chunk 1 / chunk 3), verify
  45.0–45.8 ms on one core, 18/18 fresh-process negatives.
* **One wrap setup for every chunk.** All tree proofs share one vk and one pinned height vector;
  the node program `P_node` is the same at every level and over every leaf mix; the template set
  holds the 3 D0a shape classes + PAD. The template class is a boundary field folded into
  `D_wrap`, because V_d recomputes the D0a `ctx` under per-class base parameters (found when the
  first run's setups differed by `w_stack`). Chunk 3, proved against chunk 1's setup, reproduces it
  byte for byte (`SETUP.json` 4,487,284 B; the tree vk too). The D-4 "setup reveals the shape class" caveat is gone
  for the wrap.
* **Blocker 1 done, with a defect found:** the pinned aggregation overlay had emptied the program
  binding branch (no NV child was bound). Fixed; BIND serves one child, so the others are bound
  by `root_i = root_0`.
* **Blockers 2, 3 done for the D0a template; PAD built (6); wrap Init/done/`a = 0` (7).** Status
  per blocker in the table of §5.0.1.3.
* **Review-D4 (independent review of D-4) folded in.** F1: the D-4 pinned heights depended on
  rejection sampling of the hidden L_n transcript; heights are now pinned from the shape alone
  (`shape_pinned_heights`, abort ≤ 2^-192), for the D0a FINAL and the wrap. F2: fresh chain: FINAL fit the shape pin, but the setup's program differed (inner L-level floors depended on rejection sampling); fixed with shape floors at every level. Measured: chains A and B converge to the same floors (L1 421,592 / 1,158,784; L2+ 297,140 / 1,113,972), the same 145,438-row program and the same FINAL pin (291,996 / 1,090,432), although B's base point `u` differs; **B's `SETUP.json` is byte-identical to A's** (`FRESH_CHAIN_SETUP_IDENTICAL`), and both packets (326,077 / 325,279 B) verify against A's pinned setup in fresh processes (`results/zk/shape/`).. F3 (§3.4
  bound), F4 (§6.5.1 setup independence) corrected in ZK-ARGUMENT. F5: `R` counted: 1,284–1,298
  (FINAL), so `R ≤ 2^11`. Tight floor: consumed per proof, loud on mismatch.
* **Tree-layer parameters:** `ns20lb5` (an arity-2 node's SHA work, 2.39M rows, exceeds the 2^21
  ceiling of `ns19lb6`), queries [54, 41, 31, 25], 268.2 bits per round; wrap 268.2.

**Open (D-5):**
* **Owner decision on `u` in the QROM** (unchanged): base `zk = 2` is not drop-in (measured: `w_stack` must grow from 8 to ≥ 15, so the base vk, L1 and every setup change); the salt is not built. `R` is counted, so the FINAL part is 2^-121.5
* Arity 8 (≈ 4× the arity-2 node's SHA rows: beyond one SHA AIR at the BabyBear domain) and
  depth ≥ 2 on D0a (depth 2 runs on the Fib fixture: a second level-2 node over other leaves and the level-3 node both have program root `C_node`).
* Lanes A/B templates: blockers 4, 5, 8, 9 (canonical boundary statement, fixed template
  shapes, in-circuit cached roots, M6/M5b).
* Re-prove the three D0a classes with shape floors (only chunk 1 has one, `results/zk/shape/`)
  and rebuild the tree's template set from them: this run's `C_L4` come from the D-4 chains, whose
  programs depend on their transcripts (review-D4 F2, found in D-5).
* `zero_knowledge_established` for the tree wrap (kept `false`: the FINAL argument carries over
  but has not been re-read for the wrap program).

#### D-4 status (superseded by D-5 above)

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

#### D-3 status (superseded by D-4)

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

#### 5.0.1 M9 wrap interface (lane D draft, 2026-11-03; built for the D0a template in D-5)

**D-5 update.** Items 1(a)–(d) below are built for the D0a template (`nv/tree.rs`, driver
`tree-prove` / `tree-verify`), with these differences from the draft: arity 2 and depth 1 in the
run (both setup parameters); the boundary state is the placeholder `[phase, class]`; `D_wrap` is
`SHA-384(tag 8, [WRAP_MARKER, n_ctx, ctx.., B_0.class])` (tag 8 with a leading marker, like tape-eval,
instead of a new tag); for the D0a template `ctx` is the chain's statement digest, so the packet
still carries `hint ‖ u` and V_d recomputes `ctx` from them (blocker 8); the tree layer runs
`ns20lb5`. The status of each blocker is in the table of §3 below.

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

##### 3. Blockers and open questions, in order (status after D-9)

| # | item | owner | D-5 status |
|---|---|---|---|
| 1 | **Rebase the agg overlay** (`agg.rs`, `build_agg`, `RangeStmt`, per-child BIND, `restart_transcript`) onto the current stack: `e2e-verify` + `zk-pcs` + `zk-piop` + tape-eval + D-4 | D (M8) | **done** (`patches/e2e-tree.patch`, `E2E_TREE=1`). **Defect found and fixed:** the pinned overlay had emptied the binding branch (`if b.bind \|\| b.bind_child {} else if false {…}`), so no NV child was program-bound (`patches/README-agg-patch.md`). BIND serves one child (one E-table point): now child 0 by BIND, later children by `root_i = root_0`, anchor-level children by the anchor constant or set. Two pre-existing test compile errors (`WhirLevers::zk`) fixed; `agg_tests` 6/6 non-ignored pass |
| 2 | **A chunk-independent root shape:** fixed arity, `d_min`, pinned node heights, the `P*` fixpoint across levels and siblings, the root level not exposed | D (M8) | **done for the D0a template** (`nv/tree.rs`, driver `tree-prove`/`tree-verify`). Every tree proof shares one vk and one pinned `(log, tight)` height vector; the node program is one program `P_node` from level 2 on (no fixpoint iteration: leaves and nodes have the same vk and heights); the wrap forces the root level `1 + d` and anchors at `C_node`, and exposes `[LEVEL_WRAP, D_wrap]`. Measured: two chunks of different shape classes give a **byte-identical wrap setup**. The 232,318 vs 232,702 row difference is explained by unpinned child heights: with pinned heights `C_node` is the same over different leaves (and across chunks). Arity 2, depth 1 run on D0a; depth 2 on the Fib fixture; D-6: **depth 2 on real D0a chunks** (chunks 2 and 3, one byte-identical setup; every node at levels 2 and 3 runs `C_node`); the setup is now byte-identical over all three chunks at depth 1 and its template set is reproduced by a fresh chain; D-7: **two node shapes** (`P_2` over leaves at the leaf heights, `P_*` at the node heights; the wrap anchors at `C_2` or `C_*`), a template class is a **pinned base shape shared by several chunks** (review-D6 F1: in D-6 each chunk was its own class); arity 2 depth 3 on two classes with one byte-identical setup |
| 3 | **Template heterogeneity:** per-template normaliser with `{C_t}` set binding (option A) | D (M8) | **done (option A)**: `build_norm` (child level forced to the template's anchor level M, child program root = `C_M`), `Builder::anchor_set` (one-hot witness selector, `Σ s_t (root − C_t) = 0` gated by the level flag). Template set = the normaliser of each of the 3 D0a shape classes + PAD |
| 4 | **Fixed shape per template** (pinned per-AIR log and tight heights, prover pads) | A, B, C | **D0a: done in D-7** (`BaseClass`, `statedump --class`, `set_tight_floor`; 2 classes, 7 member chunks re-cut, 4 bases proved; the generator re-cuts a table up to its classical render height only, so a production class set needs headroom chosen over the corpus); open for lanes A/B/C. For D0a each shape class is its own template (its L4 vk and heights are class constants); D-6: plan in §5.0.1.4 (pinned parameters per template, height classes, cut-on-overflow, save proof + vk, same backend); **D-8: production class set for D0a** (census of 1,311 chunks, classes S / M / L, 100 % assigned, coverage checked per chunk; any table grows past its render; TAPE pinned per class), 2 chunks per class proved against one setup |
| 5 | **Canonical boundary statement** `(claimDigest, h(B_in), h(B_out))` | A, B; E | open. The D-5 tree uses a placeholder boundary `[phase, class]` (init = 1, done = 2; `class` = the template class, set by the template leaf and folded into `D_wrap`); D-6: plan in §5.0.1.4 (`s = [phase, h(B)]`; M5a split at RCH cuts into INTAKE / STATE / FINAL leaves) |
| 6 | **Padding policy for N:** PAD template + `A^d` padding, or published depth classes | owner; then B, D | **PAD built** (`build_pad`: identity on a done boundary, no child) and used to pad to `A^d`. The policy itself remains an owner decision; the measured PAD leaf costs a full leaf proof (672 s), because it is padded to the uniform heights; D-6: costed: with uniform heights PAD leaves cost a node each (an 8-ary tree pads 64 leaves at node size); PAD at any level (one per missing subtree) + leaf heights ≠ node heights is the fix (not built); D-7: **built** (`PAD_L` at the leaf heights, `PAD_N` at the node heights with a witness level, accepted at level 2 by `P_*`'s anchor set and above as a later sibling): a tree over `n` leaves proves at most `arity − 1` PAD per level |
| 7 | **Init and FinalOut placement** | B (M5d), E | wrap asserts `a = 0`, `B_0.phase = init`, `B_N.phase = done`; FinalOut is carried by the template (the D0a leaf goes init → done itself), i.e. recommendation 1(b)(ii) |
| 8 | **In-circuit cached-root binding**, no `u` in the wrap statement | A, D | open for the D0a template: its ctx is the chain's `StatementClaim` digest, which covers `(u, TAPE*(u))`, so `u` is still in the packet and V_d recomputes ctx from (claim, hint, u). A template with a canonical `claimDigest` removes it; D-6: the wrapper's in-circuit cached-root binding prototyped on the D0a base (`build_base_leaf`: TAPE bound in-circuit by tape-eval, statement digest computed in the leaf); for lane A it is CODE/FUNC = `B.codeRoot`/`funcRoot` (§5.0.1.4); D-7: the base-template leaf is the **default** tree leaf (statement and soundness link in ZK-ARGUMENT §10.2), so the D0a tree has no chain levels |
| 9 | **M6/M5b** | A, B | open (lanes A/B) |
| 10 | **Wrap ZK obligations carried over** | D | H: the wrap heights are pinned from the shape alone (review-D4 F1 fix (b), ZK-ARGUMENT §7.1) and the setup is chunk-independent, so the D-4 "setup reveals the shape class" caveat is gone for the tree wrap. Q unchanged (owner); D-6: **ZK re-read for the wrap program, flag set** (ZK-ARGUMENT §10.1), classical ROM |
| 11 | **Soundness budget** | E, D | wrap 268.2 bits per round (`ns19lb6`, queries [46, 41, 31, 25]); tree layer 268.2 bits (`ns20lb5`, queries [54, 41, 31, 25]); `R` counted (≤ 2^11); D-6: the tree layer's 268.2 bits come from WHIR round 1; round 0 is the Johnson fallback at 271.9 (review-D5 Info); D-7: recorded per tree run (`soundness.txt`): wrap 268.2, leaf/node vks 268.2, base class A 269.6 (`n_stack` 18), class B 268.4 (`n_stack` 14); D-8: leaf vk at `ns20lb2` 268.5 (queries [81, 60, 40, 30]); class S / M bases 269.6 (`n_stack` 18, lb 7), class L 268.5 (`n_stack` 22, lb 2); D-9: same bits on the family setup; every layer at 274 measured on one chunk (`NEARPROOF_RBR_ALL`): wrap 274.0 [47, 43, 31, 25], node 274.0 [55, 43, 31, 25], leaf 275.6 [83, 62, 41, 31], base 276.3 [45, 36, 28, 24]; packet +6,130 B |
| 12 | **Lean:** `aggWrapV` `a = 0` and wrap tag; PAD-leaf soundness in `SegSound` | E | open (lane E); the D-5 wrap tag is `TAG_STATEMENT` with leading cell `WRAP_MARKER` |

##### 4. Lane A/B templates as tree leaves (D-6 plan; blockers 4, 5, 8, 9)

**M8 additions (2026-11-21, the generic leaf is built: `nv/htree.rs`).** What a template must give
lane D now:
* proof + vk saved in the stack's forms (`SavedVk` envelope with the domain factor, `Proof::encode`),
  verifiable by `nearproof-chunk-e2e m8-import` (lanes A and B: done for T1);
* **every** public value and cached commitment accounted for in its layout (the leaf refuses free
  ones); AIRs that read one public vector must hold the same values (a shorter vector = a prefix);
* **pinned tight heights** as well as log heights (lane A's T1 segments differ in CODE / SHA-512 tight
  heights: two leaf programs);
* for INIT / FINAL (lane G): `claimDigest` as public values 0..14 (three-byte limbs), as specified;
* target form of the boundary: `bdigest(BndRec)` as 14 limbs in, 14 out (lane E §3.4.1); until then
  lane D's prototype record (README §0) maps the lanes' raw fields.

**D-8 additions for lanes A/B (from lane D's measurements and review-D7).**
* **Segment WHIR parameters set the leaf cost.** Every segment proof is verified in-circuit once,
  by its leaf; the leaf's hashing is ≈ Σ(queries × Merkle depth). At a 2^22-row segment the seg-v1
  parameters (lb 1, list decoding m = 16, 24 PoW bits, no first-order certificates) need
  [536, 256, 83, 50, 36] queries (21,789 query·depth units); the stack's base configuration at the
  same rate (`profile::shaped_params_geom`: first-order certificates, m = 64, k_first 2) needs
  [97, 69, 41, 31] (5,192), both at the 268-bit target (`results/zk/d8/base-whir.txt`); the gain is
  the first-order certificates + m = 64, not the grinding: with seg-v1's 24 grinding bits the base
  configuration needs [100, 71, 43, 32] (5,366), so the segment prover's grinding stays at 2^24 per
  round. Adopting it cuts the segment leaf's in-circuit hashing ≈ 4× (projection below).
* **I3 (review-D7): a segment template must not accept a `done` input boundary.** Only the
  template leaf may expose `init` (the wrap requires `s_a = init`, `a = 0`); PAD proofs map
  `done → done`. A lane A/B segment template that accepted `B_in.phase = done` could be placed
  after the final segment and prove an arbitrary continuation; its AIR must constrain
  `B_in.phase ≠ done` (or the leaf must check it), as the D0a template leaf does by construction.
* **One leaf geometry per setup.** A setup has one leaf geometry (P_2's program embeds its
  children's heights): the largest template sets every leaf's heights. Group templates of similar
  leaf size per setup (D-8: class L's leaf is 1.6× class S's). *[D-9: resolved inside one setup.]*
  A setup now has **leaf geometry families**, each with its own `P_2^f`, all at one node
  geometry; the wrap anchors the set `{C_2^f}`. A lane A/B template joins the family of its leaf
  size: a new family adds a `P_2` program to the setup, not a new setup.
* **I5 (review-D8): seg-v1 at 32 grinding bits is below the target.** `base-whir`'s seg-v1 row
  at `PQD1_POW=32` is 266.9 bits (< 268; `results/zk/d8/base-whir.txt`). The lanes' seg-v1
  schedule is calibrated at its own 24 bits (268.2). Raising the grinding without recomputing the
  query counts loses bits. Lanes A/B: recompute the queries at whatever grinding is pinned (or
  adopt the base configuration, which is calibrated per call).

Read from the lanes' code and logs (lane D did not edit them). Paths are lane A's
`native/wasm-base` and `e2e-general/m4`, lane B's `e2e-general/m5a`.

**What the templates are today.**

| | Wasm segment (`wasmBaseSegAirMP`, lane A) | state (M5a / M5b, lane B) |
|---|---|---|
| prover | `native/wasm-base` `segprove` (`src/segcmd.rs`), BabyBear Ext12, SHA-384, the same backend family (its own copy of `stark-backend-unified`; zk additions off) | `e2e-general/m5a/prover`, own backend copy (no `max_log_trace_height`: its vks do not hash like the verifier backend's) |
| parameters | l_skip 2, **log_blowup 1**, k 4, final poly 2^7, list decoding m = 16, query PoW 24, zk 0, no tight heights; **n_stack / w_stack chosen per call** (`params_for`: 14 / 18 / 22) | same seg-v1 shape, LogUp 2^6 / 2^30; n_stack / w_stack per run; the AIR is parametrised by the working-set depth D |
| AIRs | 34 (32 JSON tables + the SHA-512 chip pair); cached CODE (17), FUNC (21) | 12 Lean tables + TAPE (cached) + HTAPE (cached, M5b) + chip pair |
| public values | 105: base boundary fields, in/out (pc, t, S, sb, cid, S_seg, segb), ctxDigest in/out (18 limbs each), memRoot in/out, tree depth, block count | 17: prev_state_root (16 × 16-bit) and wsLen |
| checked natively today | CODE / FUNC roots recomputed from the contract code (`statement_ok`) | TAPE root (write log + root-chain ends) and HTAPE root, recomputed from public data |
| segment cut | exactly the public in/out fields | none: INTAKE, the working-set segments and FINAL are one proof; RCH crosses internal cuts on a bus |
| heights | vary per segment and contract (also CODE / FUNC) | vary with D, keys, writes |
| proofs on disk | none saved (`segprove` keeps no proof / vk) | none in the verifier's backend |

**The leaf wrapper (`build_seg_leaf`, per template class `t`).** One NV program per template
class (and per height class, below), a member of the level-1 template set `{C_t}`:
1. `b.agg = true`; no anchor, no BIND (the child is not an NV proof; `build_norm`'s binding would
   fail on it). `build_verifier(vk_t, π)` with the template vk and every per-table log height as
   program constants: the leaf's program root `C_t` pins the template vk (its `pre_hash` is
   observed as a constant) and the heights.
2. Witness `B_in`, `B_out` (plan §3.2 records), hash both in-circuit (lane E's codec digest, about
   10 SHA-512 compressions); `s_in = [phase, h(B_in)]`, `s_out = [phase, h(B_out)]` (the D-5
   placeholder `class` cell goes: the template set already hides the class).
3. Wasm: equate the `B.wasm` fields with the in/out public values; equate `B_in.codeRoot`,
   `B_in.funcRoot` with the proof's cached CODE / FUNC roots in-circuit (packed lo/hi comparison,
   as the wrap compares the root digest) and carry them into `B_out`; copy every non-Wasm field;
   phase `inCall` (and `halted` → the phase transition). State: split M5a at its RCH cuts into
   INTAKE (witness the public statement `S`, check `SHA-384(S) = ctx`, `B_in.phase = init ⇒ B_in =
   Init(ctx)`), STATE (`B.stRoot`: `RCH(k) → RCH(k+1)`) and FINAL (post root and header outputs =
   FinalOut(S), recommendation 1(b)(ii)) leaves; TAPE's chain ends become public values the leaf
   maps into `B`; HTAPE goes once Wasm and state rows share a trace (or becomes a cached-root
   equality carried in `B`).
4. `ctx = claimDigest` (one value for the chunk), `a` = segment index; expose
   `H9(ctx, a, a + 1, s_in, s_out)` at level 1.

Nothing of the template reaches V_d: no boundary field, cached root, `u`, `t`, `S`, state roots,
`wsLen` or counts. V_d checks `[LEVEL_WRAP, D_wrap(ctx)]` with `ctx` from the public statement
alone, so the packet loses `hint ‖ class ‖ u` (blocker 8).

**What lanes A/B must provide (blocker 4).**
* Pin one parameter set per template (n_stack, w_stack, log_blowup) and build the proofs under the
  verifier's backend (identical vk hashing).
* A small menu of height classes per template, each its own leaf program in `{C_t}` (the
  one-hot anchor-set check hides which class a segment used): lane A cuts a segment as soon as any
  table would exceed its class cap and pads every table to the caps; CODE / FUNC caps become
  contract-size classes, and the padded height is part of the `codeRoot` definition (PREP's
  `codeRoot` must be the same commitment: l_skip, n_stack, log_blowup, padding). M5a: D-classes or
  a sparse working-set tree.
* Save proof + vk per segment.
* Lane A to confirm: HOSTT is described as cached but exported uncommitted (no constraints); the
  M3 type-mask lookup may depend on it alone.

**Cost.** The verifier cost scales with the child's queries. A segment at log_blowup 1 has
925 queries (536 / 256 / 83 / 50, `T2c0`) against the D0a base's 129: about 2.5× the D0a L1's
WHIR rows and 2.5–3.5× its SHA work, above the arity-2 tree pin. Two levers: raise the segment's
log_blowup (≤ 3 at n_stack 22, ≤ 7 at n_stack 18), or one compression level at the segment's
own geometry before the tree leaf.

**Prototype (D-6, built): the base-template leaf** (`nv/tree.rs::build_base_leaf`, driver
`NEARPROOF_TREE_TEMPLATE=base`). No Wasm segment proof exists in a usable form (none saved,
parameters per call), so the wrapper mechanics are prototyped on the one standalone non-NV
template proof with cached tables on disk: the D0a base proof. The leaf verifies the class's
base proof directly (vk and heights as program constants, no anchor), computes the template's
statement digest in-circuit exactly as an L1 level does (G1 over the public values, the
cached TAPE tables bound by tape-eval at `u`; `Builder::capture_statement`), binds 18 ctx limb
cells to it, and exposes `H9(ctx, 0, 1, [init, class], [done, class])`. Since `ctx` is the same
digest the chain carries, V_d is unchanged; and the chain L1..L4 disappears from the tree path.
Measured on chunk 1 (arity 2, depth 1, `results/zk/d6/tree-base-a2d1/`): leaf program 230,072 rows
(D0a L1: 230,754), tree pin (20, 1,048,576) / (22, 2,998,576), packet 327,449 B, verify 40.9–41.6
ms on one core, 17/17 negatives, prove 2,175 s (no chain: ≈ 25 min less per chunk).

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

**M5a-6 / M5b first STATE rows (2026-11-03) [M][K][S]:** README §"M5b", §"M5a-6".
* **AIR range checks:** `BR` version-published value-length bytes in `RNG`; `WSA` time `t` as 3
  `RNG` bytes (`WsDecode3.wsa_t_rng`: `t < 2^24` from `Holds`; the tape-time premise of
  `ws_entries` / `FinalOrder.Prem` is gone). T1/T2/synthetic/T2-seg3x5 + synthetic `bvnref`
  re-proved, roots = Lean oracle, 83/83 mutants (new `nvlbyte`, `tbig`, `twrap`).
* **M5b design** (Wasm ↔ state join, §3.3): the execution side sends `SREQ [ts, pr, seg, klen,
  kptr, vlen, vptr]` (lane A's `HOSTQ` with `pr` from the host id) and the bytes `HB [ts, pos,
  byte]` (= `HOSTB`); STATE rows `STB` (one per byte, one run per message, `DESC` descriptor) and
  `STW` (one per write) hash key and value in a second SHA-256 instance (`SB2`/`SD2`, ids
  `ID_ST + m`) and send `WRITE(seg, ts, kd, pr, |v|, vh)` to `WSA`; `t = ts` is ranged by `WSA`
  and ordered per entry by `WM`. Reads (`WM` read access, value bytes back through the same
  machinery) are design only. ≈ 145 cells per hashed byte, ≈ 36 k used cells per T1 write.
* **Implemented on T1 [M]:** writes and removes from the raw bytes (public `HTAPE` stands in for
  lane A), proves (1,526,081 B, 80 s), root = Lean oracle, 9/9 mutants (tampered key / value
  byte, dropped write, …). **Lean [K]:** `M5b.prem` — every M5a theorem applies to the M5b AIR the
  prover runs (static extra-table premises discharged); the STATE rows' own soundness (`WRITE` =
  digests of the `HB` bytes) and `committed ~ cs` are open.
* **Lean, premises from `Holds` [K]:** `SnFinal4.air_final_sorted_sn4` — batched FINAL in the
  spec's order with, newly from `Holds`: distinct version ids (`snVers`, `vers_nodup`), `BR` `hVl`/`hVP`
  (`BrVl`, using the new `RNG [nvl]`), `OslApart` (`WalkEnd`), the `SN` records `SnOldAll`/`SnNewAll`/
  `SnOldAny`/`SnNewAny` (`SnStore2.sn_oldOK`/`sn_newOK`; `SN` nodes `Hashed` from the SHA-256 contract,
  `SnRec`), `SnLimbs3`/`SnLeafMemLt`/`SnMatLeaf` (`SnRange`) — for heads with `cont = 0`; these
  premises are restated for `cont = 0` rows (as stated before they were unsatisfiable on
  continued-key rows and unused there). Left: `SnRest2` (split rows — partly done in
  `lean-wip/`, over the memory budget as written — and continued keys), `SnUpLimbs`/`SnMatLimbs`,
  `hlongS`/`hlongM`.

**M5a-7 (eighth session, 2026-11-03) [K][M]:** README §"M5a-7", log
[`docs/logs/e2e-m5a7-state-2026-11-03.md`](../logs/e2e-m5a7-state-2026-11-03.md). No AIR change.
* **M5b end to end [K]:** `M5bFinal.m5b_final` — from `Holds` of the M5b prover AIR, the chip
  contract and CR premises, the named producer premise `HostReqs` (the execution side's
  `SREQ`/`HB` sends are the request list, memory a function of `(ts, pos)`, `(seg, ts)` order) and the
  continued-key row relations: the **spec's own overlay** of the requests (`Ovl` set / remove /
  commit) applied to the pre-state reaches `post_state_root`. Built from: STATE rows sound
  (`StSound.write_sent`: every `WRITE` = `(seg, ts, sha256 key, pr, |v|, sha256 v)` of the `HB` bytes
  of its `SREQ`), `committed ~ cs` (`StSound.final_changes_m5b`), and
  `SnFinal5.air_final_sorted_sn5`.
* **Split rows and limbs [K]:** the M5a-6 `lean-wip/` split proofs compiled (the > 24 GB was
  `omega` over trace-column atoms; plain-Nat lemmas instead, every module < 1 GB); `SnUpLimbs`,
  `SnMatLimbs`, `OslNodeLimbs`, the `oEP`/`oEM` child limbs and the continued keys' memory limbs
  (`SnCont*`, `snContMem_of`) from `Holds`; continued-key full-key records
  `SnContRec4.cont_oldOK` / `cont_newOK` (the decoder's `snKey` reads past the head for `cont = 1`).
* **Tooling / cost [M]:** mutant battery no longer aborts on a tamper without a target row (`vbyte`
  on `bval`: NOT APPLICABLE); the M5b +287 kB is not the stacking width (sweep: `w` 10 → 12 +4 kB,
  `n` 22 worse) but the extra tables (`SHAS` openings +57 kB, WHIR +231 kB) — merging `SHAS` into the
  SHA-256 table is the lever, left open.
* **Open:** continued-key rows (`ckey` ↔ walk key, then `SnContRest`, `hlongS`/`hlongM`,
  `SnFreshLong`), `HostReqs` from lane A's HOST rows, reads, `SHAS` merge, completeness gaps (keys
  > ~254 bytes: `hplen < 256` — new; empty key), lane E `StViewE`.

**M5a-8 (ninth session, 2026-11-03) [K][M]:** README §"M5a-8", log
[`docs/logs/e2e-m5a8-state-2026-11-03.md`](../logs/e2e-m5a8-state-2026-11-03.md). AIR change, all
cases re-proved (roots = Lean oracle), 121 mutant runs: 119 rejected, 2 not applicable.
* **`m5b_final` without continued-key premises [K]:** premises are now `Holds`, chip contract,
  `CompressOK`, `NodeCR`/`LeafCR`/`Sha256CR`, `1 ≤ D ≤ 20`, `HostOK`/`HostReqs` (+ `n < p`, the
  32-byte roots, the pre-state facts). The continued head's full key is tied to the walk key
  (`SnContKey1..5`: head cells, `KC`-chain fields of every `SNC` chunk, chunk bytes via `Sha256CR`);
  `SnContResp` (`hlongS`/`hlongM`/`SnFreshLong`), `SnContLocA/B/X` + `SnContRestAll` (`SnContRest`),
  `SnFinal6`. `StHost.m5b_final_tape`: on the T1 tape `HostReqs` follows from checks of the public
  request list (`MemAgree`, bounds, order) — the producer premise is satisfiable, not vacuous.
* **Keys up to 2 KiB [M][K]:** `u32 |hp|` = `(hplen − 256·hph, hph, 0, 0)` (new `SN` column `hph`,
  `(1 − cont)·hph = 0`; `SnContRec2.u32_split`); synthetic `longkey` (keys of 1–2 KiB, node keys up
  to 4,088 nibbles, 571 `SNC` rows) proves, 1,266,342 B. `STW` empty-key flag `ke` (no `STB` run);
  an empty *trie* key still needs `KEY`-table support (never occurs on NEAR).
* **`SHAS` merged [M][K]:** `STB`/`STW` use the M5a SHA-256 table (`KeyDigest.XSbHi`: extra senders'
  ids `≥ ID_ST`); M5b T1 1,526,081 → **1,476,227 B**. The rest of the M5b overhead (+238 kB over M5a
  T1) is `whir` on `STB`/`HTAPE`.
* **Open:** completeness gaps (designs for "key ends at the new branch" and "squash onto an
  extension / branch sibling" — several sessions each; mismatch past the head; long extension
  under a delete; empty trie), `HostReqs` from lane A's HOST rows, reads, `STB` packing, lane E
  `StViewE`.

**M5a-9 (tenth session, 2026-11-21) [M]:** README §"M5a-9", log
[`docs/logs/e2e-m5a9-state-2026-11-21.md`](../logs/e2e-m5a9-state-2026-11-21.md). No AIR or Lean
change.
* **Corpus census [M]:** all 19,007 `d3` cases of d3c7–d3c10 (M5b AIR): **16,205 (85.3 %) trace
  and pass `check`**, none fails `check`; 15 sampled proofs verify (1.10–1.86 MB). First gaps:
  squash onto an extension sibling 5.65 %, old-leaf-ends split (`alice` → `alice.near`) 3.64 %,
  squash to a value leaf 1.86 %, `VBITS` (≥ 128 working-set keys) 1.58 %, squash onto a branch
  sibling 1.13 %, squash after a branch-value delete 0.77 %, written-key-ends split 0.12 %. Greedy
  order to 100 %: ext-sibling squash (→ 89.5 %), old-ends split (→ 92.6 %), `VBITS` (→ 94.8 %),
  branch-sibling squash (→ 97.1 %), value-leaf squash (→ 99.05 %), branch-value squash, the rest.
* **`extract_state.py` fix:** witness nodes first read during finalize (squash siblings) were
  dropped; 1,171 cases turn OK.
* **Timestamps restart per boundary [M]:** the working-set side accepts it (T2, `--segs 47`, a
  key written in two segments at `t = 1`); the M5b `HB(ts, pos, b)` needs one proof per segment or
  `seg` in `HB`.
* **Not built:** branch-end split, `STB` packing. **Open:** as README "Open after M5a-9";
  `FitsReach` → lane E's `FitsReachK` after rebasing on main `7358a938d`; lane D leaf requirements.

**B-T1 (eleventh session, 2026-11-21) [M][K]:** README §"B-T1", log
[`docs/logs/e2e-bt1-state-2026-11-21.md`](../logs/e2e-bt1-state-2026-11-21.md). Items 1–3 done,
item 4 (completeness) not started.
* **`FitsReach` in the `stOfK` form [K]** (`∀ I c, R I c → fitsB E (stOfK (κ I) c)`); lane E's
  `FitsReachK κ R = FitsReach stViewE κ R` by `rfl` (`lean/join-check/`), so `fitsReachK_engine`
  discharges it.
* **The state side as pinned-shape tree leaves [M][K].** The M5b AIR is cut at `RCH` into two
  templates (`Tmpl.lean`): **`m5tIF D`** (INTAKE + FINAL; no cached table: the `TCH` ends are
  public values) and **`m5tSeg D`** (one STATE segment; cached `HTAPE`), each with `WSX`, which
  extends the depth-`D` root to lane E's depth-24 committed root in-circuit (`TmplView.wsRoot_ext`,
  `Merkle.root_pad`, `FieldWsx.wsx_layout`). Public values = `StCommit`'s fields: `prev_state_root`,
  `wsLen`, two depth-24 roots (`R_0`/`R_n`; `R_in`/`R_out`), `post_state_root`, the change count;
  times restart per segment (`idxOf = 0`), cut evenly or on overflow (`--seg-cap`). Prover on the
  **verifier's backend** at **lane D's base configuration** (first-order certificates, m = 64,
  `domain_odd_factor` 15, grinding 24, tight heights floored to the pinned heights); proof + vk +
  statement saved in `pq-chunk-e2e`'s format, which **lane D's `fs-count` verifies**.
  Templates over the census of all 19,007 `d3` cases: **S / M / L** (D 5 / 6 / 7) cover
  **16,203 / 16,205 (99.99 %)** of the trace-OK cases. **T1 at S:** IF 490,156 B + seg 473,236 B,
  39 s / 37 s; **T2 at M:** 516,654 B + 510,652 B, 123 s / 122 s; chains and roots = Lean oracle.
  Mutants on T1: see README.
* **The M6 join, state side [M][K]:** `StHostIf.m5tSegH` — the STATE rows on lane A's `HOSTQ`
  (208) / `HOSTR` (209) / `HOSTB` (210) (`storage_write` id 58, `storage_remove` id 60) in place of
  `SREQ`/`HB`; either feeds the same working-set tables. Needs from lane A: `HOSTB`'s 4th field
  as the linear-memory address (`memAddr`), and `HOSTO` not answering storage calls. The response
  (`HOSTR` values) stays a witness (M6.4).
* **Lane E's template system (main `1461c97f6`) [S]:** the `m5tSeg` proof is the state component
  of a STATE leaf; `SegSoundState` needs the joined trace (lane F's engine rows + these rows);
  `m5b_final` is FINAL's root (lane G). README §"Lane E's T1 template system" (proposal).
* **Open:** per-template restatement of the M5b soundness theorems (`m5tIF`, `m5tSeg`,
  `m5tSegH`) and the `WSX` bus step; lane B's component of `SegSoundState`; M6.4; item 4
  (squash onto an extension sibling, old-leaf-ends split, `VBITS` 9).

**B-T1b (twelfth session, 2026-11-21) [M][K]:** README §"B-T1b", log
[`docs/logs/e2e-bt1b-state-2026-11-21.md`](../logs/e2e-bt1b-state-2026-11-21.md).
* **Per-template soundness [K]** (std axioms): the M5a stack reused on the templates through a
  re-indexed trace (`TmplSeg.reix`, `eval` by `rfl`); **`TmplSeg.m5tSeg_ws`** (the segment: every
  working set with root `a₀` becomes, after the segment's `WSL`/`WSP` update, one with root `b₀`;
  touched leaves real and agreeing; closing values = latest writes given distinct touched keys),
  **`TmplWsx.wsx_ext`** (the `WSX` bus step: public depth-24 roots = row-0 roots extended by
  `24 − D` zero levels, chip contract), **`seg_rin_rout`** (`R_in → R_out` at depth 24),
  **`TmplIf.m5tIF_roots`** (the IF's INTAKE / FINAL tree roots = public `R_0` / `R_n`). Open: the
  IF's FINAL half restated (conditional on the FINAL leaves: `ws_entries` crosses the cut),
  `wsn_roots` for `ifAir`, the composition.
* **Soundness fix [K][M]:** `m5tIF`'s `RCH` had a second matching (`WSN` closing its own INTAKE
  root with `nw = 0`, `WSX` closing itself with `sb = 0`), letting the IF publish `R_0 = R_n` = any
  root when FINAL = INTAKE; pinned `sb = 1` (`Tmpl.Wsx.sbPin`, `TmplIf.rch_if`: unique matching).
  Mutant `wsxsb` accepted by B-T1's AIR, rejected now. T1 IF re-proved at S (491,416 B); T2 at M
  and the mutant battery: README.
* **Lane G's requests [S]:** the IF has no claim decoder, so the ℓ_B span check needs a new
  `.init`-leaf framing walk over INIT's `CLM` bytes (designed, README); `.final` = this FINAL +
  M5c + lane G's `tailNew`, `post_state_root` to lane G's `FinIn` bytes 0..32 on a byte bus
  (designed). M6.4 (`HOSTR` evicted flag from `WSA` via a new `EVK` bus; `g_after` lane A's) and
  item 4: not built.
* **Lane A join (A-T1):** `StbH` accepts the value buffer's wire id 314; the 8 messages lane A's
  joined T1 segment lacks are `StwH`/`StbH`'s, placed in the WASM leaf's trace (a storage call is in
  a WASM segment); building that joined trace and `StorageJoinObl` (`hb`, M6.4 `ans` in `SpecU` form,
  `regFill`) are open. T1 mutants 24 / 24 rejected; T2 IF re-proved at M (515,982 B).

### 5.2 M5-T1 runtime (lane F): status, 2026-11-21

See `research/near-compression/e2e-general/m5t1/README.md`; log
[`docs/logs/e2e-m5t1-runtime-2026-11-21.md`](../logs/e2e-m5t1-runtime-2026-11-21.md).

* **T1's FunctionCall receipt step proves on the main stack [M]:** 1,158,991 B, 268.2-bit, prove
  5.7 s, verify 105 ms. Tables: a schema-driven Borsh engine `MSG` (parses `encodeRcpts` of the
  incoming receipts and the receiver account; emits the account write, action hash, seed, refund
  receipt id, refund receipt, logs, `partialEncode` and the outcome leaf), `DG` (digests as fields),
  `RX` (one row per receipt: `actExec`, merge, storage stake, `burn = min`, `D2.refunds`, tokens burnt,
  receiver reward, totals), the SHA-256 table. Outputs = the Lean run's (`m5t1-tool dump`: the
  checker's own `intakeK`/`estep` with the receipt step through `pwO`): outcome leaf `e63a8497…`,
  gas burnt 1,009,188,008,301, refund receipt `aa203713…` (54,888,077,387,472·10⁹ yocto), receiver
  account, totals. Mutants **8/8 rejected** (gas burnt, refund, status, receipt id, statement, account
  write, log byte, VM burnt).
* **Interfaces (§3.3):** the call request is `VMCALL (qf, ts)` with the context as the receipt
  family's `FB` fields (what lane A's context getters read); the answer `VMRES` + `FB` fields; the
  account write is lane B's `SREQ`/`HB`; the read follows lane B's §M5b read design (`SRQ`/`SRS`/`HBR`).
  On T1 a public stand-in tape plays lanes A and B (as lane B's `HTAPE`) → M6.
* **Lean [K]:** `RxField.rx_rel_of_row` (any trace: `RX` constraints + `act` + `RNG` facts ⇒ `RxRel`
  of the decoded row), `SpecLink` (`refunds_fc`, `stake_fc`, `merge_fc`, `burnt_fc`, `totals_fc`,
  `actExec_fc`, `validActs_fc`, `consts`: the spec's functions compute `RxRel`'s values), `T1.t1_rel`
  (non-vacuity); std axioms, no `sorry`; spec unchanged (checker sha `644495ff…`), `pin-check` ok.
* **Open:** `SegSoundRt` / `TmplComplete .rt` (§3.5 table) — the `MSG`/`DG` row lemmas, the `RNG`
  bus fact, composition into `CutW.applyActionReceiptW` and the RS boundary view; template coverage
  beyond T1's shape (README "Open").

**F-2 (lane F, 2026-11-21)** — README §F-2, log [`docs/logs/e2e-f2-runtime-2026-11-21.md`](../logs/e2e-f2-runtime-2026-11-21.md).
* **Finding F2-1 (for lane E / all lanes) [K]:** `TmplSound` is absolute — `Obl.tmplSound_image`:
  every input digest a template's AIR accepts must be in the image of `bndOf V.bnd` (or `Bad`), which
  no segment's rows can check. The relative form `TmplSoundFrom` (given `bndOf x = d`) suffices:
  `Obl.e2e_sound_t1_from` re-derives `e2e_sound_t1`'s conclusion from the five relative premises;
  `from_of_sound` (absolute ⇒ relative modulo collision). Recommendation: state the per-template
  premises in the relative form.
* **[K]** `Bus.rx_rel_of_holds` (the `RNG` byte-range premise discharged from `Holds (fullAir …)`);
  `MsgSpec` (every schema walk = the spec encoder: `encodeRcpts`, `Acct.encode`, `kAccount`,
  `actionHash`/seed/`receiptIdFrom` preimages, refund `Rcpt.encode`, `partialEncode`, `leaf`);
  `MsgRow.msg_walk` (rows of a message span are a walk), `sch_row`, `span_of`, `dg_digest`
  (digest = `sha256` of the message, via ZkFormal's SHA-256 table soundness), `mIdBound_of`;
  `SegRt.segSoundRt_enter_from` (enter edge, relative, under the named view contract `EnterView`).
  Open: the resume composition into `estepO (strictO (K ++ [(q, r)]))` and the resume view contract.
* **[M] The `rt` leaves as pinned-shape templates** (lane D's base configuration, pow 24; public
  values = the boundary pair as `BndRec.encode` bytes; proof + vk + statement saved): enter
  **87,001 B** (8.9 s), resume **431,245 B** (23.7 s, 9.9 GB); boundary digests = lane I's plan
  (`a2e7b254… → c667b45b…`, `6048b455… → aecc4056…`); mutants 11/11 (resume) + 4/4 (enter).
* **[M] Size:** `SCHT` preprocessed, one row per entry (3,255 → 44 columns): `relations`
  290,732 → 136,608 B. `RX` split not done (plan in README).

**F-3 (lane F, 2026-11-25)** — README §F-3, log [`docs/logs/e2e-f3-runtime-2026-11-25.md`](../logs/e2e-f3-runtime-2026-11-25.md).
* **[K] `EnterC.enter_relC`**: the rt enter leaf in the M11i form (`TmplRelC` shape; M8:
  `enter_relC8`, `enter_notInit`) **from the leaf's constraints** — every canonical opening `eng I c`
  of the input digest steps by `MRt.enter` to the canonical opening `call I c [] q' .pre` of the
  output digest (`q'` = the ghost query with the context's store, by S1 store-blindness), or a 42-B
  SHA-384 collision. Premises: view laws `RtView` (lane A: S2 `.pre` record `preRec`; lane B:
  position check; lane E: clear-field law, singleton outgoing accumulator, `wf`, `blind`) and the
  leaf's named checks `EntChecks` (lane A's remainder digest; `rPrepaid` and the code hash = the
  query's — lane F, open until enter is joined with the receipt rows; lane B's position).
  **Non-vacuity on T1's real enter leaf** (`T1Enter`): `Holds` of the exported AIR on its 1,284
  public values, SHA-256 of T1's contract in the kernel, a view meeting every law
  (`t1_enter_nonvac`, `t1_enter_opens`). **`SplitC.split_sound_relC`** (split leaves in the relative
  canonical form), `glue_of` (glue = lane F's `ReqsFaithful` + lane B's `ApplyFaithful`), `rt_relC8`
  (the `rt` kind from enter + the named `RtOthers`).
* **[M] S2 in the enter AIR** (`codeRoot = code hash ‖ 0^10`, the `.pre` record's constants) and the
  M11i record (`gasLeft`, singleton `outRcptAcc`: `engF` 450 B, `callF` 834 B): T1 enter **87,739 B**
  (2.4 s, 268.8-bit, mutants 10/10), resume **430,143 B** (17.0 s, 9.9 GB, 11/11), both imported by
  lane D's `m8-import`. Digests ≠ lane I's run4 plan (pre-M11i; the plan's enter output is the
  entry record, now PREP's).
* **Findings.** F3-1: the resume AIR carries `stRoot`/accumulators/`vmAcc`, so its relative
  obligation is unprovable until the lane B split, the accumulator appends and the `estepO`
  composition exist. F3-2: `ViewE.clearE` (counters 0) vs the resume leaf's / lane I's real
  counters — lane E / owner decision (no change of `S`, `claimDigest`, checker). Lane A's A-T3
  `fbBnd` writes S2, so `RtView.preW` is its `.pre` branch (definitional, not cross-checked in
  Lean). Lane F has no STATE engine rows.

### 5.3 M5d (FINAL and INIT templates, lane G): status, 2026-11-25 (G-4)

See `research/near-compression/e2e-general/m5d/README.md` (commands, tables, costs) and
`LEAF-TEMPLATE-SPEC.md` (for lane D); log `docs/logs/e2e-laneG-m5d-2026-11-21.md`.

**Done [M] (T1 = `d3c8/d3/02-h10196-s3`, main stack, 8 threads):**
* **FINAL template, class F1** (V5 header, no proposals / bandwidth requests / split /
  transactions, 6 shards, Reed–Solomon (5, 16)): every output `headerOk` compares is computed
  in-circuit from the post-`finK` record `FinIn` — outcome root (`merklize` of the accumulated
  leaves), outgoing receipts root (per-shard `u64 s ‖ encodeRcpts` double hash, `merklizeBorsh`),
  the chunk body, its Reed–Solomon parity (GF(2)-linear rows, the spec's `buildMatrix`) and parts
  root, `encoded_length`, `tx_root` — and compared byte by byte with the chunk header inside the
  public statement, whose SHA-384 digest is the public `claimDigest` — lane E's canonical §3.4.1
  `S` (T1: `bb5aad11…9f2f01`). New generic table `S384`: SHA-384 of byte messages (padding
  in-circuit) over the native SHA-512 chip. **992,188 B, 268.2-bit, prove 30.3 s, verify 83 ms**; every output = the Lean checker's (`m5d-tool dump`:
  lane E's `CM.step` to `fin I out`, then `finK` + `tailNew` verbatim). **Mutants 32/32 rejected**:
  one per compared header field (13), five `FinIn` fields, six data mutants (leaf, receipt byte /
  shard / drop / swap, outcome drop), six row tampers, two public values.
* **INIT template:** `claimDigest` and `ctxRoot = bdigest(0x00 ‖ u32 ℓ_B ‖ u32 |cb| ‖ cb ‖ wb)` from
  one byte stream, `claimDigest` over the canonical `S`: 790,307 B, 268.2-bit, prove 56 s, verify
  58 ms; mutants 7/7 rejected.
* **Against lane E's T1 template system (`Templates.lean`):** INIT supplies `B_0`'s digests of
  `SegSoundInit`'s `init` boundary, the intake step itself is lane B's INTAKE (one leaf INIT ∘
  INTAKE); FINAL proves the `tailNew` + `headerOk` part of `SegSoundFinal`'s `MFinal`, `finK` is lane
  B / M5c (joined in one segment, leaf spec §4 (a)).
* **Reed–Solomon cost:** the GF arithmetic is ≈ 41–44 cells per body byte (2 % of T1's trace);
  `encoded_merkle_root` costs the spec's SHA-256 over `t/d ≈ 3×` the body, ≈ 440–460 cells per
  body byte, so ≈ 500 cells / body byte in all, ≈ 0.5 G cells for a 1 MB body [E].

**Lean [K]** (`m5d/lean/FinalM5d`, std axioms, `Audit.lean`): `decode_F1` (the class layout
decodes with the spec's `decodeChunkInner`), `row_headerOk`, `rowOK_of_constraints` /
`fin_headerOk` (the exported `FIN` table's constraints over BabyBear ⇒ `headerOk`),
`tailNew_outputsOf` / **`final_template_sound`** (with `FinInOK`, `ClassF1`, `Computed`: the
checker's own `tailNew` output passes `headerOk` against the decoded public header),
`RsCoeff.coeff_linear` (kernel: the class matrix's GF(2) bit matrices are `gfMul`'s), `T1Check` (non-vacuity:
T1's row values satisfy `RowOK`, the window is T1's `chunk_inner`, `headerOk` holds).

**G-2 (lane G, 2026-11-21)** — log `docs/logs/e2e-laneG-g2-2026-11-21.md`, README §G-2.
* **[K] from `Holds` of the deployed AIR** (`finalAirS` = `finalAir` + lane B's `IF384` chip stub;
  `precheck_holds_final`: precheck-accepted traces give `Holds finalAirS` with the chip's sends):
  `hb_bytes` (`HbBytes` is no longer a premise; `final_template_sound_holds`), `rs_parity_byte_holds`
  (an `RS` row's parity bytes are the spec's `parityPart` bytes; `RsRow` now in the library, 0.8 s),
  `sha_msg` (SHA-256 message identification from lane L5's closed contract), `walkRoot_eq` (the `MRK`
  walk is nearcore `merklize`, record level), `s384_comp` / `s384_chain` (an `S384` message's rows
  fold the chip compression from IV384, under lane B's `Sha512IfContract`), `sha384_of_blocks`.
  Std axioms only.
* **[K] item 3, the leaf joins** (`Split.lean`; lane E's M11i split was not on main):
  `finK_bind` (the checker's `finK` splits at `t`, any driver), `fin_split` (honest runs factor),
  lane B's `FinalBPart` + lane G's `FinalGPart` (joined by the `FinIn` bus) ⇒ **`SegSoundFinal`**;
  `InitGPart` + lane B's `InitBPart` (joined by the `CLM` bytes) ⇒ **`SegSoundInit`**.
* **Item 2 [M]:** the prover on lane D's base configuration (lane B's B-T1 backend, grinding 24),
  pinned per-class heights (templates `F1`/`F1-M`/`F1-L`, `INIT-14..18`; SHA-256 and chip padded to
  their pins), proofs saved in lane D's format and verified by lane D's driver (`fs-count`): T1 FINAL
  **480,428 B** (was 992,188), INIT **346,723 B** (was 790,307), 268.2-bit. `B_out`: `FIN` computes
  `ctxD(.header H)` and `outD(.done o)`'s digest (public values 30..58), equal on T1 to Lean's
  `BOut` definitions (dump cross-check). **INIT now decodes section B's framing** (`BLK`: `ℓ_B` is the
  block vector's exact span) and exposes the main slot's `prev_state_root` (bus `PSR` = 22 for the
  `.init` join; `FinIn` bus `FINB` = 23 — leaf spec §5); the slot *selection* (`walkSegment`) is open.
  Mutant batteries not re-run (the shared `zkbuild.slice` was saturated by other lanes).
* **Item 4 [M], class census** (7,477 `d3` cases): F1 3.7 %, transactions 81 %, `(d, t)` ∈ {(1,3),
  (2,8), (5,16), (33,100)} on 4/5/6 shards, proposals 3.3 %, bandwidth requests 0.65 %, split 0.
  `gen_class.py` generates the FINAL AIR per `(NS, d, t)` (`Cls.f1_eq`: the generated F1 is
  `finalAir`); proved and verified on one case each of (4, 2, 8) 977,328 B, (5, 33, 100)
  1,110,996 B, (4, 1, 3) precheck OK, proof not completed (host throttling) — natural heights, seg-v1.

**G-3 (lane G, 2026-11-25)** — log `docs/logs/e2e-laneG-g3-2026-11-25.md`, README §G-3.
* **[M] T1's INIT and FINAL re-proved on the G-2 AIRs** (`SLOT` `sel`, `BLK` walk with the `ℓ_B`
  check, `PSR` 22 / `FINB` 23, `B_out` digests), lane D's base configuration, templates `F1` /
  `INIT-14`: FINAL **485,862 B**, 21.8 s, 6.86 GB; INIT **350,435 B**, 19.0 s, 6.24 GB; 268.2-bit;
  native verify + statement check, lane D `fs-count` and **`m8-import`** OK. Saved in lane D's M8
  leaf format at `/data/illia/nearproof-deps/e2e-m5d/g3/tmpl/{init,final}/` (`TMPL.proof`,
  `TMPL.vk.json`, `INFO.json`; hashes in `m5d/results/g3/SHA256SUMS`) — drop-in for the stub
  INIT / FINAL of `results/zk/m8/t1real`. INIT's `prev_state_root` public values = lane B
  STATE_IF's `WSB` limbs 0..15 on T1.
* **[M] Batteries with the prover:** FINAL 35/35 rejected (AIR precheck); INIT 10/10 (6 AIR, 4
  statement check: `pre_byte`, `blk_byte`, `wit_byte` — other chunks — and `psr_slot`, the open
  slot selection).
* **`BndRec` gap** (README §G-3 table): INIT's `B_0` needs only lane E's view constants
  (`stD .none`, `outD .none`, `vmD []`, `clear` at `init`) and the adoption of `ctxD(.raw)`; INIT's
  `B_out` (`eng I start`) and FINAL's `B_in` need lane B's parts (INTAKE / FINAL + `finK`) in a
  joint leaf (`finInDigest` is not a `BndRec` field; `outRcptAcc` list vs one chain); FINAL's
  `B_out` lacks `V.clear (done …)` (gas burnt, compute, indices) — lane E to fix `clear` at `done`
  or the joint leaf passes them through. Owner/lane E decision, not taken here.

**G-4 (lane G, 2026-11-25)** — log `docs/logs/e2e-laneG-g4-2026-11-25.md`, README §G-4, leaf spec §6.
* **Soundness fix: INIT's main-slot selection is in-circuit** (was the open `walkSegment` item;
  `psr_slot` was rejected only by the statement check). Class E1 (one epoch record; every `d3`
  claim): `INI` reads the claim's shard id and checks `#epochs = 1`; new table `LAY` finds
  `L.index shard` (first `id_to_index` match); `BLK` selects the first new slot at that index,
  exactly one. No change to `S`, `claimDigest`, the checker or INIT's public values.
* **[K]** `WalkSel.walk_single` / `main_slot_single` (the checker's `walkSegment` on a one-epoch
  table = the first block whose slot `L.index shard0` is new), `InitSel.init_blk_main_slot`,
  `init_lay_first_pair` (from `Holds initAir`: unique first selection / first matching pair). Std
  axioms. Open [S]: the bus glue between the three tables and the walks' row ↔ decode correspondence.
* **[M]** T1 INIT re-proved: **355,691 B**, 23.8 s, 6.27 GB, 268.2-bit, `fs-count` + `m8-import` OK,
  saved at `/data/illia/nearproof-deps/e2e-m5d/g4/tmpl/init/` (new vk; AIR list gains `LAY`).
  Battery **13/13**: `psr_slot`, new `psr_ix`, `sel_two`, `sel_none` rejected by the AIR.
* Out of class (≥ 2 epoch records) INIT rejects; the general walk is not built.

**Open, in order:** (1) `Computed` — the functional-sender facts per SHA-256 consumer (then
`sha_msg`), the `MRK` rows ⇒ `walkLevel` (functional `NODE` bus), `BODY`/`SEG` ⇒ `encodeRcpts`,
`S384` padding + digest bytes (then `s384_chain` + `sha384_of_blocks` give SHA-384); (2) lane B's
`FinalBPart` / `InitBPart` (INTAKE's `ℓ_B` check); INIT's general walk (≥ 2 epochs); (3) transactions (81 % of cases), then proposals,
bandwidth requests; templates per generated class; (4) lane D: `h(B_out)` assembly in the FINAL
leaf from the exposed component digests.

