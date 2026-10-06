# A formally admitted STARK for v3 D0 (`RelD0`): design

Status: **design phase, for review**, 2026-10-06. Branch `lane/v3-air`.
Statement: `spec/near-chunk-validation-v0.md` (`NearSpecV3.RelD0`, draft challenge
`challenges/drafts/near-chunk-validation-d0.draft.json`). Protocol stack reused
unchanged in its soundness core: `docs/zk-formal/DESIGN.md` (np-udr-stark, L1–L8),
`NEAR-AIR.md` (v1 tables), `STATUS-L*.md`.
PoC: `zk-formal/ZkFormal/V3/Hint.lean` (§8). It is kernel-checked and has no
`sorry`. Its axioms are ⊆ {propext, Classical.choice, Quot.sound}.

Labels used below:
* **proved**: a closed Lean theorem.
* **measured**: run on this host, pinned to CPUs 8–15.
* **estimated**: arithmetic from a stated model.
* **proposed**: a decision for the lead.

---

## 0. Decisions at a glance

| # | Question | Proposal | Main reason |
|---|---|---|---|
| D-1 | Where are the claim-only parts of `RelD0` checked? These are borsh decoding of the claim, the block-hash chain, `chunk_headers_root`, the backward walk (implicit / B2 / source blocks), ChaCha20 shuffles, binary64 congestion, the n-shard bandwidth scheduler, Reed–Solomon + `encoded_merkle_root`, the outgoing-receipts root and the forwarding limits. | **Natively, in the deployed verifier, by calling the trusted spec's own functions** (`NearSpecV3.*`). The inputs are the claim plus a small **proof-carried hint** `h` (§2.3). The STARK proves only the witness-dependent core. | (i) Lean proof cost is close to zero: a value computed by `NearSpecV3.encodedMerkleRoot` *is* the spec value, so no AIR-semantics proof is needed for RS, ChaCha20, f64 or the scheduler. (ii) It is sound in the ROM game (**proved**: `romSound_hint`, §8). (iii) It is cheap: tens of ms on typical claims (**measured**, §5.4). (iv) In-AIR RS costs `(t−d)·d·L` GF(2⁸) multiply-adds, about 61 M at the worst-case body, which does not fit 2²² rows (§2.5). |
| D-2 | Public data of variable length (source roots in applied order, own-shard boundaries, the outgoing body `B`, fixed-key value digests) | **Protocol extension: a public-message bus.** The verifier injects messages decoded from the prepared statement into the grand product. `Holds` gains the public multiset. | The DSL reads `pub i` only at static indices and has no row selectors, so variable-length public data cannot enter the AIR any other way. Hashing the public data instead would make the *semantic* soundness theorem depend on SHA-256 collision resistance, which is not allowed (§2.4). |
| D-3 | AIR scope | v1 tables **extended**: `node`, `walk`, `rcpt`; v1 tables **reused**: `acct`, `mrk`, `sort`; **L5 SHA twice** (`sha_t`, `sha_r`); **new**: `srcp`, `akey`, `bnd`, `uniq`, `size`. **No ChaCha20, RS, f64, scheduler, borsh-decoder or header-chain tables.** | §3. W_eq ≈ 3,080 at `g = 1` and ≈ 2,580 at `g = 3`. |
| D-4 | Finding: the store is hash-indexed | The AIR must prove that revealed store entries are **hash-functional**: distinct digests, with identical subtrees shared as a DAG. This is a new obligation (`uniq`, §3.3). | `RelD0` rebuilds tries from `base_state` *by hash lookup* (`TrieBuild`). If the extracted tree contained two different preimages of one digest, the relation would see a different trie, and soundness would fail. v1 did not have this issue, because its witness was a structured trie. |
| D-5 | D0 capacity | **Amendments A1 and A2 are required.** A1 caps `gas_limit` at 10¹⁵, so at most 4481 receipts are applied (**proved**, `max_receipts`). A2 requires every receipt of a used source proof to route to the target shard. **A3 and A4** are needed only to keep the formal proof-size bound under 8 MiB. **A5** is a performance import. (§4) | Without A1, `n` is bounded only by the 8 MiB witness size (≈ 65 k receipts, ≈ 20 M `rcpt` rows). Without A2, receipts that are hashed but filtered out (≤ 5 MB) overflow `rcpt` and `sha`. |
| D-6 | Parameters | Keep rate 1/16, 216 queries (24 × 9, `queryLog ≥ 8`), arity 8 and final degree < 2. **Adopt `auxGroup = 3`** (L3 `NpOk` generalized from `Params.default` to `{default with auxGroup := g}`), and **tighten L7's FRI size bound** to the deployed schedule. | §5.3. Typical proof ≈ 2.4–2.8 MB, worst (A1-max) ≈ 4.3 MB. Formal bound ≈ 5.2 MB plus hints ≤ 1.05 MB, under 8 MiB. Recursion is rejected: it cannot be proved in the ROM game (§5.5). |
| D-7 | PoC | `romSound_hint`, the ROM transfer through hints and native preprocessing, and `stream_eq_of_count`, the binding of the public body to the AIR stream. **Proved** (§8). | These are the two new protocol-level pieces that the whole "native" architecture rests on. The RS and ChaCha20 AIR soundness PoCs are moot because neither is in the AIR. |

Effort (§7): **≈ 50–80 k Lean LOC plus 9–13 k Rust, ≈ 40–60 agent-days, 5–7 weeks
wall-clock on 6–8 lanes.**

Top risks:
1. **Elaboration budget.** v1's candidate already takes 647 s of the 1,800 s budget.
2. Volume of the node/rcpt view re-proofs.
3. Approval of amendments A1/A2 (spec governance).

---

## 1. What `RelD0` checks, and where each check is proved

`checkD0` (`spec/lean/v3/NearSpecV3/ChunkValidationV0.lean`) splits three ways:

* **C**: a function of the claim alone.
* **H**: a function of the claim plus a small hint that is bound to the witness by the AIR.
* **W**: a statement about witness content (tries, receipts, Merkle paths).

C and H are **executed** by the verifier (§2). Only W is arithmetized.

| `checkD0` step (spec §3) | class | how it is established |
|---|---|---|
| claim decode, `wf`, PV 86, single epoch, layout V2/V3 ≤ 64 shards, RS params, `n_blocks ≤ 32`, `tx_valid = []`, `epoch_start_after`, `apply_facts` | C | native: `decodeClaimE`, `decodeLayout`, `rsGenesisParamsOk`, … |
| `decodeBlk`: block hash `sha256(sha256(sha256 lite ‖ sha256 rest) ‖ prev)`, `chunk_headers_root` Merkle over `ChunkHashHeight` leaves, chain linking, slot counts, `height_included ≤ height` | C | native (≈ 20 k SHA-256 compressions at 32 blocks × 64 shards, about 22 ms with `sha256Fast`) |
| walk: implicit blocks, B2, source blocks, stop block, `n_blocks` exactness, `not_genesis` | C | native |
| source chunks: keys `chunk_hash`, `from_shard`, roots `prev_outgoing_receipts_root`; distinct used keys (`distinctKeys = used`) | C | native. The constructed witness holds exactly one entry per used key. |
| `shuffle_receipt_proofs` (ChaCha20 + Lemire + Fisher–Yates, seed `S.prev_hash`, length = #new chunks of `S`) | C | native → **applied order** of the source lists, passed as public data |
| filter by layout (`shardOf receiver = own`) | W | `rcpt` routing check against the own shard's two boundary strings (A2: every receipt must route to `own`) |
| `verifyReceiptProof`: `rootFromPath(sha256(sha256(u64 to ‖ borsh list)), path) = root` | W | `rcpt` emits the list as `RC(j)` and `srcp` hashes the leaf and the path to the public `root_j` |
| `applied_receipts_hash = sha256(borsh R)` | — | **free**: a witness field. The constructed witness sets it to `sha256(encodeReceipts R)`, so the AIR hashes nothing for it |
| `tx_root` of B2's slot, own congestion zero, `H.tx_root`, proposals, bandwidth requests, `proposed_split`, `H.gas_limit`, `H.congestion_info` with `allowed_shard` | C | native |
| `e.distinct_ids` | W | v1 `sort` |
| `w.size` (≤ 8 MiB total, base_state ≤ 3,000,000) | W | v1 node `SUM` plus the new `size` table (byte count of the *constructed* witness) |
| main trie: `partialTrie` by hash, `hashOf = prev_state_root` (B2 slot) | W | `node`/`walk` (instance τ = 0, root from public data), `uniq` |
| `readKey` `[7]`, `[13]`, `[16]‖u64 s`, `[10]` (queues empty; values parsed) | H | hint values `v_k` (or absent). Native: `queueEmpty`, `bufferedShards`. AIR: a walk to the public key ends at *absent* or at a value whose `(len, digest)` is the public one |
| `schedStep`: read `0x0f`, `Scheduler.run`, upsert | H | hint `s₀`. Native: `run` → new state `out₀` and grants. AIR: read `0x0f` = `s₀`, write `out₀` (public digests) |
| per receipt: `applyReceipt` (v1) or `applySystemReceipt` | W | `rcpt`, `walk`, `acct`, `akey` (system gas refunds: access key absent or `FullAccess`) |
| `e.compute` (`(n−1)·G < gas_limit`), `H.prev_gas_used = n·G` | H | hint `n` (number of applied receipts), native; the AIR fixes `n` through `mrk`/`rcpt` |
| forwarding (`tryForward` per refund: shard, size, congestion gas vs limits from `outGas` and grants) | H | native over the hint body `B` (refunds decoded from `B` with the spec's `pReceipt`) |
| outcome root (`H.prev_outcome_root`) | W | v1 `rcpt` PEO/LEAF + `mrk` (`n` public) |
| tokens burnt (`H.prev_balance_burnt`) | W | v1 `rcpt` running `tok`; system receipts burn 0 |
| post state root after main + implicit transitions = `H.prev_state_root` | W | `node` instances τ = 0..K chained by the `ROOT` bus; the last instance's root goes to the public bus |
| implicit transitions: read `[7]` (determinacy), scheduler step on `0x0f` | H/W | per τ: hint (or "same as `out_{τ−1}`", A3), native `run`; AIR walks and upserts in instance τ |
| `H.prev_outgoing_receipts_root = merklize(per-shard sha256(u64 s ‖ borsh refunds_s))` | H | native over `B` |
| `encoded_merkle_root`, `encoded_length` (RS over `u32 0 ‖ borsh(outgoing)`) | H | native over `B`: `NearSpecV3.encodedMerkleRoot d t B` |
| `w.no_txs`, `w.no_code`, `w.proof_shape`, `r.shape`, `r.success`, `r.refunds` | W | by construction of the extracted witness (`rcpt` emits only D0-shaped encodings) plus v1 arithmetic and `akey` |

`B` is bound to the witness exactly. The AIR's refund stream (v1 `RF` bytes, preceded by
`u32 0`) sends `(pos, byte)` on a public bus that the verifier balances with `(pos, B[pos])`.
`stream_eq_of_count` (**proved**) gives `|stream| = |B|` and stream = `B`.

---

## 2. Architecture

### 2.1 Verifier pipeline (the deployed `Model.verifier`)

```
verify(pub, cb, pb):
  guard:  claimOk cb                                   -- R-L7-2 canonical claim (as v1)
  split:  pb = hintBytes ‖ π                           -- u32 length-prefixed hint
  prep:   p ← prepD0 cb (decodeHint hintBytes)         -- native, NearSpecV3 functions; reject on error
  stark:  Stark.verifier Fp Fp8 nearAirV3 prmV3 on (cb' := Prep.encode p, π)
```

`prepD0` does three things:
* it runs every C/H check of §1;
* it computes the D0 out-of-domain conditions that are decidable from `(c, h)`;
* it emits the **prepared statement** `cb'`.

`cb'` has two parts:
* a fixed header read at static `pub` indices: τ count `K+1`, `n`, `own` index, gas price, height, `prev_state_root` of B2, `H.prev_state_root`, `H.prev_outcome_root`, `H.prev_balance_burnt`, segment counts and offsets;
* **public-bus segments**:
  * applied-order source lists `(j, root_j)`;
  * own boundaries `(lo/hi, i, byte)`;
  * `B` as `(pos, byte)`;
  * fixed-key walks (`KEYNIB` nibbles, expected terminals);
  * value digests `(Id, len, sha256 v)` of hint values and of every scheduler state written;
  * `ROOT` endpoints `(0, prev_state_root)` and `(K+1, H.prev_state_root)`.

The STARK's statement is `cb'`. Its transcript absorbs `cb'`, and `cb'` is a function of `(cb, h)`.

### 2.2 Why this is sound and complete

* **ROM soundness** (`FORMAL_CRYPTO_SOUNDNESS`). `romSound_hint` (**proved**, §8)
  transfers L2's `stark_romSound_full` for the inner verifier and the language
  `AirLang nearAirV3` over prepared statements to the composed verifier. Budgets and bounds
  are unchanged. Its only premise is the deterministic implication
  `prepD0 cb h = some cb' → AirLang nearAirV3 cb' → L cb`, which is semantic soundness (§6).
* **Semantic soundness.** `prepD0 cb h = ok p → Holds nearAirV3 (pubOf p) tr → ∃ w, RelD0 cb w`.
  It has three parts:
  * extraction: AIR → relational spec `GoodV3 p e` (§6.2);
  * `FactorSound`: `prepD0 = ok p ∧ GoodV3 p e → RelD0 cb (witnessOfV3 cb h e)`;
  * a witness **encoder** `witnessOfV3` with a decode∘encode lemma. No AIR decoder is needed: the witness is *re-encoded* from the extracted records, as v1 does with `witnessOf`.
* **Completeness.** `RelD0 cb w → prepD0 cb (hintOf cb w) = ok (prepOf cb w) ∧ Holds … (renderV3 …)`.
  The hint is read off the relation's own execution: the `0x0f` value read, the queue values, `n` and `out.outgoing`.
  * Collision witnesses: if an implicit transition reads a `0x0f` value `v'` that differs from the previously written `out_τ` but has the same SHA-256, then completeness needs an explicit hint for `v'`. A3 removes this case from D0 (§4); otherwise the hint format allows explicit values and the size bound must count them.
* **Impl connection.** The model is the Lean definition above (`rfl`).
  * The verifier may import `NearSpecV3`: it is part of the challenge's trusted tree, exactly as v1's model imports `NearSpec`.
  * The scratch spec for v1 already pins `allowed_packages = [ArenaCore, NearSpec]`. v3 adds `NearSpecV3`.

### 2.3 The hint

| field | content | typical | worst (formal) |
|---|---|---|---|
| `n` | number of applied receipts | 4 B | 4 B |
| `B` | `u32 0 ‖ u32 nref ‖ Σ borsh(refund)` = spec step 18's body | 8 B – 2 KB | ≤ 0.91 MB (A1: 4481 refunds × ≤ 204 B) |
| `s₀` | `0x0f` value of the main pre-state, or absent | 901 B (6 shards) | 98,341 B (64 shards, A4) / ≤ 3 MB (no A4) |
| `v_{[7]}, v_{[10]}, v_{[13]}, v_{[16]‖s}` | queue values or absent | ≤ 100 B | A4: total fixed-key values ≤ 128 KiB |
| `v_τ` (implicit τ ≥ 1) | `same` (1 B) or explicit | 1 B each | A3: always `same`; no A3: ≤ 8 MiB total |

The hint is public (np-udr-stark is validity-only, `FORMAL_ZK` not applicable).
Every hint value is bound to the witness by the AIR:
* `B` exactly, through the public bus;
* `s₀` and the queue values through their digests, as touched values of the trie;
* `n` through `mrk`/`rcpt`.

So a wrong hint cannot be accepted.

### 2.4 Protocol extension: the public-message bus (L4/L3/L7/L8)

```lean
-- L4 (Air/Basic.lean): additive; v1 AIRs keep `pubSegs := []`
structure PubSeg where
  bus : Nat; send : Bool; width : Nat
  countAt : Nat   -- static pub index holding the record count
  start : Nat     -- pub offset of the first record (records are consecutive, `width` each)
structure Air where
  tables : List Table; numBuses : Nat; numPub : Nat
  pubSegs : List PubSeg := []
def pubCount (A : Air) (pub : List F) (b : Nat) (send : Bool) (m : List F) : Nat
structure HoldsP (A : Air) (pub : List F) (tr : Trace F) : Prop where
  …same fields as Holds…
  balance : ∀ b m, busCount A tr pub b true m + pubCount A pub b true m =
                   busCount A tr pub b false m + pubCount A pub b false m
theorem holdsP_iff_holds (A : Air) (h : A.pubSegs = []) : HoldsP A pub tr ↔ Holds A pub tr
```

* **L3.** `gpAlpha`/`gpGamma` already work on arbitrary multisets `a`, `b`. The `Np` instance (`BusRounds`, `Msg4`, `Global8`) appends `pubMsgs` to `busMsgs`. The fingerprint bound `fpBound` and the multiplicity bound `multBound` gain `|pubMsgs|·(w+1)` and `|pubMsgs|`. These are ≤ 2²¹ for `|cb'| ≤ 2 MB` and fit in `busBudget = 2^36`.
* **Verifier.** The final check becomes `Π_send · Π_pub,send = Π_recv · Π_pub,recv`. That costs one fingerprint and one `K` multiplication per public message. At 0.9 M messages (worst `B`) this is estimated at 0.3–0.5 s, and in typical cases it is < 5 ms.
* **L7 / L8.** The honest prover's final products include the public product (Rust plus the Lean prover model).
* v1 stays byte-identical: `pubSegs = []`, and `holdsP_iff_holds` adapts L5/L6 to `HoldsP`.

Alternatives considered:
* Static `pub i` reads need one constraint per public value and per-row selectors, which the DSL does not have.
* A digest of the public data, opened in-AIR through the SHA bus, would make `Holds ⇒ Rel` depend on collision resistance. That is semantically unsound: the extracted statement would be *some* preimage of the digest.

### 2.5 Reed–Solomon, ChaCha20, binary64, scheduler: why not in the AIR

* **RS (`encoded_merkle_root`).** The parity is `parity_i[b] = ⊕_j M[d+i][j]·data_j[b]` over GF(2⁸), with `M = V·V_top⁻¹`.
  * **Cost.** Mainnet is (d, t) = (33, 100), and `L = ⌈|B|/33⌉`. That is `(t−d)·d·L ≈ 67·|B|` GF multiply-adds: ≈ 61 M at `|B| = 0.91 MB`, and ≈ 154 M at (85, 256).
  * **Lookup per product.** One lookup per product means ≈ 61 M rows. That is > 2²² even at 1 row each.
  * **Column-wise layout.** Each parity bit is `Σ (Â x) mod 2`, so the layout needs `8(t−d)` parity bits and quotient columns per position: 536 parity bits plus ≈ 4.3 k quotient bits at (33, 100). That is far beyond `W_eq ≤ 3000`.
  * **Freivalds or random evaluation.** BabyBear has characteristic `p ≠ 2`, so a random F_p combination does not respect GF(2⁸)-linearity. The parity can be lifted to integers (`Âx − π − 2q = 0` holds exactly in F_p because every entry is < p). That makes it F_p-linear, but `q` still needs the same width. A Freivalds check would also need **a new challenge round with challenge-dependent constraints**. L3's schedule has no such round: every challenge is a bus or ALI/FRI challenge. Adding one means a new `RbrWith` stage (`bad_query_bound` instance, error ≤ L/|K|) and re-threading `Shape`/`Early`/`Msg4`: about 3–5 k LOC of L3 changes, for a check that still costs ≈ 3·|B| GF(2^{8k}) scalar products in-AIR.
  * **Decision.** RS runs natively on the hint `B`.
    * **Measured** with the spec's own List code: 0.25 s for `buildMatrix 33 100`, and 2.5 s for encode+merkle at |B| = 900 KB. Of that 2.5 s, ≈ 1.7 s is the slow `ArenaCore.sha256` path, because `NearSpecV3` does not import `SHA256Fast` (A5).
    * At (85, 256): 2.5 s for the matrix and 3.6 s for encode+merkle.
    * A csimp fast path (Array Gauss–Jordan plus ByteArray `mulSliceXor`, proved equal) brings the worst case to an estimated ≲ 0.3 s.
* **ChaCha20.**
  * In the shuffle, the seed (`S.prev_hash`) and the length (#new chunks of `S`) are claim-only, so the permutation is native.
  * In the scheduler, the RNG is used inside `Scheduler.run`, whose only witness input is the `0x0f` value (hint `s₀`), so it is native too.
  * **No ChaCha20 table is needed.** An in-AIR ChaCha20 (word adds, xors and rotates in an OpenVM-like layout, ≈ 20 rows/block) would cost about 3–5 k LOC. It is not needed for D0.
* **binary64 congestion.**
  * `level`, `is_fully_congested` and `mix` read only the slots' congestion infos (claim) and the missed counts (claim), so they are native with the exact `F64` model.
  * The integer characterization (tested, not proved) is then **not needed at all**: the verifier runs `F64` itself.
* **Scheduler.**
  * **Measured** native `Scheduler.run`: 1 ms at 6 shards; 134–217 ms at 64 shards with every link requesting a full bitmap.
  * The worst case of 32 runs is ≈ 4–7 s with the List spec code. It needs a csimp fast path, estimated at < 0.5 s for 32 runs.
  * Arithmetizing the scheduler (BTreeMap buckets with `pop_last`, per-bucket Fisher–Yates, stable sorts) would cost an estimated 20–40 k LOC.

---

## 3. AIR `nearAirV3`

### 3.1 Tables

| table | origin | width | interactions | `W_eq` (g=1) | `maxLog` | rows (worst, A1+A2) |
|---|---|---:|---:|---:|---:|---|
| `sha_t` (trie: nodes, account/access-key values) | **L5, unchanged** | 544 | 17 | 704 | 22 | 3.75 M (3 MB of nodes, pre+post) + 0.39 M values ≈ 4.14 M |
| `sha_r` (receipt lists, paths, outcomes, mrk, implicit tries) | **L5, unchanged** (2nd instance) | 544 | 17 | 704 | 21 | 0.39 + 0.29 + 0.47 + 0.16 + 0.03 ≈ 1.34 M |
| `node` | v1, **extended** | ≈ 185 | 17 | ≈ 345 | 22 | 3 M + 1 |
| `walk` | v1, **extended** | ≈ 24 | 7 | ≈ 104 | 21 | 4481 × (133 + 265 access-key steps) ≈ 1.8 M |
| `rcpt` | v1, **extended** | ≈ 290 | 21 | ≈ 482 | 22 | 4481 × ≤ 474 ≈ 2.1 M |
| `acct` | v1, reused (`maxLog` only) | 16 | 13 | 144 | 17 | 16 × 4481 |
| `mrk` | v1, reused (`maxLog`, `n ≤ 4481`) | 58 | 5 | 122 | 19 | 1 + 64·4480 + 13 |
| `sort` (receipt ids) | v1, reused | 49 | 1 | 81 | 18 | 32 × 4481 |
| `uniq` (store digests) | v1 `sort`, 2nd instance | 49 | 1 | 81 | 21 | 32 × ≈ 58 k entries |
| `srcp` (source-proof leaf + path) | new (mrk-like) | ≈ 60 | 5 | ≈ 124 | 17 | ≤ 1984 lists × (2 + depth ≤ 6) × 64 |
| `akey` (access-key values) | new (acct-like) | ≈ 20 | 4 | ≈ 76 | 13 | 9 rows × system gas refunds |
| `bnd` (own-shard boundaries, chained provider) | new | ≈ 8 | 3 | ≈ 48 | 8 | ≤ 2 × 65 |
| `size` (witness byte count) | new | ≈ 30 | 1 | ≈ 62 | 4 | ≤ 16 |
| **total** | | ≈ 1,877 | 112 | **≈ 3,080** | | |

At `g = 3` (D-6) the aux columns drop from 112 to ≈ 46, giving **`W_eq ≈ 2,580`**. All tables have
degree ≤ 4, so with `g ≤ 3` the quotient chunks stay at 3 per table.

**Why two SHA tables.** The SHA demand at A1+A2 worst case is ≈ 5.5 M rows, above 2²².
The alternatives are:
* rate 1/8, which allows `maxLog 23` within LDE 2²⁶ but needs new L7 numerics, the L3 degree check (≤ 8) and +10 % queries;
* a tighter `base_state` amendment.

Two instances keep L5 untouched. The link proof quantifies over a list of SHA
tables (`ShaFacts` per instance; an `Id` is hashed by at most one instance because the
NEAR side sends each `(Id, pos)` once). The cost is +704 `W_eq` (≈ +0.6 MB of proof).

### 3.2 Trie: `node` and `walk` extensions (instances, DAG, reads, upsert)

1. **Instances τ = 0..K** (main transition τ = 0, then implicit transitions oldest first).
   * The node record and the walk carry `τ`.
   * Root rows have `rootf = 1`. A root receives `DIGEST (NPRE(root), len, d)` and `ROOT (τ, d)`, and sends `ROOT (τ+1, d')` from `NPOST`.
   * The public bus closes the chain: it sends `ROOT (0, B2.prev_state_root)` and receives `ROOT (K+1, H.prev_state_root)`.
   * This replaces v1's `nid = 0` root rule.
2. **DAG and acyclicity.**
   * `PARENT` becomes a chained provider: a node provides `(N, len)` with use count `u`. This allows hash-consed identical subtrees (D-4).
   * Acyclicity is by **id order** (`cid > N`) instead of v1's `depth`.
3. **Variable-length touched values.**
   * The window receives `DIGEST (V*(k), vlen, d)`, where `vlen` is a column tied to the leaf's `u32` length bytes. v1 had the constant 72.
   * `V*` is `VPRE`/`VPOST` for accounts (SHA-provided), `VAK` for access keys (SHA-provided), and `VPUB` for hint values and scheduler states (public-bus-provided digest; no in-AIR hashing).
4. **Non-membership.** `walk` gets terminal kinds:
   * `ABS_BR`: a branch whose bitmap bit for `sym` is 0. `node` provides `BMAP (N, bm)` (chained).
   * `ABS_KEY`: a leaf or extension key nibble `≠ sym`, or one key ended before the other. `node` key rows provide `KEYAT (N, i, nib)` (chained); the walk checks `nib ≠ sym` by an inverse.
   * `ABS_VAL`: a branch value slot that is empty at `END`.
   * The walk sends `FINAL (r, kind, k)`. `rcpt` (access-key walks) or the public bus (fixed keys) receives it.
5. **Public-key walks.** For `[7]`, `[10]`, `[13]`, `[15]`, `[16]‖u64 s` (τ = 0) and `[7]`, `[15]` (τ ≥ 1):
   * `KEYNIB` and the expected `FINAL` come from the public bus;
   * the value digests come from the public bus (`VPUB`).

   No new table is needed.
6. **`0x0f` upsert.**
   * Present: same as a set. The leaf serialization has fixed length (`u32 len ‖ hash`), and pre/post digests are public.
   * Absent: insertion along a 2-nibble key (`[0, 15]`) changes at most 3 nodes and creates at most 3.
     * With **A4**, this case is out of domain.
     * Without A4, a bounded-case `ins` mode of `node` is needed (≈ 3–5 k extra LOC, mirroring `NearSpec.PTrie.upsert`).
7. **Write order.** The relation upserts `0x0f` before the receipts and reads `[10]` after them. The AIR applies all writes to one pre/post node set. This needs:
   * the `PTrie` lemmas `find_set_ne` and `find_upsert_ne` (a read of key k is unaffected by writes to k' ≠ k);
   * `set_upsert_comm` for distinct keys.

### 3.3 `uniq`: hash-functional stores (new obligation)

`TrieBuild.buildFor` looks every node and value up **by its SHA-256** in the witness store
(first match). The extracted witness's store is the list of revealed entries. If two
entries with different bytes had the same digest, the relation's trie would differ from the AIR's,
and `Holds ⇒ RelD0` would fail. The AIR therefore proves, per store τ, that **all revealed
entry digests are distinct**. Identical subtrees are shared (DAG, §3.2), so distinctness
costs nothing in completeness: an honest witness's relation-built trie maps each digest to one
value.

Mechanism: every digest consumer (node root/child windows, touched values, public `VPUB`)
also sends `(τ, digest)` bytes on a `DIGS` bus, LSB-first like v1 `RIDS`. `uniq` is a second
instance of v1's `sort` table (strictly increasing ⇒ distinct). Its proof is reused, parametric in the bus.

Rows: ≈ 32 × (#nodes + #values) ≤ 32 × 58 k ≈ 1.9 M at 3 MB of 56-byte nodes.

### 3.4 `rcpt` extensions

* **Source lists.**
  * One `RC(j)` message per applied list `j`: `u64 to ‖ u32 n_j ‖ Σ borsh(receipt)`. This is exactly v1's `RC` format, with `to` = own shard taken from the public header.
  * Its digest is consumed by `srcp`, not compared to a claim field.
  * List boundaries are rows of a new `LH` state.
* **Routing (A2).**
  * During the `V` (receiver) rows, the receiver is compared lexicographically with the own shard's `lo` and `hi` boundaries (`lexLe lo recv ∧ ¬ lexLe hi recv`; a missing side is unconstrained).
  * Boundary bytes come from `bnd` by chained lookups `(side, i, byte, u)`.
  * The comparison is a 3-state machine (equal so far / decided less / decided greater) with end-of-string handling.
* **System receipts.**
  * `sys = [predecessor = "system"]`, by a running accumulator over the 6 bytes and the length.
  * If `sys`: no burn, no refund, `tokens_burnt = 0` in PEO, `gas_burnt = G`.
  * Gas-refund case (`signer = receiver`): the prover's flag `e` is checked.
    * Equality: the `S` rows look up `(r, i, byte)` provided by the `V` rows through a chained bus, plus equal lengths.
    * Inequality: different lengths, or one looked-up position whose bytes differ (inverse).
  * If `sys ∧ e`: an access-key walk `[2] ‖ receiver ‖ [2] ‖ pk` is emitted on `KEYNIB` (walk index `r + N_R`). Its `FINAL` is absent, or a touched value `VAK(k)` from `akey` whose 9 bytes end in `1` (FullAccess).
* **Body.**
  * Refund bytes are sent as `(pos, byte)` on `BODY` (offset 4; positions 0–3 are the constant `u32 0`).
  * This replaces v1's `DIGEST (RF, len_RF, pub rfc)`. The public bus receives `(pos, B[pos])`.
* **Claim rows.** v1's `CLAIM` rows (claim-level checks and the `rc`/`rfc` digests) are replaced by reads of the prepared header (`n`, gas price, height, `H.prev_balance_burnt`). The running `tok` is compared with the public value.
* `maxLog 22`.

### 3.5 `srcp`

For each applied list `j`:
* hash the `RC(j)` digest again (`LF(j)` = 32 bytes, from a register loaded by the `DIGEST` lookup);
* then hash one 64-byte message per path item (`dir = 0`: `sibling ‖ acc`; `dir = 1`: `acc ‖ sibling`; sibling bytes free);
* the final digest must equal `root_j`, received from the public bus as `(j, root)`.

Path length is unconstrained, as in `rootFromPath`. The layout is v1 `mrk`'s 64-row segment, with
`MPOS`-like chaining replaced by a `PATH (j, step)` counter.

### 3.6 Small tables

* **`akey`**: 9 rows per touched access key. It emits `VAK(k)` bytes (8 free nonce bytes, then `1`) to `sha_t`, and sends `VSLOT`. It is a degenerate `acct`.
* **`bnd`**: receives `(side, i, byte)` from the public bus once and provides chained lookups.
* **`size`**: receives per-table byte totals on `SIZE` and checks with bits that `Σ ≤ 8,388,608 − overhead(public)` and node `SUM ≤ 3,000,000`. The overhead (header, list headers, path counts) is computed natively from `cb'`.

### 3.7 Buses (v1's 10 plus new)

| # | bus | message | producers → consumers |
|---|---|---|---|
| 0–9 | v1 `BYTES … MPOS` | as `NEAR-AIR.md` §2 | +`τ` in `PARENT`/`EDGE`/`FINAL`; `PARENT` becomes chained |
| 10 | `ROOT` | `(τ, d[32])` | node roots ↔ node roots; public endpoints |
| 11 | `BMAP` | `(N, bm[16])` | node (chained) → walk |
| 12 | `KEYAT` | `(N, i, nib)` | node key rows (chained) → walk |
| 13 | `BODY` | `(pos, byte)` | rcpt → public |
| 14 | `SRC` | `(j, root[32])` | public → srcp |
| 15 | `BND` | `(side, i, byte, u)` | bnd (chained) ↔ rcpt |
| 16 | `SREC` | `(r, i, byte, u)` | rcpt `V` rows (chained) → rcpt `S` rows |
| 17 | `DIGS` | `(τ, i, byte)` | every digest consumer → `uniq` |
| 18 | `SIZE` | `(table, total)` | tables → `size` |

Public-bus segments: `SRC`, `BND`, `BODY`, `KEYNIB`, `FINAL`, `DIGEST (VPUB…)`, `ROOT`.

---

## 4. D0 amendments (proposed; the draft is unsigned, so `NearSpecV3` may change)

| id | condition (added to `InD0`) | needed for | real-chain impact | test obligation |
|---|---|---|---|---|
| **A1** `c.gas_limit` | B2 slot `gas_limit ≤ 10¹⁵` (mainnet genesis value; verify that nearcore 2.13.4 never changes chunk gas limits) | heights: `n ≤ 4481` (**proved** `max_receipts`). Without it, `n` ≲ 65 k and `rcpt` would need ≈ 20 M rows | none on mainnet (constant 1000 Tgas) | oracle classifier and difftest: a chain with gas limit 10 Tgas stays in D0; a mutated claim with a limit > 10¹⁵ is out of D0 |
| **A2** `w.proof_routing` | every receipt of every used source proof routes (final layout) to the target shard | heights: no filtered-but-hashed receipts (≤ 5 MB otherwise) | none on single-epoch honest chains (proofs are built per target shard under the same layout) | witness mutant with a foreign receipt in a valid-path proof: out of D0 (nearcore accepts it, so a positive Rel case outside D0) |
| A3 `e.sched_chain` | in every implicit transition, the `0x0f` value read equals the value written by the previous transition | proof-size bound under 8 MiB (hints compact) | none (holds under SHA-256 CR for every accepting witness: spec §6 "determined under CR") | positive cases unchanged; a constructed collision is impossible to test, so it is stated |
| A4 `e.fixed_values` | `0x0f` present in the main pre-state; total size of values read at fixed keys ≤ 128 KiB | removes trie insertion (§3.2.6); bounds `s₀` and the queue values | excludes only the first apply after genesis, upgrade or resharding of a shard | case with absent `0x0f`: out of D0 |
| A5 (perf) | `NearSpecV3` modules import `ArenaCore.SHA256Fast` | native SHA in the verifier at 1.1 µs/block instead of 41 µs | none (`@[csimp]`, semantics unchanged) | rebuild; the difftest is unchanged |

**Fallbacks.**
* Without **A3/A4**, set the challenge's formal `max_proof_bytes` to the draft's 64 MiB (the formal bound then covers hints of up to ≈ 8 MiB). Proofs for honest chains are unchanged.
* Without **A1/A2**, there is no single-STARK design within 2²² rows. The options would be multi-instance `rcpt`, or rate 1/8 with `maxLog 23` plus a third SHA instance.

---

## 5. Budgets and parameters

### 5.1 Heights

These follow from the table in §3.1. The binding tables are:
* `sha_t`: 4.14 M of 4.19 M at the absolute worst case (3 MB of 56-byte nodes plus 4481 accounts); this needs proving, as v1's R7 did;
* `node`: 3 M;
* `rcpt`: 2.1 M.

`honestTraceV3_fits` must be proved from `RelD0`, A1 and A2 (v1's analogue: `honestTrace_fits'`).

### 5.2 Width

`W_eq ≈ 3,080` at `g = 1` and ≈ 2,580 at `g = 3`. The budget is 3,000, set by DESIGN §8 for 216 queries.
`Budget.weq_le` and `Air.wf` are kernel-checked as in v1 (`multBound ≈ 2^28`,
`fpBound ≈ 2^33.5 ≤ 2^36` including public messages); `NpOk` likewise.

### 5.3 Proof size (8 MiB cap) and parameters

| quantity | v1 (measured) | v3 estimate |
|---|---|---|
| typical (largest table 2¹²–2¹⁶) | 1.84–2.47 MB | ≈ 2.4–2.8 MB (g=3) + hint < 2 KB |
| max header (2²⁶ LDE) | 3.56 MB (max witness) | ≈ 4.3 MB (g=3) / 4.7 MB (g=1) + hint ≤ 1.05 MB (A1+A4) |
| formal bound `sizeMax` | 7.43 MB (`near_sizeMax`) | **8.6 MB at g=1, over the cap.** With the exact FRI bound (below): ≈ 5.6 MB (g=1) / 5.2 MB (g=3), + 1.05 MB hints ≤ 8 MiB |

`sizeMax` charges every one of the 21 fold layers a full 64-byte path (`pot`, κ = 86):
22 KB per query, or 4.74 MB of the 7.43 MB. The deployed schedule commits every third fold (arity 8): ≈ 8 KB per query without dedup.
**Proposal P1:** prove `sizeBound ≤ sizeMaxSched A prm` for the deployed arity schedule.
This is L7 proof work only (≈ 1–2 k LOC) and saves ≈ 3 MB of the bound.

| option | effect on proof bytes | effect on verify | cost | proposal |
|---|---|---|---|---|
| P1 exact FRI bound | bound −3.0 MB, actual 0 | 0 | L7 1–2 k LOC | **yes** (needed at g=1) |
| P2 `auxGroup` 3 | actual −0.46 MB (−66 ext cols × 32 B × 216) | slightly faster | generalize `NpOk` (`prm = default` → `prm = {default with auxGroup := g}`, `g ≤ 3`); 201 uses of `Params.default` in `Udr/`, mostly symbolic | **yes** |
| P3 final degree < 2⁵ | ≈ −0.1–0.2 MB | ≈ 0 | new L7 numerics | no |
| P4 arity 16 | ≈ −1 % with dedup | ≈ 0 | schedule numerics | no |
| P5 rate 1/8 | +5 %; allows one SHA table at 2²³ | +10 % | L7 query numerics (≈ 238 queries), L3 degree ≤ 8 | fallback for A1/A2 only |
| P6 Johnson-regime queries (≈ −45 %) | −35–40 % | −40 % | L3 is UDR-only; weighted correlated agreement without Mathlib (the part still sorried in ArkLib) | no (research) |
| P7 recursion | §5.5 | | | **no** |

### 5.4 Verify time (10 s cap; target ≤ 1.5 s typical, ≤ 5 s worst)

| component | typical (6 shards, 1–3 blocks, few receipts) | worst (64 shards, 32 blocks, A1 max) |
|---|---|---|
| STARK (hashing, ALI, FRI) | ≈ 0.9–1.3 s (v1 measured 0.5–1.1 s local, ≤ 1.69 s judge VM) | ≈ 1.5–2 s |
| public bus products | < 5 ms | ≈ 0.3–0.5 s (0.9 M body bytes; packing 3 B/msg ÷3) |
| native `checkD0` claim part | **measured** 45–67 ms for whole `checkD0` (incl. witness) on (2,8)/(5,16) fixtures | header chain + roots ≈ 25 ms (fast SHA) |
| RS matrix + encode | **measured** 250 ms (33,100) matrix; csimp fast path → < 10 ms | **measured** 2.5 s + 3.6 s (85,256, 900 KB, slow SHA) → fast path ≈ 0.3 s (est.) |
| scheduler | **measured** 1 ms/run | **measured** 134–217 ms/run × 32 → fast path ≈ 0.5 s (est.) |

Required perf work:
* A5 (the `SHA256Fast` import);
* csimp fast paths for `buildMatrix`/`encodeParts` and the scheduler's bucket loop (each proved equal to the spec function; ≈ 1–2 k LOC in total).

### 5.5 Recursion / compression: assessment

Wrapping the proof in a second STARK that verifies np-udr-stark in-AIR is **not provable
in the admission framework**:
* `CryptoSound`'s ROM branch runs the deployed verifier against a *random* oracle.
* An outer AIR can only arithmetize the *concrete* SHA-256.
* So the outer statement "an inner proof accepted by `V^{sha256}` exists" implies `RelD0` only under a knowledge or soundness assumption about the concrete hash. `CryptoSound`'s ROM branch carries no such hypothesis (DESIGN F1; `sha256-collision-resistance` is listed in the profile but not usable in the ROM branch).

Even ignoring that, the outer proof's floor at 216 UDR queries is ≈ 1.8 MB (v1 batch-1). The
inner verifier is ≈ 236 k SHA blocks, i.e. 4 M outer rows. The gain would be ≤ 2.5 MB, at the cost of a new
formal lane of 30–50 k LOC (verifier-as-AIR). **Rejected.**

### 5.6 Prove time and memory

* Typical D0 is tiny (v1 batch-1 class: 0.1–0.3 s; v3 adds `sha_r` and `uniq`): **< 2 s** estimated.
* The absolute A1/A2 worst case is ≈ 5.6 G cells against v1-max's 2.96 G, so ≈ 1.9× v1-max (379 s, 11.3 GB). That is ≈ 720 s and ≈ 21 GB: **over the 600 s / 16 GiB caps**.
* This matters only if a workload class reaches that size. Formal completeness is unaffected, because only the Lean prover model must handle it (as in DESIGN §8).
* Mitigations: the low-memory budget (`NPUDR_MEM_GB`), and putting `rcpt` at 2²¹ if a tighter count bound is proved.

---

## 6. Proof obligations and Lean signatures

Namespace `ZkFormal.NearV3` (candidate code, `zk-formal/ZkFormal/NearV3/`). The structure
mirrors L6 (`Near/Statements.lean`, `Near/Extract/Statements.lean`, `Near/Link/Statements.lean`):
* per-table *views* (`TableLocal → ∃ v, Wf v ∧ TableTraffic`);
* a trace-free *link* (views + SHA facts + balance ⇒ relational spec);
* a relational spec `GoodV3` with sound and complete directions;
* *render* for completeness.

### 6.1 Public side (spec-facing)

```lean
structure Hint where
  n : Nat; body : Bytes; s0 : Option Bytes
  fixed : List (List Nat × Option Bytes)         -- [7], [10], [13], [16]‖s
  implicit : List (Option Bytes)                 -- none = "same as previous output" (A3: always none)

structure Prep where                             -- prepared statement (the STARK's claim)
  hdr : PrepHdr                                  -- static-index fields (§2.1)
  lists : List (Nat × Bytes)                     -- applied order: (j, root_j)
  bnd : Option Bytes × Option Bytes              -- own shard [lo, hi)
  body : Bytes
  walks : List PubWalk                           -- fixed-key walks per τ: key, expected terminal, value (len, digest)
  states : List (Nat × Bytes)                    -- per τ: (len, sha256) of the written 0x0f state
  roots : Bytes × Bytes                          -- B2.prev_state_root, H.prev_state_root

def prepD0 (cb : Bytes) (h : Hint) : Except String Prep   -- built from NearSpecV3 functions only
def Prep.encode : Prep → Bytes
def pubOfV3 (p : Prep) : List Fp := Udr.pubOf Fp p.encode
def hintOf (cb w : Bytes) : Hint                          -- read off checkD0's execution
```

### 6.2 Relational spec and its two directions

```lean
structure ExtV3 where
  stores : List (List NodeRec3 × List (Nat × Bytes))   -- per τ: DAG records, touched values
  lists : List (List Receipt × List (Bytes × Nat))     -- per applied list: receipts, Merkle path
  akeys : List (Nat × Bytes)                           -- access-key values read
def GoodV3 (p : Prep) (e : ExtV3) : Prop
def SmallV3 (e : ExtV3) : Prop                          -- pruned (DAG, touched paths only)
def witnessOfV3 (cb : Bytes) (h : Hint) (e : ExtV3) : Bytes   -- encodes witness.bin
def extOfV3 (cb w : Bytes) : ExtV3

def FactorSoundStmt : Prop :=
  ∀ cb h p e, prepD0 cb h = .ok p → GoodV3 p e → RelD0 cb (witnessOfV3 cb h e)
def FactorCompleteStmt : Prop :=
  ∀ cb w, RelD0 cb w → ∃ p, prepD0 cb (hintOf cb w) = .ok p ∧
    GoodV3 p (extOfV3 cb w) ∧ SmallV3 (extOfV3 cb w)
-- sub-obligations of FactorSound/Complete
def EncodeWitnessStmt : Prop :=                     -- decode ∘ encode for the D0 witness shape
  ∀ sw, D0Shape sw → decodeWitnessFile (encodeWitnessFile sw) = .ok (encodeSW sw, []) ∧
                     decodeStateWitness (encodeSW sw) = .ok sw
def StoreBuildStmt : Prop :=                        -- §3.3: hash-functional DAG ⇒ buildFor = treeOf
  ∀ (ns : List NodeRec3) vals root keys, HashFunctional ns vals → RootedDag ns root →
    PathsRevealed ns keys → (partialTrie (storeOf ns vals) root keys).find = (treeOf3 ns vals).find
def TrieOpsStmt : Prop := …   -- find_set_ne, find_upsert_ne, set_upsert_comm on PTrie
```

### 6.3 Extraction (AIR ⇒ `GoodV3`), mirroring L6

```lean
def ExtractV3Stmt : Prop :=
  ∀ (p : Prep) (tr : Trace Fp), HoldsP nearAirV3 (pubOfV3 p) tr → ∃ e, GoodV3 p e

-- per table (TableLocal / TableTraffic / Traffic exactly as Near/Extract/Common.lean)
def NodeV3ViewStmt : Prop := ∀ tr pub, TableLocal NodeV3.table tr T_NODE pub →
  ∃ vs, NodeWf3 vs ∧ TableTraffic NodeV3.interactions tr T_NODE pub (nodeTraffic3 vs pub)
def WalkV3ViewStmt : Prop := ∀ tr pub, TableLocal WalkV3.table tr T_WALK pub →
  ∃ ws, WalkWf3 ws ∧ TableTraffic WalkV3.interactions tr T_WALK pub (walkTraffic3 ws)
def RcptV3ViewStmt : Prop := ∀ tr pub, TableLocal RcptV3.table tr T_RCPT pub →
  ∃ rs, RcptWf3 pub rs ∧ TableTraffic RcptV3.interactions tr T_RCPT pub (rcptTraffic3 pub rs)
def SrcpViewStmt  : Prop := ∀ tr pub, TableLocal Srcp.table tr T_SRCP pub →
  ∃ v, SrcpWf v ∧ TableTraffic Srcp.interactions tr T_SRCP pub (srcpTraffic v)
def AkeyViewStmt  : Prop := …   -- as AcctViewStmt
def BndViewStmt   : Prop := …
def SizeViewStmt  : Prop := …
-- reused verbatim (maxLog-parametric versions): AcctViewStmt, MrkViewStmt (n ≤ 4481), SortViewStmt (bus param: RIDS, DIGS)
-- SHA: ShaFactsStmt for T_SHA_T and T_SHA_R (L5's sha_digest_contract, unchanged)

def LinkV3Stmt : Prop :=
  ∀ (p : Prep) (vs ws rs sv av as mv ids dg bv zv) (shaS shaR : List (Nat → List Fp → Nat)),
    let pub := pubOfV3 p
    NodeWf3 vs → WalkWf3 ws → RcptWf3 pub rs → SrcpWf sv → AkeyWf av → AcctWf as → MrkWf pub mv →
    SortWf ids → SortWf dg → BndWf bv → SizeWf zv → (∀ k, ShaFacts (shaS k) (shaR k)) →
    (∀ b m, Σₖ shaS k b m + cnt (nearSendsV3 pub …) m + pubCount nearAirV3 pub b true m =
            Σₖ shaR k b m + cnt (nearRecvsV3 pub …) m + pubCount nearAirV3 pub b false m) →
    ∃ e, GoodV3 p e
```

`LinkV3Stmt` splits like v1's into `ShaStmt` (now over two instances), `ClaimStmt`
(prepared header), `ListsStmt` (RC(j) + srcp ⇒ `rootFromPath … = root_j`), `NodupStmt`,
`TrieStmt` (per τ, DAG, distinct digests), `WalksStmt` (incl. absent terminals),
`RunStmt` (v1 run + system receipts + access keys), `PostStmt` (ROOT chain), `OutStmt`
(reused), `BodyStmt` (`stream_eq_of_count` ⇒ refunds encode to `B`), `SizeStmt`.

### 6.4 Completeness, heights, static facts, assembly

```lean
def renderV3 (p : Prep) (e : ExtV3) : Trace Fp
def RenderV3Stmt : Prop := ∀ p e, GoodV3 p e → SmallV3 e → HoldsP nearAirV3 (pubOfV3 p) (renderV3 p e)
def FitsV3Stmt : Prop := ∀ p e, GoodV3 p e → SmallV3 e → InD0Cap p e →   -- A1/A2 consequences
  ∀ t < nearAirV3.tables.length, (renderV3 p e).log t ≤ nearAirV3.tables[t]!.maxLog
theorem nearAirV3_wf   : Air.wf nearAirV3 16 = true             -- decide +kernel
theorem nearAirV3_npOk : NpOk nearAirV3 prmV3                   -- decide +kernel (after P2)
theorem nearAirV3_weq  : weq nearAirV3 prmV3.auxGroup ≤ 3000    -- decide +kernel
theorem nearV3_size    : ∀ hdr, headerOk … → sizeBound … ≤ 8388608 - maxHintBytes   -- P1

-- top theorems
theorem nearAirV3_sound : ∀ cb h p tr, prepD0 cb h = .ok p →
  HoldsP nearAirV3 (pubOfV3 p) tr → ∃ w, RelD0 cb w
theorem nearAirV3_complete : ∀ cb w, RelD0 cb w → ∃ p, prepD0 cb (hintOf cb w) = .ok p ∧
  HoldsP nearAirV3 (pubOfV3 p) (renderV3 p (extOfV3 cb w))
-- assembly (L7): the composed verifier hintTree split prep (guard ∘ Stark.verifier …)
theorem nearV3_admission : AdmissionStatement NearSpecV3.challengeParams artV3
```

The assembly uses:
* `romSound_hint` (**proved**) with `hprep := nearAirV3_sound`;
* `stark_romSound_full` (L2/L3, AIR-generic, given `NpOk`);
* `romSound_guard`;
* `np_proverComplete` (L7, AIR-generic) for the composed prover `hint ‖ π`;
* size = `|hint| + sizeBound`.

---

## 7. Lanes, effort, risk

Calibration (current tree): `Near/` (L6) is 52.2 k lines, `Sha/` (L5) 8.6 k, `Udr/` (L3) 11.2 k; DESIGN.md §9 estimated L6 at 25–40 k / 8–14 agent-days, so v1's actual L6 volume ran ≈ 1.3–2× over its estimate (the ranges below include that factor).

| lane | scope | deliverables (Lean) | deps | LOC | agent-days | risk |
|---|---|---|---|---|---|---|
| **V0 spec** | A1–A5 in `checkD0` and the oracle classifier; difftest re-run; `prepD0` (in `NearSpecV3`, so it is trusted and reused by the model) | `prepD0`, `hintOf`; difftest 0 disagreements; native-vs-relation agreement test | — | 1–2 k | 2–3 | low (governance) |
| **V1 factor** | witness encoder plus round trips; `StoreBuildStmt`; `TrieOpsStmt`; `FactorSound`/`FactorComplete` (checkD0's `for`-loops in `Except` → list lemmas) | `FactorSoundStmt`, `FactorCompleteStmt`, `EncodeWitnessStmt`, `StoreBuildStmt`, `TrieOpsStmt` | V0 | 8–12 k | 5–7 | **medium-high** (largest new semantic proof; hash-store reasoning) |
| **P-bus** | public-message bus (L4 `PubSeg`/`HoldsP`/verifier/export, L3 `Np` bus rounds, L7 prover model, L8 Rust) | `holdsP_iff_holds`, `rbrWith` for `HoldsP`, `npIopComplete'` with public product | — | 3–5 k (+0.5 k Rust) | 3–4 | medium |
| **P-asm** | `romSound_hint` (done), v3 assembly, P1 exact FRI size bound, P2 `auxGroup` generalization | `nearV3_admission`, `sizeMaxSched`, `NpOk` with `g ≤ 3` | P-bus | 2–4 k | 2–3 | low-medium |
| **A-trie** | `node`/`walk` extensions (τ, DAG, id order, `vlen`, absent terminals, public walks, `0x0f` upsert); `uniq` | `NodeV3ViewStmt`, `WalkV3ViewStmt`, Link `TrieStmt`/`WalksStmt`/`PostStmt`, render | P-bus | 12–20 k | 7–10 | **high** (touches L6's largest proof bodies) |
| **A-rcpt** | `rcpt` extensions (lists, routing, system receipts, signer=receiver, access-key walks, `BODY`) | `RcptV3ViewStmt`, Link `RunStmt`/`BodyStmt`/`ListsStmt`, render | P-bus | 10–16 k | 6–9 | **high** (volume) |
| **A-small** | `srcp`, `akey`, `bnd`, `size`; `mrk`/`sort`/`acct` `maxLog` generalization | five view stmts, render | P-bus | 4–7 k | 3–4 | low-medium |
| **A-link** | `GoodV3`, `LinkV3Stmt` composition, `ExtractV3`, `RenderV3`, `FitsV3`, static kernel checks | top theorems §6.4 | all A, V1 | 6–10 k | 4–6 | medium |
| **L8-v3** | Rust: trace generation for every table (cell-for-cell vs Lean `renderV3`), hints, `prep` mirror (vs Lean `prepD0`), 2nd SHA, public bus, prover in the package | `out/prove` v3; conformance, mutants; judge-verify runs | P-bus, A tables | 9–13 k Rust | 6–8 | medium |
| **perf** | A5, csimp fast paths (RS, scheduler), verify-time benchmarks on the judge VM | `buildMatrix_eq_fast`, `encodeParts_eq_fast`, `run_eq_fast` | V0 | 1–2 k | 2 | low |

**Totals:** ≈ 50–80 k Lean LOC plus 9–13 k Rust; ≈ 40–60 agent-days; 5–7 weeks with 6–8
lanes (≤ 2 sub-agents per lane, as in the preamble).

**Critical paths.**
* Risk: `V1 factor` and `A-trie`.
* Volume: `P-bus → A-rcpt → A-link → assembly`.

**Recommended first milestone (M-v3-1).** P-bus, plus `romSound_hint` composition on a toy AIR with a public segment and a hint. That gives a full toy admission with the new pipeline, before any NEAR table work, mirroring v1's M2.

**Risks.**
1. **Elaboration budget.** v1's candidate elaboration is 647 s, and v3 adds an estimated +60–80 %, so ≈ 1,050–1,200 s of 1,800 s.
   * Mitigation: keep v1 modules out of the v3 closure where unused; avoid large `decide +kernel` (the RealCase-style 2.5 min kernel evaluations must stay out of the candidate); ask governance for a larger elaboration budget early.
2. **v1 proof reuse is partial.** The node and rcpt layouts change, so roughly 30–40 % of the `Extract/Node*`/`Rcpt*` and `Link/*` modules are touched.
   * Mitigation: append columns, keep v1 column indices stable, and gate new constraints with new selectors.
3. **A1/A2 rejected by governance.** Then the design needs multi-instance `rcpt` or rate 1/8 (§4 fallbacks): +2–3 weeks.
4. **Native verify time at the extremes** without the fast paths: ≈ 10 s worst (§5.4). The perf lane is mandatory before benchmarking.
5. **Worst-case prove time and memory** over the caps (§5.6). This is relevant only if a workload class goes near A1-max.
6. **`checkD0` refactors in the spec** while the lanes run. Freeze `NearSpecV3` (with A1–A5) before V1 starts.

---

## 8. Proof of concept (kernel-checked)

`zk-formal/ZkFormal/V3/Hint.lean` builds with `lake build ZkFormal.V3.Hint` in ≈ 0.3 s (plus its deps).
There is no `sorry` and no `native_decide`.

| theorem | statement | axioms |
|---|---|---|
| `romSound_hint` | For any `split`, `prep` and tree verifier `V`: `RomSound S L' V …` and `(∀ cb h cb', prep cb h = some cb' → L' cb' → L cb)` ⇒ `RomSound S L (hintTree split prep V) …` with **the same budgets and bound**. The reduction post-composes the adversary with a pure map (`CoinAdversary.simulate_bind_pure`) and uses `queryBound_bind_pure`. Overflow cases use `Assembly.runH_overflow`, as `romSound_guard` does. | propext, Classical.choice, Quot.sound |
| `queryBound_bind_pure` | Weighted query budgets are preserved by post-composition with a pure function. | — |
| `stream_eq_of_count` | Bus balance between an AIR stream `(i, s i)_{i<n}` and public messages `(i, B i)_{i<m}` ⇒ `n = m ∧ ∀ i < n, s i = B i`. This binds the hint body `B` to the refund stream. | propext, Quot.sound |
| `max_receipts` | `4480·G < 10¹⁵ ∧ ¬(4481·G < 10¹⁵)`, so A1 gives `n ≤ 4481`. | none |
| `schedStateLen_64`, `schedStateLen_6` | canonical `0x0f` sizes 98,341 B and 901 B. | none |

**Why these PoCs, and not an RS or ChaCha20 AIR.** This design keeps both out of the AIR
(§2.5): RS is too costly to arithmetize at the worst-case body, and ChaCha20 is claim-only in the
shuffle and hint-only in the scheduler. The new risk is the *boundary*: can native work
on public data and prover hints be bolted onto the admitted ROM-sound verifier without
re-opening L2/L3? `romSound_hint` answers that generically: the only remaining obligation is
the deterministic semantic implication (§6). `stream_eq_of_count` is the exactness lemma
behind binding a hint to the trace.

**Measurements behind §2.5 and §5.4.**
* Scratch benchmarks against a copy of the main checkout's `NearSpecV3` build, compiled with Lean 4.34.1 and pinned to CPUs 8–15: `rsbench`, `schedbench`.
* `nearspec-v3-check` on the 64 public D0 fixtures: 64/64 accepted, 30 s in total. Cases with (2,8) or (5,16) take 45–67 ms; (33,100) cases take ≈ 0.5 s, dominated by `buildMatrix`.

---

## 9. Open questions for review

1. Approve A1 and A2 (required), and A3/A4 (or the 64 MiB formal cap instead).
2. Approve the public-message bus as a protocol change (L3/L4/L7/L8). v1 is unaffected (`pubSegs = []`).
3. Confirm that the v3 challenge's `allowed_packages` include `NearSpecV3` for the model (native `prepD0`).
4. A1 premise: confirm against nearcore 2.13.4 that a chunk's `gas_limit` is never adjusted from genesis (`ChunkExtra.gas_limit` propagation).
5. Elaboration budget for v3 (an estimated ≈ 1,100 s of 1,800 s).

---

## 10. Review decisions (lead, 2026-10-06) and source checks

Approved with conditions:
1. Native claim-only work: the verifier calls the trusted `NearSpecV3` functions only. Any faster code enters through kernel-proved `@[csimp]` lemmas, including the `SHA256Fast` import into `NearSpecV3`. Verify time is first-class: typical ≤ 1.5 s, worst ≤ 10 s with fast paths, measured per component.
2. The public-message bus is a **new protocol version `np-udr-stark-v2`**. v1 (`np-udr-stark-v1`, admitted) stays byte-for-byte unchanged: new modules, no edits to v1 definitions.
3. Digest distinctness / shared subtrees (§3.3) is a required, *proved* AIR obligation.
4. Amendments:
   * **A1** is approved after the source check below.
   * **A2** is approved after the source check below, plus a test that it holds on every honest D0 case.
   * **A3/A4 are not adopted** for proof-size reasons. Instead: tighten L7's FRI size bound (P1), and give the D0 challenge an honest succinct `max_proof_bytes` (target 8 MiB, not 64 MiB). The open consequence is in §10.2.
5. Recursion is out of scope (§5.5).
6. The worst-case prove time (≈ 720 s / 21 GB) is tracked; a max-witness workload class comes later.

### 10.1 Source checks (nearcore 2.13.4, `44f7ae6c`, `/data/illia/nearproof-deps/nearcore`)

**A1: chunk `gas_limit` is fixed.**
* The genesis chunk extra takes `genesis_config.gas_limit` (`chain/chain/src/types.rs:288`, `chain/chain/src/chain.rs:430,614`).
* A chunk producer copies `chunk_extra.gas_limit()` into the new header (`chain/client/src/chunk_producer.rs:393`).
* Validation requires `prev_chunk_extra.gas_limit() == chunk_header.gas_limit()` (`chain/chain/src/validate.rs:154`).
* Applying a chunk stores `to_chunk_extra(chunk_header.gas_limit())` (`chain/chain/src/chain_update.rs:472,519`; `types.rs:166-172`). A missing chunk reuses `prev_chunk_extra.gas_limit()` (`update_shard.rs:224`).

So the chunk gas limit equals the genesis value forever; there is no dynamic adjustment. The 10¹⁵ figure is mainnet genesis (1000 Tgas; oracle chains `gas_limit_tgas: 1000`). It is a genesis fact, not a PV 86 runtime parameter. A1 is therefore stated as the **claim-decidable** condition `B2-slot gas_limit ≤ 10¹⁵`; the B2 slot is authenticated chain data in the claim.

**A2: receipt proofs contain only receipts for `to_shard`.**
* `Chain::create_receipts_proofs_from_outgoing_receipts` (`chain/chain/src/chain.rs:4132-4150`) builds the proof for `to_shard_id = shard_layout.get_shard_id(i)` from `group_receipts_by_shard(outgoing, shard_layout)`. Its root is checked against the header (`chain/chunks/src/logic.rs:77-95`).
* Routing is `receipt.receiver_shard_id(layout)`, which is `account_id_to_shard_id(receiver_id)` for Action receipts (`core/primitives/src/receipt.rs:438-447`).
* The layout used is `get_shard_layout_from_prev_block(chunk.prev_block_hash)`. In D0 (single epoch) that is `L(c.epoch_id)`, the same layout the validator filters with.
* The witness producer passes these stored proofs through unchanged (`stateless_validation/state_witness.rs:264-320`, `ReceiptFilter::All`).

Hence A2 holds on every honest D0 witness. Lane V0 also tests it on the oracle's honest D0 cases.

### 10.2 Open: proof-size cap without A3/A4

The hint must carry every value the native scheduler reads:
* `s₀`, any decodable `BandwidthSchedulerState`, up to the 3 MB base-state bound;
* in the collision case, the `0x0f` value of each implicit transition.

Formally the hint is therefore bounded only by the witness size (≤ 8 MiB). Under an 8 MiB cap, `ProverComplete` cannot hold for such witnesses. Options:
* (a) A canonicality-style D0 condition on `0x0f` (nearcore always writes the canonical state for the current layout);
* (b) a cap of about 16 MiB;
* (c) the scheduler in-AIR (estimated 20–40 k LOC).

This is raised to the lead; lanes that do not depend on it proceed.

## 11. Decisions round 2 (lead, 2026-10-06) and consequences

* **Governance change.** `near-chunk-validation-d0-1` is now live: `reexec-v3-d0` is admitted on it, and it pins the NearSpecV3 tree `sha256:89903b98…`. Consequences:
  * Every v3 amendment is **additive**, in new files: `RelD0a cb w := RelD0 cb w ∧ A1 ∧ A2 ∧ Canon0f`, plus a new successor draft challenge with `max_proof_bytes = 8,388,608`.
  * A5 becomes candidate-side, kernel-proved `@[csimp]` redirections of the spec functions `prepD0` calls. Pinned modules cannot gain imports.
  * Extracted witnesses are emitted in the v3-ref normal form `normalW`. The encoder reuses `normSW`/`normW` and their lemmas from main.
* **8 MiB cap, option (a) then (c).**
  * Canonicality of `0x0f` bounds the main-transition `s₀` at 98,341 B.
  * It does **not** make the hint complete under 8 MiB, for two reasons:
    1. A `RelD0a` witness may read, in each implicit transition, a canonical `0x0f` value that differs from the previously written one but has the same SHA-256 digest. Collision resistance cannot be used in the semantic theorems, so the hint must carry each such value: ≤ 31 × 98,341 B ≈ 3.0 MB.
    2. The queue values (`[13]`, `[16]‖s`) are unbounded.
  * Formal budget: STARK bound ≈ 6.4 MB (P1 corrected by +1 MB for roll-in commits, see STATUS-V3-BUS), plus `B` ≤ 0.91 MB, leaves ≈ 1.1 MB.
  * Per the lead's rule this means **(c): the bandwidth scheduler (with its ChaCha20) and the fixed-key value parsers move into the AIR.**
  * After (c) the hint is only `{n, B}`: ≤ 0.91 MB under A1.
  * Native in the verifier, unchanged: the claim-only parts (header chain, walk, shuffle permutation, f64 congestion, RS/emr over `B`, outgoing root, forwarding).
  * The scheduler's *claim-only inputs* become public data, also computed natively: link permissions from congestion and missed chunks, base bandwidth, converted request increase lists. Its state-dependent core (allowances, budgets, bucket processing, distribute-remaining, state encoding) is in-AIR.
  * Canon0f is kept: in-AIR decoding of the previous state then reads exactly `n²` links in order.
  * New lanes, after the spec lane reports:
    * `v3-chacha`: ChaCha20 block table and `gen_index`/Lemire;
    * `v3-sched`: scheduler tables, sound and complete against `Scheduler.run`;
    * `v3-qvals`: queue-value parsers.

  Estimated effort: +20–35 k LOC, +3 weeks.
* **A6 rejected; weak `uniq` instead.** "Equal digest ⇒ equal bytes" is proved in-AIR, with tree-shaped records. This is in lane `v3-trie`.
* **P2 runs now** in lane `v3-p2`.

## 12. SHA message-id kind registry (program lead, binding for all v3 lanes)

`Id = kind + 16·idx` with `idx < 2^22`. Kinds must be distinct mod 16, and a kind may be shared only by tables whose `idx` spaces are provably disjoint.

| kind | name | owner | idx |
|---:|---|---|---|
| 1–10 | `K_RC, K_RF, K_PEO, K_LEAF, K_RID, K_MRK, K_NPRE, K_NPOST, K_VPRE, K_VPOST` | v1 meanings, reused by v3 rcpt/mrk/trie (v3-trie: value ids start at 0, `d153d30f`) | per v1 / per v3 table |
| 11 | `K_SCH` | v3-sched (sanity hash) | τ |
| 12 | `K_VUPS` | v3-trie `upsV3` (post `0x0f` value) | τ |
| 13 | `K_SRC` | srcp (leaf rehash and path nodes) | `2·step + (j-indexed offset)`, fixed by the srcp lane |
| 14 | `K_VAK` | akey (access-key values) | touched slot k |
| 15, 0 | reserved | ask the program lead | — |

The assembly lane proves one global lemma: every BYTES/DIGEST id produced by any table falls in that table's kind, and the idx ranges are disjoint.

**upsV3 ↔ scheduler interface (decided):**
* `S0F (τ, present, vid)`: upsV3 → sched.
* `VBYTES (vid, pos, b)`: codec → valV3.
* `SPOST (τ, pos, b)`, for `pos < L`: codec → upsV3.
* **`SPLEN (τ, L)`**: sent once per τ by the codec. This is an explicit length message, not an end flag. It pins the length the way DIGEST consumers do.

No consumer relies on `L = 37 + 24·n²`.
