# A formally admitted STARK for v3 D1 (Transfer transactions): design

Status: **design phase**, 2026-10-14; decisions P-D1-1 … P-D1-7 taken by the user 2026-10-14 (§0). Branch `lane/v3-d1-air` (from main `216d9f04`).
Statement: `spec/near-chunk-validation-d1.md`, `NearSpecV3.RelD1`
(`spec/lean/v3/NearSpecV3/ChunkValidationD1.lean`, `RuntimeD1.lean`, `TxD1.lean`, `Ed25519.lean`,
`SHA512.lean`); tier `challengeParamsChunk .d1` of `near-chunk-v3`
(`challenges/drafts/near-chunk-v3.draft.json`, classes `d1-transfers`, `d1-mixed`, `d1-receipts`).
Builds on `V3-D0-DESIGN.md` (the D0a architecture, its §1 C/H/W split and §2 native verifier),
the D0a certificate `nearV3_admission_final` (`zk-formal/ZkFormal/NearV3/Assembly/AdmissionV3.lean`)
and the Rust prover `npudr` (`examples/np-udr-stark-v2/source`).
Progress notes: `docs/logs/v3-d1-air-2026-10.md`. Spike code: `examples/d1-air-spike/`.

Labels: **measured** (run here, CPUs 10–11/26–27), **estimated** (arithmetic from a stated model),
**PROPOSAL** (a relation, spec, challenge or protocol change: **the user decides**; nothing in
this lane changes any of them).

---

## 0. Summary and decisions requested

**Finding 1: `RelD1` has no bounded tier yet.** `RelTier .d1 = RelD1` carries none of D0a's
amendments (A1, A2, Canon0f, A7–A10, A12). It also does not bound the transaction count: a failed
transaction burns 0 gas, so an 8 MiB witness can carry about 49,000 of them. A succinct STARK
cannot be complete on `RelD1`, for the same reason it could not be complete on `RelD0`. A
**bounded tier `D1a`** is needed (§3, PROPOSAL P-D1-1).

**Finding 2: the transactions are claim-committed, so their signatures can be checked natively.**
The relation takes `w.txs` from the witness. It checks `merklize(txs.raw) = tx_root` against the
B2 slot of the claim, and every transaction-only step reads nothing from the state:
* the duplicate check;
* the expiry flag, which comes from the claim;
* `sizeOk ∧ Ed25519.verify`;
* `txCost`;
* the receipt id and the outcome leaves.

So these steps are class **H** in V3-D0-DESIGN §1 terms. The verifier can run them with the
trusted spec functions on a hint that carries the transactions. That is exactly how D0a already
handles Reed–Solomon, the header chain and the ChaCha shuffles (decision D-1, approved
2026-10-06).

What is left for the AIR is the state-dependent core. For each *candidate* transaction (one that
reaches step 5) it must prove:
* two trie reads (signer account, access key);
* the access-key decode;
* the nonce, balance and storage-stake comparisons;
* two writes;
* the local-receipt credits;
* a few public-offset changes in `rcpt`.

| | **D1-N** (recommended first) | **D1-S faithful** | **D1-S optimized** |
|---|---|---|---|
| Ed25519 + SHA-512 | native: `Ed25519.verify` is the spec function, so no proof is needed | in-AIR, replaying the spec's operation sequence exactly | in-AIR: comb, window, hinted roots |
| field muls per signature (**measured**, spike §4.3) | 0 in-AIR | 7,469 max (+ ≈ 800 const-muls) | 3,095 max |
| signature bound per chunk | `NT = 4,096` transactions (verify time) | `NS ≈ 512` (one 2²² gadget table) | `NS ≈ 1,350` |
| added prove time at the bound (est.) | ≈ 5–20 s | ≈ +135 s (more with fixed 2²² heights) | ≈ +100 s |
| added verify time at the bound | ≈ 14 s (3.4 ms/sig compiled spec; a csimp fast path brings it to ≈ 1–3 s) | ≈ 0.1 s | ≈ 0.1 s |
| added formal-proof size (STARK bound) | ≈ +0.1–0.2 MB | ≈ +1.5 MB | ≈ +1.5 MB |
| formal effort | smallest: native parts are spec functions | + field gadget, SHA-512 table, a replay proof of `smulAux`/`powAux` | + Edwards group law (associativity), unique roots, Fermat; all **without Mathlib**: high risk |
| succinctness in the transaction count | verify grows linearly (≈ 0.3–3.4 ms/tx) | yes | yes |

**Recommendation.** Build **D1-N first**, as one combined AIR `nearAirV3D1`: a superset of
`nearAirV3`, in which the transaction part is simply empty for D0 chunks. Admit it under a **new
admission statement for a new tier `.d1a`**. Plan **D1-S faithful** as the succinctness upgrade
if the user rules out native signature verification, or once cross-shard verify time makes it
necessary. GKR/sumcheck sub-arguments are allowed by the security profile but would be a new
protocol version; they are not recommended for D1 (§4.4).

**User decisions (2026-10-14, binding; implemented by lane `v3-d1a-spec`, spec
`spec/near-chunk-validation-d1a.md`, `NearSpecV3.ChunkValidationD1a`):**

| id | decision |
|---|---|
| **P-D1-1** | **DECIDED YES**: bounded tier `RelD1a = RelD1 ∧` the D0a amendments restated for the D1 witness/run `∧ T1`, in new files, plus `Tier.d1a` in `ChallengeChunkV3`. `RelD1`, `RelD0`, `RelD0a` and every existing tier's relation unchanged. |
| **P-D1-2** | **DECIDED**: signatures are verified **natively** in the verifier (D1-N). The relation implies no in-AIR obligation. |
| **P-D1-3** | **DECIDED**: at most `NT0 = 4,096` transactions per chunk (T1). |
| **P-D1-4** | **DECIDED**: A7 bound `B1 = B0 = 2,000,000` (same as D0a). |
| **P-D1-5** | **DECIDED**: proof cap = near-chunk-v3's 64 MiB, no extra bound (so no T2). |
| **P-D1-6** | **DECIDED**: native prep (`prepD1`) lives candidate-side (zk-formal), not in the pinned spec. |
| **P-D1-7** | **DECIDED NO** (T4 not adopted): not full-access-only; function-call and gas-key failure cases stay in scope. |

**Decisions requested (all PROPOSALS; decided 2026-10-14 as above):**

| id | question | proposal |
|---|---|---|
| **P-D1-1** | Bounded tier | Add `RelD1a := RelD1 ∧ A1 ∧ A2 ∧ Canon0f ∧ A7 B1 ∧ A8 ∧ A9 W0 ∧ A10 Dp0 ∧ A12 ∧ T1 NT` (each stated over the D1 decoder and the D1 run), `Tier.d1a`, `rel_mono`/`relD1a_relD1`, in new files (§3). |
| **P-D1-2** | Native signatures | Allow D1-N: the verifier runs `pTxD1`, `Ed25519.verify`, `txCost`, dedup, `merklize` and the outcome leaves natively on a hint carrying `transactions` (§2, §4). The alternative is D1-S faithful with `NS = 512`. |
| **P-D1-3** | `T1` (`w.tx_count`) | `|transactions| ≤ NT = 4,096`. The honest-producer maximum is ≈ 2,241 successful transfers (`max_tx_gas` 500 Tgas / 223.18 Ggas). This is a domain bound and costs liveness only (§3.2). |
| **P-D1-4** | `B1` (A7 bound for D1a) | Keep `B1 = B0 = 2,000,000`: no new SHA rows. Liveness: on mainnet-sized tries this admits ≈ 150–250 transfers per chunk (§5.4). Raising B1 is a separate cost lever. |
| **P-D1-5** | Formal proof-size cap of D1a | D1-N's bound is ≈ 6.6 MB of STARK plus a hint (refunds ≤ 1.30 MB, transactions ≤ 1.21 MB, new transactions ≤ 1.21 MB under T2) ≈ 10.3 MB, which is over 8 MiB. Proposal: **16 MiB**, or the draft's 64 MiB `maxProofBytesV3`. Honest proofs ≈ 5.5–6.5 MB plus about 0.3 KB per transaction. `T2` (`|new_transactions| ≤ NT`) is needed only for a cap below about 16 MiB. |
| **P-D1-6** | `prepD1` location | As with `prepD0`: in `NearSpecV3` (trusted, reused by the model; this changes the pinned tree digest of the draft) **or** candidate-side in `zk-formal` (proved, with no governance change). Recommend candidate-side. |
| P-D1-7 | (not recommended) `T4` FullAccess-only keys | It would remove the in-AIR access-key decoder but excludes the `fc_key_*`/`gas_key_v0` validity classes, which the D1 spec lists as *inside* D1 (§3.3). |

The prototype (§4.3) checks two in-AIR Ed25519 schedules against nearcore's verdict on all
**7,265** signature vectors: **0 disagreements** for both. It also bounds the 32×8-bit limb
gadget for 𝔽_{2²⁵⁵−19} inside BabyBear: coefficients ≤ 2^28.2 < p_BB/2 and carries ≤ 2^20.2.
A fixture measurement (§5.1) gives the D1 workload of all 188 public-d1 cases.

---

## 1. What `RelD1` requires beyond `RelD0a`: gap list

`checkD1` (`ChunkValidationD1.lean`) is `checkD0` with transaction steps added. `RelD0a` is
`RelD0` plus amendments. Each item below is classified as in V3-D0-DESIGN §1:
* **C** — native from the claim;
* **H** — native from claim plus hint, with the hint bound by the AIR;
* **W** — in-AIR.

The table shows the mapping under D1-N.

| # | `RelD1` obligation (spec / nearcore ref) | class | maps onto | new / changed |
|---|---|---|---|---|
| G1 | decode `transactions`, `new_transactions` with `pTxD1`: V0/V1, plain nonce, one `Transfer`, ED25519 key and signature; `sig[63]&0xE0≠0` is a decode error (`TxD1.pTxD1`) | H | `prepD1` parses the hint's transaction lists | hint fields `txs`, `newTxs` |
| G2 | `|tx_valid| = |txs|`; `c.no_tx_flags` dropped | C/H | native | — |
| G3 | step 6: every `newTxs` passes `sizeOk` (no signature check) | H | native | — |
| G4 | step 8: `merklizeBorsh(txs.raw) = slotB2.txRoot` | H | native (SHA-256 fast path A5) | — |
| G5 | `H.txRoot = merklizeBorsh(newTxs.raw)` | H | native | — |
| G6 | RS body `u32 |newTxs| ‖ newTxs.raw ‖ encodeReceipts(fwd ++ refunds)` | H | native over the hint (D0a's `B` grows a prefix) | `prepD1` body layout |
| G7 | partial-trie keys `+ txKeys` (signer account `[0]‖signer`, access key `[2]‖signer‖[2]‖pk`) | W | `walkV3` (unchanged), keys sent as **public `KEYNIB`** segments (the keys are native data) | public segment |
| G8a | step 1: duplicate hash, skipped with no outcome and no reads | H | native | — |
| G8b | step 2: `tx_valid = 0` gives a failed outcome | C | native | — |
| G8c | step 3: `sizeOk ∧ Ed25519.verify pk sig (sha256 body)` | H (D1-N) / W (D1-S) | native `Ed25519.verify`, or §4 tables | D1-S: new tables |
| G8d | step 4: `txCost`; u64/u128 overflow gives a failed outcome | H | native | — |
| G8e | step 5: signer account read. Absent: fail. V2 sentinel: out of domain (`t.signer_v1`). Not 72 bytes: reject | W | walk `FINAL`; `acctV3` value window (72 B; `amt ≠ u128::MAX` check already present) | `txV3` consumes it |
| G8f | step 6: access-key read. Absent: fail. `decodeAccessKey = none`: **reject** (`invalid`) | W | walk `FINAL`; access-key value bytes | **`akmV3`** (decoder for FC/gas keys, see §2.4) |
| G8g | step 7 `verifyAndCharge`: gas key fails; nonce check (strict `= k+1`, checked overflow; monotonic `> k`); `t.nonce < min(height·10⁶, 2⁶⁴−1)`; `amount ≥ total`; FC allowance; storage stake on the new amount; FC fails (`RequiresFullAccess`) | W + H | `k.nonce`, account fields, perm: in-AIR comparators in **`txV3`**. The `height·10⁶` bound and `total` are native | **`txV3`** |
| G8h | step 8: receipt `Receipt::from_tx`, `rid = sha256(h‖u64 height‖u64 0)`, `rgp = max(price, 10⁹)` | H | native, given the public success bit `ok_i` | hint `okbits` |
| G8i | local iff `receiver = signer`; otherwise `tryForward` (`e.forwarded`) | H + W | gas part native; size part via D0a's `Prep.fwd` demand vs in-AIR grants (demands grow by the transaction receipts) | `Prep.fwd` values |
| G8j | `tokens + burnt ≥ 2¹²⁸`: no outcome, no write (receipt already emitted); gas `≥ 2⁶⁴`: reject | H | native (the transaction token/gas sums are native) | — |
| G8k | writes: account `amount − total`; access key `encodeFullAccessKey nonce` (9 B), both visible to later transactions | W | account: v1 `MEM` offline-memory bus with timestamps (tx ops before receipts); access key: new `AKMEM` chain | `txV3`, `akmV3` |
| G8l | outcomes: failed `{id, [], 0, 0, signer, Failure}`, success `SuccessReceiptId` | H | native leaves, injected as **public `DIGEST`/`MPOS`** messages into `mrkV3` (unchanged) | public segment |
| G9 | local receipts, `r.shape` (named), applied *first* by `applyReceiptsC` with compute = transaction gas + i·G (`e.compute`) | H + W | native: shape, compute, outcomes, refunds, ids, tokens. In-AIR: the credit (`amount + deposit`, `≠ u128::MAX`, `+locked < 2¹²⁸`, storage stake) as a credit op in `txV3`. Incoming receipts stay in `rcptV3` | `txV3` credit op |
| G10 | `e.distinct_ids` over local ++ incoming ids | H + W | `sortV3` (unchanged) gets local ids as **public `RIDS`** messages | public segment |
| G11 | outcome root: tx outcomes ++ local ++ incoming | H + W | `mrkV3` unchanged; `rcptV3` leaf index starts at public `m₀` | **`rcptV3`** first-row change |
| G12 | `gasUsed`, `tokensBurnt` | H + W | native prefix; `rcptV3` running `tok` starts at public `tok₀` | **`rcptV3`** first-row change |
| G13 | outgoing = forwarded tx receipts ++ refunds | H + W | native prefix; `rcptV3` `BODY` offset starts at public `o₀` (was the constant 4) | **`rcptV3`** first-row change |
| G14 | `MEM` timestamps: tx ops `0..m−1`, receipts `m..` | W | `rcptV3` receipt counter starts at public `m₀` | (same edit as G11) |
| G15 | new domain conditions `w.tx_shape`, `t.signer_v1`, `e.forwarded` (transaction receipts), `r.shape`/`r.success` for local receipts | H/W | `tx_shape`: native. `signer_v1`: AIR (sentinel). `forwarded`: native + `Prep.fwd`. local `r.success`: `txV3` credit op | — |
| G16 | D1-S only: `SHA-512(R‖A‖h) mod ℓ`, decompression, `[s]B − [k]A`, compress, byte compare | W | §4 tables `fmulV3`, `sha512V3`, `edctlV3` | new |

Unchanged from D0a, reused verbatim:
* the source proofs (`srcpV3`, `bndV3`), the shuffle, the scheduler (`codecV3`…`scpV3`, ChaCha);
* the fixed-key queue values (`qvV3`);
* the trie tables (`nodeV3`, `headV3`, `valV3`, `walkV3`, `uniqV3`, `upsV3`, `sizeV3`, including A7's running sums);
* `acctV3`, `mrkV3`, `sortV3`, the two SHA-256 instances;
* the implicit transitions;
* the header comparisons.

`applyNewChunkD1` runs `schedStep` and the queue checks exactly as D0 does, so the scheduler and
queue AIR is untouched.

### 1.1 Why "any failing reason" is not an AIR shortcut, and why reads still matter

Every failed outcome hashes alike (`PartialExecutionStatus::Failure`). Steps 1–4 never throw;
steps 5–6 throw only on undecodable values. Two consequences:
* For a candidate transaction it is *sound* to prove failure by any failing check, as long as
  the reads it relies on are proved.
* *Completeness*, however, needs every candidate's reads (signer and access key) to be revealed.
  The relation reads them whenever step 5 is reached, and a missing node there rejects the
  chunk.

D1-N therefore computes exactly the relation's verdict. `txV3` derives `ok_i` from exact
comparisons, and the AIR checks that it equals the public bit.

---

## 2. Architecture for D1-N

### 2.1 Verifier pipeline

The pipeline is unchanged from D0a except for `prepD1`:

```
verify(pub, cb, pb):
  guard claimOk cb
  split pb = hintBytes ‖ π
  prep  p ← prepD1 cb (decodeHintD1 hintBytes)   -- native; NearSpecV3 functions only
  stark Stark.verifier Fp Fp8 nearAirV3D1 prm on (Prep.encode p, π)
```

`prepD1 = prepClaim ≫ prepTx ≫ prepBody`:
* `prepClaim` is D0a's, unchanged.
* `prepTx` and `prepBody` are new and described below.

**Hint `HintD1`.** It adds these fields to D0a's `{n, B}`:
* `txs` — the raw `transactions`;
* `newTxs` — the raw `new_transactions`;
* `okbits` — one bit per candidate transaction (step-7 verdict).

`B` keeps only the refund part. The forwarded transaction receipts are native data.

**`prepTx`** runs `processTxs` for steps 1–4 natively:
* `pTxD1` on every raw transaction;
* the hash and the `seen` set;
* the `tx_valid` flag;
* `sizeOk ∧ Ed25519.verify`;
* `txCost`.

That yields the candidate list `C`. For each candidate it emits a public **tx record**:

`(i, signerKeyNibbles, akKeyNibbles, nonce, strict, nonceBound = min(height·10⁶, 2⁶⁴−1), total, deposit, local, ok_i)`

Using `okbits` it then computes:
* the outcome leaves (failed or success);
* the local receipts and their outcomes and refunds;
* the forwarded receipts and their `tryForward` gas simulation;
* the per-link size demands, added to `Prep.fwd`;
* the gas and token prefixes, and `e.compute` (`gas_tx + (n_loc + n − 1)·G < gasLimit`);
* the local receipt ids;
* `m₀ = |tx outcomes| + n_loc`, `tok₀`, the offset `o₀`;
* `merklize` against `slotB2.txRoot` and `H.txRoot`, and the RS body.

**Soundness template (unchanged).** `romSound_hint` (proved, V3-D0-DESIGN §8) needs only the
deterministic step `prepD1 cb h = ok p → HoldsP nearAirV3D1 (pubOf p) tr → ∃ w, RelD1a cb w`.
The extracted witness puts the hint's raw transactions into `w.txs`/`w.newTxs`. The relation
re-parses them, and every native value is literally the spec function's output, so no
collision-resistance argument is needed. That is the same argument as D0a's for RS and the
header chain.

### 2.2 New and changed AIR pieces (`nearAirV3D1` = `nearAirV3` + 2 tables + `rcptV3` variant)

| table | rows (worst at the D1a bounds) | width est. | interactions est. | role |
|---|---|---|---|---|
| **`txV3`** (new) | 16 per op. Ops are tx debits (≤ NT = 4,096) and local credits (≤ NT), so ≤ 131,072 rows (maxLog 17) | ≈ 45 | ≈ 12 | Byte-serial (LSB-first) lanes for: `k.nonce` vs `t.nonce` (strict / monotonic), `amount ≥ total`, `new = amount − total`, `new + locked < 2¹²⁸`, `10¹⁹·storage ≤ new + locked ∨ storage ≤ 770` (the v1 `DEP`-row arithmetic, reused as a pattern), and the local credit (`aft = bef + dep`, `≠ u128::MAX`). `MEM` read/write `(k, t, i, …)` for the account. `AKMEM` read/write for the nonce. Receives the public tx record and `FINAL`. Asserts `ok_i` = AND of the flags. |
| **`akmV3`** (new; `akeyV3` stays for D0a's system-refund keys) | 1 per access-key value byte (≤ A7 bytes) + 9 per write; maxLog 21 | ≈ 25 | ≈ 8 | Decodes `AccessKey` (nonce u64, permission tag 0/1/2/3, `FunctionCallPermission` with Option<u128>, UTF-8 `String`s via a 4-state FSM, `GasKeyInfo`, no trailing bytes). Emits value bytes to `sha_t` (`VAK`), the `AKMEM` initial value, and the 9-byte post value on write. |
| **`rcptV3D1`** (variant of `tableQ`) | unchanged (A1 + `e.compute` keep `n_loc + n ≤ 4,481`) | 263 (+0) | 18 (+0) | Three first-row constraints change from constants to public header reads: receipt index / `MEM` timestamp start `m₀`, running `tok` start `tok₀`, `BODY` offset `o₀`. No new columns. |
| public segments (new) | — | — | — | tx records; tx `KEYNIB` walks; tx/local outcome `DIGEST` + `MPOS` (leaf positions `0..m₀−1`); local ids on `RIDS`; local credit records |

The new tables add `W_eq ≈ 45 + 25 + 8·(⌈12/2⌉ + ⌈8/2⌉) + quotient ≈ 200`, which is about **+0.17 MB**
of proof-size bound at ≈ 864 B per `W_eq`. The tables are tiny next to the six fixed 2²² D0a tables.

### 2.3 Why `rcptV3` cannot be avoided entirely, and why local receipts do not go through it

Local receipt *bytes* are not in the witness. Hashing them in `rcptV3` and comparing the digest
with a native digest would make `Holds ⇒ Rel` depend on SHA-256 collision resistance, which is
not allowed (V3-D0-DESIGN §2.4).

Feeding the bytes in as public `BYTES` would change `rcptV3`'s list logic. Instead, the only
witness-dependent part of a local receipt is the signer account's credit, together with the
`r.success` conditions. Its outcome, refund, id, gas and tokens are native once `ok_i` is
public. So the credit is a `txV3` op, and `rcptV3` needs only the three offset edits.

### 2.4 Access keys: in-AIR decoder rather than a hint or an amendment

`decodeAccessKey = none` makes the relation reject, so a sound AIR must prove the key decodes
whenever it claims a failure past step 6. Three options:
* **(a) `akmV3` with a UTF-8 FSM (recommended).** Rows are bounded by A7 bytes.
* **(b) Hint.** Carry non-FullAccess key values in the hint and decode them natively, matched by
  a public value digest (D0's `VPUB` pattern). The hint then grows by ≤ ≈ 2.1 KB per key, ≈ 8.6 MB
  worst case at NT.
* **(c) Amendment `T4`** (FullAccess keys only, P-D1-7). It drops spec-listed validity classes.

---

## 3. D1a amendments (all PROPOSALS)

`RelD1a B cb w := RelD1 cb w ∧ a1ᴰ¹ ∧ a2ᴰ¹ ∧ canon0fᴰ¹ ∧ a7ᴰ¹ B ∧ a8 ∧ a9ᴰ¹ W0 ∧ a10ᴰ¹ Dp0 ∧ a12 ∧ t1 NT`
goes in a new file `NearSpecV3/ChunkValidationD1a.lean` (additive; `RelD1` is untouched).

### 3.1 Lifted from D0a (restated, not reused verbatim)

The D0a predicates decode with `decodeStateWitness` (the D0 format). That decoder is `false` on
any witness with transactions, so each predicate needs a D1 version:

| id | D1 version | AIR enforcement |
|---|---|---|
| A1 `c.gas_limit` | identical (claim only) | native |
| A2 `w.proof_routing` | same predicate over `decodeStateWitnessD1` | `rcptV3` routing (unchanged) |
| Canon0f | same, with `reads0f` over the D1 witness | sched/codec (unchanged) |
| A7 `w.unfolded ≤ B1` | `unfoldBytes` over the **D1 run's** pre tries (keys incl. `txKeys`) and the native post tries (`applyNewChunkD1(…).trie`, including the transaction writes) | `sizeA7` running sums (unchanged mechanism; they count the extra paths) |
| A8 `c.bw_requests`, A12 `c.layout_wf` | identical (claim only) | native |
| A9 `e.chacha_words ≤ W0` | same count over the D1 run (`applyNewChunkD1` runs `schedStep` as D0 does) | ChaCha lane (unchanged) |
| A10 `w.path_depth ≤ Dp0` | same over the D1 witness | `srcpV3` counter (unchanged) |
| empty main pre-state | already rejected by `checkD1` (same `partialTrie` on `prev_state_root`); test it like the D0a mutant | — |

### 3.2 New

| id | condition | why | honest-chain impact | test obligation |
|---|---|---|---|---|
| **T1** `w.tx_count` | `|transactions| ≤ NT = 4,096` | Bounds native verify time (`NT × 3.4 ms ≈ 14 s` with the compiled spec; ≈ 1–3 s with a fast path). Bounds `txV3` (2¹⁷), `mrkV3` leaves (`NT + 4,481 ≤ 8,577`: `mrkV3` maxLog 19 holds ≤ 8,192 leaves, so either NT ≤ 3,711 or `mrkV3` maxLog 20, ≈ +0.06 G cells) and the hint size. | None. Honest producers stop at `max_tx_gas = 500 Tgas` of transaction gas (`runtime_configs/68.yaml:50`, `chain/chain/src/runtime/mod.rs:1683-1700`), i.e. ≤ 2,241 successful transfers, and at `combined_transactions_size_limit = 4,194,304` B. Invalid transactions are injected only by adversarial producers. | oracle classifier + difftest: a crafted chunk with NT+1 failing transactions is out of D1a |
| T2 `w.new_tx_count` (only if P-D1-5 picks a cap < 16 MiB) | `|new_transactions| ≤ NT` | proof size: `newTxs` sit raw in the hint (RS body is native) | none (same producer limits) | as T1 |
| T3 (only D1-S) `e.sig_count` | signature checks (non-duplicate, `tx_valid = 1`) `≤ NS` | in-AIR gadget table height | NS = 512 is ≈ 23 % of the honest gas maximum: **liveness cost on busy chunks** | as T1 |

Under A1 and `e.compute`, `n_loc + n ≤ 4,481` still holds whenever there is at least one receipt,
because the transaction gas counts toward the compute limit. So `rcptV3`, `sortV3`, `srcpV3` and
both SHA instances keep their D0a heights.

### 3.3 Not proposed

* A cap on gas price, to kill the u128 token-overflow drop: unnecessary, because it is native in D1-N.
* `T4` FullAccess-only keys (§2.4 (c)).

### 3.4 Tier and challenge (PROPOSAL)

* `Tier.d1a` with `RelTier .d1a := RelD1a B1`.
* `rel_mono` extended through `relD1a_relD1 : RelD1a B cb w → RelD1 cb w`.
* `challengeParamsChunk .d1a` with the proof cap of P-D1-5.
* A tier entry in `near-chunk-v3` with the D1 classes, `rank` between D0 and D1 (or D1a
  replacing D1 for succinct candidates).

`ChallengeChunkV3.lean` is part of the draft's pinned tree, so this is a draft revision, done
in a versioned successor.

D0a ⊂ D1a (needed so a D1a prover also covers the `d0-*` classes) is **tested, not proved**.
D0 ⊂ D1 is proved: `NearSpecV3.relD0_relD1 : RelD0 cb w → RelD1 cb w`
(`spec/lean/v3/NearSpecV3/D0SubD1.lean`; the D1 run on an empty transaction list matches D0). Optionally prove `RelD0a B cb w ∧ txs = [] → RelD1a B cb w` for the trivial
transaction list; this is a contained proof about `processTxs ctx st [] = ok st`.

---

## 4. Ed25519: native vs in-AIR

### 4.1 Native (D1-N)

The verifier calls `NearSpecV3.Ed25519.verify` (a trusted spec function).
* **Measured** cost (spec doc §6): 3.4 ms per call compiled. The Rust reference of the same
  operation sequence takes 117 µs (spike, single core).
* A kernel-proved `@[csimp]` fast path is allowed under decision §10.1 of the D0 design. Two kinds:
  * **Same schedule, faster arithmetic** (`UInt64` limbs, proved equal to the `Nat` operations):
    est. 0.3–1 ms. Lean effort about 2–4 k LOC, and no group law is needed.
  * **A different schedule** (comb or window): needs the same group-law proofs as D1-S optimized.
    Not recommended.

Verify-time budget: the draft allows 60 s. The D0 design targets ≤ 1.5 s typical and ≤ 10 s
worst:
* typical D1 chunks (≈ 10–100 transactions): 0.03–0.34 s with the plain spec function;
* worst case at NT: 14 s, or about 1–3 s with the fast path.

### 4.2 In-AIR options (D1-S)

The security profile (`validity-classical-128`, ROM, transparent; allowed assumptions SHA-256 CR
and ROM Fiat–Shamir) allows any IOP whose round-by-round soundness is proved. The pure-AIR path
reuses everything:
* L2/L3 `stark_romSound_full` with buses and public segments;
* L7 sizes;
* L8 prover.

**Sumcheck / GKR (e.g. for batched field multiplications).** It needs a new challenge round with
challenge-dependent claims: a new `RbrWith` stage, sumcheck bad-event bounds (`deg/|Fp8|` per
round), and threading through `Shape`/`Early`/`Msg4`. It also needs a new Rust prover/verifier
and Lean verifier model, so it is a protocol version `np-udr-stark-v3`. The D0 design priced a
single Freivalds round at 3–5 k LOC of L3 work (§2.5); a GKR layer is several times that.
**Allowed, but not for D1.** Revisit it for D3 (WASM), where the arithmetic volume is far larger.

**Batch verification** (a random linear combination of the equations) is *not* equivalent to
nearcore's cofactorless per-signature check:
* torsion components can cancel;
* failing signatures must be proved failing, not just batched.

Rejected.

**Pure AIR.** One field multiplication `r ≡ a·b mod 2²⁵⁵−19` per row (`fmulV3`):
* 32 × 8-bit limbs for `a`, `b`, `r`;
* `t_k = Σ_{i+j=k} a_i b_j + 38·Σ_{i+j=k+32} a_i b_j`;
* `t_k + c_{k−1} = r_k + 2⁸c_k`, with `c_{−1} := 38·c_31`;
* limbs `< 2⁸`, carries `< 2²¹` (range lookups);
* operands wired by a value bus.

All 32 equations have degree 2. Estimated cost per row: ≈ 160 base columns, ≈ 67 interactions
(≈ 34 Fp8 aux columns at g = 2), so `W_eq ≈ 450`.

Also needed:
* `sha512V3`: 64-bit words. It is a new table family (L5 is SHA-256-only), est. `W_eq ≈ 1,100`,
  ≈ 25–40 k W-cells per block. A transaction signature hashes exactly one block: 32 + 32 + 32 = 96
  bytes, plus padding, is ≤ 128.
* `edctlV3`: point-operation control, scalar bits and nibbles, `k = h mod ℓ` as a linear integer
  identity, `s < ℓ`, canonical `y`, the final 32-byte compare. Est. `W_eq ≈ 200`.

### 4.3 Prototype (measured): `examples/d1-air-spike/ed25519-cost`

The spike is a dependency-free Rust program. It runs two schedules on every signature vector in
`oracle/fixtures/v3/ed25519/*.jsonl` (7,265 vectors; nearcore's `verify_raw` verdicts).
Every field operation goes through counted reference arithmetic. The first 200 vectors'
multiplications (1,355,312 products) also go through the limb gadget, which checks each equation
over ℤ, in BabyBear and against the reference result.

| | faithful (spec sequence) | optimized |
|---|---|---|
| agree with nearcore | **7,265 / 7,265** | **7,265 / 7,265** |
| var × var muls per verify (mean / max) | 6,122 / **7,469** | 2,655 / **3,095** |
| const muls (mean) | 1,293 (`P.T·2d`, `Z·2`; ≈ half are linear) | 16 |
| linear ops (mean) | 5,172 | 2,565 |
| point additions / doublings (mean) | 646 / 0 | 121 / 217 |
| SHA-512 blocks (mean over vectors with arbitrary messages; 1 for transactions) | 1.83 | 1.83 |
| Rust reference time per verify (1 core, plain u64 limbs) | 117 µs | 59 µs |

Gadget bounds:
* **measured** over all products, and **worst case** with every input limb at the lazy-addition
  maximum 2⁹ − 1: `max t_k = 307,861,659 ≈ 2^28.20`, which is below `p_BB/2 = 1,006,632,960`
  (≈ 2^29.9), so a BabyBear identity implies the integer identity;
* `max carry = 1,207,470 ≈ 2^20.2`, giving 21-bit carry range checks.

SHA-512 was checked on 503/503 `hashlib` vectors.

* **"Faithful"** replays exactly `F.sqrtRatio`, `F.pow`, `smulAux 256`, `Point.add` and `encode`
  from `Ed25519.lean`. An AIR that does the same proves equality to the spec *step by step*. It
  needs no group law, no primality of p, and no uniqueness of square roots: these are exactly the
  facts the spec says are "not proved". This is the formally cheap in-AIR route.
* **"Optimized"** consists of:
  * a hinted root with a non-square witness via `√−1`;
  * a 64 × 16 fixed-base comb with affine-Niels madds;
  * a 4-bit window for `[k](−A)`;
  * dedicated doubling;
  * a hinted `Z⁻¹`.

  It produces the same *affine* points through different projective representations, so proving
  it equal to the spec needs Edwards associativity and doubling-formula equivalence over 𝔽_p.
  That is hard without Mathlib's `ring`/`field_simp`, which `ZkFormal` does not use.

### 4.4 In-AIR cost at the bounds (estimated)

Throughput model, calibrated on D0a:
* **measured** 263–312 s for ≈ 2.47–2.82 G main cells at 2²², which is ≈ 3.5–4 G
  W-eq cells including aux and quotient (`docs/logs/v3-prover-perf-2026-10.md`);
* so ≈ **75 s per G W-eq cells** (± 30 %);
* memory ≈ 12.6 GiB cgroup peak.

| | faithful | optimized |
|---|---|---|
| mul-equivalents per signature | ≈ 7,900 | ≈ 3,100 |
| W-eq cells per signature (`× 450`, + SHA-512 + control) | ≈ 3.6 M | ≈ 1.45 M |
| signatures per 2²² `fmulV3` instance | ≈ 530 | ≈ 1,350 |
| prove time per signature | ≈ 0.27 s | ≈ 0.11 s |
| at 500 signatures | +135 s → ≈ 400–450 s on this host | +55 s |
| cloud 8 vCPU (×1.3–1.6) | **≈ 520–720 s: at or over the 600 s cap** | ≈ 430–580 s |
| memory | ≈ +4–7 GB of trace/LDE at 2²²: **over 16 GiB** unless the prover's block budget is reworked | similar |
| proof-size bound | +≈ 1.5 MB (`fmulV3` 0.39 + `sha512V3` 0.95 + control 0.17) | same |

So D1-S at more than about 300 signatures needs two prover changes first. The D0a scheduler and
`rcpt` tables, which are fixed at 2²² today, must be padded only to their honest heights. And the
memory schedule must be reworked.

Note that A7 at `B1 = 2 MB` already limits real mainnet-trie chunks to roughly 150–250 transfers
(§5.4). At that size D1-S faithful costs about +40–70 s, which is feasible. The binding cases are
synthetic chunks on small tries, so `NS` should be set where the table fits.

---

## 5. Cost model for D1-N

### 5.1 Fixture measurements (**measured**, `examples/d1-air-spike/measure_d1_fixtures.py`, 188 public-d1 cases, all accepted by the independent Python D1 checker)

| quantity | max per case | sum over 188 |
|---|---:|---:|
| transactions | 13 | 262 |
| signature checks (non-duplicate, not expired) | 11 | 248 |
| candidates (reach step 5: walks + `txV3` ops) | 9 | 225 |
| successes | 5 | 175 |
| local receipts | 2 | 29 |
| new transactions | 13 | 270 |
| incoming receipts | 805 | 3,043 |
| trie keys read (main transition) | 18 | 1,712 |
| of which transaction keys | 10 | 328 |
| unfolded pre-trie bytes (A7 pre term), all keys | 3,389 | 397,061 |
| marginal of the transaction keys | 2,191 | 68,802 (mean **353 B / candidate**, max 1,191) |
| witness bytes | 116,494 | 1,162,967 |

All public fixtures are tiny. At these sizes D1-N's added rows are negligible: ≤ 9 ops × 16 rows
in `txV3`, ≤ 10 extra walks of ≤ 200 rows each, and < 1 KB of extra A7 bytes. The STARK shape is
D0a's, dominated by the six fixed 2²² tables.

**Expected prove time on the public-d1 fixtures: ≈ D0a's 263–312 s plus < 5 s.**

### 5.2 Rows at the D1a bounds (NT = 4,096; A1: receipts ≤ 4,481; B1 = 2 MB)

| table | D0a worst | D1a worst | maxLog |
|---|---|---|---|
| `walkV3` | 1.8 M (receipts, access keys of refunds) | + NT × ≤ 330 (signer ≤ 130 + access key ≤ 198 nibble steps) = +1.35 M → ≈ 3.15 M | 22 (fits) |
| `txV3` | — | 16 × (NT debits + ≤ NT local credits) ≤ 131,072 | 17 |
| `akmV3` | — | ≤ A7 value bytes + 9/write ≤ ≈ 2.04 M | 21 |
| `acctV3` | 16 × 4,481 | + 16 × NT signer slots (bounded with receivers, ≤ 16 × 8,577) ≈ 137 k | 19 (fits) |
| `mrkV3` | 64 × 4,481 | 64 × (NT + 4,481) ≈ 549 k | **20** (or NT ≤ 3,711 at 19) |
| `sortV3`, `rcptV3`, `srcpV3`, SHA ×2, trie, scheduler | unchanged | unchanged (A1 + `e.compute`, A7, A9, A10) | unchanged |

Added committed cells at the bound: `walkV3` already pads to 2²² in the worst case;
`txV3` + `akmV3` + `mrkV3` ≈ 2¹⁷·45 + 2²¹·25 + 2²⁰·60 ≈ 0.12 G base cells.

**Prove time ≈ D0a + ≈ 10–20 s (est.)**, memory unchanged. Proof size is D0a's (5.3–5.7 MB
measured) plus 0.1–0.2 MB plus hint bytes (≈ 0.3 KB per transaction and new transaction).

### 5.3 Against the near-chunk-v3 limits

| limit | D0a measured | D1-N est. at bounds | D1-S faithful est. at NS = 512 |
|---|---|---|---|
| prove 600 s (8 vCPU) | 263–312 s (cloud est. 360–500 s) | 275–335 s (cloud 380–530 s) | 400–450 s (cloud 520–720 s) ✗ risk |
| RAM 16 GiB | ≤ 12.6 GiB | ≈ 12.7 GiB | > 16 GiB without rework ✗ |
| proof 64 MiB (draft) / 16 MiB (P-D1-5) | 5.3–5.7 MB (bound 6.44 MB + hint) | bound ≈ 6.6 MB + hint ≤ 3.7 MB ≈ 10.3 MB | bound ≈ 8.1 MB + hint |
| verify 60 s | 2.6–3.1 s (Lean) | + NT × 3.4 ms ≤ 14 s (fast path: ≈ 1–3 s) | ≈ 3.5 s |

### 5.4 Liveness on mainnet-sized tries (estimated)

* Each transaction reads two keys under different top-level columns (`[0]…` and `[2]…`).
* For N random keys in a 16-ary trie of M leaves, roughly `log₁₆(M) − log₁₆(2N)` branch levels per
  key are unshared, at ≈ 530 B per full branch.
* At M ≈ 10⁸ this is ≈ 2.5–3 KB per key, ≈ 11 KB per transaction with the native post term,
  against the 353 B measured on oracle tries.
* So `B1 = 2 MB` admits ≈ 150–250 transfers per chunk (fewer with many incoming receipts).

This inherits D0a's liveness envelope (B0 binds receipts the same way). It is a **domain**
statement: chunks above it are unprovable in D1a, never wrongly accepted.

Raising B1 costs SHA rows (1.25 rows/B on `sha_t`, already at 2²² in the worst case), i.e. a third
SHA instance at about +2.3 G cells, ≈ +170 s. That is a separate user decision, best taken
together with a mainnet replay measurement (HANDOVER §8).

---

## 6. Formal effort

### 6.1 What the D0a certificate gives for free

The D0a certificate is structured per table:
* `TableLocal → ∃ v, Wf v ∧ TableTraffic`;
* trace-free link: views + SHA facts + balance ⇒ `GoodV3`;
* `FactorSound`: `prepD0 = ok p ∧ GoodV3 ⇒ RelD0a`;
* render for completeness.

Every **table whose definition is unchanged** keeps its view and render theorems verbatim
(statements are per table): both SHA instances, the trie tables (`nodeV3`, `headV3`, `valV3`,
`walkV3`, `uniqV3`, `upsV3`, `sizeA7`), ChaCha ×3, scheduler ×5, `acctV3`, `akeyV3`, `bndV3`,
`srcpV3`, `qvV3`, `mrkV3`, `sortV3`. That is 23 of 25 tables.

Also reusable:
* `romSound_hint`, `stream_eq_of_count`;
* the public-bus protocol (`PubSeg`, `HoldsP`), `Size.*`;
* the A7/A9/A10 machinery, `ExtractV3`/`CompleteV3` *patterns*;
* `NearAirCheck` style kernel checks.

### 6.2 New obligations (D1-N)

| module group | content | est. Lean lines | risk |
|---|---|---|---|
| spec (`ChunkValidationD1a`, `PrepD1`/`hintOfD1`, `Tier.d1a`) | P-D1-1, P-D1-6; executable checks + iff lemmas + `relD1a_relD1` | 2–4 k | low (governance) |
| `FactorSoundD1` / `FactorCompleteD1` | `processTxs` split into native steps 1–4 (equal to the spec by `rfl`/definitional unfolding) and AIR steps 5–8. `applyReceiptsC` with local receipts first. The D1 witness codec (`pTxD1` prefix stability and round trip for `witnessOfV3D1`; `decodeStateWitnessD1 ∘ encode`). `MEM`/`AKMEM` interleaving lemmas (`find_set_ne` for the two new key families) | 15–30 k | **high**: the largest new semantic proof, like D0a's `V1 factor` |
| `txV3` view + render | byte-serial comparator lanes, timestamps, flag AND | 6–12 k | medium (v1 `DEP`-row lemmas are a template) |
| `akmV3` view + render | access-key decoder incl. the UTF-8 FSM, equal to `decodeAccessKey`/`utf8Ok` | 6–12 k | medium |
| `rcptV3D1` | three first-row constraints: re-prove only the first-row lemmas and the affected traffic; the other ≈ 900 constraint proofs are reused if columns and constraint indices are kept | 3–8 k | medium (Rcpt is 70 k lines; edits must stay local) |
| public segments D1 | `bindPreparedD1` (tx records, `KEYNIB`, `DIGEST`/`MPOS` leaves, `RIDS`, credits), `pubFit`, size | 3–6 k | low-medium |
| link + assembly | `GoodD1`, `LinkD1`, `ExtractD1Stmt`, `CompleteD1Stmt`, heights (`FitsD1`), `nearAirV3D1` wf/npOk/size, `nearV3D1_admission_final : AdmissionStatement (challengeParamsChunk .d1a) …` | 10–20 k | medium |
| **total D1-N** | | **≈ 45–90 k** (≈ 10–20 % of D0a's ≈ 450 k lines in `NearV3/`) | |
| D1-S faithful extra | `fmulV3` (integer identity ⇒ mod-p, ranges), `sha512V3` (an L5 analogue, 64-bit words), replay of `powAux`/`smulAux`/`Point.add`/`encode` as a trace relation | +40–70 k | high |
| D1-S optimized extra | + Edwards group law, doubling equivalence, unique square roots, Fermat via a Pratt certificate | +30–60 k on top | **very high** (no Mathlib) |

Calibration: the D0 design estimated D0a at 50–80 k lines; `NearV3/` is now ≈ 450 k lines in
4,670 files (much of it superseded candidate variants that remain in the tree). D1-N reuses the
mature per-table framework, so a 2–3× over-run is assumed; that is already in the ranges above.

### 6.3 Judge budgets

The judge budgets (`runners/formal-checker/src/pipeline.rs` `Limits::default`) are:
* 4 h serial elaboration in total, 1 h per module;
* recheck: 2 h per module run, 4 h per rechecker.

D0a's packaged closure is 3,964 modules, 8,734 s single-core: **2.43 h of 4 h**. lean4lean takes
≈ 1.6 h of its 4 h.

**Projection for a combined D1a certificate.** The D0a closure stays in, minus ≈ 5–10 % of D0a-only
assembly. Add ≈ 600–1,400 new modules at D0a's mean of 2.2 s per module, plus a few render
modules of 50–200 s:

**≈ 10,000–12,500 s single-core (2.8–3.5 h) of 14,400 s.** It fits, but with little margin, and
a judge VM slower than this host would erase it.

lean4lean: ≈ 1.9–2.3 h of 4 h (fits).

**Module-structure plan to stay within budget:**
1. **Apply the known D0a levers first** (lane F below). They are pure proof refactors with
   identical statements and benefit D0a too:
   * `Render.Codec{EndInt,RecInt,Header}` = 3,285 s (38 % of the closure): pre-evaluated row-table
     facts, a per-constraint `first` cascade, per-case modules. Est. −1,500 to −2,500 s.
   * a g = 2-only `NearAirCheck`: −35 s.
2. **New code in small modules.** One module per `txV3`/`akmV3` constraint family and per
   `FactorD1` step (as `Render.Ups.*` is split), so no module exceeds about 100 s and the judge
   could parallelise if ever allowed.
3. **No `decide +kernel` over real cases in the certificate closure.** `RealCaseD1` (266 s, 12 GB)
   stays in `NearSpecV3.Examples`. Keep kernel checks to the `nearAirV3D1` shape facts, as
   `NearAirCheck` does.
4. **Import hygiene from day one.** Run `ClosureDeps.lean` / `judge-time.py` (`zk-formal/scripts/`)
   at every merge. A D1 module must import `*Core` splits, never the D0a assembly roots it
   replaces.
5. **Do not re-prove reused tables.** Phrase `LinkD1` over the existing per-table `Wf`/traffic
   statements; only `GoodD1` is new.
6. **Keep the D0a certificate separate and frozen.** A D1a candidate is a separate artifact (P-D1-1
   tier), so D0a's admission is unaffected whatever happens to D1a's budget.

### 6.4 Separate tier proof vs one combined AIR

**Recommendation: one combined AIR `nearAirV3D1` (a superset of `nearAirV3`), admitted under a new
admission statement for `challengeParamsChunk .d1a`.**

Reasons:
* The D1 main transition is the D0 transition with a prefix (transactions, local receipts). A D0
  chunk is the D1 run with an empty transaction list, so the D1 tables are simply empty and
  `rcptV3D1`'s offsets are 0, 0, 4.
* Two separate AIRs would double the prover, conformance and size-bound surface, and a D1a-only
  AIR would still have to contain every D0a table.
* Completeness on the `d0-*` classes of the D1 tier comes for free, given D0a ⊂ D1a (tested).
* The D0a certificate and artifact stay frozen and admitted. `nearAirV3` is not edited. The new AIR
  is a new constant built from the same table values (`nearTablesFull` with `tableQ` replaced and
  two tables appended), so all 23 unchanged tables' theorems apply by `rfl`.

---

## 7. Plan (≤ 4 parallel lanes)

**Phase 0 — decisions (user): P-D1-1 … P-D1-6.** Lanes A, F and the spike work below do not depend
on them; everything else waits.

**Phase 1 — foundation (4 lanes, ≈ 1 week)**

| lane | scope | milestone |
|---|---|---|
| **A `v3-d1-spec`** | `ChunkValidationD1a.lean` (lifted A-predicates, T1), `relD1a_iff`, `relD1a_relD1`; `spec_check_v3_d1a.py`; D1a classifier + mutants (new crate dir, `oracle/v3` untouched); difftest on public-d1 and the D1 corpus (53,048 cases); D0a ⊂ D1a test; `prepD1` + `hintOfD1` (location per P-D1-6) with a native-vs-relation agreement test | **M1**: 0 disagreements; `RelD1a` kernel-evaluated on `RealCaseD1`-style cases |
| **B `v3-d1-tables`** | Lean `txV3`, `akmV3`, `rcptV3D1` table values; `nearAirV3D1`; kernel `wf`/`npOk`/`weq`; `sizeMaxAligned` bound; public segment layout | **M2**: `nearAirV3D1` exported, size bound ≤ the P-D1-5 cap |
| **C `v3-d1-prover`** | Rust: `prepD1` mirror (difftested against Lean), `txV3`/`akmV3` trace generation, `rcptV3D1` offsets, public tape; `npudr v3prove --tier d1a` (D0a path untouched); `--check-only` on 188 public-d1 + 81 D0a fixtures | **M3**: all buses balance, constraints hold on 269 fixtures; first real D1a proof |
| **F `v3-d1-budget`** | codec_int refactor and g = 2 `NearAirCheck` (D0a statement fingerprints unchanged, `TypeHashes`); `judge-time.py` baseline; Ed25519 `@[csimp]` fast path (same schedule, limb arithmetic) and native verify-time measurement | **M4**: closure ≤ 7,000 s single-core; `Ed25519.verify` fast path ≤ 1 ms |

**Phase 2 — formal core (4 lanes, ≈ 2–3 weeks)**

| lane | scope | milestone |
|---|---|---|
| **D `v3-d1-factor`** | `GoodD1`, `FactorSoundD1`, `FactorCompleteD1`, D1 witness codec, `MEM`/`AKMEM` trie lemmas | **M5**: both proved, no `sorry` |
| **E `v3-d1-views`** | `txV3`/`akmV3`/`rcptV3D1` views + `LinkD1` ⇒ `ExtractD1Stmt` | **M6**: soundness `ExtractD1Stmt` proved |
| **G `v3-d1-render`** | renders + `CompleteD1Stmt`, `FitsD1` (heights at the D1a bounds) | **M7**: completeness proved |
| C (continued) | negatives, conformance (`run-v2.d`), Lean-verifier acceptance, timing at the bounds (synthetic NT-sized fixtures) | **M8**: Lean `np-lean-verify-v3d1` accepts; 14/14 negatives |

**Phase 3 — assembly (2–3 lanes, ≈ 1 week).** `nearV3D1_admission_final`, guarded axiom audit,
judge-style timing of the packaged closure, rechecks (leanchecker / nanoda / lean4lean),
packaging, conformance, live run on `near-chunk-v3` once the tier is signed. **M9**: admitted in
the local judge.

**Phase 4 (optional, user decision) — D1-S faithful.** `fmulV3` + `sha512V3` + `edctlV3`,
replacing the native `valid` bit with an AIR-derived one. The prerequisite is prover rework:
honest heights instead of fixed 2²² for the scheduler and `rcpt` tables, and the memory schedule.

### Risks

1. **Elaboration budget** (§6.3): the combined closure is projected at 2.8–3.5 h of 4 h.
   Mitigation: lane F first, module discipline, a separate D1a artifact.
2. **`FactorD1` volume**: the transaction/receipt interleaving and the two memory chains.
   Mitigation: the native split keeps steps 1–4 and all outcome/receipt construction out of the
   proof.
3. **`rcptV3D1` edits ripple** through the Rcpt proofs. Mitigation: no new columns, constraint
   indices kept, only first-row lemmas re-proved; measure the dependents before committing to it.
4. **Governance**: P-D1-2 (native signatures) may be refused. Fallback: D1-S faithful at NS ≈ 512,
   with prover rework first (§4.4), +6–8 weeks.
5. **Liveness on mainnet**: B1 = 2 MB admits ≈ 150–250 transfers per chunk on mainnet-sized tries
   (§5.4); needs mainnet replay data.
6. **Verify time at NT without the fast path**: ≈ 14 s, over the D0 design's ≤ 10 s worst-case
   target. Lane F's fast path, or NT = 2,048, fixes it.
7. Spec transcription of D1 is tested, not proved, against nearcore (53,048-case difftest). This
   is the same standing as D0.

---

## 8. Spike artifacts in this lane

* `examples/d1-air-spike/ed25519-cost/` — standalone Rust crate, no dependencies, not a
  workspace member. Run: `cargo run --release --offline -- oracle/fixtures/v3/ed25519 --gadget 200`.
  It exits non-zero on any disagreement with nearcore or any gadget violation.
* `examples/d1-air-spike/measure_d1_fixtures.py` — the §5.1 table:
  `python3 examples/d1-air-spike/measure_d1_fixtures.py oracle/fixtures/v3/public-d1/d1/*`.

No existing AIR, certificate, spec relation, challenge, oracle or prover path was modified.
