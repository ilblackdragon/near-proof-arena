# `near/pv86/chunk-validation/v0` — domain D1: + Transfer transactions

Companion to `spec/near-chunk-validation-v0.md` (the statement, §1–§5, and the domain
ladder, §6) and `spec/claim-v3.md` (formats, unchanged). This document states domain D1
exactly: what a nearcore 2.13.4 chunk validator (`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`,
protocol version 86) does with transactions, the Ed25519 verification it relies on, the
conditions `InD1`, and how each part is formalized and tested. Every `file:line` is relative
to the pinned nearcore checkout (`/data/illia/nearproof-deps/nearcore`) unless it names a
third-party crate (`~/.cargo/registry/src/index.crates.io-*/<crate>-<ver>/`).

> **Rel_D1(c, w) := Rel(c, w) ∧ InD1(c, w)**, with the same `claim.bin` / `witness.bin` as
> every other rung. `InD0 ⊂ InD1`: every D0 condition except `w.no_txs` and `c.no_tx_flags`
> is kept, and the new conditions hold trivially when there are no transactions. So a D1
> prover validates every D0 chunk, and `Rel_D1 ⇒ Rel`.

## 1. Where transactions enter chunk validation

A `ChunkStateWitness` carries two transaction lists (`state_witness.rs:103-166`):

* `transactions` — the transactions of the **last new chunk** of the shard (the chunk the
  main transition applies, in block B2);
* `new_transactions` — the transactions of the **endorsed chunk** itself (applied by the
  *next* chunk's validation).

| step | nearcore | what is checked |
|---|---|---|
| P2 | `chunk_validation.rs:323-341` | every `new_transactions[i]` passes `ValidatedTransaction::check_valid_for_config` (`transaction.rs:315-354`): V1 needs GasKeys (PV 85 ✓), `Strict` nonce needs StrictNonce (PV 85 ✓), PQ keys need PostQuantumSignatures (PV 85 ✓), `wire_size ≤ max_transaction_size = 1 572 864` (`runtime_configs/69.yaml:3`). **No signature, nonce, key or balance check.** |
| P6 | `chunk_validation.rs:368-380` | `merklize(transactions).root` = `tx_root` of the last new chunk's header (leaf = `sha256(borsh(SignedTransaction))`) |
| P7 | `chunk_validation.rs:382-401` | per `transactions[i]`: `check_transaction_validity_period(header(B2.prev), tx.block_hash)` (`chain/chain/src/store/utils.rs:56-75`; `transaction_validity_period` of genesis) → the **trusted** flags `c.tx_valid` (claim-v3 T13) |
| main transition | `Runtime::apply` step 2 (`runtime/runtime/src/lib.rs:1797`) | `process_transactions` (`lib.rs:1882-2279`), §3 |
| receipts | `process_receipts` (`lib.rs:2658-2721`) | local receipts first (`process_local_receipts`, `lib.rs:2357-2433`), then delayed, then incoming |
| final | `chunk_validation.rs:763-766`, `validate.rs:233-260` | `tx_root = merklize(new_transactions).root`; Reed–Solomon body = `borsh((new_transactions, outgoing_receipts))` |

`RelaxedChunkValidation` (deprecated, always on at PV ≥ 74, `core/primitives-core/src/version.rs:532`)
means an invalid transaction in a chunk never makes the chunk invalid: it yields a failed
outcome (`InvalidTxGenerateOutcomes`, PV 83, `version.rs:549`) and no state change.

## 2. Ed25519 as nearcore verifies it

`ValidatedTransaction::new` (`transaction.rs:288-310`) verifies
`signed_tx.signature.verify(tx_hash, public_key)` with `tx_hash = sha256(borsh(Transaction))`
(`transaction.rs:139-145, 465-469`) — the signed message is the 32-byte hash, not the
transaction bytes. `near_crypto::Signature::verify` for an ED25519 pair
(`core/crypto/src/signature.rs:1086-1093`):

```
match ed25519_dalek::VerifyingKey::from_bytes(&pk) { Err(_) => false, Ok(k) => k.verify(msg, &sig).is_ok() }
```

Dependency versions in nearcore's lock: `ed25519-dalek 2.2.0`, `curve25519-dalek 4.1.3`
(`Cargo.toml:192, 202`). Feature set of the node build (from `cargo tree -e features` on the
oracle, which links the whole node): ed25519-dalek {`hazmat`, `rand_core`}, curve25519-dalek
{`alloc`, `digest`, `precomputed-tables`} — in particular **not** `legacy_compatibility`;
nearcore's own manifests never enable it. The resulting predicate (`Ed25519.verify pk sig msg`):

| rule | source | semantics |
|---|---|---|
| signature encoding | `core/crypto/src/signature.rs:1168-1183` | borsh: tag 0 + 64 bytes; `sig[63] & 0xE0 ≠ 0` ⇒ **decode error** (the whole witness fails to decode) |
| `A = decompress(pk)` | ed25519-dalek-2.2.0 `src/verifying.rs:165-174`; curve25519-dalek-4.1.3 `src/edwards.rs:194-241`, `src/field.rs` (`from_bytes`, `sqrt_ratio_i`) | `y` = little-endian `pk` with bit 255 cleared, reduced mod p (**non-canonical `y ≥ p` accepted**); `x` = the non-negative root of `(y²−1)/(d·y²+1)` (fails iff not a square), negated iff `pk[31] ≥ 128` (`x = 0` with the sign bit set is **accepted**) |
| `s` | `src/signature.rs:89-96, 151-163` | `s = LE(sig[32..64])` must be `< ℓ` (`Scalar::from_canonical_bytes`) |
| challenge | `src/verifying.rs:494-560` (`RCompute`) | `k = SHA-512(R_bytes ‖ pk_bytes ‖ msg) mod ℓ`, with the **original** 32 bytes of `R` and of `pk` |
| equation | `src/verifying.rs:201-218` (`raw_verify`), `:563-567` (`Verifier::verify`) | accept iff `compress([s]B − [k]A) = R_bytes` byte-for-byte — cofactorless; `R` is never decompressed (a non-canonical `R` never verifies); small-order and mixed-order `A` and `R` are **accepted** (this is `verify`, not `verify_strict`) |

So nearcore's check is neither RFC 8032 §5.1.7 "strict" (RFC rejects non-canonical `y` and
`x = 0` with sign 1 at decoding, and permits the cofactored equation) nor libsodium's
(which rejects small-order keys and `R`). The Lean and Python implementations transcribe
the table; the vector evidence is in §6.

## 3. `process_transactions` in D1 (exact semantics)

Inputs: the last new chunk's transactions `T₀ … T_{n−1}` (witness order), the trusted flags
`c.tx_valid`, block context of B2 (`height`, `gas_price = header(B2.prev).next_gas_price`).
For each `T` in order (`lib.rs:1979-2266`):

1. **Duplicate hash** (`UniqueChunkTransactions`, PV 85, `lib.rs:1981-1992`): if the hash of
   `T` (of its `Transaction`, not of the signature) was already seen in this chunk, `T` is
   skipped entirely — no outcome. Expired and invalid transactions count as seen. Hence a
   valid transaction preceded by the same `Transaction` with a corrupted signature is
   skipped, and only the failed outcome of the first copy is recorded.
2. **Expired** (`tx_valid = 0`) ⇒ failed outcome (`lib.rs:1902-1905, 1994-2003`).
3. **`validate_transaction`** (`verifier.rs:109-121`): for a single `Transfer` the action
   checks pass (`action_validation.rs:62-125, 142`); `check_valid_for_config` (size, §1);
   `Ed25519.verify(pk, sig, tx_hash)`. Failure ⇒ failed outcome.
4. **`tx_cost`** (`runtime/runtime/src/config.rs:400-479`) for one Transfer to receiver `r`:
   `burnt_gas = new_action_receipt.send + transfer_send_fee(r) + sig_verification(ED25519)`
   (`cost.rs:750-777`: + `create_account.send` for ETH-implicit / deterministic `r`, + both
   `create_account.send` and `add_full_access_key.send` for NEAR-implicit `r`; ED25519
   verification costs 0, `parameter_table.rs:434-441`); `remaining_gas =
   new_action_receipt.exec + transfer_exec_fee(r)` (`cost.rs:722-748`);
   `receipt_gas_price = max(gas_price, min_gas_purchase_price = 10⁹)` (`runtime_configs/85.yaml:41`);
   `total = gas_price·burnt_gas + receipt_gas_price·remaining_gas + deposit`. Any u64/u128
   overflow ⇒ failed outcome (`CostOverflow`, `lib.rs:2010-2028`).
5. **Signer account** (`lib.rs:2030-2049`): absent ⇒ failed outcome (`InvalidSignerId`) —
   this includes a signer that lives on another shard (the account is looked up in *this*
   shard's trie). A storage error is surfaced here only (the value was prefetched for every
   non-expired transaction, `lib.rs:1922-1977`, but an error is returned only when a
   transaction reaches this step).
6. **Access key** `(signer, pk)` (`lib.rs:2050-2076`): absent ⇒ failed outcome
   (`AccessKeyNotFound`).
7. **`verify_and_charge_tx_ephemeral`** (`verifier.rs:272-378`), all failures ⇒ failed outcome:
   gas key (`GasKeyFullAccess`/`GasKeyFunctionCall`) used without a gas-key nonce ⇒ fail
   (`:283-291`); nonce: Monotonic `tx_nonce > ak.nonce`, Strict `tx_nonce = ak.nonce + 1`
   (checked), and `tx_nonce < height·10⁶` (saturating, `:212-238`); `amount ≥ total`; a
   function-call key with an allowance needs `allowance ≥ total` (`:240-270`); storage stake
   with the new amount (`check_storage_stake`, `:48-86`; zero-balance accounts ≤ 770 bytes
   are exempt); **a function-call key always fails for a Transfer** (`RequiresFullAccess`,
   `verify_function_call_permission`, `:167-210`). At PV 86 nothing is written on failure
   (`FixAccessKeyAllowanceCharging`, PV 83, `:319-325`).
8. **Success** (`lib.rs:2146-2197, 2238-2266`): receipt `Receipt::from_tx` (`receipt.rs:344-365`,
   predecessor = signer, signer key, gas price = `receipt_gas_price`, the Transfer action) with
   id `sha256(tx_hash ‖ u64 height ‖ u64 0)` (`utils.rs:270-275, 328-335`); a **local receipt**
   iff `receiver = signer` (`lib.rs:2187-2195`), otherwise `ReceiptSink::forward_or_buffer_receipt`
   (congestion gas = `new_action_receipt.exec + transfer_exec_fee(r)`). Outcome
   `SuccessReceiptId(rid)`, `receipt_ids = [rid]`, `gas_burnt = burnt_gas`,
   `tokens_burnt = gas_price·burnt_gas`, executor = signer. If `tx_burnt_amount + burnt`
   overflows u128 the outcome and the state change are dropped (the receipt was already
   emitted; `lib.rs:2212-2236`). Chunk gas/compute += `burnt_gas` (u64 overflow panics).
   Writes: the signer's account amount (`amount − total`) and the access key's nonce
   (`= tx_nonce`), visible to later transactions of the chunk.

A **failed outcome** is `{id: tx_hash, receipt_ids: [], gas 0, tokens 0, executor: signer,
status: Failure(InvalidTxError)}` (`transaction.rs:723-744`), and the outcome root hashes
`PartialExecutionStatus::Failure` without the error (`transaction.rs:597-612`): **every
failure reason has the same effect** on the chunk. Outcomes are ordered: transactions, then
local receipts, then incoming receipts.

**Which access keys apply to a Transfer?** Only a `FullAccess` key (with a plain nonce). A
`FunctionCall` key always fails (`RequiresFullAccess`, or earlier on its nonce / allowance);
a gas key fails at once for a transaction without a gas-key nonce, and a transaction with a
gas-key nonce (`TransactionNonce::GasKeyNonce`, V1) takes the gas-key path
(`verify_and_charge_gas_key_tx_ephemeral`), which is outside D1.

**Local receipts** are processed before the incoming receipts under the same compute limit
(`lib.rs:2384-2392`) and exactly like an incoming single-Transfer receipt (v1/v2's
`TransferV1.applyReceipt`: credit, storage stake, burn at `min(receipt price, block price)`,
gas refund of the surplus forwarded as a `system` receipt).

**Reads.** nearcore prefetches the signer account and access key of every non-expired
transaction (`lib.rs:1922-1977`) but surfaces a missing trie value only when step 5/6 uses
it. The relation reads exactly at steps 5/6: a witness missing a node needed only by, e.g.,
a transaction with a bad signature is still accepted (this is exercised by the single-node
drop mutants).

## 4. `InD1`

D1 keeps every D0 condition of `spec/near-chunk-validation-v0.md` §6 except `w.no_txs` and
`c.no_tx_flags`, extends three of them to local receipts, and adds:

| id | condition | reason |
|---|---|---|
| `w.tx_shape` | every `SignedTransaction` in `transactions` and `new_transactions` is `V0`, or `V1` with `TransactionNonce::Nonce` (either `NonceMode`); exactly one action, `Transfer`; ED25519 public key; ED25519 signature | Transfer-only conversion; no gas-key path, no secp256k1 recovery, no ML-DSA |
| `t.signer_v1` | every signer account read at step 5 is `AccountV1` (72 bytes, no V2 sentinel) | v1 account codec |
| `r.shape`, `r.success` | also for local receipts: receiver (= signer) is a named account; the receipt succeeds | D0 receipt semantics |
| `e.distinct_ids` | incoming and local receipt ids pairwise distinct | as D0 |
| `e.compute` | no local or incoming receipt is delayed by the compute limit (the transactions' gas counts) | delayed queue |
| `e.forwarded` | every transaction receipt and refund is forwarded, none buffered | outgoing buffers |

**Inside D1** (formalized, not excluded): every validity class — invalid signatures of every
kind (§2 edge rules), expired transactions, duplicate hashes, cost overflow, missing / foreign
signers, missing keys, function-call keys (with and without allowance), gas keys used without
a gas-key nonce, monotonic and strict nonces (too low, duplicate, gap, too large), insufficient
balance, storage stake (`LackBalanceForState`), V0 and V1 transactions, self-transfers (local
receipts), transfers to implicit receivers (forwarded), the u128 burnt-overflow drop, and the
`new_transactions` rules (size gate, `tx_root`, Reed–Solomon body). Mainnet relevance: the
bulk of mainnet transactions are FunctionCalls (D3); D1 adds the plain-transfer traffic.

## 5. Formalization (`spec/lean/v3`, Lake package `NearSpecV3`)

| module | content |
|---|---|
| `SHA512` | FIPS 180-4 SHA-512, Nat words, structural recursion (kernel-reducible) |
| `Ed25519` | field 𝔽_p (p = 2²⁵⁵−19), scalars mod ℓ, twisted-Edwards group law, dalek decompression and canonical compression, `Ed25519.verify` (§2 table), `sigEncodingOk` |
| `TxD1` | `pTxD1` (borsh `SignedTransaction`, two-byte look-ahead, D1 shape), `Tx.valid`, `txCost`, access-key decoding, `verifyAndCharge` |
| `RuntimeD1` | `processTx`/`processTxs` (§3 steps 1–8), `applyReceiptsC` (local then incoming with the compute accumulator), `applyNewChunkD1`, outcomes with statuses (`OutD1`, `outcomeRootD1`) |
| `ChunkValidationD1` | `decodeStateWitnessD1`, `checkD1`, `RelD1` |
| `ChallengeD1` | `challengeSpecD1` (`Rel = RelD1`, same claim codec and round-trip proof as D0) |

Executable: `nearspec-v3-check-d1 [--d0] CASE…` (compiled `checkD1`, or `checkD0` with `--d0`).
Independent Python: `oracle/tools/spec_check_v3_d1.py` (D0 machinery from
`spec_check_v3.py`; transaction semantics and Ed25519 written separately:
`oracle/tools/v3lib/ed25519.py`, pure Python from RFC 8032 §5.1/§6 with the §2 deviations,
SHA-512 from `hashlib`).

## 6. Evidence

*Filled in by the D1 results (§8).*

## 7. Reference oracle for D1

`near-arena-oracle-v3 gen --domain d1` (`oracle/v3/src/{d1gen,d1}.rs`):

* **Chains** as for D0 (§7 of the v0 doc), plus genesis keys per shard: a gas key (a06),
  function-call keys with unlimited and 1-yocto allowance (a07, a08), and 14 extra
  full-access keys plus a secp256k1 key on a09 (storage usage > 770 bytes, so it is not a
  zero-balance account). Honest traffic (accounts a00–a04) adds self-transfers (local
  receipts) and V1 transactions.
* **Adversarial chunk producer.** With probability ½ per height a shard's next chunk producer
  processes the block without producing chunks and then produces them exactly as
  `Client::produce_chunks` (`chain/client/src/client.rs:2093-2160`), except that the chosen
  shard's chunk is rebuilt with `ShardChunkWithEncoding::new` (`sharding.rs:1427-1482`)
  carrying the pool transactions plus 3–9 crafted ones at random positions. Classes:
  `valid`, `valid_self`, `valid_zero_deposit`, `valid_implicit_receiver`, `valid_v1_monotonic`,
  `valid_v1_strict`, `bad_sig_{flip_r, flip_s, wrong_msg, s_plus_l, wrong_key, negated_r}`,
  `nonce_{zero, dup, too_large}`, `v1_strict_gap`, `insufficient_balance`, `lack_storage`,
  `cost_overflow`, `missing_account`, `foreign_signer`, `missing_key`,
  `fc_key_{unlimited, allowance}`, `gas_key_v0`, `expired_{unknown, old}_block`,
  `dup_identical`, `dup_bad_sig_first`, and (8 % of injections) the out-of-D1 shapes
  `ood_{two_actions, secp256k1, add_key, gas_key_nonce}`. The injector reads the exact
  pre-state the transactions will be applied to, so balance and storage classes are hit
  precisely. Everything downstream is unmodified nearcore; nearcore's own outcome for every
  transaction is recorded (`tx_results`).
* **Judge**: nearcore's validator as for D0. `tx_valid` mutants (trusted facts) are judged by
  nearcore with the store's validity answers replaced by the claim's (`judge::nearcore_judge_flags`).
* **D1 classifier**: `d1::classify` from the node's full state and stored outcomes.
* **D1 mutants**: each `tx_valid` flag flipped, dropped / swapped / signature-flipped
  transactions, a signature with the borsh-rejected high bits, and `new_transactions`
  changed with the endorsed header re-hashed (`tx_root`, encoded merkle root and length).
* `ed25519-judge` / `ed25519-sign`: nearcore's verdict on arbitrary `(pk, sig, msg)` and
  signatures made by `near_crypto::SecretKey::sign`.

Note: nearcore's store debug-asserts that two values stored under one key are equal
(`core/store/src/db/refcount.rs:107-119`); a chunk with two different `SignedTransaction`s of
one hash (class `dup_bad_sig_first`) trips it in debug builds, so the oracle builds
`near-store` without debug assertions (release nodes have none).

## 8. Results

*Filled in after the D1 difftest.*
