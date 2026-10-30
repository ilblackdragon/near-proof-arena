# ML-DSA-65 signatures: Lean verification and whole-chunk fixtures (W06)

ML-DSA-65 used to be admitted only as a stored key (`PublicKey.handle`). Lean now verifies
ML-DSA-65 signatures (FIPS 204) and charges `ml_dsa_65_verification_cost`. The successor tier
admits ML-DSA keys and signatures in every signing position: transaction key and signature,
delegate key and signature, and receipt signer key. It also admits a key/signature type mismatch,
which nearcore decodes and then rejects as `InvalidSignature`.

Nearcore target: `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (2.13.4), PV86.

## 1. What nearcore does (pinned sources)

| item | nearcore 2.13.4 | source |
|---|---|---|
| crate | `aws-lc-rs` `=1.16.2` (`unstable`), `aws-lc-sys` 0.39.0; `UnparsedPublicKey::new(&ML_DSA_65, pk).verify(data, sig)` | `Cargo.toml:156`, `core/crypto/src/signature.rs:3-4, 1125-1128` |
| scheme | FIPS 204 **final**, **pure** ML-DSA, **empty context**. `verify_sig` → `EVP_DigestVerify` with no digest → `pkey_pqdsa_verify_generic` RAW mode → `ml_dsa_65_verify(pk, sig, len, msg, len, NULL, 0)` → `mld_sign_verify` (prefix `0 ‖ 0`) → `mld_sign_verify_internal` (Algorithm 8; `SampleInBall` seeded with the full 48-byte `c̃`) | `aws-lc-rs-1.16.2/src/pqdsa/signature.rs:104-113`; `aws-lc/crypto/fipsmodule/evp/p_pqdsa.c:183-189`; `aws-lc/crypto/fipsmodule/ml_dsa/mldsa/sign.c:976-1125` |
| rejections | signature length ≠ 3,309; malformed hint (`mld_unpack_hints`: running count decreasing or > ω, indices not strictly increasing within a polynomial, non-zero unused slot); `‖z‖∞ ≥ γ1 − β`; challenge mismatch. The public key has no invalid encoding (length only) | `sign.c:1022-1040`, `mldsa/packing.c:192-268` |
| sizes | public key 1,952 B, signature 3,309 B, secret key 4,032 B | `signature.rs:21-25` |
| Borsh | `KeyType`/`PublicKey`/`Signature` tag 2; `PublicKeyHandle` tag 3 = `SHA3-256("near:ml-dsa-65-pubkey-hash:v1" ‖ pk)` | `signature.rs:40-44, 156-174, 380-410, 1149-1196, 674-720` |
| signed message | the 32-byte `SignedTransaction` hash; the 32-byte NEP-461 delegate hash | `core/primitives/src/transaction.rs:291-293`; `action/delegate.rs:89, 211-214` |
| verification sites | `ValidatedTransaction::new` (tx signature, `InvalidSignature`); `SignedDelegateAction::verify` / `VersionedSignedDelegateAction::verify` (`DelegateActionInvalidSignature`). **No host function verifies ML-DSA**: contracts only pass ML-DSA keys to promise AddKey/gas-key hosts (`near-vm-runner/src/logic/logic.rs:236-250`) | as left |
| key/signature mismatch | `Signature` decodes independently of the key. `Signature::verify`'s catch-all `_ => false` arm returns `false`, so the transaction is dropped as `InvalidSignature` | `signature.rs:1086-1130` |
| gas | `ml_dsa_65_verification_cost: { old: 0, new: 100_000_000_000 }` (PV85, gas = compute). `signature_verification_cost` = the cost for the signer key's scheme plus, for each **top-level** `Delegate`/`DelegateV2` action, the cost for the inner signer key's scheme. It is added to `burnt` in `calculate_tx_cost` **after** the send fees, so it enters `gas_burnt`, `compute_burnt`, `burnt_amount`, `gas_cost` and `total_cost`, never `gas_remaining`. ED25519 / secp256k1 cost 0 | `85.yaml:11-15`; `runtime/src/config.rs:417-479, 485-526`; `parameter_table.rs:434-442` |
| size limit | from `PostQuantumSignatures` (PV85), `max_transaction_size` uses `wire_size` = body + Borsh signature (1 + 64 / 65 / 3,309 bytes) | `transaction.rs:302-339, 446-465` |

## 2. Lean

* **`NearSpecV3/MlDsa65.lean`** (new) implements FIPS 204 verification. It has its own SHAKE128/256
  sponge with block-wise squeezing; the Keccak-f permutation is reused from `Wasm.Crypto`. It also
  has the NTT/NTT⁻¹ over q = 8,380,417, `RejNTTPoly`/`ExpandA`, `SampleInBall`, `pkDecode`,
  `sigDecode`, `HintBitUnpack` with all three malformed-encoding rejections, the `z` norm bound,
  `Decompose`/`UseHint`, `w1Encode`, `verifyMu` / `verifyInternal` / `verifyCtx`, and
  `verify` (pure, empty context: nearcore's arm). Everything is `UInt64` arithmetic, and every loop
  is a bounded `for`. Rejection sampling has a fuel bound of 4,096 SHAKE blocks; the chance of
  exhausting it is below 2⁻¹⁰⁰⁰. Axioms: `propext`, `Quot.sound`.
* **Unit pin**: `NearSpecV3/Examples/MlDsaVectors.lean`, in `defaultTargets`. The `#guard`s check
  two vector sets:
  * 45 NIST ACVP `ML-DSA-sigVer-FIPS204` tests: groups 3 (pure external with contexts), 9
    (external μ) and 10 (internal). 9 accept, 36 reject. The source sha256 is in
    `generation.json`.
  * 74 verdicts of the pinned crate itself (12 accept, 62 reject), from `near-arena-oracle-v3-successor
    mldsa-vectors` (`oracle/v3-successor/src/mldsa_vectors.rs`, which calls
    `near_crypto::Signature::verify`). They cover 32-byte messages, an empty context and two keys:
    wrong key or message, `c̃`/`z` flips, `z` at ±γ1, every malformed-hint class, two
    well-formed-but-wrong hints, and all-zero / all-0xFF signatures. Two of the classes,
    `hint-unordered` and `hint-padding-nonzero`, keep the same hint *set*, so only the encoding
    rule rejects them.

  Compressed data: `crate-vectors.json.gz`. The vectors run in about 70 s of build time.
* **Speed.** `nearspec-v3-bench-mldsa` (`BenchMlDsa.lean`, not a default target) times the
  compiled code: 8–11 ms per verification. That is 1,480 verifications with 0 mismatches,
  measured on this 32-core host while other jobs were loading it (load average 58–92). It is
  single-threaded, and no checker optimisation has been tried.
* **Wiring.**
  * `TxD2.sigOk`: arm `2, 2 => MlDsa65.verify`.
  * `D2.actDelegate` / `Logged.actDelegateL`: the `e.mldsa_sig` throw is replaced by
    `MlDsa65.verify`. The refinement proof `R_actDelegate` still checks.
  * `D2.txCostD2` takes the signer key. `sigVerifyCost` / `txSigVerifyCost` add 100 Ggas of gas
    and of compute for an ML-DSA signer, plus 100 Ggas per top-level delegate with an ML-DSA
    inner key. They use checked `u64` addition.
  * `TxD2.sizeOk` is `body + 1 + |sig|`. That is unchanged for ED25519, one byte stricter for
    secp256k1 (as nearcore), and the ML-DSA size for ML-DSA.
* **Successor codecs** (`Successor/GlobalCodecs.lean`).
  * `pTxD2Global` admits ML-DSA keys and signatures. It no longer refuses a key/signature type
    mismatch: the signature is decoded by its own tag and `sigOk` returns `false`.
  * `pDelegateBodyGlobal` and the new `pSigGlobal` admit ML-DSA delegate keys and signatures.
  * `pActionRGlobal` admits ML-DSA receipt signer keys. Refunds and allowance updates reach the
    key through `PublicKey.handle`.
  * Removed exclusions: `e.mldsa_tx` (both messages), `e.mldsa_sig`, and the successor's
    `w.shape: ML-DSA-65 public key` on delegate and receipt-signer keys and
    `w.shape: ML-DSA-65 signature` on delegates.
  * The signed decoders (`D2.pTxD2`, `D2.pSig`, `D2.pPk`) are unchanged, and so is
    `oodMlDsaKey`/`oodMlDsaSig`.

## 3. Whole-chunk fixtures from pinned nearcore

The generator is the `mldsa` scenario of `oracle/v3-successor` (README "ML-DSA-65 scenario";
`src/keys/mldsa.rs`, 47 labelled steps on the `keys` driver). Each of four seeds runs 300 blocks
with `--mutate-every 10 --code-mutant-p 0.2 --ood-cap 2000`. Seed 1618 uses gas price 0, where
every cost is 0 and the boundary steps degenerate; the other three use 10⁸. The step tables
(`steps-<seed>.md/json`) give nearcore's transaction-stage result, its outcome tree and the
`allFeatures` verdicts before and after for every step. All steps appear in every run, and every
label has a chunk.

Seed 6151, nearcore outcomes (the other three are the same, except where price 0 changes the
boundary steps):

* ML-DSA-signed transfer → success; bad `z`, bad `c̃`, hint unordered, hint padding, hint count
  over ω, decreasing hint count, all-zero signature, wrong ML-DSA key, ED25519 / secp256k1 signature
  on an ML-DSA key, ML-DSA signature on an ED25519 key → `InvalidSignature`;
* stale nonce → `InvalidNonce`; nonce ≥ height·10⁶ → `NonceTooLarge`; strict-nonce gap →
  `InvalidNonce`; V1 strict nonce → success;
* AddKey of ML-DSA full and FC (allowance 1 NEAR) keys, then a multi-action transaction and a
  `signer_account_pk` call signed by them. The contract returns the 1,953-byte Borsh key, and the
  refund goes to the ML-DSA FC key's allowance. ML-DSA-signed AddKey of a fourth ML-DSA key, which
  is then used; ML-DSA-signed DeleteKey → the deleted key gives `InvalidAccessKeyError`;
* **gas-key boundary.** An ML-DSA gas key is funded with `gas_cost − verification cost`
  → `NotEnoughGasKeyBalance`. It is topped up to `gas_cost − 1` → `NotEnoughGasKeyBalance`, then
  to `gas_cost` → success. A bad signature on that key gives `InvalidSignature`;
* **balance boundary** (`s2kmlpoor`, 1 NEAR). Total cost = balance + verification cost →
  `NotEnoughBalance`; balance + 1 → `NotEnoughBalance`; exactly the balance → success;
* **delegates** with an ML-DSA inner key: valid, V2, inner AddKey of an ML-DSA key then used, and
  an ML-DSA relayer wrapping the ML-DSA delegate (two verification costs) → success. Bad `z`, hint
  unordered, hint padding, both type mismatches and wrong key → `DelegateActionInvalidSignature`;
  stale nonce → `DelegateActionInvalidNonce`;
* a Stake with an ML-DSA key → `ActionsValidation` (`UnsuitableStakingKey`).

### Verdicts (`tools/d3/replay_successor.py`, `nearspec-v3-check-successor` `23bfc8c3…`)

Every selected case is replayed, honest and nearcore-judged mutant: chunks that carry a step's
transaction, chunks that validate one of its receipts, and the mutants of those.
Binaries: "before" is main at `ad55805ea` (`29bf5217…`); "after" is this branch.

| seed | honest agree / ood / disagree | nearcore-invalid mutants agree / ood | nearcore-valid mutants agree / ood |
|---|---|---|---|
| 6151 after | **128 / 0 / 0** | 851 / 0 | 229 / 0 |
| 6151 before | 18 / 110 / 0 | 96 / 755 | 20 / 209 |
| 1618 after | **138 / 0 / 0** | 786 / 0 | 229 / 0 |
| 1618 before | 21 / 117 / 0 | 24 / 762 | 16 / 213 |
| 2718 after | **132 / 0 / 0** | 1,056 / 0 | 250 / 0 |
| 2718 before | 23 / 109 / 0 | 289 / 767 | 64 / 186 |
| 31415 after | **135 / 0 / 0** | 352 / 0 | 133 / 0 |
| 31415 before | 21 / 114 / 0 | 137 / 215 | 44 / 89 |

In total, 533 honest chunks and 3,886 mutants agree with nearcore. Nothing is out of domain and
nothing disagrees. Every before→after move is `out_of_domain → accept|reject`, and every
before-side reason is one of `e.mldsa_tx` (key or signature), `w.shape: ML-DSA-65 public key` or
`w.shape: ML-DSA-65 signature`.

**Blind replay** (`tools/mainnet-replay/blind_corpus.py`): every produced value is zeroed, and
the computed outputs are graded against nearcore's header.

| seed | graded | match |
|---|---|---|
| 6151 | 128 | 128 |
| 1618 | 138 | 138 |
| 2718 | 132 | 132 |
| 31415 | 135 | 135 |
| committed `cases/` | 67 | 67 |

The 1618 count includes 8 cases that first timed out under host load and matched on re-run. There
are 0 output mismatches and 0 leaks.

**Committed cases.** `cases/` holds 67 honest chunks from seed 6151: per step, the chunk that
applies the transaction and the chunk that executes its first receipt (`index.json`). After: 67
accept. Before: 4 accept, 63 out of domain.

**Breakage controls.** `checker-ctl` (`6f3f709c…`) is the same tree with two edits:
`sigVerifyCost ≡ 0`, and hint unpacking without the ordering and unused-slot rules. Results:

| seed | disagreements | honest chunks wrong |
|---|---|---|
| 6151 | 101 | 33 |
| 1618 | 75 | 32 |
| 2718 | 45 | 34 |
| 31415 | 59 | 32 |

Lean reports a post-state root or outcome-proof mismatch on every ML-DSA-signed transaction,
delegate and boundary chunk. At price 0 the cost term still changes gas and compute, so it shows
up in the outcome proof. On `mldsa-tx-hint-unordered` / `-hint-padding`, Lean applies a
transaction that nearcore drops. On the delegate variants it reaches an access key outside the
witness (`replay/control-<seed>.txt`). Building `MlDsaVectors` against the control tree fails at
`#guard crateFailures == []`; the ACVP set alone does not catch the hint-rule removal. Both
wirings and both hint rules are load-bearing.

### Key/signature type mismatch (task 5)

Nearcore decodes the signature by its own tag and `Signature::verify` returns `false`, so the
transaction is dropped (`InvalidSignature`); a delegate fails with
`DelegateActionInvalidSignature`. Lean now does the same.

* In this set, steps 09–11 (transactions) and 39–40 (delegates) accept with matching outputs and
  blind match.
* In the `key-family-fixtures` committed cases, the secp-key/ED25519-signature chunk (step 06)
  moves `out_of_domain → accept`, together with the ML-DSA-signed transaction and its receipt
  chunk. That is 79/79 accept, against 76 accept / 3 out of domain before
  (`replay/keyfamily-committed-*.jsonl`).

## 4. Signed tier

The signed decoders still refuse every ML-DSA key and signature and every non-ED25519 transaction
key (`D2.pTxD2`, `D2.pPk`, `D2.pSig`). Every shared change is unreachable from the signed layer:
the `2, 2` arms, a verification cost that is 0 for tags 0/1, and `sizeOk` (identical for a 64-byte
ED25519 signature).

| population | signed before | signed after | moves |
|---|---|---|---|
| 3,138-case census (`nearcore == ok ∧ expected_rel_d3 == false`, d3c7–d3c10) | 2,403 ood / 735 accept | 2,403 / 735 | **0** (0 reason changes either) |
| the four `mldsa` runs (4,419 cases) | as after | — | 0 |
| key-family committed (79) | 31 ood / 48 accept | same | 0 |

`allFeatures` on the census: 3,138 accept before and after, with 0 moves
(`replay/census-3138.json`).

## 5. Files

* `generation.json`: binary, ACVP and crate-vector hashes, source hashes, commands and per-run
  totals.
* `manifest-<seed>.json.gz`: collector output (`tools/d3/collect_keys.py --scenario mldsa`). It
  holds per-step results and outcome trees, plus the sha256 of every selected case. The raw runs
  are local and are bound by these hashes.
* `steps-<seed>.md/json`: per-step nearcore outcome and Lean verdicts before and after.
* `replay/summary.json`: all splits.
* `replay/verdicts-<seed>.jsonl.gz`: per-case verdicts, before and after, at both tiers.
* `replay/blind-<seed>.json`, `replay/committed-*`, `replay/keyfamily-committed-*`,
  `replay/census-3138.json`, `replay/control-<seed>.txt`.
* `cases/`: the 67 committed chunks.

## 6. Not covered / open

* ML-DSA signing in aws-lc is randomized, so two runs of a seed differ in signature bytes. The
  fixtures are bound by hash, not by regeneration.
* Byte-level malformed signatures are covered at the transaction and delegate positions: the
  hint classes, `z`, `c̃`, all-zero, and wrong key. Truncated or over-long ML-DSA signatures cannot
  appear in a chunk, because Borsh fixes the length; the unit pin covers them.
* *Superseded 2026-10-29:* this section said a `z` coefficient exactly at the norm bound "cannot be
  produced without forging". That is wrong for the key holder: near_crypto derives ML-DSA-65 keys
  from a seed, and a FIPS 204 signer that keeps only candidates with `‖z‖∞ = γ1−β` produces them.
  Whole-chunk fixtures at the bound and at `γ1−β−1` are in
  [remaining-shapes](../remaining-shapes/README.md).
* The ACVP pre-hash groups are not pinned; nearcore verifies pure ML-DSA only.
* `TxD1.lean` (the D1 path) is unchanged: ED25519 only, by design.
