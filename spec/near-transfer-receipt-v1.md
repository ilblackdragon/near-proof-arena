# `near/pv86/receipt-transfer-batch/v0` — NEAR Transfer-receipt batch transition

Challenge name `near-transfer-receipt-v1`; claim format `near-arena-claim-v1`
(`spec/claim-v1.md`). Pinned nearcore `2.13.4` =
`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, protocol version **86**, mainnet
runtime parameters (`RuntimeConfigStore::new(None).get_config(86)`).
This is a **subset** of NEAR's chunk transition, not "NEAR state transition".
Background and source citations: `docs/research/nearcore-boundary.md`,
`docs/research/first-slice.md`.

## 1. The relation

Lean: `NearSpec.TransferV1.NearRelation (c : Claim) (w : Witness) : Prop`
(module `NearSpec.TransferV1`, file `spec/lean/NearSpec/TransferV1.lean`).

```lean
structure Witness where
  receipts : List Receipt      -- the ordered batch (single-Transfer action receipts)
  trie     : PTrie             -- partial pre-state trie (revealed paths + subtree hashes)

def NearRelation (c : Claim) (w : Witness) : Prop :=
  DomainStatic c w ∧                                              -- §3
  receiptsCommitment c.shardId w.receipts = c.receiptsCommitment ∧
  w.trie.hashOf = c.preStateRoot ∧
  (runBatch c.ctx w.trie w.receipts).map Outputs.ofAcc = some (Outputs.ofClaim c)

def Domain (c : Claim) (w : Witness) : Prop :=
  DomainStatic c w ∧ (runBatch c.ctx w.trie w.receipts).isSome = true
def NearRelationBytes (cb : Bytes) (w : Witness) : Prop := ∃ c, c.encode = cb ∧ NearRelation c w
```

`Outputs = (slicePostRoot, outcomeRoot, refundCount, refundsCommitment,
gasBurntTotal, tokensBurntTotal)`. Proved: `NearRelation.domain`
(relation ⇒ domain), `NearRelation.outputs_unique` (outputs are a function of
the context and the witness), `decodeClaim_encode` / `Claim.encode_injective`
(claim bytes bind every field). For formal-core's `ArenaCore.ChallengeSpec`:
`Claim := WfClaim`, `Rel := WfClaim.Rel`, `Domain := WfClaim.ClaimDomain`,
`encodeClaim := WfClaim.encode`, `decodeClaim := WfClaim.decode`,
`decode_encode := WfClaim.decode_encode` (`NearSpec/ClaimCodec.lean`).

Informally: *applying the ordered batch of incoming Transfer receipts to the
shard state with root `pre_state_root`, as nearcore 2.13.4 `Runtime::apply`
does for a chunk with no transactions, no local/delayed/yield receipts and no
validator updates, writes the Account values whose root is `slice_post_root`,
produces outcomes with root `outcome_root`, generates exactly the committed gas
refunds, burns `gas_burnt_total` gas and `tokens_burnt_total` yoctoNEAR.*

## 2. Semantics (per receipt, in order)

For receipt `r` with receiver `a = Account(r.receiver_id)` (read from the
current state), `p = min(r.gas_price, block_gas_price)`, `G = 223 182 562 500`
(`new_action_receipt` exec 108 059 500 000 + `transfer` exec 115 123 062 500,
named receiver):

1. `a.amount' = a.amount + deposit`; `locked`, `code_hash`, `storage_usage`
   unchanged; the receiver's 72-byte AccountV1 value is rewritten
   (`actions.rs:148-153`, `lib.rs:887-893`). The predecessor is not touched
   (debits happened at tx→receipt conversion, outside the slice).
2. Outcome: `{id: r.receipt_id, receipt_ids: [refund_id?], gas_burnt: G,
   tokens_burnt: G·p, executor_id: r.receiver_id, status: SuccessValue([]),
   logs: []}` (`lib.rs:1117-1155`; `compute_usage`/`metadata` not hashed).
3. If `r.gas_price > block_gas_price`: one gas-refund receipt
   `Receipt::new_gas_refund(signer_id, (r.gas_price − p)·G, signer_public_key)`
   with id `sha256(r.receipt_id ‖ block_height_le64 ‖ 0_le64)`
   (`lib.rs:1166-1301`, `receipt.rs:519-537`, `utils.rs:278-335`). Penalty is 0
   (`gas_refund_penalty` 0/100, `min_gas_refund_penalty` 0, unused gas 0).
4. `tx_burnt_amount += G·p`; `gas_used += G`.

Lean: `applyReceipt`, `applyAll`, `runBatch` in `TransferV1.lean`.
Both price cases (with and without refunds) are in the relation; the Lean
kernel checks one instance of each (`NearSpec/Examples/TierA.lean`, `TierB.lean`).

## 3. Domain (restrictions)

Machine ids are used in the challenge definition. `S` = checked by
`DomainStatic`; `D` = checked dynamically by `runBatch` returning `some`.

| id | restriction | why (nearcore behaviour otherwise) | Lean |
|---|---|---|---|
| `pv86` | protocol_version = 86 | other feature gates / config | S |
| `mainnet_params` | chain_id = `mainnet` (selects mainnet runtime config) | testnet parameters differ | S |
| `claim_wf` | all claim fields within their encoded widths | encoding injectivity | S |
| `batch_size` | 1 ≤ n ≤ 256 | bounds sizes; n = 0 is a different (empty) chunk | S |
| `compute_limit` | (n−1)·G < gas_limit | otherwise trailing receipts go to the delayed queue (`lib.rs:2563-2585`); oracle confirms the boundary is exact | S |
| `receipt_shape` | `Receipt::V0`, `ReceiptEnum::Action`, exactly one `Transfer`, no input/output data | other actions/variants | type + decoder |
| `valid_account_ids` | predecessor/receiver/signer are valid AccountIds | not decodable by nearcore | S |
| `signer_key_type` | ED25519 or SECP256K1 signer key | ML-DSA keys excluded (size) | S |
| `not_system_predecessor` | predecessor ≠ `system` | refund-receipt path (no burn, allowance/gas-key refund) | S |
| `named_receiver` | receiver is a NamedAccount (not 64-hex, `0x`+40hex, `0s`+40hex) | implicit-account fee/creation path (`cost.rs:722-748`) | S |
| `distinct_receipt_ids` | receipt ids pairwise distinct | outcome/refund id collisions | S |
| `witness_size` | revealed partial-trie bytes ≤ 3 000 000 | keeps recorded storage proof under `main_storage_proof_size_soft_limit` 4 000 000 (else receipts are delayed); the 1 MB margin covers the non-slice reads of `apply` (delayed/buffered/yield indices, bandwidth scheduler state) | S |
| `receiver_exists_v1` | receiver Account exists, is 72-byte AccountV1 (first u128 ≠ u128::MAX) | `AccountDoesNotExist` failure + deposit refund; V2 path | D |
| `no_balance_overflow` | amount + deposit ≤ 2^128 − 2 and amount' + locked < 2^128 | `apply` aborts (`StorageInconsistentState`); amount' = u128::MAX would be read back as the V2 sentinel | D |
| `storage_stake` | amount' + locked ≥ 10^19·storage_usage or storage_usage ≤ 770 | `LackBalanceForState` failure, rollback, refund | D |
| `burn_fits_u128` | G·p < 2^128, G·(gas_price − p) < 2^128, Σ tokens_burnt < 2^128 | `apply` aborts (`IntegerOverflowError`) | D |
| `apply_context` | the chunk has no transactions, no local/delayed/yield receipts, no validator-account update, is a new chunk | those run before/around incoming receipts and touch other keys/outcomes | stated assumption (not checkable from the claim) |

The judge only issues jobs in the domain (the oracle checks it with an
independent Rust implementation, `oracle/src/domain.rs`, and additionally
requires nearcore to behave "cleanly": all outcomes `SuccessValue([])`, no
delayed receipts, only Account keys plus `0x0f` changed, outgoing receipts =
generated refunds). Out-of-domain requests (fixtures in
`oracle/fixtures/rejection/`, one per restriction family) must be refused by
provers and classified `out_of_domain` by checkers.

## 4. Trie: why value replacement suffices

The relation works on a **partial trie** (`NearSpec.PTrie`): nodes on the
paths to the receivers' `TrieKey::Account` keys (`0x00 ‖ account_id`), every
other subtree given only by its hash, each revealed node carrying its stored
`memory_usage`. Hashing follows `RawTrieNodeWithSize` exactly
(`raw_node.rs`, `nibble_slice.rs`, `state.rs` `ValueRef`; values are never
inlined). The update `PTrie.set` replaces the value in place and keeps every
`memory_usage`. This is exactly nearcore's result because, inside the domain:

* no key is inserted or deleted (the receiver must exist; transfers never
  delete), so the set of keys — hence the canonical trie shape — is unchanged;
* the value length is unchanged (AccountV1 is always 72 bytes), so every node's
  `memory_usage` (`50 + 2·|key| + (|value|+50)` for leaves, sums above) is
  unchanged;
* nearcore's `TrieUpdate::finalize` feeds only the final value per key to
  `trie.update` (`update.rs:242-262`), so repeated receivers reduce to the last
  write, which is what sequential in-place replacement computes.

Account keys may be prefixes of other keys (`ab` vs `ab.near`), so values also
live in `BranchWithValue` nodes; the model handles both (the generator covers
it: 517 of 1502 in-domain cases of the reported run). Well-formedness
(`PTrie.wf`: nibbles < 16, exactly 16 child slots, 32-byte hashes, widths in
range) makes node serialization injective, so under SHA-256 collision
resistance a partial trie hashing to the real `pre_state_root` reveals the real
values. (This is an argument, not a Lean theorem: collision resistance is a
cryptographic assumption handled by formal-core.)

## 5. Projection: `slice_post_root` is not the on-chain root

`Runtime::apply` always writes `TrieKey::BandwidthSchedulerState` (`0x0f`),
also for empty chunks (`lib.rs:1765-1771`). The chunk's real post-state root
(`ChunkExtra.state_root`, the next chunk header's `prev_state_root`) is
therefore `root(pre ⊕ account writes ⊕ {0x0f ↦ bw'})`, while
`slice_post_root = root(pre ⊕ account writes)`. The oracle checks this
decomposition for every case (`decomposition_ok`; the full root is recorded in
`diagnostics.json` as `full_apply_state_root`). `pre_state_root` IS the real
pre-state root. Adding the single-shard bandwidth-scheduler write is the
natural next version.

## 6. What is formalized vs. only tested

| part | status |
|---|---|
| claim encoding, strict decoding, round trip, injectivity | Lean definitions + **proved** theorems |
| relation ⇒ domain; outputs determined by witness | **proved** |
| SHA-256 | formal-core's `ArenaCore.sha256` (FIPS 180-4, kernel-reducible, vector-tested in formal-core); agrees with nearcore/Python on every differential case |
| account-id validity / account types, AccountV1, receipt borsh, trie node hashing, outcome hashing, merklize, refund ids, transfer arithmetic | Lean definitions written from the cited nearcore source; **faithfulness is tested, not proved** (differential testing vs real nearcore, §7) |
| non-vacuity | **kernel-checked** (`decide +kernel`, no `native_decide`): the relation holds for the oracle's real worked example in both price cases (`NearSpec.Examples.TierA/TierB.relation`), and fails for tampered outputs/receipts (`NearSpec.Examples.Negative`); axioms used: `propext` only |
| "value replacement = nearcore trie update" (§4) | argued in this document + oracle-tested (witness-only re-execution with nearcore's `Trie::from_recorded_storage` equals the slice root on every case) |
| domain completeness (each `none` of `runBatch` corresponds to non-slice nearcore behaviour) | tested on generated out-of-domain cases with nearcore's actual behaviour recorded |
| storage-proof-limit margin (`witness_size`) | argued (§3), not tested near the limit |
| memtrie / flat-storage code paths of nearcore | not exercised (oracle uses the disk-trie path; roots are identical by design) |

## 7. Differential testing

Three implementations must agree byte-for-byte on `claim.bin` and on
in-domain-ness for every generated case:
(1) `near-arena-oracle` — the real pinned nearcore `Runtime::apply`;
(2) `nearspec-check` — the compiled Lean reference semantics (also evaluates
`decide (NearRelation c w)` on the decoded claim);
(3) `oracle/tools/spec_check.py` — independent Python, rebuilding the full trie
from `state.bin` from scratch before/after (algorithmically different from
both nearcore's in-place update and Lean's partial-trie update) and walking the
witness separately. Harness: `oracle/tools/difftest.py`. Results are in
`spec/difftest-report.json`: seed 4242, **1712 cases** (1500 valid + 2 worked
examples + 210 out-of-domain: 14 rejection families × 15), **0 disagreements**;
1502 in-domain cases byte-identical across all three (1366 with refunds, 136
without; batch sizes 1..254, mean 35.8) and `decide (NearRelation c w)` true
on each; all 210 out-of-domain cases classified out-of-domain by all three.
Wall time: oracle 4.5 s, Lean checker 94 s, Python 3.9 s.

How to run:
```
oracle/scripts/link-nearcore.sh /path/to/nearcore@44f7ae6c && (cd oracle && cargo build -j 8)
(cd spec/lean && lake build)
python3 oracle/tools/difftest.py --seed 4242 --valid 1500 --invalid 210
```

Generator coverage (`oracle/src/casegen.rs`): random valid named account ids
of length 2..64 incl. near-misses of implicit forms (63/65-hex, `0x`+39/41,
non-hex chars) and prefix families (branch-with-value / extension nodes);
balances near `u128::MAX`, zero-balance accounts (storage ≤ 770), locked
balances, contract code hashes; deposits 0 and maximal; batches 1..256; repeated
receivers; prices with and without refunds, receipt price below block price,
zero prices, near-overflow prices; tight compute limit `(n−1)·G + 1`;
ED25519 and SECP256K1 signer keys; extra access-key / contract-data keys.
Out-of-domain generators: missing receiver, balance overflow, sentinel
balance, storage stake, implicit/eth/deterministic receiver, `system`
predecessor, multi-action, non-Transfer action, compute limit, duplicate ids,
AccountV2 receiver, tokens-burnt overflow, wrong protocol version, empty batch.

## 8. `runtime_config_digest`

`runtime_config_digest = sha256(JCS(D))` where `D` is the JSON emitted by
`near-arena-oracle params` (`spec/challenge-inputs/runtime-config-pv86.json`):
`{schema: "near-arena-runtime-config-v1", nearcore_commit, protocol_version: 86,
config_source, parameter_files: [{path, sha256}] (parameters.yaml then every
NN.yaml with NN ≤ 86, in PV order — exactly the files RuntimeConfigStore folds),
runtime_config_view_json_sha256 (sha256 of serde_json of
RuntimeConfigView::from(get_config(86))), slice_parameters: {every constant the
slice uses, read from the live config and asserted equal to NearSpec.Params}}`.
JCS = RFC 8785 (sorted keys, no whitespace, integers only; big values are
decimal strings).

## 9. Honest gaps and dependencies

* SHA-256 is formal-core's `ArenaCore.sha256` (Lake `require` of
  `../../formal-core`), the same function used by the NPAI `SHA256` opcode and
  the `sha256_cr` assumption; `NearSpec.sha256` is an `abbrev` for it.
* The faithfulness of the Lean semantics to nearcore is established by source
  reading + differential testing, not by proof (nearcore has no formal model).
* Synthetic states only; no historical replay (§10).
* The memtrie/flat-storage path, multi-shard layouts (oracle runs the
  single-shard layout, `shard_id` is bound but non-semantic), and receipts
  buffered by congestion control (the domain bound keeps refunds forwarded;
  the oracle rejects any case where they are not) are not exercised.

## 10. Historical mainnet replay (unavailable here)

Replaying a real mainnet chunk would need: the chunk's `prev_state_root` and a
state witness for the touched receivers' Account paths — obtainable from an
archival node (`EXPERIMENTAL_view_state`/state proof RPC with `include_proof`,
the chunk's `ChunkStateWitness.main_state_transition.base_state`, or a
`state_parts` dump at that epoch); the chunk's incoming receipts
(`EXPERIMENTAL_receipt` / chunk RPC) and receipt proofs; the block header
(height, gas price) and chunk header (gas limit); and a chunk whose incoming
receipts are *all* in-domain Transfers with no transactions, local or delayed
receipts — rare on mainnet, so practical replay would more likely target the
next slice versions. No archival node or network access was used for this
version; all fixtures are synthetic states executed by the real pinned nearcore
runtime, and are labelled so in `provenance.json`.

## 11. Explicit exclusions (`excludes`)

`block_finality`, `data_availability`, `receipt_inclusion`,
`pre_state_root_on_chain`, `epoch_and_protocol_version_selection`,
`onchain_post_state_root` (bandwidth-scheduler write), `transactions`,
`signature_verification`, `function_calls_and_wasm`, `non_transfer_actions`,
`implicit_account_creation`, `failure_paths_and_rollback`,
`refund_receipt_inputs`, `data_postponed_yield_receipts`,
`delayed_receipt_queue`, `congestion_control_and_buffering`,
`bandwidth_scheduler`, `outgoing_receipts_root_and_routing`,
`validator_updates_and_rewards`, `account_v2_global_contracts`,
`receipt_enum_action_v2`, `other_protocol_versions`, `testnet_parameters`.

## 12. ArenaCore instance and v1 parameters

`spec/lean/NearSpec/Challenge.lean`:

* `NearSpec.TransferV1.challengeSpec : ArenaCore.ChallengeSpec` —
  `Claim := WfClaim`, `Witness`, `Rel := WfClaim.Rel` (= `NearRelation`),
  `Domain := WfClaim.ClaimDomain`, `decodeClaim := WfClaim.decode`,
  `encodeClaim := WfClaim.encode`, `decode_encode := WfClaim.decode_encode`.
* `challengeParamsWith profile verifyFuel maxProofBytes maxReductionFuel` — what
  the judge's Expected module instantiates (`spec/lean/judge/Expected.lean.template`,
  rendered by `runners/formal-checker` from
  `runners/formal-checker/challenges/near-transfer-receipt-v1.json`, values
  spliced as literals from the frozen challenge's `security_profile` and
  `formal_params`).
* `challengeParams` — the canonical v1 instance:

| parameter | value | rationale |
|---|---|---|
| profile | `validity-classical-128`: ROM model, 128-bit target, `sha256-collision-resistance` + `random-oracle-fiat-shamir-sha256`, prover queries 2^40, hash queries 2^64 | `security/profiles/validity-classical-128.json` |
| `maxProofBytes` | 8 388 608 (8 MiB) | a re-execution proof that carries the whole witness (`max_witness_bytes` 4 MiB) plus the receipts (`max_request_bytes` 128 KiB) fits with framing; succinct backends are far below |
| `verifyFuel` | 1 073 741 824 (2^30) NPAI fuel | ≈128 instructions per byte of a maximal proof — enough for a byte-level NPAI re-execution verifier (node parsing, nibble walks, SHA256 opcode at 1 fuel/64 B) |
| `maxReductionFuel` | 1 073 741 824 (2^30) | same budget for an explicit standard-model CR reduction program |

Only the NPAI interpreter route (`.interp`) has a template; a native-route
challenge would need the judge to supply the verifier model, which this
challenge does not define.

## 13. Workload suite (v1)

Three classes, by receipts per request (generator specs in
`spec/workloads/near-transfer-receipt-v1/*.json`, each class's `generator`
digest = `sha256(JCS(spec))`; every spec pins the oracle source tree digest and
the nearcore commit): `batch-1` (200 000 ppm), `batch-16` (300 000 ppm),
`batch-256` (500 000 ppm); 8 requests per measured batch. Public dev fixtures:
`oracle/fixtures/public` (TreeDigest in the challenge). Held-out set: 24 cases
per class generated by `oracle/scripts/gen-heldout.sh` from a secret seed kept
off-repo; only its TreeDigest (`spec/challenge-inputs/heldout-commitment.json`)
is committed, revealed at season end. Baselines are null until the reference
backend is measured (scores stay null; admission is still decided).
