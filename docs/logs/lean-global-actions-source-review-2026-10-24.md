# Global action source review — 2026-10-24

Reviewed against nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, including its pinned Borsh 1.5.7 dependency. This note covers successor global action semantics and codecs; whole-chunk runner integration and independent replay evidence are maintained by their respective lanes.

## Findings and corrections

- `runtime/runtime/src/actions.rs` (`clear_account_contract_storage_usage`) uses saturating subtraction. Lean's natural-number subtraction matches this, including inconsistent smaller recorded usage. The local code length comes from a trie reference read; switching to a global reference deletes the local code value and adds the global identifier's storage usage.
- Borsh `de/mod.rs` decodes a BTreeMap through a vector and collection. The pinned build does not enable `de_strict_order`: unordered entries are sorted and duplicate keys keep the last value. `Successor.GlobalCodecs.pDsiGlobal` implements this normalization. The original standalone L4 strict decoder is unchanged and is not used by the successor codec.
- `core/primitives/src/transaction.rs` hashes reserialized transactions. The successor parser now reconstructs canonical action, delegate payload, and transaction bytes after state-init normalization, including both transaction versions. Hashing the original input bytes would disagree for a noncanonical map.
- `runtime/runtime/src/verifier.rs` storage balance checking includes locked balance and the zero-balance small-account exemption. State-init uses that same predicate, consumes only the required subsidy, and refunds the remainder to the receipt's balance-refund receiver. A 2048-byte value with zero deposit exercises insufficient storage funds; a small account with zero deposit can succeed.
- Deployment storage charging saturates its multiplication at u128, burns tokens, and increments the nonce immediately. A failed receipt still requires the surrounding receipt rollback; these action helpers deliberately leave writes to that integration boundary.
- Distribution freshness is greater-than-or-equal, so equal nonce reapplies and charges compute. Stale nonce skips writes and compute but still forwards. V1 supplies nonce zero. Distribution materialization is separate from literal `ContractStorage.record_deploy` tracking.

## Explicit remaining domain boundary

`core/primitives-core/src/code.rs`, `ContractCode::new`, trusts a supplied hash in release builds; equality to the actual bytes is only a debug assertion. Global distribution validation does not establish equality. Thus a CodeHash distribution whose identifier disagrees with SHA-256(code) must not be declared impossible merely because honest DeployGlobal generation produces matching pairs.

The current materialized-code source is keyed by the actual raw-code hash. It cannot faithfully represent the supplied compiled-code identity in this malformed case. `applyDistributionL` explicitly rejects it with `out of domain (w.shape): global_code_identity`. This exclusion applies to both cache policies until the identity model or an authenticated invariant closes it. Distribution targets absent from the current layout also remain explicitly excluded under `c.same_layout` pending ancestor-shard mapping.

## Validation

- `lake build NearSpecV3.Successor.GlobalCodecs NearSpecV3.Successor.GlobalExecution` passed after the codec correction.
- `lake build NearSpecV3.Logged.D2Runtime` passed after the typed extensions, including the legacy receipt proofs.
- `lake env lean --run TestGlobalActions.lean` passed. Directed cases cover codec legacy rejection, normalized map/delegate/transaction bytes, fees and permissions, deploy/use/state-init storage and refunds, nonce overflow, fresh/equal/stale distribution forwarding, V1 behavior, and the explicit code-identity exclusion.
- The independent fixture lane's actual pinned Rust codec probe confirms reversed-map sorting and duplicate-last-wins behavior for StateInit, Action, SignedDelegateAction, and SignedTransaction. Its vectors live in `docs/evidence/lean-chunk-completion/global-cache-fixtures/codec-vectors.json` when integrated.
- Independent whole-chunk fixtures contain incoming distribution receipts in source receipt proofs, so distribution reachability is positively witnessed; emitted receipt descriptors alone are not the evidence.
