| # | step | family | mode | nearcore tx | nearcore receipts | Lean main | Lean fix |
|---|---|---|---|---|---|---|---|
| 00 | secp-tx-transfer | secp256k1 tx key | pool | success | ok; ok | accept 4 | accept 4 |
| 01 | secp-tx-recid-flip | secp256k1 tx key | inject | success | ok; ok | accept 4 | accept 4 |
| 02 | secp-tx-bad-sig | secp256k1 tx key | inject | InvalidSignature (Transaction is not signed with the given public key) | - | accept 2 | accept 2 |
| 03 | secp-tx-high-s | secp256k1 tx key | inject | InvalidSignature (Transaction is not signed with the given public key) | - | accept 1 reject 1; 00-h10018-s3: reject (invalid: main transition post state root) | accept 2 |
| 04 | secp-tx-recid-4 | secp256k1 tx key | inject | InvalidSignature (Transaction is not signed with the given public key) | - | accept 2 | accept 2 |
| 05 | secp-tx-stale-nonce | secp256k1 tx key | inject | InvalidNonce (Transaction nonce 2 must be larger than nonce of the used access key 2) | - | accept 2 | accept 2 |
| 06 | secp-tx-ed25519-sig | secp256k1 tx key | inject | InvalidSignature (Transaction is not signed with the given public key) | - | out_of_domain 2; 00-h10030-s3: out_of_domain (out of domain (w.shape): non-ED25519 transaction signature); 00-h10031-s3: out_of_domain (out of domain (w.shape): non-ED25519 transaction signature) | out_of_domain 2; 00-h10030-s3: out_of_domain (out of domain (w.shape): non-ED25519 transaction signature); 00-h10031-s3: out_of_domain (out of domain (w.shape): non-ED25519 transaction signature) |
| 07 | secp-add-keys | secp256k1 tx key | pool | success_local | ok; ok | accept 3 | accept 3 |
| 08 | secp-new-key-multi-action | secp256k1 tx key | pool | success | ok; ok | accept 4 | accept 4 |
| 09 | secp-fc-key-call | secp256k1 tx key | pool | success | CompilationError(CodeDoesNotExist { account_id: AccountId("s0a00") }; ok | accept 4 | accept 4 |
| 10 | secp-signed-delete-key | secp256k1 tx key | pool | success_local | ok; ok | accept 3 | accept 3 |
| 11 | secp-deleted-key-tx | secp256k1 tx key | inject | InvalidAccessKeyError (Signer AccountId("s0ksecp") doesn't have access key with the given pub) | - | accept 2 | accept 2 |
| 12 | secp-add-off-curve-key | secp256k1 tx key | pool | success_local | ok; ok | accept 3 | accept 3 |
| 13 | secp-off-curve-key-tx | secp256k1 tx key | inject | InvalidSignature (Transaction is not signed with the given public key) | - | accept 2 | accept 2 |
| 14 | secp-delete-off-curve-key | secp256k1 tx key | pool | success_local | ok; ok | accept 3 | accept 3 |
| 15 | deleg-secp-valid | secp256k1 delegate | pool | success | ok; ok; ok; ok | accept 5 | accept 5 |
| 16 | deleg-secp-bad-sig | secp256k1 delegate | pool | success | DelegateAction is not signed with the given public key; ok; ok | accept 4 | accept 4 |
| 17 | deleg-secp-high-s | secp256k1 delegate | pool | success | DelegateAction is not signed with the given public key; ok; ok | accept 3 reject 1; 00-h10077-s1: reject (invalid: MissingTrieValue (access key)) | accept 4 |
| 18 | deleg-secp-stale-nonce | secp256k1 delegate | pool | success | DelegateAction nonce 1 must be larger than nonce of the used access ke; ok; ok | accept 4 | accept 4 |
| 19 | deleg-secp-recid-flip | secp256k1 delegate | pool | success | ok; ok; ok; ok | accept 5 | accept 5 |
| 20 | deleg-secp-inner-add-key | secp256k1 delegate | pool | success | ok; ok; ok; ok | accept 5 | accept 5 |
| 21 | deleg-v2-secp | secp256k1 delegate | pool | success | ok; ok; ok; ok | accept 5 | accept 5 |
| 22 | deleg-secp-key-ed25519-sig | secp256k1 delegate | pool | success | DelegateAction is not signed with the given public key; ok; ok | accept 4 | accept 4 |
| 23 | mldsa-add-keys | ML-DSA-65 key | pool | success_local | ok; ok | accept 3 | accept 3 |
| 24 | mldsa-delete-key | ML-DSA-65 key | pool | success_local | ok; ok | accept 3 | accept 3 |
| 25 | mldsa-signed-tx | ML-DSA-65 key | inject | success | ok; ok | out_of_domain 4; 00-h10107-s0: out_of_domain (out of domain (e.mldsa_tx): ML-DSA-65 transaction key); 00-h10108-s0: out_of_domain (out of domain (e.mldsa_tx): ML-DSA-65 transaction key); 00-h10109-s0: out_of_domain (out of domain (w.shape): ML-DSA-65 public key); 00-h10110-s0: out_of_domain (out of domain (w.shape): ML-DSA-65 public key) | out_of_domain 4; 00-h10107-s0: out_of_domain (out of domain (e.mldsa_tx): ML-DSA-65 transaction key); 00-h10108-s0: out_of_domain (out of domain (e.mldsa_tx): ML-DSA-65 transaction key); 00-h10109-s0: out_of_domain (out of domain (w.shape): ML-DSA-65 public key); 00-h10110-s0: out_of_domain (out of domain (w.shape): ML-DSA-65 public key) |
| 26 | mldsa-add-gas-key | ML-DSA-65 key | pool | success_local | ok; ok | accept 3 | accept 3 |
| 27 | gas-add-key | gas key | pool | success_local | ok; ok | accept 3 | accept 3 |
| 28 | gas-fund | gas key | pool | success_local | ok; ok | accept 3 | accept 3 |
| 29 | gas-tx-index0 | gas key | pool | success | ok; ok | accept 4 | accept 4 |
| 30 | gas-tx-index2-strict | gas key | pool | success | ok; ok | accept 4 | accept 4 |
| 31 | gas-tx-stale-nonce | gas key | inject | InvalidNonce (Transaction nonce 10115000001 must be larger than nonce of the used ac) | - | accept 2 | accept 2 |
| 32 | gas-tx-index-out-of-range | gas key | inject | InvalidNonceIndex (Invalid nonce_index Some(3) for key with 3 nonces) | - | accept 2 | accept 2 |
| 33 | gas-tx-bad-sig | gas key | inject | InvalidSignature (Transaction is not signed with the given public key) | - | accept 2 | accept 2 |
| 34 | gas-key-plain-nonce-tx | gas key | inject | InvalidNonceIndex (Invalid nonce_index None for key with 3 nonces) | - | accept 2 | accept 2 |
| 35 | gas-withdraw | gas key | pool | success_local | ok; ok | accept 3 | accept 3 |
| 36 | gas-withdraw-too-much | gas key | pool | success_local | Gas key <key> for account s3kgas has insufficient balance: 4.00 NEAR a; ok | accept 3 | accept 3 |
| 37 | gas-add-secp-key-underfunded | gas key | pool | success_local | ok; ok | accept 3 | accept 3 |
| 38 | gas-tx-insufficient-balance | gas key | inject | NotEnoughGasKeyBalance (Gas key for AccountId("s3kgas") does not have enough balance <0.001 NE) | - | accept 2 | accept 2 |
| 39 | gas-fund-secp-key | gas key | pool | success_local | ok; ok | accept 3 | accept 3 |
| 40 | gas-secp-key-tx | gas key | pool | success | ok; ok | accept 4 | accept 4 |
| 41 | gas-delegate-v2-gas-key-nonce | gas key | pool | success | ok; ok; ok; ok | accept 6 | accept 6 |
| 42 | gas-delete-key-with-balance | gas key | pool | success_local | Gas key <key> for account s3kgas has balance 4.00 NEAR which is too hi; ok | accept 3 | accept 3 |
| 43 | gas-deleted-key-tx | gas key | inject | success | ok; ok | accept 4 | accept 4 |
| 44 | gas-add-key-zero-nonces | gas key | inject | ActionsValidation (Transaction actions validation error: gas key requested invalid number) | - | accept 2 | accept 2 |
| 45 | gas-fund-missing-key | gas key | pool | success_local | Gas key <key> does not exist for account s3kgas; ok; ok | accept 3 | accept 3 |
| 46 | gas-fund-regular-key | gas key | pool | success_local | Gas key <key> does not exist for account s3kgas; ok; ok | accept 3 | accept 3 |
| 47 | host-add-gas-key-full | gas-key host | pool | success_local | ok; ok; ok; ok | accept 4 | accept 4 |
| 48 | host-add-gas-key-function-call | gas-key host | pool | success_local | An new action receipt created during a FunctionCall is not valid: Gas ; ok | accept 3 | accept 3 |
| 49 | host-fund-gas-key | gas-key host | pool | success_local | ok; ok; ok; ok | accept 4 | accept 4 |
| 50 | host-add-and-fund-secp-gas-key | gas-key host | pool | success_local | ok; ok; ok; ok | accept 4 | accept 4 |
| 51 | host-fund-other-account-gas-key | gas-key host | pool | success_local | ok; ok; ok; ok | accept 4 | accept 4 |
| 52 | host-fund-missing-gas-key | gas-key host | pool | success_local | ok; Gas key <key> does not exist for account s3kgashost; ok; ok; ok | accept 4 | accept 4 |
| 53 | host-malformed-key | gas-key host | pool | success_local | ExecutionError("VM Logic provided an invalid public key"; ok | accept 3 | accept 3 |
| 54 | host-add-mldsa-gas-key | gas-key host | pool | success_local | ok; ok; ok; ok | accept 4 | accept 4 |
| 55 | host-gas-key-tx | gas-key host | pool | success | ok; ok | accept 4 | accept 4 |
| 56 | gas-withdraw-all | gas key | pool | success_local | ok; ok | accept 3 | accept 3 |
| 57 | gas-delete-empty-key | gas key | pool | success_local | ok; ok | accept 3 | accept 3 |
| 58 | gas-removed-key-tx | gas key | inject | InvalidAccessKeyError (Signer AccountId("s3kgas") doesn't have access key with the given publ) | - | accept 2 | accept 2 |
| 59 | gas-nonce-index-on-regular-key | gas key | inject | InvalidNonceIndex (Invalid nonce_index Some(0) for key with 0 nonces) | - | accept 2 | accept 2 |
