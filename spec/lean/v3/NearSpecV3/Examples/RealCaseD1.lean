import NearSpecV3.Examples.RealCaseD1Data

/-!
# Non-vacuity of `RelD1` on real nearcore cases (kernel-checked)

`decide +kernel` evaluates the whole D1 relation, including Ed25519 verification
(SHA-512, field and curve arithmetic) of every transaction that reaches it, on:

* `00-h10017-s2` — honest D1 case; tx: valid_self→success_local, foreign_signer→InvalidSignerId, expired_old_block→Expired, valid_v1_strict→InvalidNonce, bad_sig_flip_r→InvalidSignature, nonce_too_large→NonceTooLarge; nearcore: "ok"
* `06-h10069-s3` — honest D1 case; tx: valid_self→success_local, missing_account→InvalidSignerId, bad_sig_negated_r→InvalidSignature; nearcore: "ok"
* `00-h10017-s2-t.tx_valid_flip.1` — mutant `t.tx_valid_flip.1`; tx: —; nearcore: "ok"
* `00-h10017-s2-t.tx_valid_flip.0` — mutant `t.tx_valid_flip.0`; tx: —; nearcore: "validate: InvalidChunkStateWitness('Post state root DCATTrFN"
* `00-h10017-s2-hdr.prev_outcome_root` — mutant `hdr.prev_outcome_root`; tx: —; nearcore: "validate: InvalidOutcomesProof"
-/

namespace NearSpecV3.Examples

set_option maxRecDepth 100000 in
theorem relD1_00_h10017_s2 : RelD1 claimD1_00_h10017_s2 witnessD1_00_h10017_s2 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem relD1_06_h10069_s3 : RelD1 claimD1_06_h10069_s3 witnessD1_06_h10069_s3 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem relD1_00_h10017_s2_t_tx_valid_flip_1 : RelD1 claimD1_00_h10017_s2_t_tx_valid_flip_1 witnessD1_00_h10017_s2_t_tx_valid_flip_1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem not_relD1_00_h10017_s2_t_tx_valid_flip_0 : ¬ RelD1 claimD1_00_h10017_s2_t_tx_valid_flip_0 witnessD1_00_h10017_s2_t_tx_valid_flip_0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem not_relD1_00_h10017_s2_hdr_prev_outcome_root : ¬ RelD1 claimD1_00_h10017_s2_hdr_prev_outcome_root witnessD1_00_h10017_s2_hdr_prev_outcome_root := by
  decide +kernel

end NearSpecV3.Examples
