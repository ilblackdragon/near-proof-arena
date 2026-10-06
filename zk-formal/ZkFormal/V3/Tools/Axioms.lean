import ZkFormal.V3.Fast.Prep
import ZkFormal.V3.EncodeWitness
import NearSpecV3.ChallengeD0a
import ZkFormal.V3.RefundCodec
import ZkFormal.V3.Tools.A7Examples

/-! Axiom audit of lane v3-spec's theorems (`lake env lean ZkFormal/V3/Tools/Axioms.lean`). -/

#print axioms NearSpecV3.relD0a_iff
#print axioms NearSpecV3.relD0a_relD0
#print axioms NearSpecV3.relD0a_mono
#print axioms NearSpecV3.Scheduler.convertRequests_eq_raw
#print axioms NearSpecV3.Scheduler.run_eq_core
#print axioms NearSpecV3.challengeSpecD0a
#print axioms ZkFormal.V3.Fast.nearSpec_sha256_csimp
#print axioms ZkFormal.V3.Fast.merkleLevel_csimp
#print axioms ZkFormal.V3.Fast.merkleFold_csimp
#print axioms ZkFormal.V3.Fast.merkleRoot_csimp
#print axioms ZkFormal.V3.Fast.decodeBlk_csimp
#print axioms ZkFormal.V3.Fast.decodeBlockV6_csimp
#print axioms ZkFormal.V3.Fast.gfMul_csimp
#print axioms ZkFormal.V3.Fast.gfPow_csimp
#print axioms ZkFormal.V3.Fast.RSCode_newF_csimp
#print axioms ZkFormal.V3.Fast.buildMatrixF_csimp
#print axioms ZkFormal.V3.Fast.encodeParts_eq_fast
#print axioms ZkFormal.V3.Fast.partsMerkleRoot_eq_F
#print axioms ZkFormal.V3.Fast.encodedMerkleRoot_eq_fast
#print axioms ZkFormal.V3.Fast.prepClaim_csimp
#print axioms ZkFormal.V3.Fast.prepBody_csimp
#print axioms ZkFormal.V3.Fast.prepD0_csimp
#print axioms ZkFormal.V3.encodeWitness_roundtrip
#print axioms ZkFormal.V3.encodeWitness_normal
#print axioms ZkFormal.V3.normalW_encodeWitnessFile
#print axioms ZkFormal.V3.pRefund_encode
#print axioms ZkFormal.V3.decodeBody_bodyOf
#print axioms ZkFormal.V3.applyNewChunk_refunds_shape
#print axioms ZkFormal.V3.applyNewChunk_outgoing_length
#print axioms ZkFormal.V3.decodeBody_outgoing
#print axioms ZkFormal.V3.pReceipt_wf
#print axioms ZkFormal.V3.A7Examples.unfolded_shared
#print axioms ZkFormal.V3.A7Examples.built_shared
