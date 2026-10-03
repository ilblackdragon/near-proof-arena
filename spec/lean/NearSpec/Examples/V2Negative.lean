import NearSpec.ClaimCodec
import NearSpec.Examples.TierA
import NearSpec.Examples.V2TierA
import NearSpec.Examples.V2TierBbw
import NearSpec.Examples.V2Missed

/-!
Kernel-checked negative examples for `near/pv86/receipt-transfer-batch/v1`: the
v2 relation is not trivially true, rejects v1's projection root, and depends on
the scheduler inputs it binds.
-/

namespace NearSpec.Examples.V2Negative
open NearSpec NearSpec.TransferV2 NearSpec.Examples

/-- v1's `slice_post_root` (the projection without the `0x0f` write) is NOT the
v2 post-state root for the same chunk: the relation rejects it. -/
theorem projection_root_rejected :
    ¬ NearRelation { V2TierA.claim with postStateRoot := TierA.claim.slicePostRoot } V2TierA.witness := by
  decide +kernel

/-- The relation's post root is the oracle's `Runtime::apply` root, which differs from v1's projection. -/
theorem post_root_ne_projection : V2TierA.claim.postStateRoot ≠ TierA.claim.slicePostRoot := by
  decide +kernel

/-- `missed_chunks_count` is semantic: with the link allowed the allowance would be 4_400_000. -/
theorem missed_count_matters :
    ¬ NearRelation { V2Missed.claim with missedChunksCount := 0 } V2Missed.witness := by
  decide +kernel

/-- A gas refund needs bandwidth on link (S,S); with a missed chunk none is granted. -/
theorem refund_needs_grant :
    ¬ NearRelation { V2TierBbw.claim with missedChunksCount := 1 } V2TierBbw.witness := by
  decide +kernel

/-- Non-zero congestion is outside the domain. -/
theorem congestion_out_of_domain :
    ¬ NearRelation { V2TierA.claim with delayedReceiptsGas := 1 } V2TierA.witness := by
  decide +kernel

/-- Changing the stored previous scheduler state (here: deleting the old
allowance entry, a length change) changes the root that must be claimed. -/
theorem wrong_post_root :
    ¬ NearRelation { V2TierBbw.claim with postStateRoot := V2TierA.claim.postStateRoot } V2TierBbw.witness := by
  decide +kernel

/-- Cross-scope separation: v2 claim bytes are not v1 claims and vice versa. -/
theorem v1_decoder_rejects_v2 : TransferV1.decodeClaim V2TierA.claimBytes = none := by decide +kernel
theorem v2_decoder_rejects_v1 : decodeClaim TierA.claimBytes = none := by decide +kernel

/-- Trailing bytes are rejected. -/
theorem decode_rejects_trailing : decodeClaim (V2TierA.claimBytes ++ [0]) = none := by decide +kernel

end NearSpec.Examples.V2Negative
