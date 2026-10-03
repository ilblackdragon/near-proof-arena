import NearSpec.ClaimCodec
import NearSpec.Examples.TierA
import NearSpec.Examples.TierB

/-!
Kernel-checked negative examples: the relation is not trivially true. Changing
any single output of the oracle's claim, or the witness receipts, falsifies it.
-/

namespace NearSpec.Examples.Negative
open NearSpec NearSpec.TransferV1 NearSpec.Examples

theorem wrong_post_root :
    ¬ NearRelation { TierB.claim with slicePostRoot := TierB.claim.preStateRoot } TierB.witness := by
  decide +kernel

theorem wrong_tokens_burnt :
    ¬ NearRelation { TierB.claim with tokensBurntTotal := TierB.claim.tokensBurntTotal + 1 }
      TierB.witness := by
  decide +kernel

theorem wrong_refund_count :
    ¬ NearRelation { TierB.claim with refundCount := 0 } TierB.witness := by
  decide +kernel

/-- The Tier-A claim (block price = receipt price, no refunds) does not hold for
the Tier-B context: the outcome root depends on the price case. -/
theorem price_case_matters :
    ¬ NearRelation { TierB.claim with outcomeRoot := TierA.claim.outcomeRoot } TierB.witness := by
  decide +kernel

/-- Tampering with a receipt's deposit breaks the receipts commitment. -/
theorem tampered_receipt :
    ¬ NearRelation TierB.claim
      { TierB.witness with
        receipts := TierB.witness.receipts.map fun r => { r with deposit := r.deposit + 1 } } := by
  decide +kernel

/-- The strict decoder recovers the oracle's claim from `claim.bin`. -/
theorem decode_example : decodeClaim TierB.claimBytes = some TierB.claim := by decide +kernel

/-- Trailing bytes are rejected. -/
theorem decode_rejects_trailing : decodeClaim (TierB.claimBytes ++ [0]) = none := by decide +kernel

/-- Unknown format versions are rejected (`...-v2`). -/
theorem decode_rejects_version :
    decodeClaim (TierB.claimBytes.set 22 50) = none := by decide +kernel

end NearSpec.Examples.Negative
