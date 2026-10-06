import NearSpecV3.ChallengeV3
import NearSpecV3.ChunkValidationV0a

/-!
# `ArenaCore.ChallengeSpec` instance for domain D0a (`RelD0a`)

Draft challenge `near-chunk-validation-d0-stark`
(`challenges/drafts/near-chunk-validation-d0-stark.draft.json`, spec/near-chunk-validation-v0a.md).
Same claim type and codec as `NearSpecV3.challengeSpec` (D0); `Rel c w = RelD0a c.encode w`
(`RelD0 ∧ A1 ∧ A2 ∧ Canon0f`, a pure restriction of D0, `relD0a_relD0`). The formal proof-size
cap is 8 MiB (V3-D0-DESIGN §10, §11).
-/

namespace NearSpecV3

open ArenaCore

theorem relD0a_relD0 {cb w : Bytes} (h : RelD0a cb w) : RelD0 cb w := h.1

def WfClaim.RelD0a (c : WfClaim) (w : List UInt8) : Prop := NearSpecV3.RelD0a c.1.encode w
def WfClaim.DomainD0a (c : WfClaim) : Prop := ∃ w, WfClaim.RelD0a c w

def challengeSpecD0a : ChallengeSpec where
  Claim := WfClaim
  Witness := List UInt8
  Rel := WfClaim.RelD0a
  Domain := WfClaim.DomainD0a
  decodeClaim := WfClaim.decode
  encodeClaim := WfClaim.encode
  decode_encode := WfClaim.decode_encode

def maxProofBytesD0a : Nat := 8388608

def challengeParamsD0a : ChallengeParams where
  spec := challengeSpecD0a
  profile := NearSpec.TransferV1.profileValidityClassical128
  verifyFuel := verifyFuelV3
  maxProofBytes := maxProofBytesD0a
  maxReductionFuel := maxReductionFuelV3

end NearSpecV3
