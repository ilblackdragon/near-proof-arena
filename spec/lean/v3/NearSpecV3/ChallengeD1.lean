import NearSpecV3.ChallengeV3
import NearSpecV3.ChunkValidationD1

/-!
# `ArenaCore.ChallengeSpec` instance for `near/pv86/chunk-validation/v0`, domain D1

Same `Claim` type, codec and witness format as the D0 instance (`ChallengeV3.lean`); only the
relation changes: `Rel c w = RelD1 c.encode w = Rel ∧ InD1` (spec/near-chunk-validation-d1.md).
-/

namespace NearSpecV3

open ArenaCore

def WfClaim.RelD1 (c : WfClaim) (w : List UInt8) : Prop := NearSpecV3.RelD1 c.1.encode w

def WfClaim.DomainD1 (c : WfClaim) : Prop := ∃ w, WfClaim.RelD1 c w

def challengeSpecD1 : ChallengeSpec where
  Claim := WfClaim
  Witness := List UInt8
  Rel := WfClaim.RelD1
  Domain := WfClaim.DomainD1
  decodeClaim := WfClaim.decode
  encodeClaim := WfClaim.encode
  decode_encode := WfClaim.decode_encode

def challengeParamsD1 : ChallengeParams where
  spec := challengeSpecD1
  profile := NearSpec.TransferV1.profileValidityClassical128
  verifyFuel := verifyFuelV3
  maxProofBytes := maxProofBytesV3
  maxReductionFuel := maxReductionFuelV3

end NearSpecV3
