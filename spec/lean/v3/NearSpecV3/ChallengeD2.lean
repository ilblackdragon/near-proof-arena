import NearSpecV3.ChallengeV3
import NearSpecV3.ChunkValidationD2

/-!
# `ArenaCore.ChallengeSpec` instance for `near/pv86/chunk-validation/v0`, domain D2

Same `Claim` type, codec and witness format as the D0 instance (`ChallengeV3.lean`); only the
relation changes: `Rel c w = RelD2 c.encode w = Rel ∧ InD2` (spec/near-chunk-validation-d2.md).
-/

namespace NearSpecV3

open ArenaCore

def WfClaim.RelD2 (c : WfClaim) (w : List UInt8) : Prop := NearSpecV3.RelD2 c.1.encode w

def WfClaim.DomainD2 (c : WfClaim) : Prop := ∃ w, WfClaim.RelD2 c w

def challengeSpecD2 : ChallengeSpec where
  Claim := WfClaim
  Witness := List UInt8
  Rel := WfClaim.RelD2
  Domain := WfClaim.DomainD2
  decodeClaim := WfClaim.decode
  encodeClaim := WfClaim.encode
  decode_encode := WfClaim.decode_encode

def challengeParamsD2 : ChallengeParams where
  spec := challengeSpecD2
  profile := NearSpec.TransferV1.profileValidityClassical128
  verifyFuel := verifyFuelV3
  maxProofBytes := maxProofBytesV3
  maxReductionFuel := maxReductionFuelV3

end NearSpecV3
