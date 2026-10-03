import ArenaCore.Admission
import NearSpec.Challenge
import NearSpec.ClaimCodecV2

/-!
# The canonical `ArenaCore.ChallengeSpec` / `ChallengeParams` instance

for challenge `near-transfer-receipt-v2` (statement
`near/pv86/receipt-transfer-batch/v1`, claim format `near-arena-claim-v2`).
Same shape as v1 (`NearSpec.Challenge`): `Claim` = well-formed v2 claims,
`Rel` = `TransferV2.NearRelation`, `Domain` = the claim-level domain, strict
`claim.bin` codec with its proved round trip. The security profile helpers
(`profileOf`, ...) are v1's, reused unchanged. Resource parameters: same values
as v1 (spec doc §12): the v2 witness adds one root→`0x0f` path (≤ a few KiB).
-/

namespace NearSpec.TransferV2

open ArenaCore

def challengeSpec : ChallengeSpec where
  Claim := WfClaim
  Witness := Witness
  Rel := WfClaim.Rel
  Domain := WfClaim.ClaimDomain
  decodeClaim := WfClaim.decode
  encodeClaim := WfClaim.encode
  decode_encode := WfClaim.decode_encode

def challengeParamsWith (profile : SecurityProfile)
    (verifyFuel maxProofBytes maxReductionFuel : Nat) : ChallengeParams where
  spec := challengeSpec
  profile := profile
  verifyFuel := verifyFuel
  maxProofBytes := maxProofBytes
  maxReductionFuel := maxReductionFuel

def verifyFuelV2 : Nat := 1073741824
def maxProofBytesV2 : Nat := 8388608
def maxReductionFuelV2 : Nat := 1073741824

def challengeParams : ChallengeParams :=
  challengeParamsWith TransferV1.profileValidityClassical128 verifyFuelV2 maxProofBytesV2
    maxReductionFuelV2

theorem challengeParams_canonical :
    challengeParamsWith
      (TransferV1.profileOf "validity-classical-128" "random_oracle" 128
        ["sha256-collision-resistance", "random-oracle-fiat-shamir-sha256"] 40 64)
      1073741824 8388608 1073741824 = challengeParams := rfl

end NearSpec.TransferV2
