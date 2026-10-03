import ArenaCore
import NearSpec

/-!
# The challenge spec, as the judge assembles it

Same fields as `spec/lean/NearSpec/ClaimCodec.lean` documents for
`ArenaCore.ChallengeSpec`. Defined under `Candidate.` (no shadowing of judge
or spec names).
-/

namespace Candidate

open NearSpec.TransferV1 in
/-- `near/pv86/receipt-transfer-batch/v0` as an `ArenaCore.ChallengeSpec`. -/
def nearSpec : ArenaCore.ChallengeSpec where
  Claim := WfClaim
  Witness := Witness
  Rel := WfClaim.Rel
  Domain := WfClaim.ClaimDomain
  decodeClaim := WfClaim.decode
  encodeClaim := WfClaim.encode
  decode_encode := WfClaim.decode_encode

end Candidate
