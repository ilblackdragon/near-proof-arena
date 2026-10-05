import ArenaCore.Relation
import ArenaCore.Backend
import ArenaCore.Verifier
import NearSpec.ClaimCodec

/-!
# The challenge spec, as the judge assembles it (no shadowing: `Candidate.`)
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
