import ArenaCore.Verifier
import NearSpecV3.ChallengeChunkV3
import ReexecV3D3.ReadCanon

/-!
The D3α reference verifier decodes the claim, executes the proved logged checker
once, and requires exact equality with the encoding of its recorded-store read
set. The ignored fields and receipt-proof entries use the canonical byte encoder.
The native-lean executable is this definition compiled by the governed compiler.
This remains witness re-execution, not a succinct state-transition proof.
-/

namespace ReexecV3D3

open NearSpecV3

def check (cb pb : ArenaCore.Bytes) : Bool :=
  match WfClaim.decode cb with
  | none => false
  | some c => Read.check c.encode pb

/-- The verifier model as an `ArenaCore.OracleVerifier`. -/
def Model.verifier : ArenaCore.OracleVerifier where
  run := fun _ hs _pub cb pb => (check cb pb, hs)

end ReexecV3D3
